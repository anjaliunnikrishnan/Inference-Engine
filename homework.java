import java.io.BufferedReader;
import java.io.FileReader;
import java.io.PrintWriter;
import java.util.*;

public class homework {
    public static void main(String[] args) throws Exception {
        Resolves resolution = new Resolves();
        long start = System.currentTimeMillis();
        resolution.read_input();
        long end = System.currentTimeMillis();
        // System.out.println("Time taken: " + (end - start));
    }
}

class Resolves {
    private static int postfix = 0;
    private HashMap<String, ArrayList<String>> hashMapKB = new HashMap<>();
    private String originalQuery = "";
    private String[] remainingQ;
    //private int counter = 0;
    private HashSet<String> predicatesProcessed = new HashSet<>();
    private long start;
    private final int FINAL_LIMIT = 10;
    private boolean result;

    void read_input() throws Exception {
        FileReader fileReader = new FileReader("input.txt");
        PrintWriter writer = new PrintWriter("output.txt");
        boolean flag = false;
        BufferedReader br = new BufferedReader(fileReader);
        int queryLength = Integer.parseInt(br.readLine());
        ArrayList<String> queryMatchingSentences;
        String[] query = new String[queryLength];
        for (int i = 0; i < queryLength; i++) {
            query[i] = (br.readLine());
        }
        int kbLength = Integer.parseInt(br.readLine());
        String[] knowledgeBase = new String[kbLength + 1];
        for (int i = 0; i < kbLength; i++) {
            knowledgeBase[i] = br.readLine();
        }
        knowledgeBase = standardizeVariables(knowledgeBase);
        HashMap<String, String> hm;
        makeTheKB(knowledgeBase);
        for (String q : query) {
            try {
                start = System.currentTimeMillis();
                result = false;
                predicatesProcessed.clear();
                q = negateQuery(q);
                originalQuery = q;
                addQueryToKb(q);
                queryMatchingSentences = returnQueryInKB(q);
                if (queryMatchingSentences == null || queryMatchingSentences.size() == 0) {
                    writer.println("FALSE");
                    continue;
                }
                for (String queryMatchingSentence : queryMatchingSentences) {
                    String[] queryVars = q.substring(getThePredicateTerm(q).length() + 1, q.length() - 1).split(",");
                    String[] predicates = queryMatchingSentence.split("\\|");
                    for (String predicate : predicates) {
                        if (getThePredicateTerm(negateQuery(q)).equals(getThePredicateTerm(predicate))) {
                            String[] predVars = predicate.substring(getThePredicateTerm(predicate).length() + 1,
                                    predicate.length() - 1).split(",");
                            boolean check = checkIfAllConstants(predVars, queryVars);
                            if (!check) {
                                String newQuery = notCheck(queryVars, predVars, q, predicates, null);
                                flag = resolveFurther(newQuery);
                            } else {
                                String newQuery = yesCheck(queryVars, predVars, q, predicates, null);
                                flag = resolveFurther(newQuery);
                            }
                        }
                    }
                    if (flag) break;
                }
                removeQueryFromKb(q);
                if (flag) {
                    writer.println("TRUE");
                } else {
                    writer.println("FALSE");
                }
            } catch (StackOverflowError re) {
                writer.println("FALSE");
                removeQueryFromKb(q);
            }
        }
        writer.flush();
        writer.close();
    }

    private boolean resolveFurther(String newQuery) {
        long end = System.currentTimeMillis();
        if (newQuery.isEmpty()) return true;
        else if (newQuery.equals(originalQuery) || newQuery.equals("no")) return false;
        else if ((end - start) >= FINAL_LIMIT * 1000) {
            result = true;
            return false;
        }
        if (result) return false;
        String queries[] = newQuery.split("\\|");
        for (String query : queries) {
            if (predicatesProcessed.contains(query)) {
                return false;
            }
            ArrayList<String> queryMatchingSentences = returnQueryInKB(query);
            if (queryMatchingSentences == null) {
                return false;
            }
            String partialResolvedSentence = "";
            for (String queryMatchingSentence : queryMatchingSentences) {
                String[] queryVars = query.substring(getThePredicateTerm(query).length() + 1, query.length() - 1).split(",");
                String[] predicates = queryMatchingSentence.split("\\|");
                for (String predicate : predicates) {
                    if (getThePredicateTerm(negateQuery(query)).equals(getThePredicateTerm(predicate))) {
                        String[] predVars = predicate.substring(getThePredicateTerm(predicate).length() + 1,
                                predicate.length() - 1).split(",");
                        boolean check = checkIfAllConstants(predVars, queryVars);
                        if (!check) {
                            remainingQ = null;
                            partialResolvedSentence = notCheck(queryVars, predVars, query, predicates, queries);
                            if (resolveFurther(partialResolvedSentence))
                                return true;
                        } else {
                            remainingQ = null;
                            partialResolvedSentence = yesCheck(queryVars, predVars, query, predicates, queries);
                            if (resolveFurther(partialResolvedSentence))
                                return true;
                        }
                    }
                }
                predicatesProcessed.clear();
            }
        }
        return false;
    }

    private String notCheck(String[] queryVars, String[] predVars, String query, String[] predicates, String[] remainingQueries) {
        HashMap<String, String> hm = getConstants(queryVars, predVars);
        String partialResolvedSentence = "";
        if (hm == null || hm.size() == 0) {
            predicatesProcessed.clear();
            return "no";
        }
        String partialResolvedPredicates[] = unification(query, queryVars, hm, predicates, remainingQueries);
        remainingQueries = recreateKB(remainingQ);
        query = partialResolvedPredicates[partialResolvedPredicates.length - 1];
        String[] mPredicates = new String[partialResolvedPredicates.length - 1];
        System.arraycopy(partialResolvedPredicates, 0, mPredicates, 0, partialResolvedPredicates.length - 1);
        partialResolvedSentence = resolution(query, mPredicates, remainingQueries);
        return partialResolvedSentence;

    }

    private String yesCheck(String[] queryVars, String[] predVars, String query, String[] predicates, String[] remainingQueries) {
        String partialResolvedSentence = "";
        boolean result = checkIfConstantMatch(predVars, queryVars);
        if (!result) {
            return "no";
        }
        partialResolvedSentence = resolution(query, predicates, remainingQueries);
        return partialResolvedSentence;
    }

    private boolean checkIfConstantMatch(String[] predVars, String[] queryVars) {
        for (int i = 0; i < predVars.length; i++)
            if (Character.isLowerCase(queryVars[i].charAt(0)) || Character.isLowerCase(predVars[i].charAt(0))) {
                return false;
            } else if (!predVars[i].equals(queryVars[i])) {
                return false;
            }
        return true;
    }

    private boolean checkIfAllConstants(String[] predicate, String[] query) {
        for (int i = 0; i < predicate.length; i++) {
            if (Character.isLowerCase(query[i].charAt(0)) || Character.isLowerCase(predicate[i].charAt(0)))
                return false;
        }
        return true;
    }

    private String[] unification(String query, String[] queryVariables, HashMap<String, String> hm, String[] predicates, String[] remainingQueries) {
        String newPredicate[] = new String[predicates.length + 1];
        int k = 0;
        for (String predicate : predicates) {
            String[] predVars = predicate.substring(getThePredicateTerm(predicate).length() + 1, predicate.length() - 1).split(",");
            for (int i = 0; i < predVars.length; i++)
                if (hm.containsKey(predVars[i]))
                    predVars[i] = hm.get(predVars[i]);
            StringBuilder newS = new StringBuilder();
            for (String s1 : predVars)
                newS.append(s1).append(",");
            newPredicate[k++] = (predicate.substring(0, getThePredicateTerm(predicate).length())) + ("(") + (newS.substring(0, newS.length() - 1)) + (")");
        }
        for (int i = 0; i < queryVariables.length; i++)
            if (hm.containsKey(queryVariables[i]))
                queryVariables[i] = hm.get(queryVariables[i]);
        StringBuilder newS = new StringBuilder();
        for (String s1 : queryVariables)
            newS.append(s1).append(",");
        query = (query.substring(0, getThePredicateTerm(query).length())) + ("(") + (newS.substring(0, newS.length() - 1)) + (")");
        newPredicate[predicates.length] = query;
        if (remainingQueries == null) return newPredicate;
        if (remainingQueries.length == 1 && remainingQueries[0].equals(query)) return newPredicate;
        ArrayList<String> ar = new ArrayList<>();
        for (String remainingQuery : remainingQueries) {
            String remainingQVars[] = remainingQuery.substring(getThePredicateTerm(remainingQuery).length() + 1,
                    remainingQuery.length() - 1).split(",");

            for (int k2 = 0; k2 < remainingQVars.length; k2++) {
                if (hm.containsKey(remainingQVars[k2]))
                    remainingQVars[k2] = hm.get(remainingQVars[k2]);
            }
            newS = new StringBuilder();
            for (String s1 : remainingQVars)
                newS.append(s1).append(",");
            String s = remainingQuery.substring(0, getThePredicateTerm(remainingQuery).length()) + "(" + (newS.substring(0, newS.length() - 1)) + (")");
            if (!s.equals(query))
                ar.add(s);
        }
        k = 0;
        remainingQ = new String[ar.size()];
        for (String s : ar) {
            remainingQ[k++] = s;
        }
        ar.clear();
        return newPredicate;
    }

    private HashMap<String, String> getConstants(String queryVars[], String predVars[]) {
        HashMap<String, String> hm = new HashMap<>();
        for (int q = 0; q < queryVars.length; q++) {
            if (queryVars[q].charAt(0) >= 'a' && queryVars[q].charAt(0) <= 'z' && predVars[q].charAt(0) >= 'A'
                    && predVars[q].charAt(0) <= 'Z') {
                if (hm.containsKey(queryVars[q])) {
                    return null;
                }
                if (!hm.containsKey(queryVars[q])) {
                    hm.put(queryVars[q], predVars[q]);
                }
            } else if (queryVars[q].charAt(0) >= 'A' && queryVars[q].charAt(0) <= 'Z' && predVars[q].charAt(0) >= 'a'
                    && predVars[q].charAt(0) <= 'z') {
                if (hm.containsKey(predVars[q])) {
                    return null;
                }
                if (!hm.containsKey(predVars[q])) {
                    hm.put(predVars[q], queryVars[q]);
                }
            } else if (queryVars[q].charAt(0) >= 'a' && queryVars[q].charAt(0) <= 'z' && predVars[q].charAt(0) >= 'a'
                    && predVars[q].charAt(0) <= 'z') {
                if (hm.containsKey(predVars[q])) {
                    return null;
                }
                if (!hm.containsKey(predVars[q])) {
                    hm.put(predVars[q], queryVars[q]);
                }
            } else if (queryVars[q].charAt(0) >= 'A' && queryVars[q].charAt(0) <= 'Z' && predVars[q].charAt(0) >= 'A'
                    && predVars[q].charAt(0) <= 'Z') {
                if (!queryVars[q].equals(predVars[q]))
                    return null;
            }
        }
        return hm;
    }

    private String resolution(String q, String[] predicates, String[] remainingQueries) {
        if (!predicatesProcessed.contains(q))
            predicatesProcessed.add(q);
        String newQuery = "";
        for (String predicate : predicates) {
            if (negateQuery(q).equals(predicate)) {
                StringBuilder qBuilder = new StringBuilder();
                for (String s : predicates) {
                    if (!s.equals(predicate)) {
                        qBuilder.append(s).append("|");
                    }
                }
                if (remainingQueries == null) {
                    if (qBuilder.toString().isEmpty())
                        return "";
                    return qBuilder.substring(0, qBuilder.length() - 1);
                }
                newQuery = joinSentences(predicate, remainingQueries, qBuilder);
            }
        }
        return newQuery;
    }

    private String joinSentences(String predicate, String[] remainingQueries, StringBuilder qBuilder) {
        for (String s : remainingQueries) {
            if (!s.equals(negateQuery(predicate)))
                qBuilder.append(s).append("|");
        }

        if (qBuilder.toString().isEmpty()) return "";
        return qBuilder.substring(0, qBuilder.length() - 1);
    }

    private ArrayList<String> returnQueryInKB(String q) {
        q = negateQuery(q);
        if (hashMapKB.containsKey(getThePredicateTerm(q))) {
            return hashMapKB.get(getThePredicateTerm(q));
        }
        return null;
    }

    private void makeTheKB(String[] knowledgeBase) {
        for (String sentence : knowledgeBase) {
            if (sentence == null) continue;
            String predicates[] = sentence.split("\\|");
            for (String predicate : predicates) {
                predicate = getThePredicateTerm(predicate);
                if (!hashMapKB.containsKey(predicate))
                    hashMapKB.put(predicate, allSentencesAssociatedWithPredicate(predicate, knowledgeBase));
            }
        }
    }

    private void addQueryToKb(String query) {
        String q = getThePredicateTerm(query);
        ArrayList<String> ar = new ArrayList<>();
        if (!hashMapKB.containsKey(q)) {
            ar.add(query);
            hashMapKB.put(q, ar);
        } else {
            ar = hashMapKB.get(q);
            ar.add(query);
            hashMapKB.put(q, ar);
        }
    }

    private void removeQueryFromKb(String query) {
        String q = getThePredicateTerm(query);
        ArrayList<String> ar;
        if (hashMapKB.containsKey(q)) {
            ar = hashMapKB.get(q);
            if (ar.contains(query)) {
                ar.remove(query);
                hashMapKB.put(q, ar);
            }
        }
    }

    private String getThePredicateTerm(String predicate) {
        int i = 0;
        if (predicate.isEmpty()) return "";
        while (predicate.charAt(i) != '(') i++;
        return predicate.substring(0, i);
    }

    private ArrayList<String> allSentencesAssociatedWithPredicate(String predicate, String[] knowledgeBase) {
        ArrayList<String> ar = new ArrayList<>();
        for (String sentence : knowledgeBase) {
            if (sentence == null) continue;
            String predicates[] = sentence.split("\\|");
            for (String pred : predicates) {
                if (predicate.equals(getThePredicateTerm(pred))) {
                    ar.add(sentence);
                    break;
                }
            }
        }
        return ar;
    }

    private String negateQuery(String query) {
        if (query.charAt(0) == '~') return query.substring(1);
        else return "~" + query;
    }

    private String[] standardizeVariables(String[] sentencesKB) {
        HashMap<String, String> hm = new HashMap<>();
        String[] standardizedSentence = new String[sentencesKB.length];
        int standardizeIndex = 0;
        for (String sentence : sentencesKB) {
            if (sentence == null) break;
            String[] predicates = sentence.split(" \\| ");
            StringBuilder newSentence = new StringBuilder();
            for (String predicate : predicates) {
                int i = 0;
                while (predicate.charAt(i) != '(') {
                    i++;
                }
                String[] variables = predicate.substring(i + 1, predicate.length() - 1).split(",");
                for (int k = 0; k < variables.length; k++) {
                    if (hm.containsKey(variables[k]) && (Character.isLowerCase(variables[k].charAt(0)))) {
                        variables[k] = hm.get(variables[k]);
                    } else if (Character.isLowerCase(variables[k].charAt(0))) {
                        hm.put(variables[k], variables[k] + postfix);
                        variables[k] = variables[k] + postfix;
                    }
                }
                StringBuilder newS = new StringBuilder();
                for (String s : variables)
                    newS.append(s).append(",");
                newSentence.append(predicate.substring(0, i)).append("(").append(newS.substring(0, newS.length() - 1)).append(")").append("|");
            }
            standardizedSentence[standardizeIndex++] = newSentence.substring(0, newSentence.length() - 1);
            postfix++;
            hm.clear();
        }
        hm.clear();
        return standardizedSentence;
    }

    private String[] recreateKB(String[] knowledgeBase) {
        if (knowledgeBase == null)
            return null;
        String[] originalKB = new String[knowledgeBase.length];
        int i = 0;
        for (String s : knowledgeBase)
            originalKB[i++] = s;
        return originalKB;
    }

}
