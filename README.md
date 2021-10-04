This is a readable Coq formalisation of two variants of Diaconescu's
theorem.

1. Predicate extensionality and the relativised axiom of choice
   together imply the excluded middle axiom.

   The proof is carried out entirely within the "higher-order logic"
   fragment of Coq. No inductive types are used except booleans,
   logical connectives and equality.

   As an intermediate step, we prove that the relativised axiom of
   choice implies decidability of equality.
2. Predicate extensionality and the axiom of choice together imply the
   excluded middle axiom.

   The proof must use some features of Coq's logic which go beyond
   higher-order logic. A single use of subset types suffices.

   As an intermediate step, we show that proof irrelevance and the
   axiom of choice together imply decidability of equality.

The formalisation is based on the paper: N. Goodman, J. Myhill,
"[Choice implies excluded middle](https://doi.org/10.1002/malq.19780242514)",
Zeitschrift für mathematische Logik und Grundlagen der Mathematik
24:461 (1978)
