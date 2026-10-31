-- Prove2me | solution 1 for OAI.CycleClique.patterns_17_8_0_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T22:58:49.907085+00:00
-- url     : https://prove2.me/submissions/e133c3c6-023b-4d72-9146-512d802e6ced

import Mathlib
import Definitions.Def_OAIQ107D130
import Definitions.Def_OAIQ107D133

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates070
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_2220_checked : certificate_2220.Valid 17 8 8 certificate_2220_q certificate_2220_edges 0 0 [] := by decide +kernel
theorem certificate_2220_valid : certificate_2220.Valid 17 8 (patternOrder [[],[],[],[],[],[],[],[]]) (patternClique [[],[],[],[],[],[],[],[]]) (patternEdges [[],[],[],[],[],[],[],[]]) (patternAmount [[],[],[],[],[],[],[],[]]) (patternEdgeCount [[],[],[],[],[],[],[],[]]) [] := certificate_2220_checked

theorem certificate_2221_checked : certificate_2221.Valid 17 8 9 certificate_2221_q certificate_2221_edges 1 1 [] := by decide +kernel
theorem certificate_2221_valid : certificate_2221.Valid 17 8 (patternOrder [[],[],[],[],[],[],[1]]) (patternClique [[],[],[],[],[],[],[1]]) (patternEdges [[],[],[],[],[],[],[1]]) (patternAmount [[],[],[],[],[],[],[1]]) (patternEdgeCount [[],[],[],[],[],[],[1]]) [] := certificate_2221_checked

theorem certificate_2222_checked : certificate_2222.Valid 17 8 10 certificate_2222_q certificate_2222_edges 2 1 [] := by decide +kernel
theorem certificate_2222_valid : certificate_2222.Valid 17 8 (patternOrder [[],[],[],[],[],[],[2]]) (patternClique [[],[],[],[],[],[],[2]]) (patternEdges [[],[],[],[],[],[],[2]]) (patternAmount [[],[],[],[],[],[],[2]]) (patternEdgeCount [[],[],[],[],[],[],[2]]) [] := certificate_2222_checked

theorem certificate_2223_checked : certificate_2223.Valid 17 8 11 certificate_2223_q certificate_2223_edges 3 1 [] := by decide +kernel
theorem certificate_2223_valid : certificate_2223.Valid 17 8 (patternOrder [[],[],[],[],[],[],[3]]) (patternClique [[],[],[],[],[],[],[3]]) (patternEdges [[],[],[],[],[],[],[3]]) (patternAmount [[],[],[],[],[],[],[3]]) (patternEdgeCount [[],[],[],[],[],[],[3]]) [] := certificate_2223_checked

theorem certificate_2224_checked : certificate_2224.Valid 17 8 12 certificate_2224_q certificate_2224_edges 4 1 [] := by decide +kernel
theorem certificate_2224_valid : certificate_2224.Valid 17 8 (patternOrder [[],[],[],[],[],[],[4]]) (patternClique [[],[],[],[],[],[],[4]]) (patternEdges [[],[],[],[],[],[],[4]]) (patternAmount [[],[],[],[],[],[],[4]]) (patternEdgeCount [[],[],[],[],[],[],[4]]) [] := certificate_2224_checked

theorem certificate_2225_checked : certificate_2225.Valid 17 8 13 certificate_2225_q certificate_2225_edges 5 1 [] := by decide +kernel
theorem certificate_2225_valid : certificate_2225.Valid 17 8 (patternOrder [[],[],[],[],[],[],[5]]) (patternClique [[],[],[],[],[],[],[5]]) (patternEdges [[],[],[],[],[],[],[5]]) (patternAmount [[],[],[],[],[],[],[5]]) (patternEdgeCount [[],[],[],[],[],[],[5]]) [] := certificate_2225_checked

theorem certificate_2226_checked : certificate_2226.Valid 17 8 14 certificate_2226_q certificate_2226_edges 6 1 [] := by decide +kernel
theorem certificate_2226_valid : certificate_2226.Valid 17 8 (patternOrder [[],[],[],[],[],[],[6]]) (patternClique [[],[],[],[],[],[],[6]]) (patternEdges [[],[],[],[],[],[],[6]]) (patternAmount [[],[],[],[],[],[],[6]]) (patternEdgeCount [[],[],[],[],[],[],[6]]) [] := certificate_2226_checked

theorem certificate_2227_checked : certificate_2227.Valid 17 8 15 certificate_2227_q certificate_2227_edges 7 1 [] := by decide +kernel
theorem certificate_2227_valid : certificate_2227.Valid 17 8 (patternOrder [[],[],[],[],[],[],[7]]) (patternClique [[],[],[],[],[],[],[7]]) (patternEdges [[],[],[],[],[],[],[7]]) (patternAmount [[],[],[],[],[],[],[7]]) (patternEdgeCount [[],[],[],[],[],[],[7]]) [] := certificate_2227_checked

theorem certificate_2228_checked : certificate_2228.Valid 17 8 16 certificate_2228_q certificate_2228_edges 8 1 [] := by decide +kernel
theorem certificate_2228_valid : certificate_2228.Valid 17 8 (patternOrder [[],[],[],[],[],[],[8]]) (patternClique [[],[],[],[],[],[],[8]]) (patternEdges [[],[],[],[],[],[],[8]]) (patternAmount [[],[],[],[],[],[],[8]]) (patternEdgeCount [[],[],[],[],[],[],[8]]) [] := certificate_2228_checked

theorem certificate_2229_checked : certificate_2229.Valid 17 8 17 certificate_2229_q certificate_2229_edges 9 1 [] := by decide +kernel
theorem certificate_2229_valid : certificate_2229.Valid 17 8 (patternOrder [[],[],[],[],[],[],[9]]) (patternClique [[],[],[],[],[],[],[9]]) (patternEdges [[],[],[],[],[],[],[9]]) (patternAmount [[],[],[],[],[],[],[9]]) (patternEdgeCount [[],[],[],[],[],[],[9]]) [] := certificate_2229_checked

theorem certificate_2230_checked : certificate_2230.Valid 17 8 10 certificate_2230_q certificate_2230_edges 2 2 [] := by decide +kernel
theorem certificate_2230_valid : certificate_2230.Valid 17 8 (patternOrder [[],[],[],[],[],[1,1]]) (patternClique [[],[],[],[],[],[1,1]]) (patternEdges [[],[],[],[],[],[1,1]]) (patternAmount [[],[],[],[],[],[1,1]]) (patternEdgeCount [[],[],[],[],[],[1,1]]) [] := certificate_2230_checked

theorem certificate_2231_checked : certificate_2231.Valid 17 8 11 certificate_2231_q certificate_2231_edges 3 2 [] := by decide +kernel
theorem certificate_2231_valid : certificate_2231.Valid 17 8 (patternOrder [[],[],[],[],[],[1,2]]) (patternClique [[],[],[],[],[],[1,2]]) (patternEdges [[],[],[],[],[],[1,2]]) (patternAmount [[],[],[],[],[],[1,2]]) (patternEdgeCount [[],[],[],[],[],[1,2]]) [] := certificate_2231_checked

theorem certificate_2232_checked : certificate_2232.Valid 17 8 12 certificate_2232_q certificate_2232_edges 4 2 [] := by decide +kernel
theorem certificate_2232_valid : certificate_2232.Valid 17 8 (patternOrder [[],[],[],[],[],[1,3]]) (patternClique [[],[],[],[],[],[1,3]]) (patternEdges [[],[],[],[],[],[1,3]]) (patternAmount [[],[],[],[],[],[1,3]]) (patternEdgeCount [[],[],[],[],[],[1,3]]) [] := certificate_2232_checked

theorem certificate_2233_checked : certificate_2233.Valid 17 8 13 certificate_2233_q certificate_2233_edges 5 2 [] := by decide +kernel
theorem certificate_2233_valid : certificate_2233.Valid 17 8 (patternOrder [[],[],[],[],[],[1,4]]) (patternClique [[],[],[],[],[],[1,4]]) (patternEdges [[],[],[],[],[],[1,4]]) (patternAmount [[],[],[],[],[],[1,4]]) (patternEdgeCount [[],[],[],[],[],[1,4]]) [] := certificate_2233_checked

theorem certificate_2234_checked : certificate_2234.Valid 17 8 14 certificate_2234_q certificate_2234_edges 6 2 [] := by decide +kernel
theorem certificate_2234_valid : certificate_2234.Valid 17 8 (patternOrder [[],[],[],[],[],[1,5]]) (patternClique [[],[],[],[],[],[1,5]]) (patternEdges [[],[],[],[],[],[1,5]]) (patternAmount [[],[],[],[],[],[1,5]]) (patternEdgeCount [[],[],[],[],[],[1,5]]) [] := certificate_2234_checked

theorem certificate_2235_checked : certificate_2235.Valid 17 8 15 certificate_2235_q certificate_2235_edges 7 2 [] := by decide +kernel
theorem certificate_2235_valid : certificate_2235.Valid 17 8 (patternOrder [[],[],[],[],[],[1,6]]) (patternClique [[],[],[],[],[],[1,6]]) (patternEdges [[],[],[],[],[],[1,6]]) (patternAmount [[],[],[],[],[],[1,6]]) (patternEdgeCount [[],[],[],[],[],[1,6]]) [] := certificate_2235_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns17x8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem patterns_17_8_0_verified_oai : ∀ D ∈ patterns_17_8_0, PatternVerified 17 8 D := by

  simp only [patterns_17_8_0, List.forall_mem_cons]

  exact ⟨⟨certificate_2220, certificate_2220_valid⟩, ⟨⟨certificate_2221, certificate_2221_valid⟩, ⟨⟨certificate_2222, certificate_2222_valid⟩, ⟨⟨certificate_2223, certificate_2223_valid⟩, ⟨⟨certificate_2224, certificate_2224_valid⟩, ⟨⟨certificate_2225, certificate_2225_valid⟩, ⟨⟨certificate_2226, certificate_2226_valid⟩, ⟨⟨certificate_2227, certificate_2227_valid⟩, ⟨⟨certificate_2228, certificate_2228_valid⟩, ⟨⟨certificate_2229, certificate_2229_valid⟩, ⟨⟨certificate_2230, certificate_2230_valid⟩, ⟨⟨certificate_2231, certificate_2231_valid⟩, ⟨⟨certificate_2232, certificate_2232_valid⟩, ⟨⟨certificate_2233, certificate_2233_valid⟩, ⟨⟨certificate_2234, certificate_2234_valid⟩, ⟨⟨certificate_2235, certificate_2235_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_17_8_0_verified_oai := @OAI.CycleClique.patterns_17_8_0_verified_oai
