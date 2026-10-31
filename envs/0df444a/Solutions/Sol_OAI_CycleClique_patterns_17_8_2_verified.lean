-- Prove2me | solution 1 for OAI.CycleClique.patterns_17_8_2_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T23:27:44.788905+00:00
-- url     : https://prove2.me/submissions/6945e364-63c6-4857-acf0-7fcd19e24034

import Mathlib
import Definitions.Def_OAIQ107D072
import Definitions.Def_OAIQ107D133

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates071
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_2252_checked : certificate_2252.Valid 17 8 12 certificate_2252_q certificate_2252_edges 4 2 [] := by decide +kernel
theorem certificate_2252_valid : certificate_2252.Valid 17 8 (patternOrder [[],[],[],[],[1],[3]]) (patternClique [[],[],[],[],[1],[3]]) (patternEdges [[],[],[],[],[1],[3]]) (patternAmount [[],[],[],[],[1],[3]]) (patternEdgeCount [[],[],[],[],[1],[3]]) [] := certificate_2252_checked

theorem certificate_2253_checked : certificate_2253.Valid 17 8 13 certificate_2253_q certificate_2253_edges 5 2 [] := by decide +kernel
theorem certificate_2253_valid : certificate_2253.Valid 17 8 (patternOrder [[],[],[],[],[1],[4]]) (patternClique [[],[],[],[],[1],[4]]) (patternEdges [[],[],[],[],[1],[4]]) (patternAmount [[],[],[],[],[1],[4]]) (patternEdgeCount [[],[],[],[],[1],[4]]) [] := certificate_2253_checked

theorem certificate_2254_checked : certificate_2254.Valid 17 8 14 certificate_2254_q certificate_2254_edges 6 2 [] := by decide +kernel
theorem certificate_2254_valid : certificate_2254.Valid 17 8 (patternOrder [[],[],[],[],[1],[5]]) (patternClique [[],[],[],[],[1],[5]]) (patternEdges [[],[],[],[],[1],[5]]) (patternAmount [[],[],[],[],[1],[5]]) (patternEdgeCount [[],[],[],[],[1],[5]]) [] := certificate_2254_checked

theorem certificate_2255_checked : certificate_2255.Valid 17 8 15 certificate_2255_q certificate_2255_edges 7 2 [] := by decide +kernel
theorem certificate_2255_valid : certificate_2255.Valid 17 8 (patternOrder [[],[],[],[],[1],[6]]) (patternClique [[],[],[],[],[1],[6]]) (patternEdges [[],[],[],[],[1],[6]]) (patternAmount [[],[],[],[],[1],[6]]) (patternEdgeCount [[],[],[],[],[1],[6]]) [] := certificate_2255_checked

theorem certificate_2256_checked : certificate_2256.Valid 17 8 16 certificate_2256_q certificate_2256_edges 8 2 [] := by decide +kernel
theorem certificate_2256_valid : certificate_2256.Valid 17 8 (patternOrder [[],[],[],[],[1],[7]]) (patternClique [[],[],[],[],[1],[7]]) (patternEdges [[],[],[],[],[1],[7]]) (patternAmount [[],[],[],[],[1],[7]]) (patternEdgeCount [[],[],[],[],[1],[7]]) [] := certificate_2256_checked

theorem certificate_2257_checked : certificate_2257.Valid 17 8 17 certificate_2257_q certificate_2257_edges 9 2 [] := by decide +kernel
theorem certificate_2257_valid : certificate_2257.Valid 17 8 (patternOrder [[],[],[],[],[1],[8]]) (patternClique [[],[],[],[],[1],[8]]) (patternEdges [[],[],[],[],[1],[8]]) (patternAmount [[],[],[],[],[1],[8]]) (patternEdgeCount [[],[],[],[],[1],[8]]) [] := certificate_2257_checked

theorem certificate_2258_checked : certificate_2258.Valid 17 8 11 certificate_2258_q certificate_2258_edges 3 3 [] := by decide +kernel
theorem certificate_2258_valid : certificate_2258.Valid 17 8 (patternOrder [[],[],[],[],[1,1,1]]) (patternClique [[],[],[],[],[1,1,1]]) (patternEdges [[],[],[],[],[1,1,1]]) (patternAmount [[],[],[],[],[1,1,1]]) (patternEdgeCount [[],[],[],[],[1,1,1]]) [] := certificate_2258_checked

theorem certificate_2259_checked : certificate_2259.Valid 17 8 12 certificate_2259_q certificate_2259_edges 4 3 [] := by decide +kernel
theorem certificate_2259_valid : certificate_2259.Valid 17 8 (patternOrder [[],[],[],[],[1,1,2]]) (patternClique [[],[],[],[],[1,1,2]]) (patternEdges [[],[],[],[],[1,1,2]]) (patternAmount [[],[],[],[],[1,1,2]]) (patternEdgeCount [[],[],[],[],[1,1,2]]) [] := certificate_2259_checked

theorem certificate_2260_checked : certificate_2260.Valid 17 8 13 certificate_2260_q certificate_2260_edges 5 3 [] := by decide +kernel
theorem certificate_2260_valid : certificate_2260.Valid 17 8 (patternOrder [[],[],[],[],[1,1,3]]) (patternClique [[],[],[],[],[1,1,3]]) (patternEdges [[],[],[],[],[1,1,3]]) (patternAmount [[],[],[],[],[1,1,3]]) (patternEdgeCount [[],[],[],[],[1,1,3]]) [] := certificate_2260_checked

theorem certificate_2261_checked : certificate_2261.Valid 17 8 14 certificate_2261_q certificate_2261_edges 6 3 [] := by decide +kernel
theorem certificate_2261_valid : certificate_2261.Valid 17 8 (patternOrder [[],[],[],[],[1,1,4]]) (patternClique [[],[],[],[],[1,1,4]]) (patternEdges [[],[],[],[],[1,1,4]]) (patternAmount [[],[],[],[],[1,1,4]]) (patternEdgeCount [[],[],[],[],[1,1,4]]) [] := certificate_2261_checked

theorem certificate_2262_checked : certificate_2262.Valid 17 8 15 certificate_2262_q certificate_2262_edges 7 3 [] := by decide +kernel
theorem certificate_2262_valid : certificate_2262.Valid 17 8 (patternOrder [[],[],[],[],[1,1,5]]) (patternClique [[],[],[],[],[1,1,5]]) (patternEdges [[],[],[],[],[1,1,5]]) (patternAmount [[],[],[],[],[1,1,5]]) (patternEdgeCount [[],[],[],[],[1,1,5]]) [] := certificate_2262_checked

theorem certificate_2263_checked : certificate_2263.Valid 17 8 16 certificate_2263_q certificate_2263_edges 8 3 [] := by decide +kernel
theorem certificate_2263_valid : certificate_2263.Valid 17 8 (patternOrder [[],[],[],[],[1,1,6]]) (patternClique [[],[],[],[],[1,1,6]]) (patternEdges [[],[],[],[],[1,1,6]]) (patternAmount [[],[],[],[],[1,1,6]]) (patternEdgeCount [[],[],[],[],[1,1,6]]) [] := certificate_2263_checked

theorem certificate_2264_checked : certificate_2264.Valid 17 8 17 certificate_2264_q certificate_2264_edges 9 3 [] := by decide +kernel
theorem certificate_2264_valid : certificate_2264.Valid 17 8 (patternOrder [[],[],[],[],[1,1,7]]) (patternClique [[],[],[],[],[1,1,7]]) (patternEdges [[],[],[],[],[1,1,7]]) (patternAmount [[],[],[],[],[1,1,7]]) (patternEdgeCount [[],[],[],[],[1,1,7]]) [] := certificate_2264_checked

theorem certificate_2265_checked : certificate_2265.Valid 17 8 12 certificate_2265_q certificate_2265_edges 4 3 [] := by decide +kernel
theorem certificate_2265_valid : certificate_2265.Valid 17 8 (patternOrder [[],[],[],[],[1,2,1]]) (patternClique [[],[],[],[],[1,2,1]]) (patternEdges [[],[],[],[],[1,2,1]]) (patternAmount [[],[],[],[],[1,2,1]]) (patternEdgeCount [[],[],[],[],[1,2,1]]) [] := certificate_2265_checked

theorem certificate_2266_checked : certificate_2266.Valid 17 8 13 certificate_2266_q certificate_2266_edges 5 3 [] := by decide +kernel
theorem certificate_2266_valid : certificate_2266.Valid 17 8 (patternOrder [[],[],[],[],[1,2,2]]) (patternClique [[],[],[],[],[1,2,2]]) (patternEdges [[],[],[],[],[1,2,2]]) (patternAmount [[],[],[],[],[1,2,2]]) (patternEdgeCount [[],[],[],[],[1,2,2]]) [] := certificate_2266_checked

theorem certificate_2267_checked : certificate_2267.Valid 17 8 14 certificate_2267_q certificate_2267_edges 6 3 [] := by decide +kernel
theorem certificate_2267_valid : certificate_2267.Valid 17 8 (patternOrder [[],[],[],[],[1,2,3]]) (patternClique [[],[],[],[],[1,2,3]]) (patternEdges [[],[],[],[],[1,2,3]]) (patternAmount [[],[],[],[],[1,2,3]]) (patternEdgeCount [[],[],[],[],[1,2,3]]) [] := certificate_2267_checked

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

theorem patterns_17_8_2_verified_oai : ∀ D ∈ patterns_17_8_2, PatternVerified 17 8 D := by

  simp only [patterns_17_8_2, List.forall_mem_cons]

  exact ⟨⟨certificate_2252, certificate_2252_valid⟩, ⟨⟨certificate_2253, certificate_2253_valid⟩, ⟨⟨certificate_2254, certificate_2254_valid⟩, ⟨⟨certificate_2255, certificate_2255_valid⟩, ⟨⟨certificate_2256, certificate_2256_valid⟩, ⟨⟨certificate_2257, certificate_2257_valid⟩, ⟨⟨certificate_2258, certificate_2258_valid⟩, ⟨⟨certificate_2259, certificate_2259_valid⟩, ⟨⟨certificate_2260, certificate_2260_valid⟩, ⟨⟨certificate_2261, certificate_2261_valid⟩, ⟨⟨certificate_2262, certificate_2262_valid⟩, ⟨⟨certificate_2263, certificate_2263_valid⟩, ⟨⟨certificate_2264, certificate_2264_valid⟩, ⟨⟨certificate_2265, certificate_2265_valid⟩, ⟨⟨certificate_2266, certificate_2266_valid⟩, ⟨⟨certificate_2267, certificate_2267_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_17_8_2_verified_oai := @OAI.CycleClique.patterns_17_8_2_verified_oai
