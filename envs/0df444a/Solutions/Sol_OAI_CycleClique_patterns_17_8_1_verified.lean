-- Prove2me | solution 1 for OAI.CycleClique.patterns_17_8_1_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T23:14:34.557201+00:00
-- url     : https://prove2.me/submissions/a648739d-a8c5-424b-81af-c908e8d728e5

import Mathlib
import Definitions.Def_OAIQ107D071
import Definitions.Def_OAIQ107D072
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

theorem certificate_2236_checked : certificate_2236.Valid 17 8 16 certificate_2236_q certificate_2236_edges 8 2 [] := by decide +kernel
theorem certificate_2236_valid : certificate_2236.Valid 17 8 (patternOrder [[],[],[],[],[],[1,7]]) (patternClique [[],[],[],[],[],[1,7]]) (patternEdges [[],[],[],[],[],[1,7]]) (patternAmount [[],[],[],[],[],[1,7]]) (patternEdgeCount [[],[],[],[],[],[1,7]]) [] := certificate_2236_checked

theorem certificate_2237_checked : certificate_2237.Valid 17 8 17 certificate_2237_q certificate_2237_edges 9 2 [] := by decide +kernel
theorem certificate_2237_valid : certificate_2237.Valid 17 8 (patternOrder [[],[],[],[],[],[1,8]]) (patternClique [[],[],[],[],[],[1,8]]) (patternEdges [[],[],[],[],[],[1,8]]) (patternAmount [[],[],[],[],[],[1,8]]) (patternEdgeCount [[],[],[],[],[],[1,8]]) [] := certificate_2237_checked

theorem certificate_2238_checked : certificate_2238.Valid 17 8 12 certificate_2238_q certificate_2238_edges 4 2 [] := by decide +kernel
theorem certificate_2238_valid : certificate_2238.Valid 17 8 (patternOrder [[],[],[],[],[],[2,2]]) (patternClique [[],[],[],[],[],[2,2]]) (patternEdges [[],[],[],[],[],[2,2]]) (patternAmount [[],[],[],[],[],[2,2]]) (patternEdgeCount [[],[],[],[],[],[2,2]]) [] := certificate_2238_checked

theorem certificate_2239_checked : certificate_2239.Valid 17 8 13 certificate_2239_q certificate_2239_edges 5 2 [] := by decide +kernel
theorem certificate_2239_valid : certificate_2239.Valid 17 8 (patternOrder [[],[],[],[],[],[2,3]]) (patternClique [[],[],[],[],[],[2,3]]) (patternEdges [[],[],[],[],[],[2,3]]) (patternAmount [[],[],[],[],[],[2,3]]) (patternEdgeCount [[],[],[],[],[],[2,3]]) [] := certificate_2239_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates071
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_2240_checked : certificate_2240.Valid 17 8 14 certificate_2240_q certificate_2240_edges 6 2 [] := by decide +kernel
theorem certificate_2240_valid : certificate_2240.Valid 17 8 (patternOrder [[],[],[],[],[],[2,4]]) (patternClique [[],[],[],[],[],[2,4]]) (patternEdges [[],[],[],[],[],[2,4]]) (patternAmount [[],[],[],[],[],[2,4]]) (patternEdgeCount [[],[],[],[],[],[2,4]]) [] := certificate_2240_checked

theorem certificate_2241_checked : certificate_2241.Valid 17 8 15 certificate_2241_q certificate_2241_edges 7 2 [] := by decide +kernel
theorem certificate_2241_valid : certificate_2241.Valid 17 8 (patternOrder [[],[],[],[],[],[2,5]]) (patternClique [[],[],[],[],[],[2,5]]) (patternEdges [[],[],[],[],[],[2,5]]) (patternAmount [[],[],[],[],[],[2,5]]) (patternEdgeCount [[],[],[],[],[],[2,5]]) [] := certificate_2241_checked

theorem certificate_2242_checked : certificate_2242.Valid 17 8 16 certificate_2242_q certificate_2242_edges 8 2 [] := by decide +kernel
theorem certificate_2242_valid : certificate_2242.Valid 17 8 (patternOrder [[],[],[],[],[],[2,6]]) (patternClique [[],[],[],[],[],[2,6]]) (patternEdges [[],[],[],[],[],[2,6]]) (patternAmount [[],[],[],[],[],[2,6]]) (patternEdgeCount [[],[],[],[],[],[2,6]]) [] := certificate_2242_checked

theorem certificate_2243_checked : certificate_2243.Valid 17 8 17 certificate_2243_q certificate_2243_edges 9 2 [] := by decide +kernel
theorem certificate_2243_valid : certificate_2243.Valid 17 8 (patternOrder [[],[],[],[],[],[2,7]]) (patternClique [[],[],[],[],[],[2,7]]) (patternEdges [[],[],[],[],[],[2,7]]) (patternAmount [[],[],[],[],[],[2,7]]) (patternEdgeCount [[],[],[],[],[],[2,7]]) [] := certificate_2243_checked

theorem certificate_2244_checked : certificate_2244.Valid 17 8 14 certificate_2244_q certificate_2244_edges 6 2 [] := by decide +kernel
theorem certificate_2244_valid : certificate_2244.Valid 17 8 (patternOrder [[],[],[],[],[],[3,3]]) (patternClique [[],[],[],[],[],[3,3]]) (patternEdges [[],[],[],[],[],[3,3]]) (patternAmount [[],[],[],[],[],[3,3]]) (patternEdgeCount [[],[],[],[],[],[3,3]]) [] := certificate_2244_checked

theorem certificate_2245_checked : certificate_2245.Valid 17 8 15 certificate_2245_q certificate_2245_edges 7 2 [] := by decide +kernel
theorem certificate_2245_valid : certificate_2245.Valid 17 8 (patternOrder [[],[],[],[],[],[3,4]]) (patternClique [[],[],[],[],[],[3,4]]) (patternEdges [[],[],[],[],[],[3,4]]) (patternAmount [[],[],[],[],[],[3,4]]) (patternEdgeCount [[],[],[],[],[],[3,4]]) [] := certificate_2245_checked

theorem certificate_2246_checked : certificate_2246.Valid 17 8 16 certificate_2246_q certificate_2246_edges 8 2 [] := by decide +kernel
theorem certificate_2246_valid : certificate_2246.Valid 17 8 (patternOrder [[],[],[],[],[],[3,5]]) (patternClique [[],[],[],[],[],[3,5]]) (patternEdges [[],[],[],[],[],[3,5]]) (patternAmount [[],[],[],[],[],[3,5]]) (patternEdgeCount [[],[],[],[],[],[3,5]]) [] := certificate_2246_checked

theorem certificate_2247_checked : certificate_2247.Valid 17 8 17 certificate_2247_q certificate_2247_edges 9 2 [] := by decide +kernel
theorem certificate_2247_valid : certificate_2247.Valid 17 8 (patternOrder [[],[],[],[],[],[3,6]]) (patternClique [[],[],[],[],[],[3,6]]) (patternEdges [[],[],[],[],[],[3,6]]) (patternAmount [[],[],[],[],[],[3,6]]) (patternEdgeCount [[],[],[],[],[],[3,6]]) [] := certificate_2247_checked

theorem certificate_2248_checked : certificate_2248.Valid 17 8 16 certificate_2248_q certificate_2248_edges 8 2 [] := by decide +kernel
theorem certificate_2248_valid : certificate_2248.Valid 17 8 (patternOrder [[],[],[],[],[],[4,4]]) (patternClique [[],[],[],[],[],[4,4]]) (patternEdges [[],[],[],[],[],[4,4]]) (patternAmount [[],[],[],[],[],[4,4]]) (patternEdgeCount [[],[],[],[],[],[4,4]]) [] := certificate_2248_checked

theorem certificate_2249_checked : certificate_2249.Valid 17 8 17 certificate_2249_q certificate_2249_edges 9 2 [] := by decide +kernel
theorem certificate_2249_valid : certificate_2249.Valid 17 8 (patternOrder [[],[],[],[],[],[4,5]]) (patternClique [[],[],[],[],[],[4,5]]) (patternEdges [[],[],[],[],[],[4,5]]) (patternAmount [[],[],[],[],[],[4,5]]) (patternEdgeCount [[],[],[],[],[],[4,5]]) [] := certificate_2249_checked

theorem certificate_2250_checked : certificate_2250.Valid 17 8 10 certificate_2250_q certificate_2250_edges 2 2 [] := by decide +kernel
theorem certificate_2250_valid : certificate_2250.Valid 17 8 (patternOrder [[],[],[],[],[1],[1]]) (patternClique [[],[],[],[],[1],[1]]) (patternEdges [[],[],[],[],[1],[1]]) (patternAmount [[],[],[],[],[1],[1]]) (patternEdgeCount [[],[],[],[],[1],[1]]) [] := certificate_2250_checked

theorem certificate_2251_checked : certificate_2251.Valid 17 8 11 certificate_2251_q certificate_2251_edges 3 2 [] := by decide +kernel
theorem certificate_2251_valid : certificate_2251.Valid 17 8 (patternOrder [[],[],[],[],[1],[2]]) (patternClique [[],[],[],[],[1],[2]]) (patternEdges [[],[],[],[],[1],[2]]) (patternAmount [[],[],[],[],[1],[2]]) (patternEdgeCount [[],[],[],[],[1],[2]]) [] := certificate_2251_checked

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

theorem patterns_17_8_1_verified_oai : ∀ D ∈ patterns_17_8_1, PatternVerified 17 8 D := by

  simp only [patterns_17_8_1, List.forall_mem_cons]

  exact ⟨⟨certificate_2236, certificate_2236_valid⟩, ⟨⟨certificate_2237, certificate_2237_valid⟩, ⟨⟨certificate_2238, certificate_2238_valid⟩, ⟨⟨certificate_2239, certificate_2239_valid⟩, ⟨⟨certificate_2240, certificate_2240_valid⟩, ⟨⟨certificate_2241, certificate_2241_valid⟩, ⟨⟨certificate_2242, certificate_2242_valid⟩, ⟨⟨certificate_2243, certificate_2243_valid⟩, ⟨⟨certificate_2244, certificate_2244_valid⟩, ⟨⟨certificate_2245, certificate_2245_valid⟩, ⟨⟨certificate_2246, certificate_2246_valid⟩, ⟨⟨certificate_2247, certificate_2247_valid⟩, ⟨⟨certificate_2248, certificate_2248_valid⟩, ⟨⟨certificate_2249, certificate_2249_valid⟩, ⟨⟨certificate_2250, certificate_2250_valid⟩, ⟨⟨certificate_2251, certificate_2251_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_17_8_1_verified_oai := @OAI.CycleClique.patterns_17_8_1_verified_oai
