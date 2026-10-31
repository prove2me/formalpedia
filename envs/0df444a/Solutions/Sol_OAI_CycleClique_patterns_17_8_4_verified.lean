-- Prove2me | solution 1 for OAI.CycleClique.patterns_17_8_4_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T23:56:32.38556+00:00
-- url     : https://prove2.me/submissions/4f357c40-c41b-44d5-8309-e9f7c45e10f2

import Mathlib
import Definitions.Def_OAIQ107D073
import Definitions.Def_OAIQ107D133

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates072
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_2284_checked : certificate_2284.Valid 17 8 17 certificate_2284_q certificate_2284_edges 9 3 [] := by decide +kernel
theorem certificate_2284_valid : certificate_2284.Valid 17 8 (patternOrder [[],[],[],[],[1,6,2]]) (patternClique [[],[],[],[],[1,6,2]]) (patternEdges [[],[],[],[],[1,6,2]]) (patternAmount [[],[],[],[],[1,6,2]]) (patternEdgeCount [[],[],[],[],[1,6,2]]) [] := certificate_2284_checked

theorem certificate_2285_checked : certificate_2285.Valid 17 8 17 certificate_2285_q certificate_2285_edges 9 3 [] := by decide +kernel
theorem certificate_2285_valid : certificate_2285.Valid 17 8 (patternOrder [[],[],[],[],[1,7,1]]) (patternClique [[],[],[],[],[1,7,1]]) (patternEdges [[],[],[],[],[1,7,1]]) (patternAmount [[],[],[],[],[1,7,1]]) (patternEdgeCount [[],[],[],[],[1,7,1]]) [] := certificate_2285_checked

theorem certificate_2286_checked : certificate_2286.Valid 17 8 12 certificate_2286_q certificate_2286_edges 4 2 [] := by decide +kernel
theorem certificate_2286_valid : certificate_2286.Valid 17 8 (patternOrder [[],[],[],[],[2],[2]]) (patternClique [[],[],[],[],[2],[2]]) (patternEdges [[],[],[],[],[2],[2]]) (patternAmount [[],[],[],[],[2],[2]]) (patternEdgeCount [[],[],[],[],[2],[2]]) [] := certificate_2286_checked

theorem certificate_2287_checked : certificate_2287.Valid 17 8 13 certificate_2287_q certificate_2287_edges 5 2 [] := by decide +kernel
theorem certificate_2287_valid : certificate_2287.Valid 17 8 (patternOrder [[],[],[],[],[2],[3]]) (patternClique [[],[],[],[],[2],[3]]) (patternEdges [[],[],[],[],[2],[3]]) (patternAmount [[],[],[],[],[2],[3]]) (patternEdgeCount [[],[],[],[],[2],[3]]) [] := certificate_2287_checked

theorem certificate_2288_checked : certificate_2288.Valid 17 8 14 certificate_2288_q certificate_2288_edges 6 2 [] := by decide +kernel
theorem certificate_2288_valid : certificate_2288.Valid 17 8 (patternOrder [[],[],[],[],[2],[4]]) (patternClique [[],[],[],[],[2],[4]]) (patternEdges [[],[],[],[],[2],[4]]) (patternAmount [[],[],[],[],[2],[4]]) (patternEdgeCount [[],[],[],[],[2],[4]]) [] := certificate_2288_checked

theorem certificate_2289_checked : certificate_2289.Valid 17 8 15 certificate_2289_q certificate_2289_edges 7 2 [] := by decide +kernel
theorem certificate_2289_valid : certificate_2289.Valid 17 8 (patternOrder [[],[],[],[],[2],[5]]) (patternClique [[],[],[],[],[2],[5]]) (patternEdges [[],[],[],[],[2],[5]]) (patternAmount [[],[],[],[],[2],[5]]) (patternEdgeCount [[],[],[],[],[2],[5]]) [] := certificate_2289_checked

theorem certificate_2290_checked : certificate_2290.Valid 17 8 16 certificate_2290_q certificate_2290_edges 8 2 [] := by decide +kernel
theorem certificate_2290_valid : certificate_2290.Valid 17 8 (patternOrder [[],[],[],[],[2],[6]]) (patternClique [[],[],[],[],[2],[6]]) (patternEdges [[],[],[],[],[2],[6]]) (patternAmount [[],[],[],[],[2],[6]]) (patternEdgeCount [[],[],[],[],[2],[6]]) [] := certificate_2290_checked

theorem certificate_2291_checked : certificate_2291.Valid 17 8 17 certificate_2291_q certificate_2291_edges 9 2 [] := by decide +kernel
theorem certificate_2291_valid : certificate_2291.Valid 17 8 (patternOrder [[],[],[],[],[2],[7]]) (patternClique [[],[],[],[],[2],[7]]) (patternEdges [[],[],[],[],[2],[7]]) (patternAmount [[],[],[],[],[2],[7]]) (patternEdgeCount [[],[],[],[],[2],[7]]) [] := certificate_2291_checked

theorem certificate_2292_checked : certificate_2292.Valid 17 8 13 certificate_2292_q certificate_2292_edges 5 3 [] := by decide +kernel
theorem certificate_2292_valid : certificate_2292.Valid 17 8 (patternOrder [[],[],[],[],[2,1,2]]) (patternClique [[],[],[],[],[2,1,2]]) (patternEdges [[],[],[],[],[2,1,2]]) (patternAmount [[],[],[],[],[2,1,2]]) (patternEdgeCount [[],[],[],[],[2,1,2]]) [] := certificate_2292_checked

theorem certificate_2293_checked : certificate_2293.Valid 17 8 14 certificate_2293_q certificate_2293_edges 6 3 [] := by decide +kernel
theorem certificate_2293_valid : certificate_2293.Valid 17 8 (patternOrder [[],[],[],[],[2,1,3]]) (patternClique [[],[],[],[],[2,1,3]]) (patternEdges [[],[],[],[],[2,1,3]]) (patternAmount [[],[],[],[],[2,1,3]]) (patternEdgeCount [[],[],[],[],[2,1,3]]) [] := certificate_2293_checked

theorem certificate_2294_checked : certificate_2294.Valid 17 8 15 certificate_2294_q certificate_2294_edges 7 3 [] := by decide +kernel
theorem certificate_2294_valid : certificate_2294.Valid 17 8 (patternOrder [[],[],[],[],[2,1,4]]) (patternClique [[],[],[],[],[2,1,4]]) (patternEdges [[],[],[],[],[2,1,4]]) (patternAmount [[],[],[],[],[2,1,4]]) (patternEdgeCount [[],[],[],[],[2,1,4]]) [] := certificate_2294_checked

theorem certificate_2295_checked : certificate_2295.Valid 17 8 16 certificate_2295_q certificate_2295_edges 8 3 [] := by decide +kernel
theorem certificate_2295_valid : certificate_2295.Valid 17 8 (patternOrder [[],[],[],[],[2,1,5]]) (patternClique [[],[],[],[],[2,1,5]]) (patternEdges [[],[],[],[],[2,1,5]]) (patternAmount [[],[],[],[],[2,1,5]]) (patternEdgeCount [[],[],[],[],[2,1,5]]) [] := certificate_2295_checked

theorem certificate_2296_checked : certificate_2296.Valid 17 8 17 certificate_2296_q certificate_2296_edges 9 3 [] := by decide +kernel
theorem certificate_2296_valid : certificate_2296.Valid 17 8 (patternOrder [[],[],[],[],[2,1,6]]) (patternClique [[],[],[],[],[2,1,6]]) (patternEdges [[],[],[],[],[2,1,6]]) (patternAmount [[],[],[],[],[2,1,6]]) (patternEdgeCount [[],[],[],[],[2,1,6]]) [] := certificate_2296_checked

theorem certificate_2297_checked : certificate_2297.Valid 17 8 14 certificate_2297_q certificate_2297_edges 6 3 [] := by decide +kernel
theorem certificate_2297_valid : certificate_2297.Valid 17 8 (patternOrder [[],[],[],[],[2,2,2]]) (patternClique [[],[],[],[],[2,2,2]]) (patternEdges [[],[],[],[],[2,2,2]]) (patternAmount [[],[],[],[],[2,2,2]]) (patternEdgeCount [[],[],[],[],[2,2,2]]) [] := certificate_2297_checked

theorem certificate_2298_checked : certificate_2298.Valid 17 8 15 certificate_2298_q certificate_2298_edges 7 3 [] := by decide +kernel
theorem certificate_2298_valid : certificate_2298.Valid 17 8 (patternOrder [[],[],[],[],[2,2,3]]) (patternClique [[],[],[],[],[2,2,3]]) (patternEdges [[],[],[],[],[2,2,3]]) (patternAmount [[],[],[],[],[2,2,3]]) (patternEdgeCount [[],[],[],[],[2,2,3]]) [] := certificate_2298_checked

theorem certificate_2299_checked : certificate_2299.Valid 17 8 16 certificate_2299_q certificate_2299_edges 8 3 [] := by decide +kernel
theorem certificate_2299_valid : certificate_2299.Valid 17 8 (patternOrder [[],[],[],[],[2,2,4]]) (patternClique [[],[],[],[],[2,2,4]]) (patternEdges [[],[],[],[],[2,2,4]]) (patternAmount [[],[],[],[],[2,2,4]]) (patternEdgeCount [[],[],[],[],[2,2,4]]) [] := certificate_2299_checked

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

theorem patterns_17_8_4_verified_oai : ∀ D ∈ patterns_17_8_4, PatternVerified 17 8 D := by

  simp only [patterns_17_8_4, List.forall_mem_cons]

  exact ⟨⟨certificate_2284, certificate_2284_valid⟩, ⟨⟨certificate_2285, certificate_2285_valid⟩, ⟨⟨certificate_2286, certificate_2286_valid⟩, ⟨⟨certificate_2287, certificate_2287_valid⟩, ⟨⟨certificate_2288, certificate_2288_valid⟩, ⟨⟨certificate_2289, certificate_2289_valid⟩, ⟨⟨certificate_2290, certificate_2290_valid⟩, ⟨⟨certificate_2291, certificate_2291_valid⟩, ⟨⟨certificate_2292, certificate_2292_valid⟩, ⟨⟨certificate_2293, certificate_2293_valid⟩, ⟨⟨certificate_2294, certificate_2294_valid⟩, ⟨⟨certificate_2295, certificate_2295_valid⟩, ⟨⟨certificate_2296, certificate_2296_valid⟩, ⟨⟨certificate_2297, certificate_2297_valid⟩, ⟨⟨certificate_2298, certificate_2298_valid⟩, ⟨⟨certificate_2299, certificate_2299_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_17_8_4_verified_oai := @OAI.CycleClique.patterns_17_8_4_verified_oai
