-- Prove2me | solution 1 for OAI.CycleClique.patterns_17_8_22_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T23:23:20.60167+00:00
-- url     : https://prove2.me/submissions/dee2ca59-46cc-495f-8b83-2bb100e2c296

import Mathlib
import Definitions.Def_OAIQ107D131
import Definitions.Def_OAIQ107D133

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates081
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_2572_checked : certificate_2572.Valid 17 8 16 certificate_2572_q certificate_2572_edges 8 5 [] := by decide +kernel
theorem certificate_2572_valid : certificate_2572.Valid 17 8 (patternOrder [[],[],[1,2,2,1,2]]) (patternClique [[],[],[1,2,2,1,2]]) (patternEdges [[],[],[1,2,2,1,2]]) (patternAmount [[],[],[1,2,2,1,2]]) (patternEdgeCount [[],[],[1,2,2,1,2]]) [] := certificate_2572_checked

theorem certificate_2573_checked : certificate_2573.Valid 17 8 17 certificate_2573_q certificate_2573_edges 9 5 [] := by decide +kernel
theorem certificate_2573_valid : certificate_2573.Valid 17 8 (patternOrder [[],[],[1,2,2,1,3]]) (patternClique [[],[],[1,2,2,1,3]]) (patternEdges [[],[],[1,2,2,1,3]]) (patternAmount [[],[],[1,2,2,1,3]]) (patternEdgeCount [[],[],[1,2,2,1,3]]) [] := certificate_2573_checked

theorem certificate_2574_checked : certificate_2574.Valid 17 8 16 certificate_2574_q certificate_2574_edges 8 5 [] := by decide +kernel
theorem certificate_2574_valid : certificate_2574.Valid 17 8 (patternOrder [[],[],[1,2,2,2,1]]) (patternClique [[],[],[1,2,2,2,1]]) (patternEdges [[],[],[1,2,2,2,1]]) (patternAmount [[],[],[1,2,2,2,1]]) (patternEdgeCount [[],[],[1,2,2,2,1]]) [] := certificate_2574_checked

theorem certificate_2575_checked : certificate_2575.Valid 17 8 17 certificate_2575_q certificate_2575_edges 9 5 [] := by decide +kernel
theorem certificate_2575_valid : certificate_2575.Valid 17 8 (patternOrder [[],[],[1,2,2,2,2]]) (patternClique [[],[],[1,2,2,2,2]]) (patternEdges [[],[],[1,2,2,2,2]]) (patternAmount [[],[],[1,2,2,2,2]]) (patternEdgeCount [[],[],[1,2,2,2,2]]) [] := certificate_2575_checked

theorem certificate_2576_checked : certificate_2576.Valid 17 8 17 certificate_2576_q certificate_2576_edges 9 5 [] := by decide +kernel
theorem certificate_2576_valid : certificate_2576.Valid 17 8 (patternOrder [[],[],[1,2,2,3,1]]) (patternClique [[],[],[1,2,2,3,1]]) (patternEdges [[],[],[1,2,2,3,1]]) (patternAmount [[],[],[1,2,2,3,1]]) (patternEdgeCount [[],[],[1,2,2,3,1]]) [] := certificate_2576_checked

theorem certificate_2577_checked : certificate_2577.Valid 17 8 16 certificate_2577_q certificate_2577_edges 8 4 [] := by decide +kernel
theorem certificate_2577_valid : certificate_2577.Valid 17 8 (patternOrder [[],[],[1,2,3],[2]]) (patternClique [[],[],[1,2,3],[2]]) (patternEdges [[],[],[1,2,3],[2]]) (patternAmount [[],[],[1,2,3],[2]]) (patternEdgeCount [[],[],[1,2,3],[2]]) [] := certificate_2577_checked

theorem certificate_2578_checked : certificate_2578.Valid 17 8 17 certificate_2578_q certificate_2578_edges 9 4 [] := by decide +kernel
theorem certificate_2578_valid : certificate_2578.Valid 17 8 (patternOrder [[],[],[1,2,3],[3]]) (patternClique [[],[],[1,2,3],[3]]) (patternEdges [[],[],[1,2,3],[3]]) (patternAmount [[],[],[1,2,3],[3]]) (patternEdgeCount [[],[],[1,2,3],[3]]) [] := certificate_2578_checked

theorem certificate_2579_checked : certificate_2579.Valid 17 8 17 certificate_2579_q certificate_2579_edges 9 5 [] := by decide +kernel
theorem certificate_2579_valid : certificate_2579.Valid 17 8 (patternOrder [[],[],[1,2,3,1,2]]) (patternClique [[],[],[1,2,3,1,2]]) (patternEdges [[],[],[1,2,3,1,2]]) (patternAmount [[],[],[1,2,3,1,2]]) (patternEdgeCount [[],[],[1,2,3,1,2]]) [] := certificate_2579_checked

theorem certificate_2580_checked : certificate_2580.Valid 17 8 17 certificate_2580_q certificate_2580_edges 9 5 [] := by decide +kernel
theorem certificate_2580_valid : certificate_2580.Valid 17 8 (patternOrder [[],[],[1,2,3,2,1]]) (patternClique [[],[],[1,2,3,2,1]]) (patternEdges [[],[],[1,2,3,2,1]]) (patternAmount [[],[],[1,2,3,2,1]]) (patternEdgeCount [[],[],[1,2,3,2,1]]) [] := certificate_2580_checked

theorem certificate_2581_checked : certificate_2581.Valid 17 8 17 certificate_2581_q certificate_2581_edges 9 4 [] := by decide +kernel
theorem certificate_2581_valid : certificate_2581.Valid 17 8 (patternOrder [[],[],[1,2,4],[2]]) (patternClique [[],[],[1,2,4],[2]]) (patternEdges [[],[],[1,2,4],[2]]) (patternAmount [[],[],[1,2,4],[2]]) (patternEdgeCount [[],[],[1,2,4],[2]]) [] := certificate_2581_checked

theorem certificate_2582_checked : certificate_2582.Valid 17 8 16 certificate_2582_q certificate_2582_edges 8 4 [] := by decide +kernel
theorem certificate_2582_valid : certificate_2582.Valid 17 8 (patternOrder [[],[],[1,3],[1,3]]) (patternClique [[],[],[1,3],[1,3]]) (patternEdges [[],[],[1,3],[1,3]]) (patternAmount [[],[],[1,3],[1,3]]) (patternEdgeCount [[],[],[1,3],[1,3]]) [] := certificate_2582_checked

theorem certificate_2583_checked : certificate_2583.Valid 17 8 17 certificate_2583_q certificate_2583_edges 9 4 [] := by decide +kernel
theorem certificate_2583_valid : certificate_2583.Valid 17 8 (patternOrder [[],[],[1,3],[1,4]]) (patternClique [[],[],[1,3],[1,4]]) (patternEdges [[],[],[1,3],[1,4]]) (patternAmount [[],[],[1,3],[1,4]]) (patternEdgeCount [[],[],[1,3],[1,4]]) [] := certificate_2583_checked

theorem certificate_2584_checked : certificate_2584.Valid 17 8 16 certificate_2584_q certificate_2584_edges 8 4 [] := by decide +kernel
theorem certificate_2584_valid : certificate_2584.Valid 17 8 (patternOrder [[],[],[1,3],[2,2]]) (patternClique [[],[],[1,3],[2,2]]) (patternEdges [[],[],[1,3],[2,2]]) (patternAmount [[],[],[1,3],[2,2]]) (patternEdgeCount [[],[],[1,3],[2,2]]) [] := certificate_2584_checked

theorem certificate_2585_checked : certificate_2585.Valid 17 8 17 certificate_2585_q certificate_2585_edges 9 4 [] := by decide +kernel
theorem certificate_2585_valid : certificate_2585.Valid 17 8 (patternOrder [[],[],[1,3],[2,3]]) (patternClique [[],[],[1,3],[2,3]]) (patternEdges [[],[],[1,3],[2,3]]) (patternAmount [[],[],[1,3],[2,3]]) (patternEdgeCount [[],[],[1,3],[2,3]]) [] := certificate_2585_checked

theorem certificate_2586_checked : certificate_2586.Valid 17 8 15 certificate_2586_q certificate_2586_edges 7 4 [] := by decide +kernel
theorem certificate_2586_valid : certificate_2586.Valid 17 8 (patternOrder [[],[],[1,3,1],[2]]) (patternClique [[],[],[1,3,1],[2]]) (patternEdges [[],[],[1,3,1],[2]]) (patternAmount [[],[],[1,3,1],[2]]) (patternEdgeCount [[],[],[1,3,1],[2]]) [] := certificate_2586_checked

theorem certificate_2587_checked : certificate_2587.Valid 17 8 16 certificate_2587_q certificate_2587_edges 8 4 [] := by decide +kernel
theorem certificate_2587_valid : certificate_2587.Valid 17 8 (patternOrder [[],[],[1,3,1],[3]]) (patternClique [[],[],[1,3,1],[3]]) (patternEdges [[],[],[1,3,1],[3]]) (patternAmount [[],[],[1,3,1],[3]]) (patternEdgeCount [[],[],[1,3,1],[3]]) [] := certificate_2587_checked

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

theorem patterns_17_8_22_verified_oai : ∀ D ∈ patterns_17_8_22, PatternVerified 17 8 D := by

  simp only [patterns_17_8_22, List.forall_mem_cons]

  exact ⟨⟨certificate_2572, certificate_2572_valid⟩, ⟨⟨certificate_2573, certificate_2573_valid⟩, ⟨⟨certificate_2574, certificate_2574_valid⟩, ⟨⟨certificate_2575, certificate_2575_valid⟩, ⟨⟨certificate_2576, certificate_2576_valid⟩, ⟨⟨certificate_2577, certificate_2577_valid⟩, ⟨⟨certificate_2578, certificate_2578_valid⟩, ⟨⟨certificate_2579, certificate_2579_valid⟩, ⟨⟨certificate_2580, certificate_2580_valid⟩, ⟨⟨certificate_2581, certificate_2581_valid⟩, ⟨⟨certificate_2582, certificate_2582_valid⟩, ⟨⟨certificate_2583, certificate_2583_valid⟩, ⟨⟨certificate_2584, certificate_2584_valid⟩, ⟨⟨certificate_2585, certificate_2585_valid⟩, ⟨⟨certificate_2586, certificate_2586_valid⟩, ⟨⟨certificate_2587, certificate_2587_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_17_8_22_verified_oai := @OAI.CycleClique.patterns_17_8_22_verified_oai
