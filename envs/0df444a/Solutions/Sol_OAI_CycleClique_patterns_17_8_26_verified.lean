-- Prove2me | solution 1 for OAI.CycleClique.patterns_17_8_26_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T23:22:58.058991+00:00
-- url     : https://prove2.me/submissions/fc135c71-f791-4266-bdca-695e3b2d7dfe

import Mathlib
import Definitions.Def_OAIQ107D131
import Definitions.Def_OAIQ107D133

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates083
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_2636_checked : certificate_2636.Valid 17 8 12 certificate_2636_q certificate_2636_edges 4 4 [] := by decide +kernel
theorem certificate_2636_valid : certificate_2636.Valid 17 8 (patternOrder [[],[1],[1],[1,1]]) (patternClique [[],[1],[1],[1,1]]) (patternEdges [[],[1],[1],[1,1]]) (patternAmount [[],[1],[1],[1,1]]) (patternEdgeCount [[],[1],[1],[1,1]]) [] := certificate_2636_checked

theorem certificate_2637_checked : certificate_2637.Valid 17 8 13 certificate_2637_q certificate_2637_edges 5 4 [] := by decide +kernel
theorem certificate_2637_valid : certificate_2637.Valid 17 8 (patternOrder [[],[1],[1],[1,2]]) (patternClique [[],[1],[1],[1,2]]) (patternEdges [[],[1],[1],[1,2]]) (patternAmount [[],[1],[1],[1,2]]) (patternEdgeCount [[],[1],[1],[1,2]]) [] := certificate_2637_checked

theorem certificate_2638_checked : certificate_2638.Valid 17 8 14 certificate_2638_q certificate_2638_edges 6 4 [] := by decide +kernel
theorem certificate_2638_valid : certificate_2638.Valid 17 8 (patternOrder [[],[1],[1],[1,3]]) (patternClique [[],[1],[1],[1,3]]) (patternEdges [[],[1],[1],[1,3]]) (patternAmount [[],[1],[1],[1,3]]) (patternEdgeCount [[],[1],[1],[1,3]]) [] := certificate_2638_checked

theorem certificate_2639_checked : certificate_2639.Valid 17 8 15 certificate_2639_q certificate_2639_edges 7 4 [] := by decide +kernel
theorem certificate_2639_valid : certificate_2639.Valid 17 8 (patternOrder [[],[1],[1],[1,4]]) (patternClique [[],[1],[1],[1,4]]) (patternEdges [[],[1],[1],[1,4]]) (patternAmount [[],[1],[1],[1,4]]) (patternEdgeCount [[],[1],[1],[1,4]]) [] := certificate_2639_checked

theorem certificate_2640_checked : certificate_2640.Valid 17 8 16 certificate_2640_q certificate_2640_edges 8 4 [] := by decide +kernel
theorem certificate_2640_valid : certificate_2640.Valid 17 8 (patternOrder [[],[1],[1],[1,5]]) (patternClique [[],[1],[1],[1,5]]) (patternEdges [[],[1],[1],[1,5]]) (patternAmount [[],[1],[1],[1,5]]) (patternEdgeCount [[],[1],[1],[1,5]]) [] := certificate_2640_checked

theorem certificate_2641_checked : certificate_2641.Valid 17 8 17 certificate_2641_q certificate_2641_edges 9 4 [] := by decide +kernel
theorem certificate_2641_valid : certificate_2641.Valid 17 8 (patternOrder [[],[1],[1],[1,6]]) (patternClique [[],[1],[1],[1,6]]) (patternEdges [[],[1],[1],[1,6]]) (patternAmount [[],[1],[1],[1,6]]) (patternEdgeCount [[],[1],[1],[1,6]]) [] := certificate_2641_checked

theorem certificate_2642_checked : certificate_2642.Valid 17 8 14 certificate_2642_q certificate_2642_edges 6 4 [] := by decide +kernel
theorem certificate_2642_valid : certificate_2642.Valid 17 8 (patternOrder [[],[1],[1],[2,2]]) (patternClique [[],[1],[1],[2,2]]) (patternEdges [[],[1],[1],[2,2]]) (patternAmount [[],[1],[1],[2,2]]) (patternEdgeCount [[],[1],[1],[2,2]]) [] := certificate_2642_checked

theorem certificate_2643_checked : certificate_2643.Valid 17 8 15 certificate_2643_q certificate_2643_edges 7 4 [] := by decide +kernel
theorem certificate_2643_valid : certificate_2643.Valid 17 8 (patternOrder [[],[1],[1],[2,3]]) (patternClique [[],[1],[1],[2,3]]) (patternEdges [[],[1],[1],[2,3]]) (patternAmount [[],[1],[1],[2,3]]) (patternEdgeCount [[],[1],[1],[2,3]]) [] := certificate_2643_checked

theorem certificate_2644_checked : certificate_2644.Valid 17 8 16 certificate_2644_q certificate_2644_edges 8 4 [] := by decide +kernel
theorem certificate_2644_valid : certificate_2644.Valid 17 8 (patternOrder [[],[1],[1],[2,4]]) (patternClique [[],[1],[1],[2,4]]) (patternEdges [[],[1],[1],[2,4]]) (patternAmount [[],[1],[1],[2,4]]) (patternEdgeCount [[],[1],[1],[2,4]]) [] := certificate_2644_checked

theorem certificate_2645_checked : certificate_2645.Valid 17 8 17 certificate_2645_q certificate_2645_edges 9 4 [] := by decide +kernel
theorem certificate_2645_valid : certificate_2645.Valid 17 8 (patternOrder [[],[1],[1],[2,5]]) (patternClique [[],[1],[1],[2,5]]) (patternEdges [[],[1],[1],[2,5]]) (patternAmount [[],[1],[1],[2,5]]) (patternEdgeCount [[],[1],[1],[2,5]]) [] := certificate_2645_checked

theorem certificate_2646_checked : certificate_2646.Valid 17 8 16 certificate_2646_q certificate_2646_edges 8 4 [] := by decide +kernel
theorem certificate_2646_valid : certificate_2646.Valid 17 8 (patternOrder [[],[1],[1],[3,3]]) (patternClique [[],[1],[1],[3,3]]) (patternEdges [[],[1],[1],[3,3]]) (patternAmount [[],[1],[1],[3,3]]) (patternEdgeCount [[],[1],[1],[3,3]]) [] := certificate_2646_checked

theorem certificate_2647_checked : certificate_2647.Valid 17 8 17 certificate_2647_q certificate_2647_edges 9 4 [] := by decide +kernel
theorem certificate_2647_valid : certificate_2647.Valid 17 8 (patternOrder [[],[1],[1],[3,4]]) (patternClique [[],[1],[1],[3,4]]) (patternEdges [[],[1],[1],[3,4]]) (patternAmount [[],[1],[1],[3,4]]) (patternEdgeCount [[],[1],[1],[3,4]]) [] := certificate_2647_checked

theorem certificate_2648_checked : certificate_2648.Valid 17 8 13 certificate_2648_q certificate_2648_edges 5 4 [] := by decide +kernel
theorem certificate_2648_valid : certificate_2648.Valid 17 8 (patternOrder [[],[1],[1,1],[2]]) (patternClique [[],[1],[1,1],[2]]) (patternEdges [[],[1],[1,1],[2]]) (patternAmount [[],[1],[1,1],[2]]) (patternEdgeCount [[],[1],[1,1],[2]]) [] := certificate_2648_checked

theorem certificate_2649_checked : certificate_2649.Valid 17 8 14 certificate_2649_q certificate_2649_edges 6 4 [] := by decide +kernel
theorem certificate_2649_valid : certificate_2649.Valid 17 8 (patternOrder [[],[1],[1,1],[3]]) (patternClique [[],[1],[1,1],[3]]) (patternEdges [[],[1],[1,1],[3]]) (patternAmount [[],[1],[1,1],[3]]) (patternEdgeCount [[],[1],[1,1],[3]]) [] := certificate_2649_checked

theorem certificate_2650_checked : certificate_2650.Valid 17 8 15 certificate_2650_q certificate_2650_edges 7 4 [] := by decide +kernel
theorem certificate_2650_valid : certificate_2650.Valid 17 8 (patternOrder [[],[1],[1,1],[4]]) (patternClique [[],[1],[1,1],[4]]) (patternEdges [[],[1],[1,1],[4]]) (patternAmount [[],[1],[1,1],[4]]) (patternEdgeCount [[],[1],[1,1],[4]]) [] := certificate_2650_checked

theorem certificate_2651_checked : certificate_2651.Valid 17 8 16 certificate_2651_q certificate_2651_edges 8 4 [] := by decide +kernel
theorem certificate_2651_valid : certificate_2651.Valid 17 8 (patternOrder [[],[1],[1,1],[5]]) (patternClique [[],[1],[1,1],[5]]) (patternEdges [[],[1],[1,1],[5]]) (patternAmount [[],[1],[1,1],[5]]) (patternEdgeCount [[],[1],[1,1],[5]]) [] := certificate_2651_checked

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

theorem patterns_17_8_26_verified_oai : ∀ D ∈ patterns_17_8_26, PatternVerified 17 8 D := by

  simp only [patterns_17_8_26, List.forall_mem_cons]

  exact ⟨⟨certificate_2636, certificate_2636_valid⟩, ⟨⟨certificate_2637, certificate_2637_valid⟩, ⟨⟨certificate_2638, certificate_2638_valid⟩, ⟨⟨certificate_2639, certificate_2639_valid⟩, ⟨⟨certificate_2640, certificate_2640_valid⟩, ⟨⟨certificate_2641, certificate_2641_valid⟩, ⟨⟨certificate_2642, certificate_2642_valid⟩, ⟨⟨certificate_2643, certificate_2643_valid⟩, ⟨⟨certificate_2644, certificate_2644_valid⟩, ⟨⟨certificate_2645, certificate_2645_valid⟩, ⟨⟨certificate_2646, certificate_2646_valid⟩, ⟨⟨certificate_2647, certificate_2647_valid⟩, ⟨⟨certificate_2648, certificate_2648_valid⟩, ⟨⟨certificate_2649, certificate_2649_valid⟩, ⟨⟨certificate_2650, certificate_2650_valid⟩, ⟨⟨certificate_2651, certificate_2651_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_17_8_26_verified_oai := @OAI.CycleClique.patterns_17_8_26_verified_oai
