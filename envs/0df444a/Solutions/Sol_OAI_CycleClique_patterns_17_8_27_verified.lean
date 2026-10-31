-- Prove2me | solution 1 for OAI.CycleClique.patterns_17_8_27_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T23:24:48.125135+00:00
-- url     : https://prove2.me/submissions/2f2a8020-1872-4681-bfad-6fbe9994671e

import Mathlib
import Definitions.Def_OAIQ107D087
import Definitions.Def_OAIQ107D088
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

theorem certificate_2652_checked : certificate_2652.Valid 17 8 17 certificate_2652_q certificate_2652_edges 9 4 [] := by decide +kernel
theorem certificate_2652_valid : certificate_2652.Valid 17 8 (patternOrder [[],[1],[1,1],[6]]) (patternClique [[],[1],[1,1],[6]]) (patternEdges [[],[1],[1,1],[6]]) (patternAmount [[],[1],[1,1],[6]]) (patternEdgeCount [[],[1],[1,1],[6]]) [] := certificate_2652_checked

theorem certificate_2653_checked : certificate_2653.Valid 17 8 13 certificate_2653_q certificate_2653_edges 5 5 [] := by decide +kernel
theorem certificate_2653_valid : certificate_2653.Valid 17 8 (patternOrder [[],[1],[1,1,1,1]]) (patternClique [[],[1],[1,1,1,1]]) (patternEdges [[],[1],[1,1,1,1]]) (patternAmount [[],[1],[1,1,1,1]]) (patternEdgeCount [[],[1],[1,1,1,1]]) [] := certificate_2653_checked

theorem certificate_2654_checked : certificate_2654.Valid 17 8 14 certificate_2654_q certificate_2654_edges 6 5 [] := by decide +kernel
theorem certificate_2654_valid : certificate_2654.Valid 17 8 (patternOrder [[],[1],[1,1,1,2]]) (patternClique [[],[1],[1,1,1,2]]) (patternEdges [[],[1],[1,1,1,2]]) (patternAmount [[],[1],[1,1,1,2]]) (patternEdgeCount [[],[1],[1,1,1,2]]) [] := certificate_2654_checked

theorem certificate_2655_checked : certificate_2655.Valid 17 8 15 certificate_2655_q certificate_2655_edges 7 5 [] := by decide +kernel
theorem certificate_2655_valid : certificate_2655.Valid 17 8 (patternOrder [[],[1],[1,1,1,3]]) (patternClique [[],[1],[1,1,1,3]]) (patternEdges [[],[1],[1,1,1,3]]) (patternAmount [[],[1],[1,1,1,3]]) (patternEdgeCount [[],[1],[1,1,1,3]]) [] := certificate_2655_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates084
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_2656_checked : certificate_2656.Valid 17 8 16 certificate_2656_q certificate_2656_edges 8 5 [] := by decide +kernel
theorem certificate_2656_valid : certificate_2656.Valid 17 8 (patternOrder [[],[1],[1,1,1,4]]) (patternClique [[],[1],[1,1,1,4]]) (patternEdges [[],[1],[1,1,1,4]]) (patternAmount [[],[1],[1,1,1,4]]) (patternEdgeCount [[],[1],[1,1,1,4]]) [] := certificate_2656_checked

theorem certificate_2657_checked : certificate_2657.Valid 17 8 17 certificate_2657_q certificate_2657_edges 9 5 [] := by decide +kernel
theorem certificate_2657_valid : certificate_2657.Valid 17 8 (patternOrder [[],[1],[1,1,1,5]]) (patternClique [[],[1],[1,1,1,5]]) (patternEdges [[],[1],[1,1,1,5]]) (patternAmount [[],[1],[1,1,1,5]]) (patternEdgeCount [[],[1],[1,1,1,5]]) [] := certificate_2657_checked

theorem certificate_2658_checked : certificate_2658.Valid 17 8 14 certificate_2658_q certificate_2658_edges 6 5 [] := by decide +kernel
theorem certificate_2658_valid : certificate_2658.Valid 17 8 (patternOrder [[],[1],[1,1,2,1]]) (patternClique [[],[1],[1,1,2,1]]) (patternEdges [[],[1],[1,1,2,1]]) (patternAmount [[],[1],[1,1,2,1]]) (patternEdgeCount [[],[1],[1,1,2,1]]) [] := certificate_2658_checked

theorem certificate_2659_checked : certificate_2659.Valid 17 8 15 certificate_2659_q certificate_2659_edges 7 5 [] := by decide +kernel
theorem certificate_2659_valid : certificate_2659.Valid 17 8 (patternOrder [[],[1],[1,1,2,2]]) (patternClique [[],[1],[1,1,2,2]]) (patternEdges [[],[1],[1,1,2,2]]) (patternAmount [[],[1],[1,1,2,2]]) (patternEdgeCount [[],[1],[1,1,2,2]]) [] := certificate_2659_checked

theorem certificate_2660_checked : certificate_2660.Valid 17 8 16 certificate_2660_q certificate_2660_edges 8 5 [] := by decide +kernel
theorem certificate_2660_valid : certificate_2660.Valid 17 8 (patternOrder [[],[1],[1,1,2,3]]) (patternClique [[],[1],[1,1,2,3]]) (patternEdges [[],[1],[1,1,2,3]]) (patternAmount [[],[1],[1,1,2,3]]) (patternEdgeCount [[],[1],[1,1,2,3]]) [] := certificate_2660_checked

theorem certificate_2661_checked : certificate_2661.Valid 17 8 17 certificate_2661_q certificate_2661_edges 9 5 [] := by decide +kernel
theorem certificate_2661_valid : certificate_2661.Valid 17 8 (patternOrder [[],[1],[1,1,2,4]]) (patternClique [[],[1],[1,1,2,4]]) (patternEdges [[],[1],[1,1,2,4]]) (patternAmount [[],[1],[1,1,2,4]]) (patternEdgeCount [[],[1],[1,1,2,4]]) [] := certificate_2661_checked

theorem certificate_2662_checked : certificate_2662.Valid 17 8 15 certificate_2662_q certificate_2662_edges 7 5 [] := by decide +kernel
theorem certificate_2662_valid : certificate_2662.Valid 17 8 (patternOrder [[],[1],[1,1,3,1]]) (patternClique [[],[1],[1,1,3,1]]) (patternEdges [[],[1],[1,1,3,1]]) (patternAmount [[],[1],[1,1,3,1]]) (patternEdgeCount [[],[1],[1,1,3,1]]) [] := certificate_2662_checked

theorem certificate_2663_checked : certificate_2663.Valid 17 8 16 certificate_2663_q certificate_2663_edges 8 5 [] := by decide +kernel
theorem certificate_2663_valid : certificate_2663.Valid 17 8 (patternOrder [[],[1],[1,1,3,2]]) (patternClique [[],[1],[1,1,3,2]]) (patternEdges [[],[1],[1,1,3,2]]) (patternAmount [[],[1],[1,1,3,2]]) (patternEdgeCount [[],[1],[1,1,3,2]]) [] := certificate_2663_checked

theorem certificate_2664_checked : certificate_2664.Valid 17 8 17 certificate_2664_q certificate_2664_edges 9 5 [] := by decide +kernel
theorem certificate_2664_valid : certificate_2664.Valid 17 8 (patternOrder [[],[1],[1,1,3,3]]) (patternClique [[],[1],[1,1,3,3]]) (patternEdges [[],[1],[1,1,3,3]]) (patternAmount [[],[1],[1,1,3,3]]) (patternEdgeCount [[],[1],[1,1,3,3]]) [] := certificate_2664_checked

theorem certificate_2665_checked : certificate_2665.Valid 17 8 16 certificate_2665_q certificate_2665_edges 8 5 [] := by decide +kernel
theorem certificate_2665_valid : certificate_2665.Valid 17 8 (patternOrder [[],[1],[1,1,4,1]]) (patternClique [[],[1],[1,1,4,1]]) (patternEdges [[],[1],[1,1,4,1]]) (patternAmount [[],[1],[1,1,4,1]]) (patternEdgeCount [[],[1],[1,1,4,1]]) [] := certificate_2665_checked

theorem certificate_2666_checked : certificate_2666.Valid 17 8 17 certificate_2666_q certificate_2666_edges 9 5 [] := by decide +kernel
theorem certificate_2666_valid : certificate_2666.Valid 17 8 (patternOrder [[],[1],[1,1,4,2]]) (patternClique [[],[1],[1,1,4,2]]) (patternEdges [[],[1],[1,1,4,2]]) (patternAmount [[],[1],[1,1,4,2]]) (patternEdgeCount [[],[1],[1,1,4,2]]) [] := certificate_2666_checked

theorem certificate_2667_checked : certificate_2667.Valid 17 8 17 certificate_2667_q certificate_2667_edges 9 5 [] := by decide +kernel
theorem certificate_2667_valid : certificate_2667.Valid 17 8 (patternOrder [[],[1],[1,1,5,1]]) (patternClique [[],[1],[1,1,5,1]]) (patternEdges [[],[1],[1,1,5,1]]) (patternAmount [[],[1],[1,1,5,1]]) (patternEdgeCount [[],[1],[1,1,5,1]]) [] := certificate_2667_checked

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

theorem patterns_17_8_27_verified_oai : ∀ D ∈ patterns_17_8_27, PatternVerified 17 8 D := by

  simp only [patterns_17_8_27, List.forall_mem_cons]

  exact ⟨⟨certificate_2652, certificate_2652_valid⟩, ⟨⟨certificate_2653, certificate_2653_valid⟩, ⟨⟨certificate_2654, certificate_2654_valid⟩, ⟨⟨certificate_2655, certificate_2655_valid⟩, ⟨⟨certificate_2656, certificate_2656_valid⟩, ⟨⟨certificate_2657, certificate_2657_valid⟩, ⟨⟨certificate_2658, certificate_2658_valid⟩, ⟨⟨certificate_2659, certificate_2659_valid⟩, ⟨⟨certificate_2660, certificate_2660_valid⟩, ⟨⟨certificate_2661, certificate_2661_valid⟩, ⟨⟨certificate_2662, certificate_2662_valid⟩, ⟨⟨certificate_2663, certificate_2663_valid⟩, ⟨⟨certificate_2664, certificate_2664_valid⟩, ⟨⟨certificate_2665, certificate_2665_valid⟩, ⟨⟨certificate_2666, certificate_2666_valid⟩, ⟨⟨certificate_2667, certificate_2667_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_17_8_27_verified_oai := @OAI.CycleClique.patterns_17_8_27_verified_oai
