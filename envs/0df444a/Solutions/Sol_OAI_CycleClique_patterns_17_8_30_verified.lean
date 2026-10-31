-- Prove2me | solution 1 for OAI.CycleClique.patterns_17_8_30_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T23:28:29.26167+00:00
-- url     : https://prove2.me/submissions/3d1aa8aa-ae36-40b2-8c87-b0f7805f9008

import Mathlib
import Definitions.Def_OAIQ107D131
import Definitions.Def_OAIQ107D133

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates085
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_2700_checked : certificate_2700.Valid 17 8 17 certificate_2700_q certificate_2700_edges 9 5 [] := by decide +kernel
theorem certificate_2700_valid : certificate_2700.Valid 17 8 (patternOrder [[],[1],[2,1,2,3]]) (patternClique [[],[1],[2,1,2,3]]) (patternEdges [[],[1],[2,1,2,3]]) (patternAmount [[],[1],[2,1,2,3]]) (patternEdgeCount [[],[1],[2,1,2,3]]) [] := certificate_2700_checked

theorem certificate_2701_checked : certificate_2701.Valid 17 8 17 certificate_2701_q certificate_2701_edges 9 5 [] := by decide +kernel
theorem certificate_2701_valid : certificate_2701.Valid 17 8 (patternOrder [[],[1],[2,1,3,2]]) (patternClique [[],[1],[2,1,3,2]]) (patternEdges [[],[1],[2,1,3,2]]) (patternAmount [[],[1],[2,1,3,2]]) (patternEdgeCount [[],[1],[2,1,3,2]]) [] := certificate_2701_checked

theorem certificate_2702_checked : certificate_2702.Valid 17 8 16 certificate_2702_q certificate_2702_edges 8 4 [] := by decide +kernel
theorem certificate_2702_valid : certificate_2702.Valid 17 8 (patternOrder [[],[1],[2,2],[3]]) (patternClique [[],[1],[2,2],[3]]) (patternEdges [[],[1],[2,2],[3]]) (patternAmount [[],[1],[2,2],[3]]) (patternEdgeCount [[],[1],[2,2],[3]]) [] := certificate_2702_checked

theorem certificate_2703_checked : certificate_2703.Valid 17 8 17 certificate_2703_q certificate_2703_edges 9 4 [] := by decide +kernel
theorem certificate_2703_valid : certificate_2703.Valid 17 8 (patternOrder [[],[1],[2,2],[4]]) (patternClique [[],[1],[2,2],[4]]) (patternEdges [[],[1],[2,2],[4]]) (patternAmount [[],[1],[2,2],[4]]) (patternEdgeCount [[],[1],[2,2],[4]]) [] := certificate_2703_checked

theorem certificate_2704_checked : certificate_2704.Valid 17 8 17 certificate_2704_q certificate_2704_edges 9 5 [] := by decide +kernel
theorem certificate_2704_valid : certificate_2704.Valid 17 8 (patternOrder [[],[1],[2,2,1,3]]) (patternClique [[],[1],[2,2,1,3]]) (patternEdges [[],[1],[2,2,1,3]]) (patternAmount [[],[1],[2,2,1,3]]) (patternEdgeCount [[],[1],[2,2,1,3]]) [] := certificate_2704_checked

theorem certificate_2705_checked : certificate_2705.Valid 17 8 17 certificate_2705_q certificate_2705_edges 9 5 [] := by decide +kernel
theorem certificate_2705_valid : certificate_2705.Valid 17 8 (patternOrder [[],[1],[2,2,2,2]]) (patternClique [[],[1],[2,2,2,2]]) (patternEdges [[],[1],[2,2,2,2]]) (patternAmount [[],[1],[2,2,2,2]]) (patternEdgeCount [[],[1],[2,2,2,2]]) [] := certificate_2705_checked

theorem certificate_2706_checked : certificate_2706.Valid 17 8 17 certificate_2706_q certificate_2706_edges 9 4 [] := by decide +kernel
theorem certificate_2706_valid : certificate_2706.Valid 17 8 (patternOrder [[],[1],[2,3],[3]]) (patternClique [[],[1],[2,3],[3]]) (patternEdges [[],[1],[2,3],[3]]) (patternAmount [[],[1],[2,3],[3]]) (patternEdgeCount [[],[1],[2,3],[3]]) [] := certificate_2706_checked

theorem certificate_2707_checked : certificate_2707.Valid 17 8 17 certificate_2707_q certificate_2707_edges 9 5 [] := by decide +kernel
theorem certificate_2707_valid : certificate_2707.Valid 17 8 (patternOrder [[],[1],[3,1,1,3]]) (patternClique [[],[1],[3,1,1,3]]) (patternEdges [[],[1],[3,1,1,3]]) (patternAmount [[],[1],[3,1,1,3]]) (patternEdgeCount [[],[1],[3,1,1,3]]) [] := certificate_2707_checked

theorem certificate_2708_checked : certificate_2708.Valid 17 8 13 certificate_2708_q certificate_2708_edges 5 5 [] := by decide +kernel
theorem certificate_2708_valid : certificate_2708.Valid 17 8 (patternOrder [[],[1,1],[1,1,1]]) (patternClique [[],[1,1],[1,1,1]]) (patternEdges [[],[1,1],[1,1,1]]) (patternAmount [[],[1,1],[1,1,1]]) (patternEdgeCount [[],[1,1],[1,1,1]]) [] := certificate_2708_checked

theorem certificate_2709_checked : certificate_2709.Valid 17 8 14 certificate_2709_q certificate_2709_edges 6 5 [] := by decide +kernel
theorem certificate_2709_valid : certificate_2709.Valid 17 8 (patternOrder [[],[1,1],[1,1,2]]) (patternClique [[],[1,1],[1,1,2]]) (patternEdges [[],[1,1],[1,1,2]]) (patternAmount [[],[1,1],[1,1,2]]) (patternEdgeCount [[],[1,1],[1,1,2]]) [] := certificate_2709_checked

theorem certificate_2710_checked : certificate_2710.Valid 17 8 15 certificate_2710_q certificate_2710_edges 7 5 [] := by decide +kernel
theorem certificate_2710_valid : certificate_2710.Valid 17 8 (patternOrder [[],[1,1],[1,1,3]]) (patternClique [[],[1,1],[1,1,3]]) (patternEdges [[],[1,1],[1,1,3]]) (patternAmount [[],[1,1],[1,1,3]]) (patternEdgeCount [[],[1,1],[1,1,3]]) [] := certificate_2710_checked

theorem certificate_2711_checked : certificate_2711.Valid 17 8 16 certificate_2711_q certificate_2711_edges 8 5 [] := by decide +kernel
theorem certificate_2711_valid : certificate_2711.Valid 17 8 (patternOrder [[],[1,1],[1,1,4]]) (patternClique [[],[1,1],[1,1,4]]) (patternEdges [[],[1,1],[1,1,4]]) (patternAmount [[],[1,1],[1,1,4]]) (patternEdgeCount [[],[1,1],[1,1,4]]) [] := certificate_2711_checked

theorem certificate_2712_checked : certificate_2712.Valid 17 8 17 certificate_2712_q certificate_2712_edges 9 5 [] := by decide +kernel
theorem certificate_2712_valid : certificate_2712.Valid 17 8 (patternOrder [[],[1,1],[1,1,5]]) (patternClique [[],[1,1],[1,1,5]]) (patternEdges [[],[1,1],[1,1,5]]) (patternAmount [[],[1,1],[1,1,5]]) (patternEdgeCount [[],[1,1],[1,1,5]]) [] := certificate_2712_checked

theorem certificate_2713_checked : certificate_2713.Valid 17 8 14 certificate_2713_q certificate_2713_edges 6 5 [] := by decide +kernel
theorem certificate_2713_valid : certificate_2713.Valid 17 8 (patternOrder [[],[1,1],[1,2,1]]) (patternClique [[],[1,1],[1,2,1]]) (patternEdges [[],[1,1],[1,2,1]]) (patternAmount [[],[1,1],[1,2,1]]) (patternEdgeCount [[],[1,1],[1,2,1]]) [] := certificate_2713_checked

theorem certificate_2714_checked : certificate_2714.Valid 17 8 15 certificate_2714_q certificate_2714_edges 7 5 [] := by decide +kernel
theorem certificate_2714_valid : certificate_2714.Valid 17 8 (patternOrder [[],[1,1],[1,2,2]]) (patternClique [[],[1,1],[1,2,2]]) (patternEdges [[],[1,1],[1,2,2]]) (patternAmount [[],[1,1],[1,2,2]]) (patternEdgeCount [[],[1,1],[1,2,2]]) [] := certificate_2714_checked

theorem certificate_2715_checked : certificate_2715.Valid 17 8 16 certificate_2715_q certificate_2715_edges 8 5 [] := by decide +kernel
theorem certificate_2715_valid : certificate_2715.Valid 17 8 (patternOrder [[],[1,1],[1,2,3]]) (patternClique [[],[1,1],[1,2,3]]) (patternEdges [[],[1,1],[1,2,3]]) (patternAmount [[],[1,1],[1,2,3]]) (patternEdgeCount [[],[1,1],[1,2,3]]) [] := certificate_2715_checked

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

theorem patterns_17_8_30_verified_oai : ∀ D ∈ patterns_17_8_30, PatternVerified 17 8 D := by

  simp only [patterns_17_8_30, List.forall_mem_cons]

  exact ⟨⟨certificate_2700, certificate_2700_valid⟩, ⟨⟨certificate_2701, certificate_2701_valid⟩, ⟨⟨certificate_2702, certificate_2702_valid⟩, ⟨⟨certificate_2703, certificate_2703_valid⟩, ⟨⟨certificate_2704, certificate_2704_valid⟩, ⟨⟨certificate_2705, certificate_2705_valid⟩, ⟨⟨certificate_2706, certificate_2706_valid⟩, ⟨⟨certificate_2707, certificate_2707_valid⟩, ⟨⟨certificate_2708, certificate_2708_valid⟩, ⟨⟨certificate_2709, certificate_2709_valid⟩, ⟨⟨certificate_2710, certificate_2710_valid⟩, ⟨⟨certificate_2711, certificate_2711_valid⟩, ⟨⟨certificate_2712, certificate_2712_valid⟩, ⟨⟨certificate_2713, certificate_2713_valid⟩, ⟨⟨certificate_2714, certificate_2714_valid⟩, ⟨⟨certificate_2715, certificate_2715_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_17_8_30_verified_oai := @OAI.CycleClique.patterns_17_8_30_verified_oai
