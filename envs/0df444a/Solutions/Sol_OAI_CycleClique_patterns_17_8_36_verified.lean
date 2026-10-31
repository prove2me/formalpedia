-- Prove2me | solution 1 for OAI.CycleClique.patterns_17_8_36_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T23:33:59.379785+00:00
-- url     : https://prove2.me/submissions/a157a65c-0dcd-4373-95a9-1f97bf49cb90

import Mathlib
import Definitions.Def_OAIQ107D005
import Definitions.Def_OAIQ107D093
import Definitions.Def_OAIQ107D133

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates088
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_2796_checked : certificate_2796.Valid 17 8 17 certificate_2796_q certificate_2796_edges 9 5 [] := by decide +kernel
theorem certificate_2796_valid : certificate_2796.Valid 17 8 (patternOrder [[],[1,1,3],[2,2]]) (patternClique [[],[1,1,3],[2,2]]) (patternEdges [[],[1,1,3],[2,2]]) (patternAmount [[],[1,1,3],[2,2]]) (patternEdgeCount [[],[1,1,3],[2,2]]) [] := certificate_2796_checked

theorem certificate_2797_checked : certificate_2797.Valid 17 8 16 certificate_2797_q certificate_2797_edges 8 5 [] := by decide +kernel
theorem certificate_2797_valid : certificate_2797.Valid 17 8 (patternOrder [[],[1,1,3,1],[2]]) (patternClique [[],[1,1,3,1],[2]]) (patternEdges [[],[1,1,3,1],[2]]) (patternAmount [[],[1,1,3,1],[2]]) (patternEdgeCount [[],[1,1,3,1],[2]]) [] := certificate_2797_checked

theorem certificate_2798_checked : certificate_2798.Valid 17 8 17 certificate_2798_q certificate_2798_edges 9 5 [] := by decide +kernel
theorem certificate_2798_valid : certificate_2798.Valid 17 8 (patternOrder [[],[1,1,3,1],[3]]) (patternClique [[],[1,1,3,1],[3]]) (patternEdges [[],[1,1,3,1],[3]]) (patternAmount [[],[1,1,3,1],[3]]) (patternEdgeCount [[],[1,1,3,1],[3]]) [] := certificate_2798_checked

theorem certificate_2799_checked : certificate_2799.Valid 17 8 17 certificate_2799_q certificate_2799_edges 9 6 [] := by decide +kernel
theorem certificate_2799_valid : certificate_2799.Valid 17 8 (patternOrder [[],[1,1,3,1,1,2]]) (patternClique [[],[1,1,3,1,1,2]]) (patternEdges [[],[1,1,3,1,1,2]]) (patternAmount [[],[1,1,3,1,1,2]]) (patternEdgeCount [[],[1,1,3,1,1,2]]) [] := certificate_2799_checked

theorem certificate_2800_checked : certificate_2800.Valid 17 8 17 certificate_2800_q certificate_2800_edges 9 6 [] := by decide +kernel
theorem certificate_2800_valid : certificate_2800.Valid 17 8 (patternOrder [[],[1,1,3,1,2,1]]) (patternClique [[],[1,1,3,1,2,1]]) (patternEdges [[],[1,1,3,1,2,1]]) (patternAmount [[],[1,1,3,1,2,1]]) (patternEdgeCount [[],[1,1,3,1,2,1]]) [] := certificate_2800_checked

theorem certificate_2801_checked : certificate_2801.Valid 17 8 17 certificate_2801_q certificate_2801_edges 9 5 [] := by decide +kernel
theorem certificate_2801_valid : certificate_2801.Valid 17 8 (patternOrder [[],[1,1,3,2],[2]]) (patternClique [[],[1,1,3,2],[2]]) (patternEdges [[],[1,1,3,2],[2]]) (patternAmount [[],[1,1,3,2],[2]]) (patternEdgeCount [[],[1,1,3,2],[2]]) [] := certificate_2801_checked

theorem certificate_2802_checked : certificate_2802.Valid 17 8 17 certificate_2802_q certificate_2802_edges 9 5 [] := by decide +kernel
theorem certificate_2802_valid : certificate_2802.Valid 17 8 (patternOrder [[],[1,1,4],[1,2]]) (patternClique [[],[1,1,4],[1,2]]) (patternEdges [[],[1,1,4],[1,2]]) (patternAmount [[],[1,1,4],[1,2]]) (patternEdgeCount [[],[1,1,4],[1,2]]) [] := certificate_2802_checked

theorem certificate_2803_checked : certificate_2803.Valid 17 8 17 certificate_2803_q certificate_2803_edges 9 5 [] := by decide +kernel
theorem certificate_2803_valid : certificate_2803.Valid 17 8 (patternOrder [[],[1,1,4,1],[2]]) (patternClique [[],[1,1,4,1],[2]]) (patternEdges [[],[1,1,4,1],[2]]) (patternAmount [[],[1,1,4,1],[2]]) (patternEdgeCount [[],[1,1,4,1],[2]]) [] := certificate_2803_checked

theorem certificate_2804_checked : certificate_2804.Valid 17 8 15 certificate_2804_q certificate_2804_edges 7 5 [] := by decide +kernel
theorem certificate_2804_valid : certificate_2804.Valid 17 8 (patternOrder [[],[1,2],[1,2,1]]) (patternClique [[],[1,2],[1,2,1]]) (patternEdges [[],[1,2],[1,2,1]]) (patternAmount [[],[1,2],[1,2,1]]) (patternEdgeCount [[],[1,2],[1,2,1]]) [] := certificate_2804_checked

theorem certificate_2805_checked : certificate_2805.Valid 17 8 16 certificate_2805_q certificate_2805_edges 8 5 [] := by decide +kernel
theorem certificate_2805_valid : certificate_2805.Valid 17 8 (patternOrder [[],[1,2],[1,2,2]]) (patternClique [[],[1,2],[1,2,2]]) (patternEdges [[],[1,2],[1,2,2]]) (patternAmount [[],[1,2],[1,2,2]]) (patternEdgeCount [[],[1,2],[1,2,2]]) [] := certificate_2805_checked

theorem certificate_2806_checked : certificate_2806.Valid 17 8 17 certificate_2806_q certificate_2806_edges 9 5 [] := by decide +kernel
theorem certificate_2806_valid : certificate_2806.Valid 17 8 (patternOrder [[],[1,2],[1,2,3]]) (patternClique [[],[1,2],[1,2,3]]) (patternEdges [[],[1,2],[1,2,3]]) (patternAmount [[],[1,2],[1,2,3]]) (patternEdgeCount [[],[1,2],[1,2,3]]) [] := certificate_2806_checked

theorem certificate_2807_checked : certificate_2807.Valid 17 8 16 certificate_2807_q certificate_2807_edges 8 5 [] := by decide +kernel
theorem certificate_2807_valid : certificate_2807.Valid 17 8 (patternOrder [[],[1,2],[1,3,1]]) (patternClique [[],[1,2],[1,3,1]]) (patternEdges [[],[1,2],[1,3,1]]) (patternAmount [[],[1,2],[1,3,1]]) (patternEdgeCount [[],[1,2],[1,3,1]]) [] := certificate_2807_checked

theorem certificate_2808_checked : certificate_2808.Valid 17 8 17 certificate_2808_q certificate_2808_edges 9 5 [] := by decide +kernel
theorem certificate_2808_valid : certificate_2808.Valid 17 8 (patternOrder [[],[1,2],[1,3,2]]) (patternClique [[],[1,2],[1,3,2]]) (patternEdges [[],[1,2],[1,3,2]]) (patternAmount [[],[1,2],[1,3,2]]) (patternEdgeCount [[],[1,2],[1,3,2]]) [] := certificate_2808_checked

theorem certificate_2809_checked : certificate_2809.Valid 17 8 17 certificate_2809_q certificate_2809_edges 9 5 [] := by decide +kernel
theorem certificate_2809_valid : certificate_2809.Valid 17 8 (patternOrder [[],[1,2],[1,4,1]]) (patternClique [[],[1,2],[1,4,1]]) (patternEdges [[],[1,2],[1,4,1]]) (patternAmount [[],[1,2],[1,4,1]]) (patternEdgeCount [[],[1,2],[1,4,1]]) [] := certificate_2809_checked

theorem certificate_2810_checked : certificate_2810.Valid 17 8 15 certificate_2810_q certificate_2810_edges 7 4 [] := by decide +kernel
theorem certificate_2810_valid : certificate_2810.Valid 17 8 (patternOrder [[],[1,2],[2],[2]]) (patternClique [[],[1,2],[2],[2]]) (patternEdges [[],[1,2],[2],[2]]) (patternAmount [[],[1,2],[2],[2]]) (patternEdgeCount [[],[1,2],[2],[2]]) [] := certificate_2810_checked

theorem certificate_2811_checked : certificate_2811.Valid 17 8 16 certificate_2811_q certificate_2811_edges 8 4 [] := by decide +kernel
theorem certificate_2811_valid : certificate_2811.Valid 17 8 (patternOrder [[],[1,2],[2],[3]]) (patternClique [[],[1,2],[2],[3]]) (patternEdges [[],[1,2],[2],[3]]) (patternAmount [[],[1,2],[2],[3]]) (patternEdgeCount [[],[1,2],[2],[3]]) [] := certificate_2811_checked

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

theorem patterns_17_8_36_verified_oai : ∀ D ∈ patterns_17_8_36, PatternVerified 17 8 D := by

  simp only [patterns_17_8_36, List.forall_mem_cons]

  exact ⟨⟨certificate_2796, certificate_2796_valid⟩, ⟨⟨certificate_2797, certificate_2797_valid⟩, ⟨⟨certificate_2798, certificate_2798_valid⟩, ⟨⟨certificate_2799, certificate_2799_valid⟩, ⟨⟨certificate_2800, certificate_2800_valid⟩, ⟨⟨certificate_2801, certificate_2801_valid⟩, ⟨⟨certificate_2802, certificate_2802_valid⟩, ⟨⟨certificate_2803, certificate_2803_valid⟩, ⟨⟨certificate_2804, certificate_2804_valid⟩, ⟨⟨certificate_2805, certificate_2805_valid⟩, ⟨⟨certificate_2806, certificate_2806_valid⟩, ⟨⟨certificate_2807, certificate_2807_valid⟩, ⟨⟨certificate_2808, certificate_2808_valid⟩, ⟨⟨certificate_2809, certificate_2809_valid⟩, ⟨⟨certificate_2810, certificate_2810_valid⟩, ⟨⟨certificate_2811, certificate_2811_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_17_8_36_verified_oai := @OAI.CycleClique.patterns_17_8_36_verified_oai
