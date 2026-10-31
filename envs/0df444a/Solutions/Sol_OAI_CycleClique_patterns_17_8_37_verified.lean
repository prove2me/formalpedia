-- Prove2me | solution 1 for OAI.CycleClique.patterns_17_8_37_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T23:35:04.976841+00:00
-- url     : https://prove2.me/submissions/24313448-b61f-447d-8d67-6d09a982cdd9

import Mathlib
import Definitions.Def_OAIQ107D132
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

theorem certificate_2812_checked : certificate_2812.Valid 17 8 17 certificate_2812_q certificate_2812_edges 9 4 [] := by decide +kernel
theorem certificate_2812_valid : certificate_2812.Valid 17 8 (patternOrder [[],[1,2],[2],[4]]) (patternClique [[],[1,2],[2],[4]]) (patternEdges [[],[1,2],[2],[4]]) (patternAmount [[],[1,2],[2],[4]]) (patternEdgeCount [[],[1,2],[2],[4]]) [] := certificate_2812_checked

theorem certificate_2813_checked : certificate_2813.Valid 17 8 16 certificate_2813_q certificate_2813_edges 8 5 [] := by decide +kernel
theorem certificate_2813_valid : certificate_2813.Valid 17 8 (patternOrder [[],[1,2],[2,1,2]]) (patternClique [[],[1,2],[2,1,2]]) (patternEdges [[],[1,2],[2,1,2]]) (patternAmount [[],[1,2],[2,1,2]]) (patternEdgeCount [[],[1,2],[2,1,2]]) [] := certificate_2813_checked

theorem certificate_2814_checked : certificate_2814.Valid 17 8 17 certificate_2814_q certificate_2814_edges 9 5 [] := by decide +kernel
theorem certificate_2814_valid : certificate_2814.Valid 17 8 (patternOrder [[],[1,2],[2,1,3]]) (patternClique [[],[1,2],[2,1,3]]) (patternEdges [[],[1,2],[2,1,3]]) (patternAmount [[],[1,2],[2,1,3]]) (patternEdgeCount [[],[1,2],[2,1,3]]) [] := certificate_2814_checked

theorem certificate_2815_checked : certificate_2815.Valid 17 8 17 certificate_2815_q certificate_2815_edges 9 5 [] := by decide +kernel
theorem certificate_2815_valid : certificate_2815.Valid 17 8 (patternOrder [[],[1,2],[2,2,2]]) (patternClique [[],[1,2],[2,2,2]]) (patternEdges [[],[1,2],[2,2,2]]) (patternAmount [[],[1,2],[2,2,2]]) (patternEdgeCount [[],[1,2],[2,2,2]]) [] := certificate_2815_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates089
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_2816_checked : certificate_2816.Valid 17 8 17 certificate_2816_q certificate_2816_edges 9 4 [] := by decide +kernel
theorem certificate_2816_valid : certificate_2816.Valid 17 8 (patternOrder [[],[1,2],[3],[3]]) (patternClique [[],[1,2],[3],[3]]) (patternEdges [[],[1,2],[3],[3]]) (patternAmount [[],[1,2],[3],[3]]) (patternEdgeCount [[],[1,2],[3],[3]]) [] := certificate_2816_checked

theorem certificate_2817_checked : certificate_2817.Valid 17 8 16 certificate_2817_q certificate_2817_edges 8 5 [] := by decide +kernel
theorem certificate_2817_valid : certificate_2817.Valid 17 8 (patternOrder [[],[1,2,1],[1,3]]) (patternClique [[],[1,2,1],[1,3]]) (patternEdges [[],[1,2,1],[1,3]]) (patternAmount [[],[1,2,1],[1,3]]) (patternEdgeCount [[],[1,2,1],[1,3]]) [] := certificate_2817_checked

theorem certificate_2818_checked : certificate_2818.Valid 17 8 17 certificate_2818_q certificate_2818_edges 9 5 [] := by decide +kernel
theorem certificate_2818_valid : certificate_2818.Valid 17 8 (patternOrder [[],[1,2,1],[1,4]]) (patternClique [[],[1,2,1],[1,4]]) (patternEdges [[],[1,2,1],[1,4]]) (patternAmount [[],[1,2,1],[1,4]]) (patternEdgeCount [[],[1,2,1],[1,4]]) [] := certificate_2818_checked

theorem certificate_2819_checked : certificate_2819.Valid 17 8 16 certificate_2819_q certificate_2819_edges 8 5 [] := by decide +kernel
theorem certificate_2819_valid : certificate_2819.Valid 17 8 (patternOrder [[],[1,2,1],[2,2]]) (patternClique [[],[1,2,1],[2,2]]) (patternEdges [[],[1,2,1],[2,2]]) (patternAmount [[],[1,2,1],[2,2]]) (patternEdgeCount [[],[1,2,1],[2,2]]) [] := certificate_2819_checked

theorem certificate_2820_checked : certificate_2820.Valid 17 8 17 certificate_2820_q certificate_2820_edges 9 5 [] := by decide +kernel
theorem certificate_2820_valid : certificate_2820.Valid 17 8 (patternOrder [[],[1,2,1],[2,3]]) (patternClique [[],[1,2,1],[2,3]]) (patternEdges [[],[1,2,1],[2,3]]) (patternAmount [[],[1,2,1],[2,3]]) (patternEdgeCount [[],[1,2,1],[2,3]]) [] := certificate_2820_checked

theorem certificate_2821_checked : certificate_2821.Valid 17 8 16 certificate_2821_q certificate_2821_edges 8 6 [] := by decide +kernel
theorem certificate_2821_valid : certificate_2821.Valid 17 8 (patternOrder [[],[1,2,1,1,1,2]]) (patternClique [[],[1,2,1,1,1,2]]) (patternEdges [[],[1,2,1,1,1,2]]) (patternAmount [[],[1,2,1,1,1,2]]) (patternEdgeCount [[],[1,2,1,1,1,2]]) [] := certificate_2821_checked

theorem certificate_2822_checked : certificate_2822.Valid 17 8 17 certificate_2822_q certificate_2822_edges 9 6 [] := by decide +kernel
theorem certificate_2822_valid : certificate_2822.Valid 17 8 (patternOrder [[],[1,2,1,1,1,3]]) (patternClique [[],[1,2,1,1,1,3]]) (patternEdges [[],[1,2,1,1,1,3]]) (patternAmount [[],[1,2,1,1,1,3]]) (patternEdgeCount [[],[1,2,1,1,1,3]]) [] := certificate_2822_checked

theorem certificate_2823_checked : certificate_2823.Valid 17 8 16 certificate_2823_q certificate_2823_edges 8 6 [] := by decide +kernel
theorem certificate_2823_valid : certificate_2823.Valid 17 8 (patternOrder [[],[1,2,1,1,2,1]]) (patternClique [[],[1,2,1,1,2,1]]) (patternEdges [[],[1,2,1,1,2,1]]) (patternAmount [[],[1,2,1,1,2,1]]) (patternEdgeCount [[],[1,2,1,1,2,1]]) [] := certificate_2823_checked

theorem certificate_2824_checked : certificate_2824.Valid 17 8 17 certificate_2824_q certificate_2824_edges 9 6 [] := by decide +kernel
theorem certificate_2824_valid : certificate_2824.Valid 17 8 (patternOrder [[],[1,2,1,1,2,2]]) (patternClique [[],[1,2,1,1,2,2]]) (patternEdges [[],[1,2,1,1,2,2]]) (patternAmount [[],[1,2,1,1,2,2]]) (patternEdgeCount [[],[1,2,1,1,2,2]]) [] := certificate_2824_checked

theorem certificate_2825_checked : certificate_2825.Valid 17 8 17 certificate_2825_q certificate_2825_edges 9 6 [] := by decide +kernel
theorem certificate_2825_valid : certificate_2825.Valid 17 8 (patternOrder [[],[1,2,1,1,3,1]]) (patternClique [[],[1,2,1,1,3,1]]) (patternEdges [[],[1,2,1,1,3,1]]) (patternAmount [[],[1,2,1,1,3,1]]) (patternEdgeCount [[],[1,2,1,1,3,1]]) [] := certificate_2825_checked

theorem certificate_2826_checked : certificate_2826.Valid 17 8 16 certificate_2826_q certificate_2826_edges 8 5 [] := by decide +kernel
theorem certificate_2826_valid : certificate_2826.Valid 17 8 (patternOrder [[],[1,2,1,2],[2]]) (patternClique [[],[1,2,1,2],[2]]) (patternEdges [[],[1,2,1,2],[2]]) (patternAmount [[],[1,2,1,2],[2]]) (patternEdgeCount [[],[1,2,1,2],[2]]) [] := certificate_2826_checked

theorem certificate_2827_checked : certificate_2827.Valid 17 8 17 certificate_2827_q certificate_2827_edges 9 5 [] := by decide +kernel
theorem certificate_2827_valid : certificate_2827.Valid 17 8 (patternOrder [[],[1,2,1,2],[3]]) (patternClique [[],[1,2,1,2],[3]]) (patternEdges [[],[1,2,1,2],[3]]) (patternAmount [[],[1,2,1,2],[3]]) (patternEdgeCount [[],[1,2,1,2],[3]]) [] := certificate_2827_checked

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

theorem patterns_17_8_37_verified_oai : ∀ D ∈ patterns_17_8_37, PatternVerified 17 8 D := by

  simp only [patterns_17_8_37, List.forall_mem_cons]

  exact ⟨⟨certificate_2812, certificate_2812_valid⟩, ⟨⟨certificate_2813, certificate_2813_valid⟩, ⟨⟨certificate_2814, certificate_2814_valid⟩, ⟨⟨certificate_2815, certificate_2815_valid⟩, ⟨⟨certificate_2816, certificate_2816_valid⟩, ⟨⟨certificate_2817, certificate_2817_valid⟩, ⟨⟨certificate_2818, certificate_2818_valid⟩, ⟨⟨certificate_2819, certificate_2819_valid⟩, ⟨⟨certificate_2820, certificate_2820_valid⟩, ⟨⟨certificate_2821, certificate_2821_valid⟩, ⟨⟨certificate_2822, certificate_2822_valid⟩, ⟨⟨certificate_2823, certificate_2823_valid⟩, ⟨⟨certificate_2824, certificate_2824_valid⟩, ⟨⟨certificate_2825, certificate_2825_valid⟩, ⟨⟨certificate_2826, certificate_2826_valid⟩, ⟨⟨certificate_2827, certificate_2827_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_17_8_37_verified_oai := @OAI.CycleClique.patterns_17_8_37_verified_oai
