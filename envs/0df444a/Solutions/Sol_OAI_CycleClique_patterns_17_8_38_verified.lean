-- Prove2me | solution 1 for OAI.CycleClique.patterns_17_8_38_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T23:41:18.079932+00:00
-- url     : https://prove2.me/submissions/b72f1ecc-7db2-4664-b42f-2ce50b9cfe3a

import Mathlib
import Definitions.Def_OAIQ107D132
import Definitions.Def_OAIQ107D133

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates089
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_2828_checked : certificate_2828.Valid 17 8 17 certificate_2828_q certificate_2828_edges 9 6 [] := by decide +kernel
theorem certificate_2828_valid : certificate_2828.Valid 17 8 (patternOrder [[],[1,2,1,2,1,2]]) (patternClique [[],[1,2,1,2,1,2]]) (patternEdges [[],[1,2,1,2,1,2]]) (patternAmount [[],[1,2,1,2,1,2]]) (patternEdgeCount [[],[1,2,1,2,1,2]]) [] := certificate_2828_checked

theorem certificate_2829_checked : certificate_2829.Valid 17 8 17 certificate_2829_q certificate_2829_edges 9 6 [] := by decide +kernel
theorem certificate_2829_valid : certificate_2829.Valid 17 8 (patternOrder [[],[1,2,1,2,2,1]]) (patternClique [[],[1,2,1,2,2,1]]) (patternEdges [[],[1,2,1,2,2,1]]) (patternAmount [[],[1,2,1,2,2,1]]) (patternEdgeCount [[],[1,2,1,2,2,1]]) [] := certificate_2829_checked

theorem certificate_2830_checked : certificate_2830.Valid 17 8 17 certificate_2830_q certificate_2830_edges 9 5 [] := by decide +kernel
theorem certificate_2830_valid : certificate_2830.Valid 17 8 (patternOrder [[],[1,2,1,3],[2]]) (patternClique [[],[1,2,1,3],[2]]) (patternEdges [[],[1,2,1,3],[2]]) (patternAmount [[],[1,2,1,3],[2]]) (patternEdgeCount [[],[1,2,1,3],[2]]) [] := certificate_2830_checked

theorem certificate_2831_checked : certificate_2831.Valid 17 8 17 certificate_2831_q certificate_2831_edges 9 5 [] := by decide +kernel
theorem certificate_2831_valid : certificate_2831.Valid 17 8 (patternOrder [[],[1,2,2],[1,3]]) (patternClique [[],[1,2,2],[1,3]]) (patternEdges [[],[1,2,2],[1,3]]) (patternAmount [[],[1,2,2],[1,3]]) (patternEdgeCount [[],[1,2,2],[1,3]]) [] := certificate_2831_checked

theorem certificate_2832_checked : certificate_2832.Valid 17 8 17 certificate_2832_q certificate_2832_edges 9 5 [] := by decide +kernel
theorem certificate_2832_valid : certificate_2832.Valid 17 8 (patternOrder [[],[1,2,2],[2,2]]) (patternClique [[],[1,2,2],[2,2]]) (patternEdges [[],[1,2,2],[2,2]]) (patternAmount [[],[1,2,2],[2,2]]) (patternEdgeCount [[],[1,2,2],[2,2]]) [] := certificate_2832_checked

theorem certificate_2833_checked : certificate_2833.Valid 17 8 16 certificate_2833_q certificate_2833_edges 8 5 [] := by decide +kernel
theorem certificate_2833_valid : certificate_2833.Valid 17 8 (patternOrder [[],[1,2,2,1],[2]]) (patternClique [[],[1,2,2,1],[2]]) (patternEdges [[],[1,2,2,1],[2]]) (patternAmount [[],[1,2,2,1],[2]]) (patternEdgeCount [[],[1,2,2,1],[2]]) [] := certificate_2833_checked

theorem certificate_2834_checked : certificate_2834.Valid 17 8 17 certificate_2834_q certificate_2834_edges 9 5 [] := by decide +kernel
theorem certificate_2834_valid : certificate_2834.Valid 17 8 (patternOrder [[],[1,2,2,1],[3]]) (patternClique [[],[1,2,2,1],[3]]) (patternEdges [[],[1,2,2,1],[3]]) (patternAmount [[],[1,2,2,1],[3]]) (patternEdgeCount [[],[1,2,2,1],[3]]) [] := certificate_2834_checked

theorem certificate_2835_checked : certificate_2835.Valid 17 8 17 certificate_2835_q certificate_2835_edges 9 6 [] := by decide +kernel
theorem certificate_2835_valid : certificate_2835.Valid 17 8 (patternOrder [[],[1,2,2,1,1,2]]) (patternClique [[],[1,2,2,1,1,2]]) (patternEdges [[],[1,2,2,1,1,2]]) (patternAmount [[],[1,2,2,1,1,2]]) (patternEdgeCount [[],[1,2,2,1,1,2]]) [] := certificate_2835_checked

theorem certificate_2836_checked : certificate_2836.Valid 17 8 17 certificate_2836_q certificate_2836_edges 9 5 [] := by decide +kernel
theorem certificate_2836_valid : certificate_2836.Valid 17 8 (patternOrder [[],[1,2,2,2],[2]]) (patternClique [[],[1,2,2,2],[2]]) (patternEdges [[],[1,2,2,2],[2]]) (patternAmount [[],[1,2,2,2],[2]]) (patternEdgeCount [[],[1,2,2,2],[2]]) [] := certificate_2836_checked

theorem certificate_2837_checked : certificate_2837.Valid 17 8 17 certificate_2837_q certificate_2837_edges 9 5 [] := by decide +kernel
theorem certificate_2837_valid : certificate_2837.Valid 17 8 (patternOrder [[],[1,2,3,1],[2]]) (patternClique [[],[1,2,3,1],[2]]) (patternEdges [[],[1,2,3,1],[2]]) (patternAmount [[],[1,2,3,1],[2]]) (patternEdgeCount [[],[1,2,3,1],[2]]) [] := certificate_2837_checked

theorem certificate_2838_checked : certificate_2838.Valid 17 8 17 certificate_2838_q certificate_2838_edges 9 5 [] := by decide +kernel
theorem certificate_2838_valid : certificate_2838.Valid 17 8 (patternOrder [[],[1,3],[1,3,1]]) (patternClique [[],[1,3],[1,3,1]]) (patternEdges [[],[1,3],[1,3,1]]) (patternAmount [[],[1,3],[1,3,1]]) (patternEdgeCount [[],[1,3],[1,3,1]]) [] := certificate_2838_checked

theorem certificate_2839_checked : certificate_2839.Valid 17 8 16 certificate_2839_q certificate_2839_edges 8 4 [] := by decide +kernel
theorem certificate_2839_valid : certificate_2839.Valid 17 8 (patternOrder [[],[1,3],[2],[2]]) (patternClique [[],[1,3],[2],[2]]) (patternEdges [[],[1,3],[2],[2]]) (patternAmount [[],[1,3],[2],[2]]) (patternEdgeCount [[],[1,3],[2],[2]]) [] := certificate_2839_checked

theorem certificate_2840_checked : certificate_2840.Valid 17 8 17 certificate_2840_q certificate_2840_edges 9 4 [] := by decide +kernel
theorem certificate_2840_valid : certificate_2840.Valid 17 8 (patternOrder [[],[1,3],[2],[3]]) (patternClique [[],[1,3],[2],[3]]) (patternEdges [[],[1,3],[2],[3]]) (patternAmount [[],[1,3],[2],[3]]) (patternEdgeCount [[],[1,3],[2],[3]]) [] := certificate_2840_checked

theorem certificate_2841_checked : certificate_2841.Valid 17 8 17 certificate_2841_q certificate_2841_edges 9 5 [] := by decide +kernel
theorem certificate_2841_valid : certificate_2841.Valid 17 8 (patternOrder [[],[1,3],[2,1,2]]) (patternClique [[],[1,3],[2,1,2]]) (patternEdges [[],[1,3],[2,1,2]]) (patternAmount [[],[1,3],[2,1,2]]) (patternEdgeCount [[],[1,3],[2,1,2]]) [] := certificate_2841_checked

theorem certificate_2842_checked : certificate_2842.Valid 17 8 17 certificate_2842_q certificate_2842_edges 9 5 [] := by decide +kernel
theorem certificate_2842_valid : certificate_2842.Valid 17 8 (patternOrder [[],[1,3,1],[2,2]]) (patternClique [[],[1,3,1],[2,2]]) (patternEdges [[],[1,3,1],[2,2]]) (patternAmount [[],[1,3,1],[2,2]]) (patternEdgeCount [[],[1,3,1],[2,2]]) [] := certificate_2842_checked

theorem certificate_2843_checked : certificate_2843.Valid 17 8 17 certificate_2843_q certificate_2843_edges 9 6 [] := by decide +kernel
theorem certificate_2843_valid : certificate_2843.Valid 17 8 (patternOrder [[],[1,3,1,1,1,2]]) (patternClique [[],[1,3,1,1,1,2]]) (patternEdges [[],[1,3,1,1,1,2]]) (patternAmount [[],[1,3,1,1,1,2]]) (patternEdgeCount [[],[1,3,1,1,1,2]]) [] := certificate_2843_checked

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

theorem patterns_17_8_38_verified_oai : ∀ D ∈ patterns_17_8_38, PatternVerified 17 8 D := by

  simp only [patterns_17_8_38, List.forall_mem_cons]

  exact ⟨⟨certificate_2828, certificate_2828_valid⟩, ⟨⟨certificate_2829, certificate_2829_valid⟩, ⟨⟨certificate_2830, certificate_2830_valid⟩, ⟨⟨certificate_2831, certificate_2831_valid⟩, ⟨⟨certificate_2832, certificate_2832_valid⟩, ⟨⟨certificate_2833, certificate_2833_valid⟩, ⟨⟨certificate_2834, certificate_2834_valid⟩, ⟨⟨certificate_2835, certificate_2835_valid⟩, ⟨⟨certificate_2836, certificate_2836_valid⟩, ⟨⟨certificate_2837, certificate_2837_valid⟩, ⟨⟨certificate_2838, certificate_2838_valid⟩, ⟨⟨certificate_2839, certificate_2839_valid⟩, ⟨⟨certificate_2840, certificate_2840_valid⟩, ⟨⟨certificate_2841, certificate_2841_valid⟩, ⟨⟨certificate_2842, certificate_2842_valid⟩, ⟨⟨certificate_2843, certificate_2843_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_17_8_38_verified_oai := @OAI.CycleClique.patterns_17_8_38_verified_oai
