-- Prove2me | solution 1 for OAI.CycleClique.finite_patterns_17_8
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T20:43:24.009018+00:00
-- url     : https://prove2.me/submissions/b0d866d3-a5ee-4a65-9aa3-4ce89ef01e80

import Mathlib
import Definitions.Def_OAIQ107D132
import Definitions.Def_OAIQ107D133
import Theorems.Thm_OAI_CycleClique_patterns_17_8_0_verified
import Theorems.Thm_OAI_CycleClique_patterns_17_8_10_verified
import Theorems.Thm_OAI_CycleClique_patterns_17_8_11_verified
import Theorems.Thm_OAI_CycleClique_patterns_17_8_12_verified
import Theorems.Thm_OAI_CycleClique_patterns_17_8_13_verified
import Theorems.Thm_OAI_CycleClique_patterns_17_8_14_verified
import Theorems.Thm_OAI_CycleClique_patterns_17_8_15_verified
import Theorems.Thm_OAI_CycleClique_patterns_17_8_16_verified
import Theorems.Thm_OAI_CycleClique_patterns_17_8_17_verified
import Theorems.Thm_OAI_CycleClique_patterns_17_8_18_verified
import Theorems.Thm_OAI_CycleClique_patterns_17_8_19_verified
import Theorems.Thm_OAI_CycleClique_patterns_17_8_1_verified
import Theorems.Thm_OAI_CycleClique_patterns_17_8_20_verified
import Theorems.Thm_OAI_CycleClique_patterns_17_8_21_verified
import Theorems.Thm_OAI_CycleClique_patterns_17_8_22_verified
import Theorems.Thm_OAI_CycleClique_patterns_17_8_23_verified
import Theorems.Thm_OAI_CycleClique_patterns_17_8_24_verified
import Theorems.Thm_OAI_CycleClique_patterns_17_8_25_verified
import Theorems.Thm_OAI_CycleClique_patterns_17_8_26_verified
import Theorems.Thm_OAI_CycleClique_patterns_17_8_27_verified
import Theorems.Thm_OAI_CycleClique_patterns_17_8_28_verified
import Theorems.Thm_OAI_CycleClique_patterns_17_8_29_verified
import Theorems.Thm_OAI_CycleClique_patterns_17_8_2_verified
import Theorems.Thm_OAI_CycleClique_patterns_17_8_30_verified
import Theorems.Thm_OAI_CycleClique_patterns_17_8_31_verified
import Theorems.Thm_OAI_CycleClique_patterns_17_8_32_verified
import Theorems.Thm_OAI_CycleClique_patterns_17_8_33_verified
import Theorems.Thm_OAI_CycleClique_patterns_17_8_34_verified
import Theorems.Thm_OAI_CycleClique_patterns_17_8_35_verified
import Theorems.Thm_OAI_CycleClique_patterns_17_8_36_verified
import Theorems.Thm_OAI_CycleClique_patterns_17_8_37_verified
import Theorems.Thm_OAI_CycleClique_patterns_17_8_38_verified
import Theorems.Thm_OAI_CycleClique_patterns_17_8_39_verified
import Theorems.Thm_OAI_CycleClique_patterns_17_8_3_verified
import Theorems.Thm_OAI_CycleClique_patterns_17_8_40_verified
import Theorems.Thm_OAI_CycleClique_patterns_17_8_41_verified
import Theorems.Thm_OAI_CycleClique_patterns_17_8_42_verified
import Theorems.Thm_OAI_CycleClique_patterns_17_8_43_verified
import Theorems.Thm_OAI_CycleClique_patterns_17_8_44_verified
import Theorems.Thm_OAI_CycleClique_patterns_17_8_45_verified
import Theorems.Thm_OAI_CycleClique_patterns_17_8_47_verified
import Theorems.Thm_OAI_CycleClique_patterns_17_8_48_verified
import Theorems.Thm_OAI_CycleClique_patterns_17_8_49_verified
import Theorems.Thm_OAI_CycleClique_patterns_17_8_4_verified
import Theorems.Thm_OAI_CycleClique_patterns_17_8_50_verified
import Theorems.Thm_OAI_CycleClique_patterns_17_8_51_verified
import Theorems.Thm_OAI_CycleClique_patterns_17_8_52_verified
import Theorems.Thm_OAI_CycleClique_patterns_17_8_53_verified
import Theorems.Thm_OAI_CycleClique_patterns_17_8_5_verified
import Theorems.Thm_OAI_CycleClique_patterns_17_8_6_verified
import Theorems.Thm_OAI_CycleClique_patterns_17_8_7_verified
import Theorems.Thm_OAI_CycleClique_patterns_17_8_8_verified
import Theorems.Thm_OAI_CycleClique_patterns_17_8_9_verified

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates093
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_2956_checked : certificate_2956.Valid 17 8 15 certificate_2956_q certificate_2956_edges 7 4 [] := by decide +kernel
theorem certificate_2956_valid : certificate_2956.Valid 17 8 (patternOrder [[1],[2],[2],[2]]) (patternClique [[1],[2],[2],[2]]) (patternEdges [[1],[2],[2],[2]]) (patternAmount [[1],[2],[2],[2]]) (patternEdgeCount [[1],[2],[2],[2]]) [] := certificate_2956_checked

theorem certificate_2957_checked : certificate_2957.Valid 17 8 16 certificate_2957_q certificate_2957_edges 8 4 [] := by decide +kernel
theorem certificate_2957_valid : certificate_2957.Valid 17 8 (patternOrder [[1],[2],[2],[3]]) (patternClique [[1],[2],[2],[3]]) (patternEdges [[1],[2],[2],[3]]) (patternAmount [[1],[2],[2],[3]]) (patternEdgeCount [[1],[2],[2],[3]]) [] := certificate_2957_checked

theorem certificate_2958_checked : certificate_2958.Valid 17 8 17 certificate_2958_q certificate_2958_edges 9 4 [] := by decide +kernel
theorem certificate_2958_valid : certificate_2958.Valid 17 8 (patternOrder [[1],[2],[2],[4]]) (patternClique [[1],[2],[2],[4]]) (patternEdges [[1],[2],[2],[4]]) (patternAmount [[1],[2],[2],[4]]) (patternEdgeCount [[1],[2],[2],[4]]) [] := certificate_2958_checked

theorem certificate_2959_checked : certificate_2959.Valid 17 8 16 certificate_2959_q certificate_2959_edges 8 5 [] := by decide +kernel
theorem certificate_2959_valid : certificate_2959.Valid 17 8 (patternOrder [[1],[2],[2,1,2]]) (patternClique [[1],[2],[2,1,2]]) (patternEdges [[1],[2],[2,1,2]]) (patternAmount [[1],[2],[2,1,2]]) (patternEdgeCount [[1],[2],[2,1,2]]) [] := certificate_2959_checked

theorem certificate_2960_checked : certificate_2960.Valid 17 8 17 certificate_2960_q certificate_2960_edges 9 5 [] := by decide +kernel
theorem certificate_2960_valid : certificate_2960.Valid 17 8 (patternOrder [[1],[2],[2,1,3]]) (patternClique [[1],[2],[2,1,3]]) (patternEdges [[1],[2],[2,1,3]]) (patternAmount [[1],[2],[2,1,3]]) (patternEdgeCount [[1],[2],[2,1,3]]) [] := certificate_2960_checked

theorem certificate_2961_checked : certificate_2961.Valid 17 8 17 certificate_2961_q certificate_2961_edges 9 5 [] := by decide +kernel
theorem certificate_2961_valid : certificate_2961.Valid 17 8 (patternOrder [[1],[2],[2,2,2]]) (patternClique [[1],[2],[2,2,2]]) (patternEdges [[1],[2],[2,2,2]]) (patternAmount [[1],[2],[2,2,2]]) (patternEdgeCount [[1],[2],[2,2,2]]) [] := certificate_2961_checked

theorem certificate_2962_checked : certificate_2962.Valid 17 8 17 certificate_2962_q certificate_2962_edges 9 4 [] := by decide +kernel
theorem certificate_2962_valid : certificate_2962.Valid 17 8 (patternOrder [[1],[2],[3],[3]]) (patternClique [[1],[2],[3],[3]]) (patternEdges [[1],[2],[3],[3]]) (patternAmount [[1],[2],[3],[3]]) (patternEdgeCount [[1],[2],[3],[3]]) [] := certificate_2962_checked

theorem certificate_2963_checked : certificate_2963.Valid 17 8 16 certificate_2963_q certificate_2963_edges 8 6 [] := by decide +kernel
theorem certificate_2963_valid : certificate_2963.Valid 17 8 (patternOrder [[1],[2,1,1,1,2]]) (patternClique [[1],[2,1,1,1,2]]) (patternEdges [[1],[2,1,1,1,2]]) (patternAmount [[1],[2,1,1,1,2]]) (patternEdgeCount [[1],[2,1,1,1,2]]) [] := certificate_2963_checked

theorem certificate_2964_checked : certificate_2964.Valid 17 8 17 certificate_2964_q certificate_2964_edges 9 6 [] := by decide +kernel
theorem certificate_2964_valid : certificate_2964.Valid 17 8 (patternOrder [[1],[2,1,1,1,3]]) (patternClique [[1],[2,1,1,1,3]]) (patternEdges [[1],[2,1,1,1,3]]) (patternAmount [[1],[2,1,1,1,3]]) (patternEdgeCount [[1],[2,1,1,1,3]]) [] := certificate_2964_checked

theorem certificate_2965_checked : certificate_2965.Valid 17 8 17 certificate_2965_q certificate_2965_edges 9 6 [] := by decide +kernel
theorem certificate_2965_valid : certificate_2965.Valid 17 8 (patternOrder [[1],[2,1,1,2,2]]) (patternClique [[1],[2,1,1,2,2]]) (patternEdges [[1],[2,1,1,2,2]]) (patternAmount [[1],[2,1,1,2,2]]) (patternEdgeCount [[1],[2,1,1,2,2]]) [] := certificate_2965_checked

theorem certificate_2966_checked : certificate_2966.Valid 17 8 17 certificate_2966_q certificate_2966_edges 9 5 [] := by decide +kernel
theorem certificate_2966_valid : certificate_2966.Valid 17 8 (patternOrder [[1],[2,1,2],[3]]) (patternClique [[1],[2,1,2],[3]]) (patternEdges [[1],[2,1,2],[3]]) (patternAmount [[1],[2,1,2],[3]]) (patternEdgeCount [[1],[2,1,2],[3]]) [] := certificate_2966_checked

theorem certificate_2967_checked : certificate_2967.Valid 17 8 17 certificate_2967_q certificate_2967_edges 9 6 [] := by decide +kernel
theorem certificate_2967_valid : certificate_2967.Valid 17 8 (patternOrder [[1],[2,1,2,1,2]]) (patternClique [[1],[2,1,2,1,2]]) (patternEdges [[1],[2,1,2,1,2]]) (patternAmount [[1],[2,1,2,1,2]]) (patternEdgeCount [[1],[2,1,2,1,2]]) [] := certificate_2967_checked

theorem certificate_2968_checked : certificate_2968.Valid 17 8 17 certificate_2968_q certificate_2968_edges 9 5 [] := by decide +kernel
theorem certificate_2968_valid : certificate_2968.Valid 17 8 (patternOrder [[1],[2,2],[2,2]]) (patternClique [[1],[2,2],[2,2]]) (patternEdges [[1],[2,2],[2,2]]) (patternAmount [[1],[2,2],[2,2]]) (patternEdgeCount [[1],[2,2],[2,2]]) [] := certificate_2968_checked

theorem certificate_2969_checked : certificate_2969.Valid 17 8 14 certificate_2969_q certificate_2969_edges 6 5 [] := by decide +kernel
theorem certificate_2969_valid : certificate_2969.Valid 17 8 (patternOrder [[1,1],[1,1],[2]]) (patternClique [[1,1],[1,1],[2]]) (patternEdges [[1,1],[1,1],[2]]) (patternAmount [[1,1],[1,1],[2]]) (patternEdgeCount [[1,1],[1,1],[2]]) [] := certificate_2969_checked

theorem certificate_2970_checked : certificate_2970.Valid 17 8 15 certificate_2970_q certificate_2970_edges 7 5 [] := by decide +kernel
theorem certificate_2970_valid : certificate_2970.Valid 17 8 (patternOrder [[1,1],[1,1],[3]]) (patternClique [[1,1],[1,1],[3]]) (patternEdges [[1,1],[1,1],[3]]) (patternAmount [[1,1],[1,1],[3]]) (patternEdgeCount [[1,1],[1,1],[3]]) [] := certificate_2970_checked

theorem certificate_2971_checked : certificate_2971.Valid 17 8 16 certificate_2971_q certificate_2971_edges 8 5 [] := by decide +kernel
theorem certificate_2971_valid : certificate_2971.Valid 17 8 (patternOrder [[1,1],[1,1],[4]]) (patternClique [[1,1],[1,1],[4]]) (patternEdges [[1,1],[1,1],[4]]) (patternAmount [[1,1],[1,1],[4]]) (patternEdgeCount [[1,1],[1,1],[4]]) [] := certificate_2971_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates097
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_3084_checked : certificate_3084.Valid 17 8 17 certificate_3084_q certificate_3084_edges 9 6 [] := by decide +kernel
theorem certificate_3084_valid : certificate_3084.Valid 17 8 (patternOrder [[1,2,1],[1,3,1]]) (patternClique [[1,2,1],[1,3,1]]) (patternEdges [[1,2,1],[1,3,1]]) (patternAmount [[1,2,1],[1,3,1]]) (patternEdgeCount [[1,2,1],[1,3,1]]) [] := certificate_3084_checked

theorem certificate_3085_checked : certificate_3085.Valid 17 8 16 certificate_3085_q certificate_3085_edges 8 5 [] := by decide +kernel
theorem certificate_3085_valid : certificate_3085.Valid 17 8 (patternOrder [[1,2,1],[2],[2]]) (patternClique [[1,2,1],[2],[2]]) (patternEdges [[1,2,1],[2],[2]]) (patternAmount [[1,2,1],[2],[2]]) (patternEdgeCount [[1,2,1],[2],[2]]) [] := certificate_3085_checked

theorem certificate_3086_checked : certificate_3086.Valid 17 8 17 certificate_3086_q certificate_3086_edges 9 5 [] := by decide +kernel
theorem certificate_3086_valid : certificate_3086.Valid 17 8 (patternOrder [[1,2,1],[2],[3]]) (patternClique [[1,2,1],[2],[3]]) (patternEdges [[1,2,1],[2],[3]]) (patternAmount [[1,2,1],[2],[3]]) (patternEdgeCount [[1,2,1],[2],[3]]) [] := certificate_3086_checked

theorem certificate_3087_checked : certificate_3087.Valid 17 8 17 certificate_3087_q certificate_3087_edges 9 6 [] := by decide +kernel
theorem certificate_3087_valid : certificate_3087.Valid 17 8 (patternOrder [[1,2,1],[2,1,2]]) (patternClique [[1,2,1],[2,1,2]]) (patternEdges [[1,2,1],[2,1,2]]) (patternAmount [[1,2,1],[2,1,2]]) (patternEdgeCount [[1,2,1],[2,1,2]]) [] := certificate_3087_checked

theorem certificate_3088_checked : certificate_3088.Valid 17 8 17 certificate_3088_q certificate_3088_edges 9 7 [] := by decide +kernel
theorem certificate_3088_valid : certificate_3088.Valid 17 8 (patternOrder [[1,2,1,1,1,1,2]]) (patternClique [[1,2,1,1,1,1,2]]) (patternEdges [[1,2,1,1,1,1,2]]) (patternAmount [[1,2,1,1,1,1,2]]) (patternEdgeCount [[1,2,1,1,1,1,2]]) [] := certificate_3088_checked

theorem certificate_3089_checked : certificate_3089.Valid 17 8 17 certificate_3089_q certificate_3089_edges 9 7 [] := by decide +kernel
theorem certificate_3089_valid : certificate_3089.Valid 17 8 (patternOrder [[1,2,1,1,1,2,1]]) (patternClique [[1,2,1,1,1,2,1]]) (patternEdges [[1,2,1,1,1,2,1]]) (patternAmount [[1,2,1,1,1,2,1]]) (patternEdgeCount [[1,2,1,1,1,2,1]]) [] := certificate_3089_checked

theorem certificate_3090_checked : certificate_3090.Valid 17 8 17 certificate_3090_q certificate_3090_edges 9 6 [] := by decide +kernel
theorem certificate_3090_valid : certificate_3090.Valid 17 8 (patternOrder [[1,2,1,1,2],[2]]) (patternClique [[1,2,1,1,2],[2]]) (patternEdges [[1,2,1,1,2],[2]]) (patternAmount [[1,2,1,1,2],[2]]) (patternEdgeCount [[1,2,1,1,2],[2]]) [] := certificate_3090_checked

theorem certificate_3091_checked : certificate_3091.Valid 17 8 17 certificate_3091_q certificate_3091_edges 9 6 [] := by decide +kernel
theorem certificate_3091_valid : certificate_3091.Valid 17 8 (patternOrder [[1,2,1,2,1],[2]]) (patternClique [[1,2,1,2,1],[2]]) (patternEdges [[1,2,1,2,1],[2]]) (patternAmount [[1,2,1,2,1],[2]]) (patternEdgeCount [[1,2,1,2,1],[2]]) [] := certificate_3091_checked

theorem certificate_3092_checked : certificate_3092.Valid 17 8 17 certificate_3092_q certificate_3092_edges 9 5 [] := by decide +kernel
theorem certificate_3092_valid : certificate_3092.Valid 17 8 (patternOrder [[1,2,2],[2],[2]]) (patternClique [[1,2,2],[2],[2]]) (patternEdges [[1,2,2],[2],[2]]) (patternAmount [[1,2,2],[2],[2]]) (patternEdgeCount [[1,2,2],[2],[2]]) [] := certificate_3092_checked

theorem certificate_3093_checked : certificate_3093.Valid 17 8 17 certificate_3093_q certificate_3093_edges 9 5 [] := by decide +kernel
theorem certificate_3093_valid : certificate_3093.Valid 17 8 (patternOrder [[1,3,1],[2],[2]]) (patternClique [[1,3,1],[2],[2]]) (patternEdges [[1,3,1],[2],[2]]) (patternAmount [[1,3,1],[2],[2]]) (patternEdgeCount [[1,3,1],[2],[2]]) [] := certificate_3093_checked

theorem certificate_3094_checked : certificate_3094.Valid 17 8 16 certificate_3094_q certificate_3094_edges 8 4 [] := by decide +kernel
theorem certificate_3094_valid : certificate_3094.Valid 17 8 (patternOrder [[2],[2],[2],[2]]) (patternClique [[2],[2],[2],[2]]) (patternEdges [[2],[2],[2],[2]]) (patternAmount [[2],[2],[2],[2]]) (patternEdgeCount [[2],[2],[2],[2]]) [] := certificate_3094_checked

theorem certificate_3095_checked : certificate_3095.Valid 17 8 17 certificate_3095_q certificate_3095_edges 9 4 [] := by decide +kernel
theorem certificate_3095_valid : certificate_3095.Valid 17 8 (patternOrder [[2],[2],[2],[3]]) (patternClique [[2],[2],[2],[3]]) (patternEdges [[2],[2],[2],[3]]) (patternAmount [[2],[2],[2],[3]]) (patternEdgeCount [[2],[2],[2],[3]]) [] := certificate_3095_checked

theorem certificate_3096_checked : certificate_3096.Valid 17 8 17 certificate_3096_q certificate_3096_edges 9 5 [] := by decide +kernel
theorem certificate_3096_valid : certificate_3096.Valid 17 8 (patternOrder [[2],[2],[2,1,2]]) (patternClique [[2],[2],[2,1,2]]) (patternEdges [[2],[2],[2,1,2]]) (patternAmount [[2],[2],[2,1,2]]) (patternEdgeCount [[2],[2],[2,1,2]]) [] := certificate_3096_checked

theorem certificate_3097_checked : certificate_3097.Valid 17 8 17 certificate_3097_q certificate_3097_edges 9 6 [] := by decide +kernel
theorem certificate_3097_valid : certificate_3097.Valid 17 8 (patternOrder [[2],[2,1,1,1,2]]) (patternClique [[2],[2,1,1,1,2]]) (patternEdges [[2],[2,1,1,1,2]]) (patternAmount [[2],[2,1,1,1,2]]) (patternEdgeCount [[2],[2,1,1,1,2]]) [] := certificate_3097_checked

theorem certificate_3098_checked : certificate_3098.Valid 17 8 17 certificate_3098_q certificate_3098_edges 9 7 [] := by decide +kernel
theorem certificate_3098_valid : certificate_3098.Valid 17 8 (patternOrder [[2,1,1,1,1,1,2]]) (patternClique [[2,1,1,1,1,1,2]]) (patternEdges [[2,1,1,1,1,1,2]]) (patternAmount [[2,1,1,1,1,1,2]]) (patternEdgeCount [[2,1,1,1,1,1,2]]) [] := certificate_3098_checked

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

theorem patterns_17_8_46_verified : ∀ D ∈ patterns_17_8_46, PatternVerified 17 8 D := by

  simp only [patterns_17_8_46, List.forall_mem_cons]

  exact ⟨⟨certificate_2956, certificate_2956_valid⟩, ⟨⟨certificate_2957, certificate_2957_valid⟩, ⟨⟨certificate_2958, certificate_2958_valid⟩, ⟨⟨certificate_2959, certificate_2959_valid⟩, ⟨⟨certificate_2960, certificate_2960_valid⟩, ⟨⟨certificate_2961, certificate_2961_valid⟩, ⟨⟨certificate_2962, certificate_2962_valid⟩, ⟨⟨certificate_2963, certificate_2963_valid⟩, ⟨⟨certificate_2964, certificate_2964_valid⟩, ⟨⟨certificate_2965, certificate_2965_valid⟩, ⟨⟨certificate_2966, certificate_2966_valid⟩, ⟨⟨certificate_2967, certificate_2967_valid⟩, ⟨⟨certificate_2968, certificate_2968_valid⟩, ⟨⟨certificate_2969, certificate_2969_valid⟩, ⟨⟨certificate_2970, certificate_2970_valid⟩, ⟨⟨certificate_2971, certificate_2971_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem patterns_17_8_54_verified : ∀ D ∈ patterns_17_8_54, PatternVerified 17 8 D := by

  simp only [patterns_17_8_54, List.forall_mem_cons]

  exact ⟨⟨certificate_3084, certificate_3084_valid⟩, ⟨⟨certificate_3085, certificate_3085_valid⟩, ⟨⟨certificate_3086, certificate_3086_valid⟩, ⟨⟨certificate_3087, certificate_3087_valid⟩, ⟨⟨certificate_3088, certificate_3088_valid⟩, ⟨⟨certificate_3089, certificate_3089_valid⟩, ⟨⟨certificate_3090, certificate_3090_valid⟩, ⟨⟨certificate_3091, certificate_3091_valid⟩, ⟨⟨certificate_3092, certificate_3092_valid⟩, ⟨⟨certificate_3093, certificate_3093_valid⟩, ⟨⟨certificate_3094, certificate_3094_valid⟩, ⟨⟨certificate_3095, certificate_3095_valid⟩, ⟨⟨certificate_3096, certificate_3096_valid⟩, ⟨⟨certificate_3097, certificate_3097_valid⟩, ⟨⟨certificate_3098, certificate_3098_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem patterns_17_8_verified : ∀ D ∈ patterns_17_8, PatternVerified 17 8 D := by

  simp only [patterns_17_8, List.forall_mem_append]

  exact ⟨patterns_17_8_0_verified, ⟨patterns_17_8_1_verified, ⟨patterns_17_8_2_verified, ⟨patterns_17_8_3_verified, ⟨patterns_17_8_4_verified, ⟨patterns_17_8_5_verified, ⟨patterns_17_8_6_verified, ⟨patterns_17_8_7_verified, ⟨patterns_17_8_8_verified, ⟨patterns_17_8_9_verified, ⟨patterns_17_8_10_verified, ⟨patterns_17_8_11_verified, ⟨patterns_17_8_12_verified, ⟨patterns_17_8_13_verified, ⟨patterns_17_8_14_verified, ⟨patterns_17_8_15_verified, ⟨patterns_17_8_16_verified, ⟨patterns_17_8_17_verified, ⟨patterns_17_8_18_verified, ⟨patterns_17_8_19_verified, ⟨patterns_17_8_20_verified, ⟨patterns_17_8_21_verified, ⟨patterns_17_8_22_verified, ⟨patterns_17_8_23_verified, ⟨patterns_17_8_24_verified, ⟨patterns_17_8_25_verified, ⟨patterns_17_8_26_verified, ⟨patterns_17_8_27_verified, ⟨patterns_17_8_28_verified, ⟨patterns_17_8_29_verified, ⟨patterns_17_8_30_verified, ⟨patterns_17_8_31_verified, ⟨patterns_17_8_32_verified, ⟨patterns_17_8_33_verified, ⟨patterns_17_8_34_verified, ⟨patterns_17_8_35_verified, ⟨patterns_17_8_36_verified, ⟨patterns_17_8_37_verified, ⟨patterns_17_8_38_verified, ⟨patterns_17_8_39_verified, ⟨patterns_17_8_40_verified, ⟨patterns_17_8_41_verified, ⟨patterns_17_8_42_verified, ⟨patterns_17_8_43_verified, ⟨patterns_17_8_44_verified, ⟨patterns_17_8_45_verified, ⟨patterns_17_8_46_verified, ⟨patterns_17_8_47_verified, ⟨patterns_17_8_48_verified, ⟨patterns_17_8_49_verified, ⟨patterns_17_8_50_verified, ⟨patterns_17_8_51_verified, ⟨patterns_17_8_52_verified, ⟨patterns_17_8_53_verified, ⟨patterns_17_8_54_verified, by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem patterns_17_8_coverage : patternChoices 8 9 [] = patterns_17_8 := by decide +kernel

theorem finite_patterns_17_8_oai : ∀ D ∈ patternChoices 8 (17-8) [], PatternVerified 17 8 D := by

  rw [patterns_17_8_coverage]

  exact patterns_17_8_verified

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.finite_patterns_17_8_oai := @OAI.CycleClique.finite_patterns_17_8_oai
