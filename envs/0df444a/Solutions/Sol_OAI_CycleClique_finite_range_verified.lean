-- Prove2me | solution 1 for OAI.CycleClique.finite_range_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T00:14:47.366507+00:00
-- url     : https://prove2.me/submissions/392f98b1-14d4-4e4b-98b1-4687fe8eb88a

import Mathlib
import Definitions.Def_OAIQ107D038
import Definitions.Def_OAIQ107D129
import Definitions.Def_OAIQ107D133
import Definitions.Def_OAIQ107D134
import Theorems.Thm_OAI_CycleClique_finite_patterns_10_5
import Theorems.Thm_OAI_CycleClique_finite_patterns_10_6
import Theorems.Thm_OAI_CycleClique_finite_patterns_11_5
import Theorems.Thm_OAI_CycleClique_finite_patterns_11_6
import Theorems.Thm_OAI_CycleClique_finite_patterns_11_7
import Theorems.Thm_OAI_CycleClique_finite_patterns_12_6
import Theorems.Thm_OAI_CycleClique_finite_patterns_12_7
import Theorems.Thm_OAI_CycleClique_finite_patterns_12_8
import Theorems.Thm_OAI_CycleClique_finite_patterns_13_6
import Theorems.Thm_OAI_CycleClique_finite_patterns_13_7
import Theorems.Thm_OAI_CycleClique_finite_patterns_13_8
import Theorems.Thm_OAI_CycleClique_finite_patterns_14_7
import Theorems.Thm_OAI_CycleClique_finite_patterns_14_8
import Theorems.Thm_OAI_CycleClique_finite_patterns_15_7
import Theorems.Thm_OAI_CycleClique_finite_patterns_15_8
import Theorems.Thm_OAI_CycleClique_finite_patterns_16_8
import Theorems.Thm_OAI_CycleClique_finite_patterns_17_8
import Theorems.Thm_OAI_CycleClique_finite_patterns_6_3
import Theorems.Thm_OAI_CycleClique_finite_patterns_7_3
import Theorems.Thm_OAI_CycleClique_finite_patterns_8_4
import Theorems.Thm_OAI_CycleClique_finite_patterns_9_4
import Theorems.Thm_OAI_CycleClique_finite_patterns_9_5

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates001
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_0_checked : certificate_0.Valid 5 3 3 certificate_0_q certificate_0_edges 0 0 [] := by decide +kernel
theorem certificate_0_valid : certificate_0.Valid 5 3 (patternOrder [[],[],[]]) (patternClique [[],[],[]]) (patternEdges [[],[],[]]) (patternAmount [[],[],[]]) (patternEdgeCount [[],[],[]]) [] := certificate_0_checked

theorem certificate_1_part_1_checked : certificate_1_part_1.Valid 5 3 4 certificate_1_q certificate_1_part_1_E 1 1 certificate_1_part_1_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩, by decide +kernel⟩⟩⟩⟩

theorem certificate_1_checked : certificate_1.Valid 5 3 4 certificate_1_q certificate_1_E 1 1 certificate_1_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_1_part_1_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_1_valid : certificate_1.Valid 5 3 (patternOrder [[],[1]]) (patternClique [[],[1]]) (patternEdges [[],[1]]) (patternAmount [[],[1]]) (patternEdgeCount [[],[1]]) [] := certificate_1_checked

theorem certificate_2_part_2_checked : certificate_2_part_2.Valid 5 3 5 certificate_2_q certificate_2_part_2_E 2 1 certificate_2_part_2_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

theorem certificate_2_part_4_checked : certificate_2_part_4.Valid 5 3 5 certificate_2_q certificate_2_part_4_E 2 1 certificate_2_part_4_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem certificate_2_part_5_checked : certificate_2_part_5.Valid 5 3 6 certificate_2_q certificate_2_part_5_E 2 1 certificate_2_part_5_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩⟩⟩

theorem certificate_2_part_6_checked : certificate_2_part_6.Valid 5 3 5 certificate_2_q certificate_2_part_6_E 2 1 certificate_2_part_6_M := by exact ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩⟩, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩, by decide +kernel⟩⟩⟩

theorem certificate_2_part_3_checked : certificate_2_part_3.Valid 5 3 5 certificate_2_q certificate_2_part_3_E 2 1 certificate_2_part_3_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_2_part_4_checked⟩, ⟨by decide +kernel, by decide +kernel, certificate_2_part_5_checked, certificate_2_part_6_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_2_part_1_checked : certificate_2_part_1.Valid 5 3 5 certificate_2_q certificate_2_part_1_E 2 1 certificate_2_part_1_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_2_part_2_checked⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_2_part_3_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_2_checked : certificate_2.Valid 5 3 5 certificate_2_q certificate_2_E 2 1 certificate_2_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_2_part_1_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_2_valid : certificate_2.Valid 5 3 (patternOrder [[],[2]]) (patternClique [[],[2]]) (patternEdges [[],[2]]) (patternAmount [[],[2]]) (patternEdgeCount [[],[2]]) [] := certificate_2_checked

theorem certificate_3_part_1_checked : certificate_3_part_1.Valid 5 3 5 certificate_3_q certificate_3_part_1_E 2 2 certificate_3_part_1_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩⟩⟩⟩

theorem certificate_3_checked : certificate_3.Valid 5 3 5 certificate_3_q certificate_3_E 2 2 certificate_3_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_3_part_1_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_3_valid : certificate_3.Valid 5 3 (patternOrder [[1,1]]) (patternClique [[1,1]]) (patternEdges [[1,1]]) (patternAmount [[1,1]]) (patternEdgeCount [[1,1]]) [] := certificate_3_checked

theorem certificate_4_checked : certificate_4.Valid 5 4 4 certificate_4_q certificate_4_edges 0 0 [] := by decide +kernel
theorem certificate_4_valid : certificate_4.Valid 5 4 (patternOrder [[],[],[],[]]) (patternClique [[],[],[],[]]) (patternEdges [[],[],[],[]]) (patternAmount [[],[],[],[]]) (patternEdgeCount [[],[],[],[]]) [] := certificate_4_checked

theorem certificate_5_checked : certificate_5.Valid 5 4 5 certificate_5_q certificate_5_edges 1 1 [] := by decide +kernel
theorem certificate_5_valid : certificate_5.Valid 5 4 (patternOrder [[],[],[1]]) (patternClique [[],[],[1]]) (patternEdges [[],[],[1]]) (patternAmount [[],[],[1]]) (patternEdgeCount [[],[],[1]]) [] := certificate_5_checked

theorem certificate_6_checked : certificate_6.Valid 5 5 5 certificate_6_q certificate_6_edges 0 0 [] := by decide +kernel
theorem certificate_6_valid : certificate_6.Valid 5 5 (patternOrder [[],[],[],[],[]]) (patternClique [[],[],[],[],[]]) (patternEdges [[],[],[],[],[]]) (patternAmount [[],[],[],[],[]]) (patternEdgeCount [[],[],[],[],[]]) [] := certificate_6_checked

theorem certificate_13_checked : certificate_13.Valid 6 4 4 certificate_13_q certificate_13_edges 0 0 [] := by decide +kernel
theorem certificate_13_valid : certificate_13.Valid 6 4 (patternOrder [[],[],[],[]]) (patternClique [[],[],[],[]]) (patternEdges [[],[],[],[]]) (patternAmount [[],[],[],[]]) (patternEdgeCount [[],[],[],[]]) [] := certificate_13_checked

theorem certificate_14_checked : certificate_14.Valid 6 4 5 certificate_14_q certificate_14_edges 1 1 [] := by decide +kernel
theorem certificate_14_valid : certificate_14.Valid 6 4 (patternOrder [[],[],[1]]) (patternClique [[],[],[1]]) (patternEdges [[],[],[1]]) (patternAmount [[],[],[1]]) (patternEdgeCount [[],[],[1]]) [] := certificate_14_checked

theorem certificate_15_part_3_checked : certificate_15_part_3.Valid 6 4 6 certificate_15_q certificate_15_part_3_E 2 1 certificate_15_part_3_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem certificate_15_part_6_checked : certificate_15_part_6.Valid 6 4 6 certificate_15_q certificate_15_part_6_E 2 1 certificate_15_part_6_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem certificate_15_part_7_checked : certificate_15_part_7.Valid 6 4 6 certificate_15_q certificate_15_part_7_E 2 1 certificate_15_part_7_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩, by decide +kernel⟩⟩

theorem certificate_15_part_5_checked : certificate_15_part_5.Valid 6 4 6 certificate_15_q certificate_15_part_5_E 2 1 certificate_15_part_5_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_15_part_6_checked⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_15_part_7_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_15_part_4_checked : certificate_15_part_4.Valid 6 4 6 certificate_15_q certificate_15_part_4_E 2 1 certificate_15_part_4_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_15_part_5_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_15_part_2_checked : certificate_15_part_2.Valid 6 4 6 certificate_15_q certificate_15_part_2_E 2 1 certificate_15_part_2_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_15_part_3_checked⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_15_part_4_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_15_part_1_checked : certificate_15_part_1.Valid 6 4 6 certificate_15_q certificate_15_part_1_E 2 1 certificate_15_part_1_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_15_part_2_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_15_checked : certificate_15.Valid 6 4 6 certificate_15_q certificate_15_E 2 1 certificate_15_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_15_part_1_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_15_valid : certificate_15.Valid 6 4 (patternOrder [[],[],[2]]) (patternClique [[],[],[2]]) (patternEdges [[],[],[2]]) (patternAmount [[],[],[2]]) (patternEdgeCount [[],[],[2]]) [] := certificate_15_checked

theorem certificate_16_part_2_checked : certificate_16_part_2.Valid 6 4 6 certificate_16_q certificate_16_part_2_E 2 2 certificate_16_part_2_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩⟩

theorem certificate_16_part_1_checked : certificate_16_part_1.Valid 6 4 6 certificate_16_q certificate_16_part_1_E 2 2 certificate_16_part_1_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_16_part_2_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_16_checked : certificate_16.Valid 6 4 6 certificate_16_q certificate_16_E 2 2 certificate_16_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_16_part_1_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_16_valid : certificate_16.Valid 6 4 (patternOrder [[],[1,1]]) (patternClique [[],[1,1]]) (patternEdges [[],[1,1]]) (patternAmount [[],[1,1]]) (patternEdgeCount [[],[1,1]]) [] := certificate_16_checked

theorem certificate_17_checked : certificate_17.Valid 6 4 6 certificate_17_q certificate_17_edges 2 2 [] := by decide +kernel
theorem certificate_17_valid : certificate_17.Valid 6 4 (patternOrder [[1],[1]]) (patternClique [[1],[1]]) (patternEdges [[1],[1]]) (patternAmount [[1],[1]]) (patternEdgeCount [[1],[1]]) [] := certificate_17_checked

theorem certificate_18_checked : certificate_18.Valid 6 5 5 certificate_18_q certificate_18_edges 0 0 [] := by decide +kernel
theorem certificate_18_valid : certificate_18.Valid 6 5 (patternOrder [[],[],[],[],[]]) (patternClique [[],[],[],[],[]]) (patternEdges [[],[],[],[],[]]) (patternAmount [[],[],[],[],[]]) (patternEdgeCount [[],[],[],[],[]]) [] := certificate_18_checked

theorem certificate_19_checked : certificate_19.Valid 6 5 6 certificate_19_q certificate_19_edges 1 1 [] := by decide +kernel
theorem certificate_19_valid : certificate_19.Valid 6 5 (patternOrder [[],[],[],[1]]) (patternClique [[],[],[],[1]]) (patternEdges [[],[],[],[1]]) (patternAmount [[],[],[],[1]]) (patternEdgeCount [[],[],[],[1]]) [] := certificate_19_checked

theorem certificate_20_checked : certificate_20.Valid 6 6 6 certificate_20_q certificate_20_edges 0 0 [] := by decide +kernel
theorem certificate_20_valid : certificate_20.Valid 6 6 (patternOrder [[],[],[],[],[],[]]) (patternClique [[],[],[],[],[],[]]) (patternEdges [[],[],[],[],[],[]]) (patternAmount [[],[],[],[],[],[]]) (patternEdgeCount [[],[],[],[],[],[]]) [] := certificate_20_checked

theorem certificate_30_checked : certificate_30.Valid 7 4 4 certificate_30_q certificate_30_edges 0 0 [] := by decide +kernel
theorem certificate_30_valid : certificate_30.Valid 7 4 (patternOrder [[],[],[],[]]) (patternClique [[],[],[],[]]) (patternEdges [[],[],[],[]]) (patternAmount [[],[],[],[]]) (patternEdgeCount [[],[],[],[]]) [] := certificate_30_checked

theorem certificate_31_checked : certificate_31.Valid 7 4 5 certificate_31_q certificate_31_edges 1 1 [] := by decide +kernel
theorem certificate_31_valid : certificate_31.Valid 7 4 (patternOrder [[],[],[1]]) (patternClique [[],[],[1]]) (patternEdges [[],[],[1]]) (patternAmount [[],[],[1]]) (patternEdgeCount [[],[],[1]]) [] := certificate_31_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates002
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_32_checked : certificate_32.Valid 7 4 6 certificate_32_q certificate_32_edges 2 1 [] := by decide +kernel
theorem certificate_32_valid : certificate_32.Valid 7 4 (patternOrder [[],[],[2]]) (patternClique [[],[],[2]]) (patternEdges [[],[],[2]]) (patternAmount [[],[],[2]]) (patternEdgeCount [[],[],[2]]) [] := certificate_32_checked

theorem certificate_33_part_3_checked : certificate_33_part_3.Valid 7 4 7 certificate_33_q certificate_33_part_3_E 3 1 certificate_33_part_3_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem certificate_33_part_7_checked : certificate_33_part_7.Valid 7 4 8 certificate_33_q certificate_33_part_7_E 3 1 certificate_33_part_7_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩

theorem certificate_33_part_8_checked : certificate_33_part_8.Valid 7 4 7 certificate_33_q certificate_33_part_8_E 3 1 certificate_33_part_8_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩⟩⟩

theorem certificate_33_part_10_checked : certificate_33_part_10.Valid 7 4 7 certificate_33_q certificate_33_part_10_E 3 1 certificate_33_part_10_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

theorem certificate_33_part_12_checked : certificate_33_part_12.Valid 7 4 7 certificate_33_q certificate_33_part_12_E 3 1 certificate_33_part_12_M := by exact ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩, by decide +kernel⟩

theorem certificate_33_part_11_checked : certificate_33_part_11.Valid 7 4 7 certificate_33_q certificate_33_part_11_E 3 1 certificate_33_part_11_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_33_part_12_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_33_part_9_checked : certificate_33_part_9.Valid 7 4 7 certificate_33_q certificate_33_part_9_E 3 1 certificate_33_part_9_M := by exact ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩⟩, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, certificate_33_part_10_checked, certificate_33_part_11_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_33_part_6_checked : certificate_33_part_6.Valid 7 4 7 certificate_33_q certificate_33_part_6_E 3 1 certificate_33_part_6_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_33_part_7_checked⟩⟩⟩⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, certificate_33_part_8_checked, certificate_33_part_9_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_33_part_5_checked : certificate_33_part_5.Valid 7 4 7 certificate_33_q certificate_33_part_5_E 3 1 certificate_33_part_5_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_33_part_6_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_33_part_4_checked : certificate_33_part_4.Valid 7 4 7 certificate_33_q certificate_33_part_4_E 3 1 certificate_33_part_4_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_33_part_5_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_33_part_2_checked : certificate_33_part_2.Valid 7 4 7 certificate_33_q certificate_33_part_2_E 3 1 certificate_33_part_2_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_33_part_3_checked⟩⟩⟩⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_33_part_4_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_33_part_1_checked : certificate_33_part_1.Valid 7 4 7 certificate_33_q certificate_33_part_1_E 3 1 certificate_33_part_1_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_33_part_2_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_33_checked : certificate_33.Valid 7 4 7 certificate_33_q certificate_33_E 3 1 certificate_33_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_33_part_1_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_33_valid : certificate_33.Valid 7 4 (patternOrder [[],[],[3]]) (patternClique [[],[],[3]]) (patternEdges [[],[],[3]]) (patternAmount [[],[],[3]]) (patternEdgeCount [[],[],[3]]) [] := certificate_33_checked

theorem certificate_34_checked : certificate_34.Valid 7 4 6 certificate_34_q certificate_34_edges 2 2 [] := by decide +kernel
theorem certificate_34_valid : certificate_34.Valid 7 4 (patternOrder [[],[1,1]]) (patternClique [[],[1,1]]) (patternEdges [[],[1,1]]) (patternAmount [[],[1,1]]) (patternEdgeCount [[],[1,1]]) [] := certificate_34_checked

theorem certificate_35_checked : certificate_35.Valid 7 4 7 certificate_35_q certificate_35_edges 3 2 [] := by decide +kernel
theorem certificate_35_valid : certificate_35.Valid 7 4 (patternOrder [[],[1,2]]) (patternClique [[],[1,2]]) (patternEdges [[],[1,2]]) (patternAmount [[],[1,2]]) (patternEdgeCount [[],[1,2]]) [] := certificate_35_checked

theorem certificate_36_checked : certificate_36.Valid 7 4 6 certificate_36_q certificate_36_edges 2 2 [] := by decide +kernel
theorem certificate_36_valid : certificate_36.Valid 7 4 (patternOrder [[1],[1]]) (patternClique [[1],[1]]) (patternEdges [[1],[1]]) (patternAmount [[1],[1]]) (patternEdgeCount [[1],[1]]) [] := certificate_36_checked

theorem certificate_37_checked : certificate_37.Valid 7 4 7 certificate_37_q certificate_37_edges 3 2 [] := by decide +kernel
theorem certificate_37_valid : certificate_37.Valid 7 4 (patternOrder [[1],[2]]) (patternClique [[1],[2]]) (patternEdges [[1],[2]]) (patternAmount [[1],[2]]) (patternEdgeCount [[1],[2]]) [] := certificate_37_checked

theorem certificate_38_checked : certificate_38.Valid 7 4 7 certificate_38_q certificate_38_edges 3 3 [] := by decide +kernel
theorem certificate_38_valid : certificate_38.Valid 7 4 (patternOrder [[1,1,1]]) (patternClique [[1,1,1]]) (patternEdges [[1,1,1]]) (patternAmount [[1,1,1]]) (patternEdgeCount [[1,1,1]]) [] := certificate_38_checked

theorem certificate_39_checked : certificate_39.Valid 7 5 5 certificate_39_q certificate_39_edges 0 0 [] := by decide +kernel
theorem certificate_39_valid : certificate_39.Valid 7 5 (patternOrder [[],[],[],[],[]]) (patternClique [[],[],[],[],[]]) (patternEdges [[],[],[],[],[]]) (patternAmount [[],[],[],[],[]]) (patternEdgeCount [[],[],[],[],[]]) [] := certificate_39_checked

theorem certificate_40_checked : certificate_40.Valid 7 5 6 certificate_40_q certificate_40_edges 1 1 [] := by decide +kernel
theorem certificate_40_valid : certificate_40.Valid 7 5 (patternOrder [[],[],[],[1]]) (patternClique [[],[],[],[1]]) (patternEdges [[],[],[],[1]]) (patternAmount [[],[],[],[1]]) (patternEdgeCount [[],[],[],[1]]) [] := certificate_40_checked

theorem certificate_41_checked : certificate_41.Valid 7 5 7 certificate_41_q certificate_41_edges 2 1 [] := by decide +kernel
theorem certificate_41_valid : certificate_41.Valid 7 5 (patternOrder [[],[],[],[2]]) (patternClique [[],[],[],[2]]) (patternEdges [[],[],[],[2]]) (patternAmount [[],[],[],[2]]) (patternEdgeCount [[],[],[],[2]]) [] := certificate_41_checked

theorem certificate_42_checked : certificate_42.Valid 7 5 7 certificate_42_q certificate_42_edges 2 2 [] := by decide +kernel
theorem certificate_42_valid : certificate_42.Valid 7 5 (patternOrder [[],[],[1,1]]) (patternClique [[],[],[1,1]]) (patternEdges [[],[],[1,1]]) (patternAmount [[],[],[1,1]]) (patternEdgeCount [[],[],[1,1]]) [] := certificate_42_checked

theorem certificate_43_checked : certificate_43.Valid 7 5 7 certificate_43_q certificate_43_edges 2 2 [] := by decide +kernel
theorem certificate_43_valid : certificate_43.Valid 7 5 (patternOrder [[],[1],[1]]) (patternClique [[],[1],[1]]) (patternEdges [[],[1],[1]]) (patternAmount [[],[1],[1]]) (patternEdgeCount [[],[1],[1]]) [] := certificate_43_checked

theorem certificate_44_checked : certificate_44.Valid 7 6 6 certificate_44_q certificate_44_edges 0 0 [] := by decide +kernel
theorem certificate_44_valid : certificate_44.Valid 7 6 (patternOrder [[],[],[],[],[],[]]) (patternClique [[],[],[],[],[],[]]) (patternEdges [[],[],[],[],[],[]]) (patternAmount [[],[],[],[],[],[]]) (patternEdgeCount [[],[],[],[],[],[]]) [] := certificate_44_checked

theorem certificate_45_checked : certificate_45.Valid 7 6 7 certificate_45_q certificate_45_edges 1 1 [] := by decide +kernel
theorem certificate_45_valid : certificate_45.Valid 7 6 (patternOrder [[],[],[],[],[1]]) (patternClique [[],[],[],[],[1]]) (patternEdges [[],[],[],[],[1]]) (patternAmount [[],[],[],[],[1]]) (patternEdgeCount [[],[],[],[],[1]]) [] := certificate_45_checked

theorem certificate_46_checked : certificate_46.Valid 7 7 7 certificate_46_q certificate_46_edges 0 0 [] := by decide +kernel
theorem certificate_46_valid : certificate_46.Valid 7 7 (patternOrder [[],[],[],[],[],[],[]]) (patternClique [[],[],[],[],[],[],[]]) (patternEdges [[],[],[],[],[],[],[]]) (patternAmount [[],[],[],[],[],[],[]]) (patternEdgeCount [[],[],[],[],[],[],[]]) [] := certificate_46_checked

theorem certificate_63_checked : certificate_63.Valid 8 5 5 certificate_63_q certificate_63_edges 0 0 [] := by decide +kernel
theorem certificate_63_valid : certificate_63.Valid 8 5 (patternOrder [[],[],[],[],[]]) (patternClique [[],[],[],[],[]]) (patternEdges [[],[],[],[],[]]) (patternAmount [[],[],[],[],[]]) (patternEdgeCount [[],[],[],[],[]]) [] := certificate_63_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates003
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_64_checked : certificate_64.Valid 8 5 6 certificate_64_q certificate_64_edges 1 1 [] := by decide +kernel
theorem certificate_64_valid : certificate_64.Valid 8 5 (patternOrder [[],[],[],[1]]) (patternClique [[],[],[],[1]]) (patternEdges [[],[],[],[1]]) (patternAmount [[],[],[],[1]]) (patternEdgeCount [[],[],[],[1]]) [] := certificate_64_checked

theorem certificate_65_checked : certificate_65.Valid 8 5 7 certificate_65_q certificate_65_edges 2 1 [] := by decide +kernel
theorem certificate_65_valid : certificate_65.Valid 8 5 (patternOrder [[],[],[],[2]]) (patternClique [[],[],[],[2]]) (patternEdges [[],[],[],[2]]) (patternAmount [[],[],[],[2]]) (patternEdgeCount [[],[],[],[2]]) [] := certificate_65_checked

theorem certificate_66_part_3_checked : certificate_66_part_3.Valid 8 5 8 certificate_66_q certificate_66_part_3_E 3 1 certificate_66_part_3_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩

theorem certificate_66_part_5_checked : certificate_66_part_5.Valid 8 5 8 certificate_66_q certificate_66_part_5_E 3 1 certificate_66_part_5_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem certificate_66_part_8_checked : certificate_66_part_8.Valid 8 5 9 certificate_66_q certificate_66_part_8_E 3 1 certificate_66_part_8_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

theorem certificate_66_part_10_checked : certificate_66_part_10.Valid 8 5 8 certificate_66_q certificate_66_part_10_E 3 1 certificate_66_part_10_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem certificate_66_part_11_checked : certificate_66_part_11.Valid 8 5 8 certificate_66_q certificate_66_part_11_E 3 1 certificate_66_part_11_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem certificate_66_part_12_checked : certificate_66_part_12.Valid 8 5 8 certificate_66_q certificate_66_part_12_E 3 1 certificate_66_part_12_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩⟩, by decide +kernel⟩⟩⟩

theorem certificate_66_part_9_checked : certificate_66_part_9.Valid 8 5 8 certificate_66_q certificate_66_part_9_E 3 1 certificate_66_part_9_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩⟩, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_66_part_10_checked⟩⟩⟩⟩, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_66_part_11_checked⟩⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_66_part_12_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_66_part_7_checked : certificate_66_part_7.Valid 8 5 8 certificate_66_q certificate_66_part_7_E 3 1 certificate_66_part_7_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_66_part_8_checked⟩⟩⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_66_part_9_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_66_part_6_checked : certificate_66_part_6.Valid 8 5 8 certificate_66_q certificate_66_part_6_E 3 1 certificate_66_part_6_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_66_part_7_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_66_part_4_checked : certificate_66_part_4.Valid 8 5 8 certificate_66_q certificate_66_part_4_E 3 1 certificate_66_part_4_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_66_part_5_checked⟩⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_66_part_6_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_66_part_2_checked : certificate_66_part_2.Valid 8 5 8 certificate_66_q certificate_66_part_2_E 3 1 certificate_66_part_2_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_66_part_3_checked⟩⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_66_part_4_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_66_part_1_checked : certificate_66_part_1.Valid 8 5 8 certificate_66_q certificate_66_part_1_E 3 1 certificate_66_part_1_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_66_part_2_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_66_checked : certificate_66.Valid 8 5 8 certificate_66_q certificate_66_E 3 1 certificate_66_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_66_part_1_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_66_valid : certificate_66.Valid 8 5 (patternOrder [[],[],[],[3]]) (patternClique [[],[],[],[3]]) (patternEdges [[],[],[],[3]]) (patternAmount [[],[],[],[3]]) (patternEdgeCount [[],[],[],[3]]) [] := certificate_66_checked

theorem certificate_67_checked : certificate_67.Valid 8 5 7 certificate_67_q certificate_67_edges 2 2 [] := by decide +kernel
theorem certificate_67_valid : certificate_67.Valid 8 5 (patternOrder [[],[],[1,1]]) (patternClique [[],[],[1,1]]) (patternEdges [[],[],[1,1]]) (patternAmount [[],[],[1,1]]) (patternEdgeCount [[],[],[1,1]]) [] := certificate_67_checked

theorem certificate_68_checked : certificate_68.Valid 8 5 8 certificate_68_q certificate_68_edges 3 2 [] := by decide +kernel
theorem certificate_68_valid : certificate_68.Valid 8 5 (patternOrder [[],[],[1,2]]) (patternClique [[],[],[1,2]]) (patternEdges [[],[],[1,2]]) (patternAmount [[],[],[1,2]]) (patternEdgeCount [[],[],[1,2]]) [] := certificate_68_checked

theorem certificate_69_checked : certificate_69.Valid 8 5 7 certificate_69_q certificate_69_edges 2 2 [] := by decide +kernel
theorem certificate_69_valid : certificate_69.Valid 8 5 (patternOrder [[],[1],[1]]) (patternClique [[],[1],[1]]) (patternEdges [[],[1],[1]]) (patternAmount [[],[1],[1]]) (patternEdgeCount [[],[1],[1]]) [] := certificate_69_checked

theorem certificate_70_checked : certificate_70.Valid 8 5 8 certificate_70_q certificate_70_edges 3 2 [] := by decide +kernel
theorem certificate_70_valid : certificate_70.Valid 8 5 (patternOrder [[],[1],[2]]) (patternClique [[],[1],[2]]) (patternEdges [[],[1],[2]]) (patternAmount [[],[1],[2]]) (patternEdgeCount [[],[1],[2]]) [] := certificate_70_checked

theorem certificate_71_checked : certificate_71.Valid 8 5 8 certificate_71_q certificate_71_edges 3 3 [] := by decide +kernel
theorem certificate_71_valid : certificate_71.Valid 8 5 (patternOrder [[],[1,1,1]]) (patternClique [[],[1,1,1]]) (patternEdges [[],[1,1,1]]) (patternAmount [[],[1,1,1]]) (patternEdgeCount [[],[1,1,1]]) [] := certificate_71_checked

theorem certificate_72_checked : certificate_72.Valid 8 5 8 certificate_72_q certificate_72_edges 3 3 [] := by decide +kernel
theorem certificate_72_valid : certificate_72.Valid 8 5 (patternOrder [[1],[1,1]]) (patternClique [[1],[1,1]]) (patternEdges [[1],[1,1]]) (patternAmount [[1],[1,1]]) (patternEdgeCount [[1],[1,1]]) [] := certificate_72_checked

theorem certificate_73_checked : certificate_73.Valid 8 6 6 certificate_73_q certificate_73_edges 0 0 [] := by decide +kernel
theorem certificate_73_valid : certificate_73.Valid 8 6 (patternOrder [[],[],[],[],[],[]]) (patternClique [[],[],[],[],[],[]]) (patternEdges [[],[],[],[],[],[]]) (patternAmount [[],[],[],[],[],[]]) (patternEdgeCount [[],[],[],[],[],[]]) [] := certificate_73_checked

theorem certificate_74_checked : certificate_74.Valid 8 6 7 certificate_74_q certificate_74_edges 1 1 [] := by decide +kernel
theorem certificate_74_valid : certificate_74.Valid 8 6 (patternOrder [[],[],[],[],[1]]) (patternClique [[],[],[],[],[1]]) (patternEdges [[],[],[],[],[1]]) (patternAmount [[],[],[],[],[1]]) (patternEdgeCount [[],[],[],[],[1]]) [] := certificate_74_checked

theorem certificate_75_checked : certificate_75.Valid 8 6 8 certificate_75_q certificate_75_edges 2 1 [] := by decide +kernel
theorem certificate_75_valid : certificate_75.Valid 8 6 (patternOrder [[],[],[],[],[2]]) (patternClique [[],[],[],[],[2]]) (patternEdges [[],[],[],[],[2]]) (patternAmount [[],[],[],[],[2]]) (patternEdgeCount [[],[],[],[],[2]]) [] := certificate_75_checked

theorem certificate_76_checked : certificate_76.Valid 8 6 8 certificate_76_q certificate_76_edges 2 2 [] := by decide +kernel
theorem certificate_76_valid : certificate_76.Valid 8 6 (patternOrder [[],[],[],[1,1]]) (patternClique [[],[],[],[1,1]]) (patternEdges [[],[],[],[1,1]]) (patternAmount [[],[],[],[1,1]]) (patternEdgeCount [[],[],[],[1,1]]) [] := certificate_76_checked

theorem certificate_77_checked : certificate_77.Valid 8 6 8 certificate_77_q certificate_77_edges 2 2 [] := by decide +kernel
theorem certificate_77_valid : certificate_77.Valid 8 6 (patternOrder [[],[],[1],[1]]) (patternClique [[],[],[1],[1]]) (patternEdges [[],[],[1],[1]]) (patternAmount [[],[],[1],[1]]) (patternEdgeCount [[],[],[1],[1]]) [] := certificate_77_checked

theorem certificate_78_checked : certificate_78.Valid 8 7 7 certificate_78_q certificate_78_edges 0 0 [] := by decide +kernel
theorem certificate_78_valid : certificate_78.Valid 8 7 (patternOrder [[],[],[],[],[],[],[]]) (patternClique [[],[],[],[],[],[],[]]) (patternEdges [[],[],[],[],[],[],[]]) (patternAmount [[],[],[],[],[],[],[]]) (patternEdgeCount [[],[],[],[],[],[],[]]) [] := certificate_78_checked

theorem certificate_79_checked : certificate_79.Valid 8 7 8 certificate_79_q certificate_79_edges 1 1 [] := by decide +kernel
theorem certificate_79_valid : certificate_79.Valid 8 7 (patternOrder [[],[],[],[],[],[1]]) (patternClique [[],[],[],[],[],[1]]) (patternEdges [[],[],[],[],[],[1]]) (patternAmount [[],[],[],[],[],[1]]) (patternEdgeCount [[],[],[],[],[],[1]]) [] := certificate_79_checked

theorem certificate_80_checked : certificate_80.Valid 8 8 8 certificate_80_q certificate_80_edges 0 0 [] := by decide +kernel
theorem certificate_80_valid : certificate_80.Valid 8 8 (patternOrder [[],[],[],[],[],[],[],[]]) (patternClique [[],[],[],[],[],[],[],[]]) (patternEdges [[],[],[],[],[],[],[],[]]) (patternAmount [[],[],[],[],[],[],[],[]]) (patternEdgeCount [[],[],[],[],[],[],[],[]]) [] := certificate_80_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates004
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_126_checked : certificate_126.Valid 9 6 6 certificate_126_q certificate_126_edges 0 0 [] := by decide +kernel
theorem certificate_126_valid : certificate_126.Valid 9 6 (patternOrder [[],[],[],[],[],[]]) (patternClique [[],[],[],[],[],[]]) (patternEdges [[],[],[],[],[],[]]) (patternAmount [[],[],[],[],[],[]]) (patternEdgeCount [[],[],[],[],[],[]]) [] := certificate_126_checked

theorem certificate_127_checked : certificate_127.Valid 9 6 7 certificate_127_q certificate_127_edges 1 1 [] := by decide +kernel
theorem certificate_127_valid : certificate_127.Valid 9 6 (patternOrder [[],[],[],[],[1]]) (patternClique [[],[],[],[],[1]]) (patternEdges [[],[],[],[],[1]]) (patternAmount [[],[],[],[],[1]]) (patternEdgeCount [[],[],[],[],[1]]) [] := certificate_127_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates005
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_128_checked : certificate_128.Valid 9 6 8 certificate_128_q certificate_128_edges 2 1 [] := by decide +kernel
theorem certificate_128_valid : certificate_128.Valid 9 6 (patternOrder [[],[],[],[],[2]]) (patternClique [[],[],[],[],[2]]) (patternEdges [[],[],[],[],[2]]) (patternAmount [[],[],[],[],[2]]) (patternEdgeCount [[],[],[],[],[2]]) [] := certificate_128_checked

theorem certificate_129_checked : certificate_129.Valid 9 6 9 certificate_129_q certificate_129_edges 3 1 [] := by decide +kernel
theorem certificate_129_valid : certificate_129.Valid 9 6 (patternOrder [[],[],[],[],[3]]) (patternClique [[],[],[],[],[3]]) (patternEdges [[],[],[],[],[3]]) (patternAmount [[],[],[],[],[3]]) (patternEdgeCount [[],[],[],[],[3]]) [] := certificate_129_checked

theorem certificate_130_checked : certificate_130.Valid 9 6 8 certificate_130_q certificate_130_edges 2 2 [] := by decide +kernel
theorem certificate_130_valid : certificate_130.Valid 9 6 (patternOrder [[],[],[],[1,1]]) (patternClique [[],[],[],[1,1]]) (patternEdges [[],[],[],[1,1]]) (patternAmount [[],[],[],[1,1]]) (patternEdgeCount [[],[],[],[1,1]]) [] := certificate_130_checked

theorem certificate_131_checked : certificate_131.Valid 9 6 9 certificate_131_q certificate_131_edges 3 2 [] := by decide +kernel
theorem certificate_131_valid : certificate_131.Valid 9 6 (patternOrder [[],[],[],[1,2]]) (patternClique [[],[],[],[1,2]]) (patternEdges [[],[],[],[1,2]]) (patternAmount [[],[],[],[1,2]]) (patternEdgeCount [[],[],[],[1,2]]) [] := certificate_131_checked

theorem certificate_132_checked : certificate_132.Valid 9 6 8 certificate_132_q certificate_132_edges 2 2 [] := by decide +kernel
theorem certificate_132_valid : certificate_132.Valid 9 6 (patternOrder [[],[],[1],[1]]) (patternClique [[],[],[1],[1]]) (patternEdges [[],[],[1],[1]]) (patternAmount [[],[],[1],[1]]) (patternEdgeCount [[],[],[1],[1]]) [] := certificate_132_checked

theorem certificate_133_checked : certificate_133.Valid 9 6 9 certificate_133_q certificate_133_edges 3 2 [] := by decide +kernel
theorem certificate_133_valid : certificate_133.Valid 9 6 (patternOrder [[],[],[1],[2]]) (patternClique [[],[],[1],[2]]) (patternEdges [[],[],[1],[2]]) (patternAmount [[],[],[1],[2]]) (patternEdgeCount [[],[],[1],[2]]) [] := certificate_133_checked

theorem certificate_134_checked : certificate_134.Valid 9 6 9 certificate_134_q certificate_134_edges 3 3 [] := by decide +kernel
theorem certificate_134_valid : certificate_134.Valid 9 6 (patternOrder [[],[],[1,1,1]]) (patternClique [[],[],[1,1,1]]) (patternEdges [[],[],[1,1,1]]) (patternAmount [[],[],[1,1,1]]) (patternEdgeCount [[],[],[1,1,1]]) [] := certificate_134_checked

theorem certificate_135_checked : certificate_135.Valid 9 6 9 certificate_135_q certificate_135_edges 3 3 [] := by decide +kernel
theorem certificate_135_valid : certificate_135.Valid 9 6 (patternOrder [[],[1],[1,1]]) (patternClique [[],[1],[1,1]]) (patternEdges [[],[1],[1,1]]) (patternAmount [[],[1],[1,1]]) (patternEdgeCount [[],[1],[1,1]]) [] := certificate_135_checked

theorem certificate_136_checked : certificate_136.Valid 9 6 9 certificate_136_q certificate_136_edges 3 3 [] := by decide +kernel
theorem certificate_136_valid : certificate_136.Valid 9 6 (patternOrder [[1],[1],[1]]) (patternClique [[1],[1],[1]]) (patternEdges [[1],[1],[1]]) (patternAmount [[1],[1],[1]]) (patternEdgeCount [[1],[1],[1]]) [] := certificate_136_checked

theorem certificate_137_checked : certificate_137.Valid 9 7 7 certificate_137_q certificate_137_edges 0 0 [] := by decide +kernel
theorem certificate_137_valid : certificate_137.Valid 9 7 (patternOrder [[],[],[],[],[],[],[]]) (patternClique [[],[],[],[],[],[],[]]) (patternEdges [[],[],[],[],[],[],[]]) (patternAmount [[],[],[],[],[],[],[]]) (patternEdgeCount [[],[],[],[],[],[],[]]) [] := certificate_137_checked

theorem certificate_138_checked : certificate_138.Valid 9 7 8 certificate_138_q certificate_138_edges 1 1 [] := by decide +kernel
theorem certificate_138_valid : certificate_138.Valid 9 7 (patternOrder [[],[],[],[],[],[1]]) (patternClique [[],[],[],[],[],[1]]) (patternEdges [[],[],[],[],[],[1]]) (patternAmount [[],[],[],[],[],[1]]) (patternEdgeCount [[],[],[],[],[],[1]]) [] := certificate_138_checked

theorem certificate_139_checked : certificate_139.Valid 9 7 9 certificate_139_q certificate_139_edges 2 1 [] := by decide +kernel
theorem certificate_139_valid : certificate_139.Valid 9 7 (patternOrder [[],[],[],[],[],[2]]) (patternClique [[],[],[],[],[],[2]]) (patternEdges [[],[],[],[],[],[2]]) (patternAmount [[],[],[],[],[],[2]]) (patternEdgeCount [[],[],[],[],[],[2]]) [] := certificate_139_checked

theorem certificate_140_checked : certificate_140.Valid 9 7 9 certificate_140_q certificate_140_edges 2 2 [] := by decide +kernel
theorem certificate_140_valid : certificate_140.Valid 9 7 (patternOrder [[],[],[],[],[1,1]]) (patternClique [[],[],[],[],[1,1]]) (patternEdges [[],[],[],[],[1,1]]) (patternAmount [[],[],[],[],[1,1]]) (patternEdgeCount [[],[],[],[],[1,1]]) [] := certificate_140_checked

theorem certificate_141_checked : certificate_141.Valid 9 7 9 certificate_141_q certificate_141_edges 2 2 [] := by decide +kernel
theorem certificate_141_valid : certificate_141.Valid 9 7 (patternOrder [[],[],[],[1],[1]]) (patternClique [[],[],[],[1],[1]]) (patternEdges [[],[],[],[1],[1]]) (patternAmount [[],[],[],[1],[1]]) (patternEdgeCount [[],[],[],[1],[1]]) [] := certificate_141_checked

theorem certificate_142_checked : certificate_142.Valid 9 8 8 certificate_142_q certificate_142_edges 0 0 [] := by decide +kernel
theorem certificate_142_valid : certificate_142.Valid 9 8 (patternOrder [[],[],[],[],[],[],[],[]]) (patternClique [[],[],[],[],[],[],[],[]]) (patternEdges [[],[],[],[],[],[],[],[]]) (patternAmount [[],[],[],[],[],[],[],[]]) (patternEdgeCount [[],[],[],[],[],[],[],[]]) [] := certificate_142_checked

theorem certificate_143_checked : certificate_143.Valid 9 8 9 certificate_143_q certificate_143_edges 1 1 [] := by decide +kernel
theorem certificate_143_valid : certificate_143.Valid 9 8 (patternOrder [[],[],[],[],[],[],[1]]) (patternClique [[],[],[],[],[],[],[1]]) (patternEdges [[],[],[],[],[],[],[1]]) (patternAmount [[],[],[],[],[],[],[1]]) (patternEdgeCount [[],[],[],[],[],[],[1]]) [] := certificate_143_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates007
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_203_checked : certificate_203.Valid 10 7 7 certificate_203_q certificate_203_edges 0 0 [] := by decide +kernel
theorem certificate_203_valid : certificate_203.Valid 10 7 (patternOrder [[],[],[],[],[],[],[]]) (patternClique [[],[],[],[],[],[],[]]) (patternEdges [[],[],[],[],[],[],[]]) (patternAmount [[],[],[],[],[],[],[]]) (patternEdgeCount [[],[],[],[],[],[],[]]) [] := certificate_203_checked

theorem certificate_204_checked : certificate_204.Valid 10 7 8 certificate_204_q certificate_204_edges 1 1 [] := by decide +kernel
theorem certificate_204_valid : certificate_204.Valid 10 7 (patternOrder [[],[],[],[],[],[1]]) (patternClique [[],[],[],[],[],[1]]) (patternEdges [[],[],[],[],[],[1]]) (patternAmount [[],[],[],[],[],[1]]) (patternEdgeCount [[],[],[],[],[],[1]]) [] := certificate_204_checked

theorem certificate_205_checked : certificate_205.Valid 10 7 9 certificate_205_q certificate_205_edges 2 1 [] := by decide +kernel
theorem certificate_205_valid : certificate_205.Valid 10 7 (patternOrder [[],[],[],[],[],[2]]) (patternClique [[],[],[],[],[],[2]]) (patternEdges [[],[],[],[],[],[2]]) (patternAmount [[],[],[],[],[],[2]]) (patternEdgeCount [[],[],[],[],[],[2]]) [] := certificate_205_checked

theorem certificate_206_checked : certificate_206.Valid 10 7 10 certificate_206_q certificate_206_edges 3 1 [] := by decide +kernel
theorem certificate_206_valid : certificate_206.Valid 10 7 (patternOrder [[],[],[],[],[],[3]]) (patternClique [[],[],[],[],[],[3]]) (patternEdges [[],[],[],[],[],[3]]) (patternAmount [[],[],[],[],[],[3]]) (patternEdgeCount [[],[],[],[],[],[3]]) [] := certificate_206_checked

theorem certificate_207_checked : certificate_207.Valid 10 7 9 certificate_207_q certificate_207_edges 2 2 [] := by decide +kernel
theorem certificate_207_valid : certificate_207.Valid 10 7 (patternOrder [[],[],[],[],[1,1]]) (patternClique [[],[],[],[],[1,1]]) (patternEdges [[],[],[],[],[1,1]]) (patternAmount [[],[],[],[],[1,1]]) (patternEdgeCount [[],[],[],[],[1,1]]) [] := certificate_207_checked

theorem certificate_208_checked : certificate_208.Valid 10 7 10 certificate_208_q certificate_208_edges 3 2 [] := by decide +kernel
theorem certificate_208_valid : certificate_208.Valid 10 7 (patternOrder [[],[],[],[],[1,2]]) (patternClique [[],[],[],[],[1,2]]) (patternEdges [[],[],[],[],[1,2]]) (patternAmount [[],[],[],[],[1,2]]) (patternEdgeCount [[],[],[],[],[1,2]]) [] := certificate_208_checked

theorem certificate_209_checked : certificate_209.Valid 10 7 9 certificate_209_q certificate_209_edges 2 2 [] := by decide +kernel
theorem certificate_209_valid : certificate_209.Valid 10 7 (patternOrder [[],[],[],[1],[1]]) (patternClique [[],[],[],[1],[1]]) (patternEdges [[],[],[],[1],[1]]) (patternAmount [[],[],[],[1],[1]]) (patternEdgeCount [[],[],[],[1],[1]]) [] := certificate_209_checked

theorem certificate_210_checked : certificate_210.Valid 10 7 10 certificate_210_q certificate_210_edges 3 2 [] := by decide +kernel
theorem certificate_210_valid : certificate_210.Valid 10 7 (patternOrder [[],[],[],[1],[2]]) (patternClique [[],[],[],[1],[2]]) (patternEdges [[],[],[],[1],[2]]) (patternAmount [[],[],[],[1],[2]]) (patternEdgeCount [[],[],[],[1],[2]]) [] := certificate_210_checked

theorem certificate_211_checked : certificate_211.Valid 10 7 10 certificate_211_q certificate_211_edges 3 3 [] := by decide +kernel
theorem certificate_211_valid : certificate_211.Valid 10 7 (patternOrder [[],[],[],[1,1,1]]) (patternClique [[],[],[],[1,1,1]]) (patternEdges [[],[],[],[1,1,1]]) (patternAmount [[],[],[],[1,1,1]]) (patternEdgeCount [[],[],[],[1,1,1]]) [] := certificate_211_checked

theorem certificate_212_checked : certificate_212.Valid 10 7 10 certificate_212_q certificate_212_edges 3 3 [] := by decide +kernel
theorem certificate_212_valid : certificate_212.Valid 10 7 (patternOrder [[],[],[1],[1,1]]) (patternClique [[],[],[1],[1,1]]) (patternEdges [[],[],[1],[1,1]]) (patternAmount [[],[],[1],[1,1]]) (patternEdgeCount [[],[],[1],[1,1]]) [] := certificate_212_checked

theorem certificate_213_checked : certificate_213.Valid 10 7 10 certificate_213_q certificate_213_edges 3 3 [] := by decide +kernel
theorem certificate_213_valid : certificate_213.Valid 10 7 (patternOrder [[],[1],[1],[1]]) (patternClique [[],[1],[1],[1]]) (patternEdges [[],[1],[1],[1]]) (patternAmount [[],[1],[1],[1]]) (patternEdgeCount [[],[1],[1],[1]]) [] := certificate_213_checked

theorem certificate_214_checked : certificate_214.Valid 10 8 8 certificate_214_q certificate_214_edges 0 0 [] := by decide +kernel
theorem certificate_214_valid : certificate_214.Valid 10 8 (patternOrder [[],[],[],[],[],[],[],[]]) (patternClique [[],[],[],[],[],[],[],[]]) (patternEdges [[],[],[],[],[],[],[],[]]) (patternAmount [[],[],[],[],[],[],[],[]]) (patternEdgeCount [[],[],[],[],[],[],[],[]]) [] := certificate_214_checked

theorem certificate_215_checked : certificate_215.Valid 10 8 9 certificate_215_q certificate_215_edges 1 1 [] := by decide +kernel
theorem certificate_215_valid : certificate_215.Valid 10 8 (patternOrder [[],[],[],[],[],[],[1]]) (patternClique [[],[],[],[],[],[],[1]]) (patternEdges [[],[],[],[],[],[],[1]]) (patternAmount [[],[],[],[],[],[],[1]]) (patternEdgeCount [[],[],[],[],[],[],[1]]) [] := certificate_215_checked

theorem certificate_216_checked : certificate_216.Valid 10 8 10 certificate_216_q certificate_216_edges 2 1 [] := by decide +kernel
theorem certificate_216_valid : certificate_216.Valid 10 8 (patternOrder [[],[],[],[],[],[],[2]]) (patternClique [[],[],[],[],[],[],[2]]) (patternEdges [[],[],[],[],[],[],[2]]) (patternAmount [[],[],[],[],[],[],[2]]) (patternEdgeCount [[],[],[],[],[],[],[2]]) [] := certificate_216_checked

theorem certificate_217_checked : certificate_217.Valid 10 8 10 certificate_217_q certificate_217_edges 2 2 [] := by decide +kernel
theorem certificate_217_valid : certificate_217.Valid 10 8 (patternOrder [[],[],[],[],[],[1,1]]) (patternClique [[],[],[],[],[],[1,1]]) (patternEdges [[],[],[],[],[],[1,1]]) (patternAmount [[],[],[],[],[],[1,1]]) (patternEdgeCount [[],[],[],[],[],[1,1]]) [] := certificate_217_checked

theorem certificate_218_checked : certificate_218.Valid 10 8 10 certificate_218_q certificate_218_edges 2 2 [] := by decide +kernel
theorem certificate_218_valid : certificate_218.Valid 10 8 (patternOrder [[],[],[],[],[1],[1]]) (patternClique [[],[],[],[],[1],[1]]) (patternEdges [[],[],[],[],[1],[1]]) (patternAmount [[],[],[],[],[1],[1]]) (patternEdgeCount [[],[],[],[],[1],[1]]) [] := certificate_218_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates011
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_350_checked : certificate_350.Valid 11 8 8 certificate_350_q certificate_350_edges 0 0 [] := by decide +kernel
theorem certificate_350_valid : certificate_350.Valid 11 8 (patternOrder [[],[],[],[],[],[],[],[]]) (patternClique [[],[],[],[],[],[],[],[]]) (patternEdges [[],[],[],[],[],[],[],[]]) (patternAmount [[],[],[],[],[],[],[],[]]) (patternEdgeCount [[],[],[],[],[],[],[],[]]) [] := certificate_350_checked

theorem certificate_351_checked : certificate_351.Valid 11 8 9 certificate_351_q certificate_351_edges 1 1 [] := by decide +kernel
theorem certificate_351_valid : certificate_351.Valid 11 8 (patternOrder [[],[],[],[],[],[],[1]]) (patternClique [[],[],[],[],[],[],[1]]) (patternEdges [[],[],[],[],[],[],[1]]) (patternAmount [[],[],[],[],[],[],[1]]) (patternEdgeCount [[],[],[],[],[],[],[1]]) [] := certificate_351_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates012
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_352_checked : certificate_352.Valid 11 8 10 certificate_352_q certificate_352_edges 2 1 [] := by decide +kernel
theorem certificate_352_valid : certificate_352.Valid 11 8 (patternOrder [[],[],[],[],[],[],[2]]) (patternClique [[],[],[],[],[],[],[2]]) (patternEdges [[],[],[],[],[],[],[2]]) (patternAmount [[],[],[],[],[],[],[2]]) (patternEdgeCount [[],[],[],[],[],[],[2]]) [] := certificate_352_checked

theorem certificate_353_checked : certificate_353.Valid 11 8 11 certificate_353_q certificate_353_edges 3 1 [] := by decide +kernel
theorem certificate_353_valid : certificate_353.Valid 11 8 (patternOrder [[],[],[],[],[],[],[3]]) (patternClique [[],[],[],[],[],[],[3]]) (patternEdges [[],[],[],[],[],[],[3]]) (patternAmount [[],[],[],[],[],[],[3]]) (patternEdgeCount [[],[],[],[],[],[],[3]]) [] := certificate_353_checked

theorem certificate_354_checked : certificate_354.Valid 11 8 10 certificate_354_q certificate_354_edges 2 2 [] := by decide +kernel
theorem certificate_354_valid : certificate_354.Valid 11 8 (patternOrder [[],[],[],[],[],[1,1]]) (patternClique [[],[],[],[],[],[1,1]]) (patternEdges [[],[],[],[],[],[1,1]]) (patternAmount [[],[],[],[],[],[1,1]]) (patternEdgeCount [[],[],[],[],[],[1,1]]) [] := certificate_354_checked

theorem certificate_355_checked : certificate_355.Valid 11 8 11 certificate_355_q certificate_355_edges 3 2 [] := by decide +kernel
theorem certificate_355_valid : certificate_355.Valid 11 8 (patternOrder [[],[],[],[],[],[1,2]]) (patternClique [[],[],[],[],[],[1,2]]) (patternEdges [[],[],[],[],[],[1,2]]) (patternAmount [[],[],[],[],[],[1,2]]) (patternEdgeCount [[],[],[],[],[],[1,2]]) [] := certificate_355_checked

theorem certificate_356_checked : certificate_356.Valid 11 8 10 certificate_356_q certificate_356_edges 2 2 [] := by decide +kernel
theorem certificate_356_valid : certificate_356.Valid 11 8 (patternOrder [[],[],[],[],[1],[1]]) (patternClique [[],[],[],[],[1],[1]]) (patternEdges [[],[],[],[],[1],[1]]) (patternAmount [[],[],[],[],[1],[1]]) (patternEdgeCount [[],[],[],[],[1],[1]]) [] := certificate_356_checked

theorem certificate_357_checked : certificate_357.Valid 11 8 11 certificate_357_q certificate_357_edges 3 2 [] := by decide +kernel
theorem certificate_357_valid : certificate_357.Valid 11 8 (patternOrder [[],[],[],[],[1],[2]]) (patternClique [[],[],[],[],[1],[2]]) (patternEdges [[],[],[],[],[1],[2]]) (patternAmount [[],[],[],[],[1],[2]]) (patternEdgeCount [[],[],[],[],[1],[2]]) [] := certificate_357_checked

theorem certificate_358_checked : certificate_358.Valid 11 8 11 certificate_358_q certificate_358_edges 3 3 [] := by decide +kernel
theorem certificate_358_valid : certificate_358.Valid 11 8 (patternOrder [[],[],[],[],[1,1,1]]) (patternClique [[],[],[],[],[1,1,1]]) (patternEdges [[],[],[],[],[1,1,1]]) (patternAmount [[],[],[],[],[1,1,1]]) (patternEdgeCount [[],[],[],[],[1,1,1]]) [] := certificate_358_checked

theorem certificate_359_checked : certificate_359.Valid 11 8 11 certificate_359_q certificate_359_edges 3 3 [] := by decide +kernel
theorem certificate_359_valid : certificate_359.Valid 11 8 (patternOrder [[],[],[],[1],[1,1]]) (patternClique [[],[],[],[1],[1,1]]) (patternEdges [[],[],[],[1],[1,1]]) (patternAmount [[],[],[],[1],[1,1]]) (patternEdgeCount [[],[],[],[1],[1,1]]) [] := certificate_359_checked

theorem certificate_360_checked : certificate_360.Valid 11 8 11 certificate_360_q certificate_360_edges 3 3 [] := by decide +kernel
theorem certificate_360_valid : certificate_360.Valid 11 8 (patternOrder [[],[],[1],[1],[1]]) (patternClique [[],[],[1],[1],[1]]) (patternEdges [[],[],[1],[1],[1]]) (patternAmount [[],[],[1],[1],[1]]) (patternEdgeCount [[],[],[1],[1],[1]]) [] := certificate_360_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns10x7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem patterns_10_7_0_verified : ∀ D ∈ patterns_10_7_0, PatternVerified 10 7 D := by

  simp only [patterns_10_7_0, List.forall_mem_cons]

  exact ⟨⟨certificate_203, certificate_203_valid⟩, ⟨⟨certificate_204, certificate_204_valid⟩, ⟨⟨certificate_205, certificate_205_valid⟩, ⟨⟨certificate_206, certificate_206_valid⟩, ⟨⟨certificate_207, certificate_207_valid⟩, ⟨⟨certificate_208, certificate_208_valid⟩, ⟨⟨certificate_209, certificate_209_valid⟩, ⟨⟨certificate_210, certificate_210_valid⟩, ⟨⟨certificate_211, certificate_211_valid⟩, ⟨⟨certificate_212, certificate_212_valid⟩, ⟨⟨certificate_213, certificate_213_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem patterns_10_7_verified : ∀ D ∈ patterns_10_7, PatternVerified 10 7 D := by

  simp only [patterns_10_7, List.forall_mem_append]

  exact ⟨patterns_10_7_0_verified, by simp⟩

theorem patterns_10_7_coverage : patternChoices 7 3 [] = patterns_10_7 := by decide +kernel

theorem finite_patterns_10_7 : ∀ D ∈ patternChoices 7 (10-7) [], PatternVerified 10 7 D := by

  rw [patterns_10_7_coverage]

  exact patterns_10_7_verified

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns10x8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem patterns_10_8_0_verified : ∀ D ∈ patterns_10_8_0, PatternVerified 10 8 D := by

  simp only [patterns_10_8_0, List.forall_mem_cons]

  exact ⟨⟨certificate_214, certificate_214_valid⟩, ⟨⟨certificate_215, certificate_215_valid⟩, ⟨⟨certificate_216, certificate_216_valid⟩, ⟨⟨certificate_217, certificate_217_valid⟩, ⟨⟨certificate_218, certificate_218_valid⟩, (by simp)⟩⟩⟩⟩⟩

theorem patterns_10_8_verified : ∀ D ∈ patterns_10_8, PatternVerified 10 8 D := by

  simp only [patterns_10_8, List.forall_mem_append]

  exact ⟨patterns_10_8_0_verified, by simp⟩

theorem patterns_10_8_coverage : patternChoices 8 2 [] = patterns_10_8 := by decide +kernel

theorem finite_patterns_10_8 : ∀ D ∈ patternChoices 8 (10-8) [], PatternVerified 10 8 D := by

  rw [patterns_10_8_coverage]

  exact patterns_10_8_verified

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns11x8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem patterns_11_8_0_verified : ∀ D ∈ patterns_11_8_0, PatternVerified 11 8 D := by

  simp only [patterns_11_8_0, List.forall_mem_cons]

  exact ⟨⟨certificate_350, certificate_350_valid⟩, ⟨⟨certificate_351, certificate_351_valid⟩, ⟨⟨certificate_352, certificate_352_valid⟩, ⟨⟨certificate_353, certificate_353_valid⟩, ⟨⟨certificate_354, certificate_354_valid⟩, ⟨⟨certificate_355, certificate_355_valid⟩, ⟨⟨certificate_356, certificate_356_valid⟩, ⟨⟨certificate_357, certificate_357_valid⟩, ⟨⟨certificate_358, certificate_358_valid⟩, ⟨⟨certificate_359, certificate_359_valid⟩, ⟨⟨certificate_360, certificate_360_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem patterns_11_8_verified : ∀ D ∈ patterns_11_8, PatternVerified 11 8 D := by

  simp only [patterns_11_8, List.forall_mem_append]

  exact ⟨patterns_11_8_0_verified, by simp⟩

theorem patterns_11_8_coverage : patternChoices 8 3 [] = patterns_11_8 := by decide +kernel

theorem finite_patterns_11_8 : ∀ D ∈ patternChoices 8 (11-8) [], PatternVerified 11 8 D := by

  rw [patterns_11_8_coverage]

  exact patterns_11_8_verified

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns5x3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem patterns_5_3_0_verified : ∀ D ∈ patterns_5_3_0, PatternVerified 5 3 D := by

  simp only [patterns_5_3_0, List.forall_mem_cons]

  exact ⟨⟨certificate_0, certificate_0_valid⟩, ⟨⟨certificate_1, certificate_1_valid⟩, ⟨⟨certificate_2, certificate_2_valid⟩, ⟨⟨certificate_3, certificate_3_valid⟩, (by simp)⟩⟩⟩⟩

theorem patterns_5_3_verified : ∀ D ∈ patterns_5_3, PatternVerified 5 3 D := by

  simp only [patterns_5_3, List.forall_mem_append]

  exact ⟨patterns_5_3_0_verified, by simp⟩

theorem patterns_5_3_coverage : patternChoices 3 2 [] = patterns_5_3 := by decide +kernel

theorem finite_patterns_5_3 : ∀ D ∈ patternChoices 3 (5-3) [], PatternVerified 5 3 D := by

  rw [patterns_5_3_coverage]

  exact patterns_5_3_verified

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns5x4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem patterns_5_4_0_verified : ∀ D ∈ patterns_5_4_0, PatternVerified 5 4 D := by

  simp only [patterns_5_4_0, List.forall_mem_cons]

  exact ⟨⟨certificate_4, certificate_4_valid⟩, ⟨⟨certificate_5, certificate_5_valid⟩, (by simp)⟩⟩

theorem patterns_5_4_verified : ∀ D ∈ patterns_5_4, PatternVerified 5 4 D := by

  simp only [patterns_5_4, List.forall_mem_append]

  exact ⟨patterns_5_4_0_verified, by simp⟩

theorem patterns_5_4_coverage : patternChoices 4 1 [] = patterns_5_4 := by decide +kernel

theorem finite_patterns_5_4 : ∀ D ∈ patternChoices 4 (5-4) [], PatternVerified 5 4 D := by

  rw [patterns_5_4_coverage]

  exact patterns_5_4_verified

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns5x5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem patterns_5_5_0_verified : ∀ D ∈ patterns_5_5_0, PatternVerified 5 5 D := by

  simp only [patterns_5_5_0, List.forall_mem_cons]

  exact ⟨⟨certificate_6, certificate_6_valid⟩, (by simp)⟩

theorem patterns_5_5_verified : ∀ D ∈ patterns_5_5, PatternVerified 5 5 D := by

  simp only [patterns_5_5, List.forall_mem_append]

  exact ⟨patterns_5_5_0_verified, by simp⟩

theorem patterns_5_5_coverage : patternChoices 5 0 [] = patterns_5_5 := by decide +kernel

theorem finite_patterns_5_5 : ∀ D ∈ patternChoices 5 (5-5) [], PatternVerified 5 5 D := by

  rw [patterns_5_5_coverage]

  exact patterns_5_5_verified

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns6x4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem patterns_6_4_0_verified : ∀ D ∈ patterns_6_4_0, PatternVerified 6 4 D := by

  simp only [patterns_6_4_0, List.forall_mem_cons]

  exact ⟨⟨certificate_13, certificate_13_valid⟩, ⟨⟨certificate_14, certificate_14_valid⟩, ⟨⟨certificate_15, certificate_15_valid⟩, ⟨⟨certificate_16, certificate_16_valid⟩, ⟨⟨certificate_17, certificate_17_valid⟩, (by simp)⟩⟩⟩⟩⟩

theorem patterns_6_4_verified : ∀ D ∈ patterns_6_4, PatternVerified 6 4 D := by

  simp only [patterns_6_4, List.forall_mem_append]

  exact ⟨patterns_6_4_0_verified, by simp⟩

theorem patterns_6_4_coverage : patternChoices 4 2 [] = patterns_6_4 := by decide +kernel

theorem finite_patterns_6_4 : ∀ D ∈ patternChoices 4 (6-4) [], PatternVerified 6 4 D := by

  rw [patterns_6_4_coverage]

  exact patterns_6_4_verified

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns6x5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem patterns_6_5_0_verified : ∀ D ∈ patterns_6_5_0, PatternVerified 6 5 D := by

  simp only [patterns_6_5_0, List.forall_mem_cons]

  exact ⟨⟨certificate_18, certificate_18_valid⟩, ⟨⟨certificate_19, certificate_19_valid⟩, (by simp)⟩⟩

theorem patterns_6_5_verified : ∀ D ∈ patterns_6_5, PatternVerified 6 5 D := by

  simp only [patterns_6_5, List.forall_mem_append]

  exact ⟨patterns_6_5_0_verified, by simp⟩

theorem patterns_6_5_coverage : patternChoices 5 1 [] = patterns_6_5 := by decide +kernel

theorem finite_patterns_6_5 : ∀ D ∈ patternChoices 5 (6-5) [], PatternVerified 6 5 D := by

  rw [patterns_6_5_coverage]

  exact patterns_6_5_verified

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns6x6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem patterns_6_6_0_verified : ∀ D ∈ patterns_6_6_0, PatternVerified 6 6 D := by

  simp only [patterns_6_6_0, List.forall_mem_cons]

  exact ⟨⟨certificate_20, certificate_20_valid⟩, (by simp)⟩

theorem patterns_6_6_verified : ∀ D ∈ patterns_6_6, PatternVerified 6 6 D := by

  simp only [patterns_6_6, List.forall_mem_append]

  exact ⟨patterns_6_6_0_verified, by simp⟩

theorem patterns_6_6_coverage : patternChoices 6 0 [] = patterns_6_6 := by decide +kernel

theorem finite_patterns_6_6 : ∀ D ∈ patternChoices 6 (6-6) [], PatternVerified 6 6 D := by

  rw [patterns_6_6_coverage]

  exact patterns_6_6_verified

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns7x4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem patterns_7_4_0_verified : ∀ D ∈ patterns_7_4_0, PatternVerified 7 4 D := by

  simp only [patterns_7_4_0, List.forall_mem_cons]

  exact ⟨⟨certificate_30, certificate_30_valid⟩, ⟨⟨certificate_31, certificate_31_valid⟩, ⟨⟨certificate_32, certificate_32_valid⟩, ⟨⟨certificate_33, certificate_33_valid⟩, ⟨⟨certificate_34, certificate_34_valid⟩, ⟨⟨certificate_35, certificate_35_valid⟩, ⟨⟨certificate_36, certificate_36_valid⟩, ⟨⟨certificate_37, certificate_37_valid⟩, ⟨⟨certificate_38, certificate_38_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem patterns_7_4_verified : ∀ D ∈ patterns_7_4, PatternVerified 7 4 D := by

  simp only [patterns_7_4, List.forall_mem_append]

  exact ⟨patterns_7_4_0_verified, by simp⟩

theorem patterns_7_4_coverage : patternChoices 4 3 [] = patterns_7_4 := by decide +kernel

theorem finite_patterns_7_4 : ∀ D ∈ patternChoices 4 (7-4) [], PatternVerified 7 4 D := by

  rw [patterns_7_4_coverage]

  exact patterns_7_4_verified

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns7x5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem patterns_7_5_0_verified : ∀ D ∈ patterns_7_5_0, PatternVerified 7 5 D := by

  simp only [patterns_7_5_0, List.forall_mem_cons]

  exact ⟨⟨certificate_39, certificate_39_valid⟩, ⟨⟨certificate_40, certificate_40_valid⟩, ⟨⟨certificate_41, certificate_41_valid⟩, ⟨⟨certificate_42, certificate_42_valid⟩, ⟨⟨certificate_43, certificate_43_valid⟩, (by simp)⟩⟩⟩⟩⟩

theorem patterns_7_5_verified : ∀ D ∈ patterns_7_5, PatternVerified 7 5 D := by

  simp only [patterns_7_5, List.forall_mem_append]

  exact ⟨patterns_7_5_0_verified, by simp⟩

theorem patterns_7_5_coverage : patternChoices 5 2 [] = patterns_7_5 := by decide +kernel

theorem finite_patterns_7_5 : ∀ D ∈ patternChoices 5 (7-5) [], PatternVerified 7 5 D := by

  rw [patterns_7_5_coverage]

  exact patterns_7_5_verified

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns7x6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem patterns_7_6_0_verified : ∀ D ∈ patterns_7_6_0, PatternVerified 7 6 D := by

  simp only [patterns_7_6_0, List.forall_mem_cons]

  exact ⟨⟨certificate_44, certificate_44_valid⟩, ⟨⟨certificate_45, certificate_45_valid⟩, (by simp)⟩⟩

theorem patterns_7_6_verified : ∀ D ∈ patterns_7_6, PatternVerified 7 6 D := by

  simp only [patterns_7_6, List.forall_mem_append]

  exact ⟨patterns_7_6_0_verified, by simp⟩

theorem patterns_7_6_coverage : patternChoices 6 1 [] = patterns_7_6 := by decide +kernel

theorem finite_patterns_7_6 : ∀ D ∈ patternChoices 6 (7-6) [], PatternVerified 7 6 D := by

  rw [patterns_7_6_coverage]

  exact patterns_7_6_verified

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns7x7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem patterns_7_7_0_verified : ∀ D ∈ patterns_7_7_0, PatternVerified 7 7 D := by

  simp only [patterns_7_7_0, List.forall_mem_cons]

  exact ⟨⟨certificate_46, certificate_46_valid⟩, (by simp)⟩

theorem patterns_7_7_verified : ∀ D ∈ patterns_7_7, PatternVerified 7 7 D := by

  simp only [patterns_7_7, List.forall_mem_append]

  exact ⟨patterns_7_7_0_verified, by simp⟩

theorem patterns_7_7_coverage : patternChoices 7 0 [] = patterns_7_7 := by decide +kernel

theorem finite_patterns_7_7 : ∀ D ∈ patternChoices 7 (7-7) [], PatternVerified 7 7 D := by

  rw [patterns_7_7_coverage]

  exact patterns_7_7_verified

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns8x5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem patterns_8_5_0_verified : ∀ D ∈ patterns_8_5_0, PatternVerified 8 5 D := by

  simp only [patterns_8_5_0, List.forall_mem_cons]

  exact ⟨⟨certificate_63, certificate_63_valid⟩, ⟨⟨certificate_64, certificate_64_valid⟩, ⟨⟨certificate_65, certificate_65_valid⟩, ⟨⟨certificate_66, certificate_66_valid⟩, ⟨⟨certificate_67, certificate_67_valid⟩, ⟨⟨certificate_68, certificate_68_valid⟩, ⟨⟨certificate_69, certificate_69_valid⟩, ⟨⟨certificate_70, certificate_70_valid⟩, ⟨⟨certificate_71, certificate_71_valid⟩, ⟨⟨certificate_72, certificate_72_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem patterns_8_5_verified : ∀ D ∈ patterns_8_5, PatternVerified 8 5 D := by

  simp only [patterns_8_5, List.forall_mem_append]

  exact ⟨patterns_8_5_0_verified, by simp⟩

theorem patterns_8_5_coverage : patternChoices 5 3 [] = patterns_8_5 := by decide +kernel

theorem finite_patterns_8_5 : ∀ D ∈ patternChoices 5 (8-5) [], PatternVerified 8 5 D := by

  rw [patterns_8_5_coverage]

  exact patterns_8_5_verified

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns8x6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem patterns_8_6_0_verified : ∀ D ∈ patterns_8_6_0, PatternVerified 8 6 D := by

  simp only [patterns_8_6_0, List.forall_mem_cons]

  exact ⟨⟨certificate_73, certificate_73_valid⟩, ⟨⟨certificate_74, certificate_74_valid⟩, ⟨⟨certificate_75, certificate_75_valid⟩, ⟨⟨certificate_76, certificate_76_valid⟩, ⟨⟨certificate_77, certificate_77_valid⟩, (by simp)⟩⟩⟩⟩⟩

theorem patterns_8_6_verified : ∀ D ∈ patterns_8_6, PatternVerified 8 6 D := by

  simp only [patterns_8_6, List.forall_mem_append]

  exact ⟨patterns_8_6_0_verified, by simp⟩

theorem patterns_8_6_coverage : patternChoices 6 2 [] = patterns_8_6 := by decide +kernel

theorem finite_patterns_8_6 : ∀ D ∈ patternChoices 6 (8-6) [], PatternVerified 8 6 D := by

  rw [patterns_8_6_coverage]

  exact patterns_8_6_verified

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns8x7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem patterns_8_7_0_verified : ∀ D ∈ patterns_8_7_0, PatternVerified 8 7 D := by

  simp only [patterns_8_7_0, List.forall_mem_cons]

  exact ⟨⟨certificate_78, certificate_78_valid⟩, ⟨⟨certificate_79, certificate_79_valid⟩, (by simp)⟩⟩

theorem patterns_8_7_verified : ∀ D ∈ patterns_8_7, PatternVerified 8 7 D := by

  simp only [patterns_8_7, List.forall_mem_append]

  exact ⟨patterns_8_7_0_verified, by simp⟩

theorem patterns_8_7_coverage : patternChoices 7 1 [] = patterns_8_7 := by decide +kernel

theorem finite_patterns_8_7 : ∀ D ∈ patternChoices 7 (8-7) [], PatternVerified 8 7 D := by

  rw [patterns_8_7_coverage]

  exact patterns_8_7_verified

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns8x8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem patterns_8_8_0_verified : ∀ D ∈ patterns_8_8_0, PatternVerified 8 8 D := by

  simp only [patterns_8_8_0, List.forall_mem_cons]

  exact ⟨⟨certificate_80, certificate_80_valid⟩, (by simp)⟩

theorem patterns_8_8_verified : ∀ D ∈ patterns_8_8, PatternVerified 8 8 D := by

  simp only [patterns_8_8, List.forall_mem_append]

  exact ⟨patterns_8_8_0_verified, by simp⟩

theorem patterns_8_8_coverage : patternChoices 8 0 [] = patterns_8_8 := by decide +kernel

theorem finite_patterns_8_8 : ∀ D ∈ patternChoices 8 (8-8) [], PatternVerified 8 8 D := by

  rw [patterns_8_8_coverage]

  exact patterns_8_8_verified

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns9x6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem patterns_9_6_0_verified : ∀ D ∈ patterns_9_6_0, PatternVerified 9 6 D := by

  simp only [patterns_9_6_0, List.forall_mem_cons]

  exact ⟨⟨certificate_126, certificate_126_valid⟩, ⟨⟨certificate_127, certificate_127_valid⟩, ⟨⟨certificate_128, certificate_128_valid⟩, ⟨⟨certificate_129, certificate_129_valid⟩, ⟨⟨certificate_130, certificate_130_valid⟩, ⟨⟨certificate_131, certificate_131_valid⟩, ⟨⟨certificate_132, certificate_132_valid⟩, ⟨⟨certificate_133, certificate_133_valid⟩, ⟨⟨certificate_134, certificate_134_valid⟩, ⟨⟨certificate_135, certificate_135_valid⟩, ⟨⟨certificate_136, certificate_136_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem patterns_9_6_verified : ∀ D ∈ patterns_9_6, PatternVerified 9 6 D := by

  simp only [patterns_9_6, List.forall_mem_append]

  exact ⟨patterns_9_6_0_verified, by simp⟩

theorem patterns_9_6_coverage : patternChoices 6 3 [] = patterns_9_6 := by decide +kernel

theorem finite_patterns_9_6 : ∀ D ∈ patternChoices 6 (9-6) [], PatternVerified 9 6 D := by

  rw [patterns_9_6_coverage]

  exact patterns_9_6_verified

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns9x7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem patterns_9_7_0_verified : ∀ D ∈ patterns_9_7_0, PatternVerified 9 7 D := by

  simp only [patterns_9_7_0, List.forall_mem_cons]

  exact ⟨⟨certificate_137, certificate_137_valid⟩, ⟨⟨certificate_138, certificate_138_valid⟩, ⟨⟨certificate_139, certificate_139_valid⟩, ⟨⟨certificate_140, certificate_140_valid⟩, ⟨⟨certificate_141, certificate_141_valid⟩, (by simp)⟩⟩⟩⟩⟩

theorem patterns_9_7_verified : ∀ D ∈ patterns_9_7, PatternVerified 9 7 D := by

  simp only [patterns_9_7, List.forall_mem_append]

  exact ⟨patterns_9_7_0_verified, by simp⟩

theorem patterns_9_7_coverage : patternChoices 7 2 [] = patterns_9_7 := by decide +kernel

theorem finite_patterns_9_7 : ∀ D ∈ patternChoices 7 (9-7) [], PatternVerified 9 7 D := by

  rw [patterns_9_7_coverage]

  exact patterns_9_7_verified

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns9x8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem patterns_9_8_0_verified : ∀ D ∈ patterns_9_8_0, PatternVerified 9 8 D := by

  simp only [patterns_9_8_0, List.forall_mem_cons]

  exact ⟨⟨certificate_142, certificate_142_valid⟩, ⟨⟨certificate_143, certificate_143_valid⟩, (by simp)⟩⟩

theorem patterns_9_8_verified : ∀ D ∈ patterns_9_8, PatternVerified 9 8 D := by

  simp only [patterns_9_8, List.forall_mem_append]

  exact ⟨patterns_9_8_0_verified, by simp⟩

theorem patterns_9_8_coverage : patternChoices 8 1 [] = patterns_9_8 := by decide +kernel

theorem finite_patterns_9_8 : ∀ D ∈ patternChoices 8 (9-8) [], PatternVerified 9 8 D := by

  rw [patterns_9_8_coverage]

  exact patterns_9_8_verified

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_FiniteRange
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

open scoped SimpleGraph

 
theorem finite_range_verified_oai {k t : ℕ} (hk : 5 ≤ k) (ht : 3 ≤ t)
    (htk : t ≤ k) (ht8 : t ≤ 8) (hhalf : k/2 ≤ t) :
    ∀ D ∈ patternChoices t (k-t) [], PatternVerified k t D := by
  have hk17 : k ≤ 17 := by omega
  interval_cases k
  · have htmin : 3 ≤ t := by omega
    have htmax : t ≤ 5 := by omega
    interval_cases t
    · exact finite_patterns_5_3
    · exact finite_patterns_5_4
    · exact finite_patterns_5_5
  · have htmin : 3 ≤ t := by omega
    have htmax : t ≤ 6 := by omega
    interval_cases t
    · exact finite_patterns_6_3
    · exact finite_patterns_6_4
    · exact finite_patterns_6_5
    · exact finite_patterns_6_6
  · have htmin : 3 ≤ t := by omega
    have htmax : t ≤ 7 := by omega
    interval_cases t
    · exact finite_patterns_7_3
    · exact finite_patterns_7_4
    · exact finite_patterns_7_5
    · exact finite_patterns_7_6
    · exact finite_patterns_7_7
  · have htmin : 4 ≤ t := by omega
    have htmax : t ≤ 8 := by omega
    interval_cases t
    · exact finite_patterns_8_4
    · exact finite_patterns_8_5
    · exact finite_patterns_8_6
    · exact finite_patterns_8_7
    · exact finite_patterns_8_8
  · have htmin : 4 ≤ t := by omega
    have htmax : t ≤ 8 := by omega
    interval_cases t
    · exact finite_patterns_9_4
    · exact finite_patterns_9_5
    · exact finite_patterns_9_6
    · exact finite_patterns_9_7
    · exact finite_patterns_9_8
  · have htmin : 5 ≤ t := by omega
    have htmax : t ≤ 8 := by omega
    interval_cases t
    · exact finite_patterns_10_5
    · exact finite_patterns_10_6
    · exact finite_patterns_10_7
    · exact finite_patterns_10_8
  · have htmin : 5 ≤ t := by omega
    have htmax : t ≤ 8 := by omega
    interval_cases t
    · exact finite_patterns_11_5
    · exact finite_patterns_11_6
    · exact finite_patterns_11_7
    · exact finite_patterns_11_8
  · have htmin : 6 ≤ t := by omega
    have htmax : t ≤ 8 := by omega
    interval_cases t
    · exact finite_patterns_12_6
    · exact finite_patterns_12_7
    · exact finite_patterns_12_8
  · have htmin : 6 ≤ t := by omega
    have htmax : t ≤ 8 := by omega
    interval_cases t
    · exact finite_patterns_13_6
    · exact finite_patterns_13_7
    · exact finite_patterns_13_8
  · have htmin : 7 ≤ t := by omega
    have htmax : t ≤ 8 := by omega
    interval_cases t
    · exact finite_patterns_14_7
    · exact finite_patterns_14_8
  · have htmin : 7 ≤ t := by omega
    have htmax : t ≤ 8 := by omega
    interval_cases t
    · exact finite_patterns_15_7
    · exact finite_patterns_15_8
  · have htmin : 8 ≤ t := by omega
    have htmax : t ≤ 8 := by omega
    interval_cases t
    · exact finite_patterns_16_8
  · have htmin : 8 ≤ t := by omega
    have htmax : t ≤ 8 := by omega
    interval_cases t
    · exact finite_patterns_17_8



end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.finite_range_verified_oai := @OAI.CycleClique.finite_range_verified_oai
