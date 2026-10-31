-- Prove2me | solution 1 for OAI.CycleClique.finite_patterns_7_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T21:56:19.512806+00:00
-- url     : https://prove2.me/submissions/799844a5-4e47-432d-8fa8-b84c212c20c6

import Mathlib
import Definitions.Def_OAIQ107D028
import Definitions.Def_OAIQ107D040
import Definitions.Def_OAIQ107D043
import Definitions.Def_OAIQ107D064
import Definitions.Def_OAIQ107D126
import Definitions.Def_OAIQ107D131
import Definitions.Def_OAIQ107D132
import Definitions.Def_OAIQ107D133

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates001
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_21_checked : certificate_21.Valid 7 3 3 certificate_21_q certificate_21_edges 0 0 [] := by decide +kernel
theorem certificate_21_valid : certificate_21.Valid 7 3 (patternOrder [[],[],[]]) (patternClique [[],[],[]]) (patternEdges [[],[],[]]) (patternAmount [[],[],[]]) (patternEdgeCount [[],[],[]]) [] := certificate_21_checked

theorem certificate_22_checked : certificate_22.Valid 7 3 4 certificate_22_q certificate_22_edges 1 1 [] := by decide +kernel
theorem certificate_22_valid : certificate_22.Valid 7 3 (patternOrder [[],[1]]) (patternClique [[],[1]]) (patternEdges [[],[1]]) (patternAmount [[],[1]]) (patternEdgeCount [[],[1]]) [] := certificate_22_checked

theorem certificate_23_checked : certificate_23.Valid 7 3 5 certificate_23_q certificate_23_edges 2 1 [] := by decide +kernel
theorem certificate_23_valid : certificate_23.Valid 7 3 (patternOrder [[],[2]]) (patternClique [[],[2]]) (patternEdges [[],[2]]) (patternAmount [[],[2]]) (patternEdgeCount [[],[2]]) [] := certificate_23_checked

theorem certificate_24_part_2_checked : certificate_24_part_2.Valid 7 3 7 certificate_24_q certificate_24_part_2_E 3 1 certificate_24_part_2_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩

theorem certificate_24_part_5_checked : certificate_24_part_5.Valid 7 3 7 certificate_24_q certificate_24_part_5_E 3 1 certificate_24_part_5_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_24_part_7_checked : certificate_24_part_7.Valid 7 3 6 certificate_24_q certificate_24_part_7_E 3 1 certificate_24_part_7_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩⟩⟩

theorem certificate_24_part_6_checked : certificate_24_part_6.Valid 7 3 6 certificate_24_q certificate_24_part_6_E 3 1 certificate_24_part_6_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_24_part_7_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_24_part_4_checked : certificate_24_part_4.Valid 7 3 6 certificate_24_q certificate_24_part_4_E 3 1 certificate_24_part_4_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, certificate_24_part_5_checked, certificate_24_part_6_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_24_part_3_checked : certificate_24_part_3.Valid 7 3 6 certificate_24_q certificate_24_part_3_E 3 1 certificate_24_part_3_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_24_part_4_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_24_part_1_checked : certificate_24_part_1.Valid 7 3 6 certificate_24_q certificate_24_part_1_E 3 1 certificate_24_part_1_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, certificate_24_part_2_checked, certificate_24_part_3_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_24_checked : certificate_24.Valid 7 3 6 certificate_24_q certificate_24_E 3 1 certificate_24_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_24_part_1_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_24_valid : certificate_24.Valid 7 3 (patternOrder [[],[3]]) (patternClique [[],[3]]) (patternEdges [[],[3]]) (patternAmount [[],[3]]) (patternEdgeCount [[],[3]]) [] := certificate_24_checked

theorem certificate_25_part_3_checked : certificate_25_part_3.Valid 7 3 8 certificate_25_q certificate_25_part_3_E 4 1 certificate_25_part_3_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

theorem certificate_25_part_2_checked : certificate_25_part_2.Valid 7 3 8 certificate_25_q certificate_25_part_2_E 4 1 certificate_25_part_2_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_25_part_3_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_25_part_5_checked : certificate_25_part_5.Valid 7 3 8 certificate_25_q certificate_25_part_5_E 4 1 certificate_25_part_5_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_25_part_4_checked : certificate_25_part_4.Valid 7 3 8 certificate_25_q certificate_25_part_4_E 4 1 certificate_25_part_4_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_25_part_5_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_25_part_7_checked : certificate_25_part_7.Valid 7 3 8 certificate_25_q certificate_25_part_7_E 4 1 certificate_25_part_7_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩⟩⟩⟩

theorem certificate_25_part_9_checked : certificate_25_part_9.Valid 7 3 7 certificate_25_q certificate_25_part_9_E 4 1 certificate_25_part_9_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩

theorem certificate_25_part_12_checked : certificate_25_part_12.Valid 7 3 8 certificate_25_q certificate_25_part_12_E 4 1 certificate_25_part_12_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem certificate_25_part_11_checked : certificate_25_part_11.Valid 7 3 8 certificate_25_q certificate_25_part_11_E 4 1 certificate_25_part_11_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_25_part_12_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_25_part_13_checked : certificate_25_part_13.Valid 7 3 7 certificate_25_q certificate_25_part_13_E 4 1 certificate_25_part_13_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

theorem certificate_25_part_14_checked : certificate_25_part_14.Valid 7 3 7 certificate_25_q certificate_25_part_14_E 4 1 certificate_25_part_14_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩

theorem certificate_25_part_15_checked : certificate_25_part_15.Valid 7 3 7 certificate_25_q certificate_25_part_15_E 4 1 certificate_25_part_15_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

theorem certificate_25_part_16_checked : certificate_25_part_16.Valid 7 3 7 certificate_25_q certificate_25_part_16_E 4 1 certificate_25_part_16_M := by exact ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩, by decide +kernel⟩

theorem certificate_25_part_10_checked : certificate_25_part_10.Valid 7 3 7 certificate_25_q certificate_25_part_10_E 4 1 certificate_25_part_10_M := by exact ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_25_part_11_checked⟩⟩⟩⟩⟩⟩⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_25_part_13_checked⟩⟩⟩⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_25_part_14_checked⟩, ⟨by decide +kernel, by decide +kernel, certificate_25_part_15_checked, certificate_25_part_16_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_25_part_8_checked : certificate_25_part_8.Valid 7 3 7 certificate_25_q certificate_25_part_8_E 4 1 certificate_25_part_8_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_25_part_9_checked⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_25_part_10_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_25_part_6_checked : certificate_25_part_6.Valid 7 3 7 certificate_25_q certificate_25_part_6_E 4 1 certificate_25_part_6_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_25_part_7_checked⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_25_part_8_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_25_part_1_checked : certificate_25_part_1.Valid 7 3 7 certificate_25_q certificate_25_part_1_E 4 1 certificate_25_part_1_M := by exact ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_25_part_2_checked⟩⟩⟩⟩⟩⟩⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, certificate_25_part_4_checked, certificate_25_part_6_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_25_checked : certificate_25.Valid 7 3 7 certificate_25_q certificate_25_E 4 1 certificate_25_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_25_part_1_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_25_valid : certificate_25.Valid 7 3 (patternOrder [[],[4]]) (patternClique [[],[4]]) (patternEdges [[],[4]]) (patternAmount [[],[4]]) (patternEdgeCount [[],[4]]) [] := certificate_25_checked

theorem certificate_26_checked : certificate_26.Valid 7 3 5 certificate_26_q certificate_26_edges 2 2 [] := by decide +kernel
theorem certificate_26_valid : certificate_26.Valid 7 3 (patternOrder [[1,1]]) (patternClique [[1,1]]) (patternEdges [[1,1]]) (patternAmount [[1,1]]) (patternEdgeCount [[1,1]]) [] := certificate_26_checked

theorem certificate_27_checked : certificate_27.Valid 7 3 6 certificate_27_q certificate_27_edges 3 2 [] := by decide +kernel
theorem certificate_27_valid : certificate_27.Valid 7 3 (patternOrder [[1,2]]) (patternClique [[1,2]]) (patternEdges [[1,2]]) (patternAmount [[1,2]]) (patternEdgeCount [[1,2]]) [] := certificate_27_checked

theorem certificate_28_part_4_checked : certificate_28_part_4.Valid 7 3 8 certificate_28_q certificate_28_part_4_E 4 2 certificate_28_part_4_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

theorem certificate_28_part_5_checked : certificate_28_part_5.Valid 7 3 7 certificate_28_q certificate_28_part_5_E 4 2 certificate_28_part_5_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

theorem certificate_28_part_6_checked : certificate_28_part_6.Valid 7 3 7 certificate_28_q certificate_28_part_6_E 4 2 certificate_28_part_6_M := by exact ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩, by decide +kernel⟩⟩⟩⟩⟩

theorem certificate_28_part_3_checked : certificate_28_part_3.Valid 7 3 7 certificate_28_q certificate_28_part_3_E 4 2 certificate_28_part_3_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_28_part_4_checked⟩⟩⟩⟩⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩, ⟨by decide +kernel, by decide +kernel, certificate_28_part_5_checked, certificate_28_part_6_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_28_part_2_checked : certificate_28_part_2.Valid 7 3 7 certificate_28_q certificate_28_part_2_E 4 2 certificate_28_part_2_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_28_part_3_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_28_part_1_checked : certificate_28_part_1.Valid 7 3 7 certificate_28_q certificate_28_part_1_E 4 2 certificate_28_part_1_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_28_part_2_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_28_checked : certificate_28.Valid 7 3 7 certificate_28_q certificate_28_E 4 2 certificate_28_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_28_part_1_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_28_valid : certificate_28.Valid 7 3 (patternOrder [[1,3]]) (patternClique [[1,3]]) (patternEdges [[1,3]]) (patternAmount [[1,3]]) (patternEdgeCount [[1,3]]) [] := certificate_28_checked

theorem certificate_29_part_6_checked : certificate_29_part_6.Valid 7 3 7 certificate_29_q certificate_29_part_6_E 4 2 certificate_29_part_6_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem certificate_29_part_10_checked : certificate_29_part_10.Valid 7 3 7 certificate_29_q certificate_29_part_10_E 4 2 certificate_29_part_10_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

theorem certificate_29_part_9_checked : certificate_29_part_9.Valid 7 3 7 certificate_29_q certificate_29_part_9_E 4 2 certificate_29_part_9_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_29_part_10_checked⟩⟩⟩⟩⟩, by decide +kernel⟩⟩⟩

theorem certificate_29_part_8_checked : certificate_29_part_8.Valid 7 3 7 certificate_29_q certificate_29_part_8_E 4 2 certificate_29_part_8_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_29_part_9_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_29_part_7_checked : certificate_29_part_7.Valid 7 3 7 certificate_29_q certificate_29_part_7_E 4 2 certificate_29_part_7_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_29_part_8_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_29_part_5_checked : certificate_29_part_5.Valid 7 3 7 certificate_29_q certificate_29_part_5_E 4 2 certificate_29_part_5_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_29_part_6_checked⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_29_part_7_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_29_part_4_checked : certificate_29_part_4.Valid 7 3 7 certificate_29_q certificate_29_part_4_E 4 2 certificate_29_part_4_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_29_part_5_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_29_part_3_checked : certificate_29_part_3.Valid 7 3 7 certificate_29_q certificate_29_part_3_E 4 2 certificate_29_part_3_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_29_part_4_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_29_part_2_checked : certificate_29_part_2.Valid 7 3 7 certificate_29_q certificate_29_part_2_E 4 2 certificate_29_part_2_M := by exact ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_29_part_3_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_29_part_1_checked : certificate_29_part_1.Valid 7 3 7 certificate_29_q certificate_29_part_1_E 4 2 certificate_29_part_1_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_29_part_2_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_29_checked : certificate_29.Valid 7 3 7 certificate_29_q certificate_29_E 4 2 certificate_29_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_29_part_1_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_29_valid : certificate_29.Valid 7 3 (patternOrder [[2,2]]) (patternClique [[2,2]]) (patternEdges [[2,2]]) (patternAmount [[2,2]]) (patternEdgeCount [[2,2]]) [] := certificate_29_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns7x3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem patterns_7_3_0_verified : ∀ D ∈ patterns_7_3_0, PatternVerified 7 3 D := by

  simp only [patterns_7_3_0, List.forall_mem_cons]

  exact ⟨⟨certificate_21, certificate_21_valid⟩, ⟨⟨certificate_22, certificate_22_valid⟩, ⟨⟨certificate_23, certificate_23_valid⟩, ⟨⟨certificate_24, certificate_24_valid⟩, ⟨⟨certificate_25, certificate_25_valid⟩, ⟨⟨certificate_26, certificate_26_valid⟩, ⟨⟨certificate_27, certificate_27_valid⟩, ⟨⟨certificate_28, certificate_28_valid⟩, ⟨⟨certificate_29, certificate_29_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem patterns_7_3_verified : ∀ D ∈ patterns_7_3, PatternVerified 7 3 D := by

  simp only [patterns_7_3, List.forall_mem_append]

  exact ⟨patterns_7_3_0_verified, by simp⟩

theorem patterns_7_3_coverage : patternChoices 3 4 [] = patterns_7_3 := by decide +kernel

theorem finite_patterns_7_3_oai : ∀ D ∈ patternChoices 3 (7-3) [], PatternVerified 7 3 D := by

  rw [patterns_7_3_coverage]

  exact patterns_7_3_verified

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.finite_patterns_7_3_oai := @OAI.CycleClique.finite_patterns_7_3_oai
