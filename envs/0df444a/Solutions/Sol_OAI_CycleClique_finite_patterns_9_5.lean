-- Prove2me | solution 1 for OAI.CycleClique.finite_patterns_9_5
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T21:03:14.483282+00:00
-- url     : https://prove2.me/submissions/f9c0ca8b-c842-4e61-8a9b-9e3b67ce7e1b

import Mathlib
import Definitions.Def_OAIQ107D058
import Definitions.Def_OAIQ107D126
import Definitions.Def_OAIQ107D133

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates004
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_106_checked : certificate_106.Valid 9 5 5 certificate_106_q certificate_106_edges 0 0 [] := by decide +kernel
theorem certificate_106_valid : certificate_106.Valid 9 5 (patternOrder [[],[],[],[],[]]) (patternClique [[],[],[],[],[]]) (patternEdges [[],[],[],[],[]]) (patternAmount [[],[],[],[],[]]) (patternEdgeCount [[],[],[],[],[]]) [] := certificate_106_checked

theorem certificate_107_checked : certificate_107.Valid 9 5 6 certificate_107_q certificate_107_edges 1 1 [] := by decide +kernel
theorem certificate_107_valid : certificate_107.Valid 9 5 (patternOrder [[],[],[],[1]]) (patternClique [[],[],[],[1]]) (patternEdges [[],[],[],[1]]) (patternAmount [[],[],[],[1]]) (patternEdgeCount [[],[],[],[1]]) [] := certificate_107_checked

theorem certificate_108_checked : certificate_108.Valid 9 5 7 certificate_108_q certificate_108_edges 2 1 [] := by decide +kernel
theorem certificate_108_valid : certificate_108.Valid 9 5 (patternOrder [[],[],[],[2]]) (patternClique [[],[],[],[2]]) (patternEdges [[],[],[],[2]]) (patternAmount [[],[],[],[2]]) (patternEdgeCount [[],[],[],[2]]) [] := certificate_108_checked

theorem certificate_109_checked : certificate_109.Valid 9 5 8 certificate_109_q certificate_109_edges 3 1 [] := by decide +kernel
theorem certificate_109_valid : certificate_109.Valid 9 5 (patternOrder [[],[],[],[3]]) (patternClique [[],[],[],[3]]) (patternEdges [[],[],[],[3]]) (patternAmount [[],[],[],[3]]) (patternEdgeCount [[],[],[],[3]]) [] := certificate_109_checked

theorem certificate_110_part_4_checked : certificate_110_part_4.Valid 9 5 9 certificate_110_q certificate_110_part_4_E 4 1 certificate_110_part_4_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

theorem certificate_110_part_8_checked : certificate_110_part_8.Valid 9 5 9 certificate_110_q certificate_110_part_8_E 4 1 certificate_110_part_8_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩

theorem certificate_110_part_7_checked : certificate_110_part_7.Valid 9 5 9 certificate_110_q certificate_110_part_7_E 4 1 certificate_110_part_7_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_110_part_8_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_110_part_12_checked : certificate_110_part_12.Valid 9 5 10 certificate_110_q certificate_110_part_12_E 4 1 certificate_110_part_12_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem certificate_110_part_11_checked : certificate_110_part_11.Valid 9 5 10 certificate_110_q certificate_110_part_11_E 4 1 certificate_110_part_11_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_110_part_12_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_110_part_10_checked : certificate_110_part_10.Valid 9 5 10 certificate_110_q certificate_110_part_10_E 4 1 certificate_110_part_10_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_110_part_11_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_110_part_9_checked : certificate_110_part_9.Valid 9 5 10 certificate_110_q certificate_110_part_9_E 4 1 certificate_110_part_9_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_110_part_10_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_110_part_14_checked : certificate_110_part_14.Valid 9 5 9 certificate_110_q certificate_110_part_14_E 4 1 certificate_110_part_14_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩⟩⟩⟩

theorem certificate_110_part_17_checked : certificate_110_part_17.Valid 9 5 10 certificate_110_q certificate_110_part_17_E 4 1 certificate_110_part_17_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩

theorem certificate_110_part_16_checked : certificate_110_part_16.Valid 9 5 10 certificate_110_q certificate_110_part_16_E 4 1 certificate_110_part_16_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_110_part_17_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_110_part_15_checked : certificate_110_part_15.Valid 9 5 10 certificate_110_q certificate_110_part_15_E 4 1 certificate_110_part_15_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_110_part_16_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_110_part_19_checked : certificate_110_part_19.Valid 9 5 9 certificate_110_q certificate_110_part_19_E 4 1 certificate_110_part_19_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩⟩

theorem certificate_110_part_20_checked : certificate_110_part_20.Valid 9 5 9 certificate_110_q certificate_110_part_20_E 4 1 certificate_110_part_20_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

theorem certificate_110_part_22_checked : certificate_110_part_22.Valid 9 5 9 certificate_110_q certificate_110_part_22_E 4 1 certificate_110_part_22_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩

theorem certificate_110_part_21_checked : certificate_110_part_21.Valid 9 5 9 certificate_110_q certificate_110_part_21_E 4 1 certificate_110_part_21_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_110_part_22_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_110_part_24_checked : certificate_110_part_24.Valid 9 5 9 certificate_110_q certificate_110_part_24_E 4 1 certificate_110_part_24_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩⟩

theorem certificate_110_part_25_checked : certificate_110_part_25.Valid 9 5 9 certificate_110_q certificate_110_part_25_E 4 1 certificate_110_part_25_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

theorem certificate_110_part_27_checked : certificate_110_part_27.Valid 9 5 9 certificate_110_q certificate_110_part_27_E 4 1 certificate_110_part_27_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩

theorem certificate_110_part_26_checked : certificate_110_part_26.Valid 9 5 9 certificate_110_q certificate_110_part_26_E 4 1 certificate_110_part_26_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_110_part_27_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_110_part_29_checked : certificate_110_part_29.Valid 9 5 9 certificate_110_q certificate_110_part_29_E 4 1 certificate_110_part_29_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩⟩

theorem certificate_110_part_31_checked : certificate_110_part_31.Valid 9 5 9 certificate_110_q certificate_110_part_31_E 4 1 certificate_110_part_31_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩

theorem certificate_110_part_35_checked : certificate_110_part_35.Valid 9 5 10 certificate_110_q certificate_110_part_35_E 4 1 certificate_110_part_35_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩⟩⟩

theorem certificate_110_part_34_checked : certificate_110_part_34.Valid 9 5 10 certificate_110_q certificate_110_part_34_E 4 1 certificate_110_part_34_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_110_part_35_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_110_part_37_checked : certificate_110_part_37.Valid 9 5 9 certificate_110_q certificate_110_part_37_E 4 1 certificate_110_part_37_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩

theorem certificate_110_part_36_checked : certificate_110_part_36.Valid 9 5 9 certificate_110_q certificate_110_part_36_E 4 1 certificate_110_part_36_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, certificate_110_part_37_checked, by decide +kernel⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_110_part_33_checked : certificate_110_part_33.Valid 9 5 9 certificate_110_q certificate_110_part_33_E 4 1 certificate_110_part_33_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_110_part_34_checked⟩⟩⟩⟩⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_110_part_36_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_110_part_32_checked : certificate_110_part_32.Valid 9 5 9 certificate_110_q certificate_110_part_32_E 4 1 certificate_110_part_32_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_110_part_33_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_110_part_30_checked : certificate_110_part_30.Valid 9 5 9 certificate_110_q certificate_110_part_30_E 4 1 certificate_110_part_30_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_110_part_31_checked⟩⟩⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_110_part_32_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_110_part_28_checked : certificate_110_part_28.Valid 9 5 9 certificate_110_q certificate_110_part_28_E 4 1 certificate_110_part_28_M := by exact ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_110_part_29_checked⟩⟩⟩⟩⟩⟩⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_110_part_30_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_110_part_23_checked : certificate_110_part_23.Valid 9 5 9 certificate_110_q certificate_110_part_23_E 4 1 certificate_110_part_23_M := by exact ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_110_part_24_checked⟩⟩⟩⟩⟩⟩⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_110_part_25_checked⟩, ⟨by decide +kernel, by decide +kernel, certificate_110_part_26_checked, certificate_110_part_28_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_110_part_18_checked : certificate_110_part_18.Valid 9 5 9 certificate_110_q certificate_110_part_18_E 4 1 certificate_110_part_18_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_110_part_19_checked⟩⟩, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_110_part_20_checked⟩, ⟨by decide +kernel, by decide +kernel, certificate_110_part_21_checked, certificate_110_part_23_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_110_part_13_checked : certificate_110_part_13.Valid 9 5 9 certificate_110_q certificate_110_part_13_E 4 1 certificate_110_part_13_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_110_part_14_checked⟩⟩⟩⟩⟩, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_110_part_15_checked⟩⟩⟩⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_110_part_18_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_110_part_6_checked : certificate_110_part_6.Valid 9 5 9 certificate_110_q certificate_110_part_6_E 4 1 certificate_110_part_6_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_110_part_7_checked⟩⟩, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_110_part_9_checked⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_110_part_13_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_110_part_5_checked : certificate_110_part_5.Valid 9 5 9 certificate_110_q certificate_110_part_5_E 4 1 certificate_110_part_5_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_110_part_6_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_110_part_3_checked : certificate_110_part_3.Valid 9 5 9 certificate_110_q certificate_110_part_3_E 4 1 certificate_110_part_3_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_110_part_4_checked⟩⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_110_part_5_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_110_part_2_checked : certificate_110_part_2.Valid 9 5 9 certificate_110_q certificate_110_part_2_E 4 1 certificate_110_part_2_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_110_part_3_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_110_part_1_checked : certificate_110_part_1.Valid 9 5 9 certificate_110_q certificate_110_part_1_E 4 1 certificate_110_part_1_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_110_part_2_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_110_checked : certificate_110.Valid 9 5 9 certificate_110_q certificate_110_E 4 1 certificate_110_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_110_part_1_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_110_valid : certificate_110.Valid 9 5 (patternOrder [[],[],[],[4]]) (patternClique [[],[],[],[4]]) (patternEdges [[],[],[],[4]]) (patternAmount [[],[],[],[4]]) (patternEdgeCount [[],[],[],[4]]) [] := certificate_110_checked

theorem certificate_111_checked : certificate_111.Valid 9 5 7 certificate_111_q certificate_111_edges 2 2 [] := by decide +kernel
theorem certificate_111_valid : certificate_111.Valid 9 5 (patternOrder [[],[],[1,1]]) (patternClique [[],[],[1,1]]) (patternEdges [[],[],[1,1]]) (patternAmount [[],[],[1,1]]) (patternEdgeCount [[],[],[1,1]]) [] := certificate_111_checked

theorem certificate_112_checked : certificate_112.Valid 9 5 8 certificate_112_q certificate_112_edges 3 2 [] := by decide +kernel
theorem certificate_112_valid : certificate_112.Valid 9 5 (patternOrder [[],[],[1,2]]) (patternClique [[],[],[1,2]]) (patternEdges [[],[],[1,2]]) (patternAmount [[],[],[1,2]]) (patternEdgeCount [[],[],[1,2]]) [] := certificate_112_checked

theorem certificate_113_checked : certificate_113.Valid 9 5 9 certificate_113_q certificate_113_edges 4 2 [] := by decide +kernel
theorem certificate_113_valid : certificate_113.Valid 9 5 (patternOrder [[],[],[1,3]]) (patternClique [[],[],[1,3]]) (patternEdges [[],[],[1,3]]) (patternAmount [[],[],[1,3]]) (patternEdgeCount [[],[],[1,3]]) [] := certificate_113_checked

theorem certificate_114_checked : certificate_114.Valid 9 5 9 certificate_114_q certificate_114_edges 4 2 [] := by decide +kernel
theorem certificate_114_valid : certificate_114.Valid 9 5 (patternOrder [[],[],[2,2]]) (patternClique [[],[],[2,2]]) (patternEdges [[],[],[2,2]]) (patternAmount [[],[],[2,2]]) (patternEdgeCount [[],[],[2,2]]) [] := certificate_114_checked

theorem certificate_115_checked : certificate_115.Valid 9 5 7 certificate_115_q certificate_115_edges 2 2 [] := by decide +kernel
theorem certificate_115_valid : certificate_115.Valid 9 5 (patternOrder [[],[1],[1]]) (patternClique [[],[1],[1]]) (patternEdges [[],[1],[1]]) (patternAmount [[],[1],[1]]) (patternEdgeCount [[],[1],[1]]) [] := certificate_115_checked

theorem certificate_116_checked : certificate_116.Valid 9 5 8 certificate_116_q certificate_116_edges 3 2 [] := by decide +kernel
theorem certificate_116_valid : certificate_116.Valid 9 5 (patternOrder [[],[1],[2]]) (patternClique [[],[1],[2]]) (patternEdges [[],[1],[2]]) (patternAmount [[],[1],[2]]) (patternEdgeCount [[],[1],[2]]) [] := certificate_116_checked

theorem certificate_117_checked : certificate_117.Valid 9 5 9 certificate_117_q certificate_117_edges 4 2 [] := by decide +kernel
theorem certificate_117_valid : certificate_117.Valid 9 5 (patternOrder [[],[1],[3]]) (patternClique [[],[1],[3]]) (patternEdges [[],[1],[3]]) (patternAmount [[],[1],[3]]) (patternEdgeCount [[],[1],[3]]) [] := certificate_117_checked

theorem certificate_118_checked : certificate_118.Valid 9 5 8 certificate_118_q certificate_118_edges 3 3 [] := by decide +kernel
theorem certificate_118_valid : certificate_118.Valid 9 5 (patternOrder [[],[1,1,1]]) (patternClique [[],[1,1,1]]) (patternEdges [[],[1,1,1]]) (patternAmount [[],[1,1,1]]) (patternEdgeCount [[],[1,1,1]]) [] := certificate_118_checked

theorem certificate_119_checked : certificate_119.Valid 9 5 9 certificate_119_q certificate_119_edges 4 3 [] := by decide +kernel
theorem certificate_119_valid : certificate_119.Valid 9 5 (patternOrder [[],[1,1,2]]) (patternClique [[],[1,1,2]]) (patternEdges [[],[1,1,2]]) (patternAmount [[],[1,1,2]]) (patternEdgeCount [[],[1,1,2]]) [] := certificate_119_checked

theorem certificate_120_checked : certificate_120.Valid 9 5 9 certificate_120_q certificate_120_edges 4 3 [] := by decide +kernel
theorem certificate_120_valid : certificate_120.Valid 9 5 (patternOrder [[],[1,2,1]]) (patternClique [[],[1,2,1]]) (patternEdges [[],[1,2,1]]) (patternAmount [[],[1,2,1]]) (patternEdgeCount [[],[1,2,1]]) [] := certificate_120_checked

theorem certificate_121_checked : certificate_121.Valid 9 5 9 certificate_121_q certificate_121_edges 4 2 [] := by decide +kernel
theorem certificate_121_valid : certificate_121.Valid 9 5 (patternOrder [[],[2],[2]]) (patternClique [[],[2],[2]]) (patternEdges [[],[2],[2]]) (patternAmount [[],[2],[2]]) (patternEdgeCount [[],[2],[2]]) [] := certificate_121_checked

theorem certificate_122_checked : certificate_122.Valid 9 5 8 certificate_122_q certificate_122_edges 3 3 [] := by decide +kernel
theorem certificate_122_valid : certificate_122.Valid 9 5 (patternOrder [[1],[1,1]]) (patternClique [[1],[1,1]]) (patternEdges [[1],[1,1]]) (patternAmount [[1],[1,1]]) (patternEdgeCount [[1],[1,1]]) [] := certificate_122_checked

theorem certificate_123_checked : certificate_123.Valid 9 5 9 certificate_123_q certificate_123_edges 4 3 [] := by decide +kernel
theorem certificate_123_valid : certificate_123.Valid 9 5 (patternOrder [[1],[1,2]]) (patternClique [[1],[1,2]]) (patternEdges [[1],[1,2]]) (patternAmount [[1],[1,2]]) (patternEdgeCount [[1],[1,2]]) [] := certificate_123_checked

theorem certificate_124_checked : certificate_124.Valid 9 5 9 certificate_124_q certificate_124_edges 4 3 [] := by decide +kernel
theorem certificate_124_valid : certificate_124.Valid 9 5 (patternOrder [[1,1],[2]]) (patternClique [[1,1],[2]]) (patternEdges [[1,1],[2]]) (patternAmount [[1,1],[2]]) (patternEdgeCount [[1,1],[2]]) [] := certificate_124_checked

theorem certificate_125_checked : certificate_125.Valid 9 5 9 certificate_125_q certificate_125_edges 4 4 [] := by decide +kernel
theorem certificate_125_valid : certificate_125.Valid 9 5 (patternOrder [[1,1,1,1]]) (patternClique [[1,1,1,1]]) (patternEdges [[1,1,1,1]]) (patternAmount [[1,1,1,1]]) (patternEdgeCount [[1,1,1,1]]) [] := certificate_125_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns9x5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem patterns_9_5_0_verified : ∀ D ∈ patterns_9_5_0, PatternVerified 9 5 D := by

  simp only [patterns_9_5_0, List.forall_mem_cons]

  exact ⟨⟨certificate_106, certificate_106_valid⟩, ⟨⟨certificate_107, certificate_107_valid⟩, ⟨⟨certificate_108, certificate_108_valid⟩, ⟨⟨certificate_109, certificate_109_valid⟩, ⟨⟨certificate_110, certificate_110_valid⟩, ⟨⟨certificate_111, certificate_111_valid⟩, ⟨⟨certificate_112, certificate_112_valid⟩, ⟨⟨certificate_113, certificate_113_valid⟩, ⟨⟨certificate_114, certificate_114_valid⟩, ⟨⟨certificate_115, certificate_115_valid⟩, ⟨⟨certificate_116, certificate_116_valid⟩, ⟨⟨certificate_117, certificate_117_valid⟩, ⟨⟨certificate_118, certificate_118_valid⟩, ⟨⟨certificate_119, certificate_119_valid⟩, ⟨⟨certificate_120, certificate_120_valid⟩, ⟨⟨certificate_121, certificate_121_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem patterns_9_5_1_verified : ∀ D ∈ patterns_9_5_1, PatternVerified 9 5 D := by

  simp only [patterns_9_5_1, List.forall_mem_cons]

  exact ⟨⟨certificate_122, certificate_122_valid⟩, ⟨⟨certificate_123, certificate_123_valid⟩, ⟨⟨certificate_124, certificate_124_valid⟩, ⟨⟨certificate_125, certificate_125_valid⟩, (by simp)⟩⟩⟩⟩

theorem patterns_9_5_verified : ∀ D ∈ patterns_9_5, PatternVerified 9 5 D := by

  simp only [patterns_9_5, List.forall_mem_append]

  exact ⟨patterns_9_5_0_verified, ⟨patterns_9_5_1_verified, by simp⟩⟩

theorem patterns_9_5_coverage : patternChoices 5 4 [] = patterns_9_5 := by decide +kernel

theorem finite_patterns_9_5_oai : ∀ D ∈ patternChoices 5 (9-5) [], PatternVerified 9 5 D := by

  rw [patterns_9_5_coverage]

  exact patterns_9_5_verified

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.finite_patterns_9_5_oai := @OAI.CycleClique.finite_patterns_9_5_oai
