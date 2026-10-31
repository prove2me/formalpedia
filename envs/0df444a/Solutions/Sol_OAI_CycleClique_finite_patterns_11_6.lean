-- Prove2me | solution 1 for OAI.CycleClique.finite_patterns_11_6
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T20:34:03.859648+00:00
-- url     : https://prove2.me/submissions/2934a939-0147-4e5d-8fa4-42dcf70491c8

import Mathlib
import Definitions.Def_OAIQ107D131
import Definitions.Def_OAIQ107D132
import Definitions.Def_OAIQ107D133

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates009
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_279_checked : certificate_279.Valid 11 6 6 certificate_279_q certificate_279_edges 0 0 [] := by decide +kernel
theorem certificate_279_valid : certificate_279.Valid 11 6 (patternOrder [[],[],[],[],[],[]]) (patternClique [[],[],[],[],[],[]]) (patternEdges [[],[],[],[],[],[]]) (patternAmount [[],[],[],[],[],[]]) (patternEdgeCount [[],[],[],[],[],[]]) [] := certificate_279_checked

theorem certificate_280_checked : certificate_280.Valid 11 6 7 certificate_280_q certificate_280_edges 1 1 [] := by decide +kernel
theorem certificate_280_valid : certificate_280.Valid 11 6 (patternOrder [[],[],[],[],[1]]) (patternClique [[],[],[],[],[1]]) (patternEdges [[],[],[],[],[1]]) (patternAmount [[],[],[],[],[1]]) (patternEdgeCount [[],[],[],[],[1]]) [] := certificate_280_checked

theorem certificate_281_checked : certificate_281.Valid 11 6 8 certificate_281_q certificate_281_edges 2 1 [] := by decide +kernel
theorem certificate_281_valid : certificate_281.Valid 11 6 (patternOrder [[],[],[],[],[2]]) (patternClique [[],[],[],[],[2]]) (patternEdges [[],[],[],[],[2]]) (patternAmount [[],[],[],[],[2]]) (patternEdgeCount [[],[],[],[],[2]]) [] := certificate_281_checked

theorem certificate_282_checked : certificate_282.Valid 11 6 9 certificate_282_q certificate_282_edges 3 1 [] := by decide +kernel
theorem certificate_282_valid : certificate_282.Valid 11 6 (patternOrder [[],[],[],[],[3]]) (patternClique [[],[],[],[],[3]]) (patternEdges [[],[],[],[],[3]]) (patternAmount [[],[],[],[],[3]]) (patternEdgeCount [[],[],[],[],[3]]) [] := certificate_282_checked

theorem certificate_283_checked : certificate_283.Valid 11 6 10 certificate_283_q certificate_283_edges 4 1 [] := by decide +kernel
theorem certificate_283_valid : certificate_283.Valid 11 6 (patternOrder [[],[],[],[],[4]]) (patternClique [[],[],[],[],[4]]) (patternEdges [[],[],[],[],[4]]) (patternAmount [[],[],[],[],[4]]) (patternEdgeCount [[],[],[],[],[4]]) [] := certificate_283_checked

theorem certificate_284_part_6_checked : certificate_284_part_6.Valid 11 6 11 certificate_284_q certificate_284_part_6_E 5 1 certificate_284_part_6_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩⟩

theorem certificate_284_part_10_checked : certificate_284_part_10.Valid 11 6 11 certificate_284_q certificate_284_part_10_E 5 1 certificate_284_part_10_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩⟩

theorem certificate_284_part_9_checked : certificate_284_part_9.Valid 11 6 11 certificate_284_q certificate_284_part_9_E 5 1 certificate_284_part_9_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_284_part_10_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_284_part_13_checked : certificate_284_part_13.Valid 11 6 12 certificate_284_q certificate_284_part_13_E 5 1 certificate_284_part_13_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩⟩

theorem certificate_284_part_12_checked : certificate_284_part_12.Valid 11 6 12 certificate_284_q certificate_284_part_12_E 5 1 certificate_284_part_12_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_284_part_13_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_284_part_11_checked : certificate_284_part_11.Valid 11 6 12 certificate_284_q certificate_284_part_11_E 5 1 certificate_284_part_11_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_284_part_12_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_284_part_15_checked : certificate_284_part_15.Valid 11 6 11 certificate_284_q certificate_284_part_15_E 5 1 certificate_284_part_15_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩⟩⟩

theorem certificate_284_part_14_checked : certificate_284_part_14.Valid 11 6 11 certificate_284_q certificate_284_part_14_E 5 1 certificate_284_part_14_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_284_part_15_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_284_part_17_checked : certificate_284_part_17.Valid 11 6 11 certificate_284_q certificate_284_part_17_E 5 1 certificate_284_part_17_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_284_part_16_checked : certificate_284_part_16.Valid 11 6 11 certificate_284_q certificate_284_part_16_E 5 1 certificate_284_part_16_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_284_part_17_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_284_part_20_checked : certificate_284_part_20.Valid 11 6 11 certificate_284_q certificate_284_part_20_E 5 1 certificate_284_part_20_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩⟩⟩

theorem certificate_284_part_21_checked : certificate_284_part_21.Valid 11 6 11 certificate_284_q certificate_284_part_21_E 5 1 certificate_284_part_21_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩⟩⟩

theorem certificate_284_part_24_checked : certificate_284_part_24.Valid 11 6 11 certificate_284_q certificate_284_part_24_E 5 1 certificate_284_part_24_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem certificate_284_part_23_checked : certificate_284_part_23.Valid 11 6 11 certificate_284_q certificate_284_part_23_E 5 1 certificate_284_part_23_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_284_part_24_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_284_part_26_checked : certificate_284_part_26.Valid 11 6 12 certificate_284_q certificate_284_part_26_E 5 1 certificate_284_part_26_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_284_part_25_checked : certificate_284_part_25.Valid 11 6 12 certificate_284_q certificate_284_part_25_E 5 1 certificate_284_part_25_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_284_part_26_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_284_part_28_checked : certificate_284_part_28.Valid 11 6 11 certificate_284_q certificate_284_part_28_E 5 1 certificate_284_part_28_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem certificate_284_part_27_checked : certificate_284_part_27.Valid 11 6 11 certificate_284_q certificate_284_part_27_E 5 1 certificate_284_part_27_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_284_part_28_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_284_part_30_checked : certificate_284_part_30.Valid 11 6 11 certificate_284_q certificate_284_part_30_E 5 1 certificate_284_part_30_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩

theorem certificate_284_part_29_checked : certificate_284_part_29.Valid 11 6 11 certificate_284_q certificate_284_part_29_E 5 1 certificate_284_part_29_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_284_part_30_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_284_part_31_checked : certificate_284_part_31.Valid 11 6 11 certificate_284_q certificate_284_part_31_E 5 1 certificate_284_part_31_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩

theorem certificate_284_part_33_checked : certificate_284_part_33.Valid 11 6 11 certificate_284_q certificate_284_part_33_E 5 1 certificate_284_part_33_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem certificate_284_part_35_checked : certificate_284_part_35.Valid 11 6 11 certificate_284_q certificate_284_part_35_E 5 1 certificate_284_part_35_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩⟩

theorem certificate_284_part_34_checked : certificate_284_part_34.Valid 11 6 11 certificate_284_q certificate_284_part_34_E 5 1 certificate_284_part_34_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_284_part_35_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_284_part_38_checked : certificate_284_part_38.Valid 11 6 12 certificate_284_q certificate_284_part_38_E 5 1 certificate_284_part_38_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩

theorem certificate_284_part_37_checked : certificate_284_part_37.Valid 11 6 12 certificate_284_q certificate_284_part_37_E 5 1 certificate_284_part_37_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_284_part_38_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_284_part_36_checked : certificate_284_part_36.Valid 11 6 12 certificate_284_q certificate_284_part_36_E 5 1 certificate_284_part_36_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_284_part_37_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_284_part_40_checked : certificate_284_part_40.Valid 11 6 11 certificate_284_q certificate_284_part_40_E 5 1 certificate_284_part_40_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩

theorem certificate_284_part_39_checked : certificate_284_part_39.Valid 11 6 11 certificate_284_q certificate_284_part_39_E 5 1 certificate_284_part_39_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_284_part_40_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_284_part_42_checked : certificate_284_part_42.Valid 11 6 11 certificate_284_q certificate_284_part_42_E 5 1 certificate_284_part_42_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_284_part_41_checked : certificate_284_part_41.Valid 11 6 11 certificate_284_q certificate_284_part_41_E 5 1 certificate_284_part_41_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_284_part_42_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_284_part_44_checked : certificate_284_part_44.Valid 11 6 11 certificate_284_q certificate_284_part_44_E 5 1 certificate_284_part_44_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

theorem certificate_284_part_46_checked : certificate_284_part_46.Valid 11 6 11 certificate_284_q certificate_284_part_46_E 5 1 certificate_284_part_46_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem certificate_284_part_48_checked : certificate_284_part_48.Valid 11 6 11 certificate_284_q certificate_284_part_48_E 5 1 certificate_284_part_48_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩⟩⟩

theorem certificate_284_part_47_checked : certificate_284_part_47.Valid 11 6 11 certificate_284_q certificate_284_part_47_E 5 1 certificate_284_part_47_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_284_part_48_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_284_part_50_checked : certificate_284_part_50.Valid 11 6 11 certificate_284_q certificate_284_part_50_E 5 1 certificate_284_part_50_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

theorem certificate_284_part_51_checked : certificate_284_part_51.Valid 11 6 11 certificate_284_q certificate_284_part_51_E 5 1 certificate_284_part_51_M := by exact ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩, by decide +kernel⟩

theorem certificate_284_part_49_checked : certificate_284_part_49.Valid 11 6 11 certificate_284_q certificate_284_part_49_E 5 1 certificate_284_part_49_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_284_part_50_checked⟩⟩⟩⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_284_part_51_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_284_part_45_checked : certificate_284_part_45.Valid 11 6 11 certificate_284_q certificate_284_part_45_E 5 1 certificate_284_part_45_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_284_part_46_checked⟩⟩⟩, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_284_part_47_checked⟩⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_284_part_49_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_284_part_43_checked : certificate_284_part_43.Valid 11 6 11 certificate_284_q certificate_284_part_43_E 5 1 certificate_284_part_43_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_284_part_44_checked⟩⟩⟩⟩⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_284_part_45_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_284_part_32_checked : certificate_284_part_32.Valid 11 6 11 certificate_284_q certificate_284_part_32_E 5 1 certificate_284_part_32_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_284_part_33_checked⟩⟩⟩⟩, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_284_part_34_checked⟩⟩⟩, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_284_part_36_checked⟩⟩, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_284_part_39_checked⟩, ⟨by decide +kernel, by decide +kernel, certificate_284_part_41_checked, certificate_284_part_43_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_284_part_22_checked : certificate_284_part_22.Valid 11 6 11 certificate_284_q certificate_284_part_22_E 5 1 certificate_284_part_22_M := by exact ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_284_part_23_checked⟩⟩⟩⟩⟩⟩⟩, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_284_part_25_checked⟩⟩⟩⟩⟩⟩, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_284_part_27_checked⟩⟩⟩⟩⟩, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_284_part_29_checked⟩⟩⟩⟩, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_284_part_31_checked⟩⟩⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_284_part_32_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_284_part_19_checked : certificate_284_part_19.Valid 11 6 11 certificate_284_q certificate_284_part_19_E 5 1 certificate_284_part_19_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_284_part_20_checked⟩, ⟨by decide +kernel, by decide +kernel, certificate_284_part_21_checked, certificate_284_part_22_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_284_part_18_checked : certificate_284_part_18.Valid 11 6 11 certificate_284_q certificate_284_part_18_E 5 1 certificate_284_part_18_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_284_part_19_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_284_part_8_checked : certificate_284_part_8.Valid 11 6 11 certificate_284_q certificate_284_part_8_E 5 1 certificate_284_part_8_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_284_part_9_checked⟩⟩⟩, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_284_part_11_checked⟩⟩, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_284_part_14_checked⟩, ⟨by decide +kernel, by decide +kernel, certificate_284_part_16_checked, certificate_284_part_18_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_284_part_7_checked : certificate_284_part_7.Valid 11 6 11 certificate_284_q certificate_284_part_7_E 5 1 certificate_284_part_7_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_284_part_8_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_284_part_5_checked : certificate_284_part_5.Valid 11 6 11 certificate_284_q certificate_284_part_5_E 5 1 certificate_284_part_5_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_284_part_6_checked⟩⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_284_part_7_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_284_part_4_checked : certificate_284_part_4.Valid 11 6 11 certificate_284_q certificate_284_part_4_E 5 1 certificate_284_part_4_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_284_part_5_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_284_part_3_checked : certificate_284_part_3.Valid 11 6 11 certificate_284_q certificate_284_part_3_E 5 1 certificate_284_part_3_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_284_part_4_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_284_part_2_checked : certificate_284_part_2.Valid 11 6 11 certificate_284_q certificate_284_part_2_E 5 1 certificate_284_part_2_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_284_part_3_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_284_part_1_checked : certificate_284_part_1.Valid 11 6 11 certificate_284_q certificate_284_part_1_E 5 1 certificate_284_part_1_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_284_part_2_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_284_checked : certificate_284.Valid 11 6 11 certificate_284_q certificate_284_E 5 1 certificate_284_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_284_part_1_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_284_valid : certificate_284.Valid 11 6 (patternOrder [[],[],[],[],[5]]) (patternClique [[],[],[],[],[5]]) (patternEdges [[],[],[],[],[5]]) (patternAmount [[],[],[],[],[5]]) (patternEdgeCount [[],[],[],[],[5]]) [] := certificate_284_checked

theorem certificate_285_checked : certificate_285.Valid 11 6 8 certificate_285_q certificate_285_edges 2 2 [] := by decide +kernel
theorem certificate_285_valid : certificate_285.Valid 11 6 (patternOrder [[],[],[],[1,1]]) (patternClique [[],[],[],[1,1]]) (patternEdges [[],[],[],[1,1]]) (patternAmount [[],[],[],[1,1]]) (patternEdgeCount [[],[],[],[1,1]]) [] := certificate_285_checked

theorem certificate_286_checked : certificate_286.Valid 11 6 9 certificate_286_q certificate_286_edges 3 2 [] := by decide +kernel
theorem certificate_286_valid : certificate_286.Valid 11 6 (patternOrder [[],[],[],[1,2]]) (patternClique [[],[],[],[1,2]]) (patternEdges [[],[],[],[1,2]]) (patternAmount [[],[],[],[1,2]]) (patternEdgeCount [[],[],[],[1,2]]) [] := certificate_286_checked

theorem certificate_287_checked : certificate_287.Valid 11 6 10 certificate_287_q certificate_287_edges 4 2 [] := by decide +kernel
theorem certificate_287_valid : certificate_287.Valid 11 6 (patternOrder [[],[],[],[1,3]]) (patternClique [[],[],[],[1,3]]) (patternEdges [[],[],[],[1,3]]) (patternAmount [[],[],[],[1,3]]) (patternEdgeCount [[],[],[],[1,3]]) [] := certificate_287_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates010
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_288_checked : certificate_288.Valid 11 6 11 certificate_288_q certificate_288_edges 5 2 [] := by decide +kernel
theorem certificate_288_valid : certificate_288.Valid 11 6 (patternOrder [[],[],[],[1,4]]) (patternClique [[],[],[],[1,4]]) (patternEdges [[],[],[],[1,4]]) (patternAmount [[],[],[],[1,4]]) (patternEdgeCount [[],[],[],[1,4]]) [] := certificate_288_checked

theorem certificate_289_checked : certificate_289.Valid 11 6 10 certificate_289_q certificate_289_edges 4 2 [] := by decide +kernel
theorem certificate_289_valid : certificate_289.Valid 11 6 (patternOrder [[],[],[],[2,2]]) (patternClique [[],[],[],[2,2]]) (patternEdges [[],[],[],[2,2]]) (patternAmount [[],[],[],[2,2]]) (patternEdgeCount [[],[],[],[2,2]]) [] := certificate_289_checked

theorem certificate_290_checked : certificate_290.Valid 11 6 11 certificate_290_q certificate_290_edges 5 2 [] := by decide +kernel
theorem certificate_290_valid : certificate_290.Valid 11 6 (patternOrder [[],[],[],[2,3]]) (patternClique [[],[],[],[2,3]]) (patternEdges [[],[],[],[2,3]]) (patternAmount [[],[],[],[2,3]]) (patternEdgeCount [[],[],[],[2,3]]) [] := certificate_290_checked

theorem certificate_291_checked : certificate_291.Valid 11 6 8 certificate_291_q certificate_291_edges 2 2 [] := by decide +kernel
theorem certificate_291_valid : certificate_291.Valid 11 6 (patternOrder [[],[],[1],[1]]) (patternClique [[],[],[1],[1]]) (patternEdges [[],[],[1],[1]]) (patternAmount [[],[],[1],[1]]) (patternEdgeCount [[],[],[1],[1]]) [] := certificate_291_checked

theorem certificate_292_checked : certificate_292.Valid 11 6 9 certificate_292_q certificate_292_edges 3 2 [] := by decide +kernel
theorem certificate_292_valid : certificate_292.Valid 11 6 (patternOrder [[],[],[1],[2]]) (patternClique [[],[],[1],[2]]) (patternEdges [[],[],[1],[2]]) (patternAmount [[],[],[1],[2]]) (patternEdgeCount [[],[],[1],[2]]) [] := certificate_292_checked

theorem certificate_293_checked : certificate_293.Valid 11 6 10 certificate_293_q certificate_293_edges 4 2 [] := by decide +kernel
theorem certificate_293_valid : certificate_293.Valid 11 6 (patternOrder [[],[],[1],[3]]) (patternClique [[],[],[1],[3]]) (patternEdges [[],[],[1],[3]]) (patternAmount [[],[],[1],[3]]) (patternEdgeCount [[],[],[1],[3]]) [] := certificate_293_checked

theorem certificate_294_checked : certificate_294.Valid 11 6 11 certificate_294_q certificate_294_edges 5 2 [] := by decide +kernel
theorem certificate_294_valid : certificate_294.Valid 11 6 (patternOrder [[],[],[1],[4]]) (patternClique [[],[],[1],[4]]) (patternEdges [[],[],[1],[4]]) (patternAmount [[],[],[1],[4]]) (patternEdgeCount [[],[],[1],[4]]) [] := certificate_294_checked

theorem certificate_295_checked : certificate_295.Valid 11 6 9 certificate_295_q certificate_295_edges 3 3 [] := by decide +kernel
theorem certificate_295_valid : certificate_295.Valid 11 6 (patternOrder [[],[],[1,1,1]]) (patternClique [[],[],[1,1,1]]) (patternEdges [[],[],[1,1,1]]) (patternAmount [[],[],[1,1,1]]) (patternEdgeCount [[],[],[1,1,1]]) [] := certificate_295_checked

theorem certificate_296_checked : certificate_296.Valid 11 6 10 certificate_296_q certificate_296_edges 4 3 [] := by decide +kernel
theorem certificate_296_valid : certificate_296.Valid 11 6 (patternOrder [[],[],[1,1,2]]) (patternClique [[],[],[1,1,2]]) (patternEdges [[],[],[1,1,2]]) (patternAmount [[],[],[1,1,2]]) (patternEdgeCount [[],[],[1,1,2]]) [] := certificate_296_checked

theorem certificate_297_checked : certificate_297.Valid 11 6 11 certificate_297_q certificate_297_edges 5 3 [] := by decide +kernel
theorem certificate_297_valid : certificate_297.Valid 11 6 (patternOrder [[],[],[1,1,3]]) (patternClique [[],[],[1,1,3]]) (patternEdges [[],[],[1,1,3]]) (patternAmount [[],[],[1,1,3]]) (patternEdgeCount [[],[],[1,1,3]]) [] := certificate_297_checked

theorem certificate_298_checked : certificate_298.Valid 11 6 10 certificate_298_q certificate_298_edges 4 3 [] := by decide +kernel
theorem certificate_298_valid : certificate_298.Valid 11 6 (patternOrder [[],[],[1,2,1]]) (patternClique [[],[],[1,2,1]]) (patternEdges [[],[],[1,2,1]]) (patternAmount [[],[],[1,2,1]]) (patternEdgeCount [[],[],[1,2,1]]) [] := certificate_298_checked

theorem certificate_299_checked : certificate_299.Valid 11 6 11 certificate_299_q certificate_299_edges 5 3 [] := by decide +kernel
theorem certificate_299_valid : certificate_299.Valid 11 6 (patternOrder [[],[],[1,2,2]]) (patternClique [[],[],[1,2,2]]) (patternEdges [[],[],[1,2,2]]) (patternAmount [[],[],[1,2,2]]) (patternEdgeCount [[],[],[1,2,2]]) [] := certificate_299_checked

theorem certificate_300_checked : certificate_300.Valid 11 6 11 certificate_300_q certificate_300_edges 5 3 [] := by decide +kernel
theorem certificate_300_valid : certificate_300.Valid 11 6 (patternOrder [[],[],[1,3,1]]) (patternClique [[],[],[1,3,1]]) (patternEdges [[],[],[1,3,1]]) (patternAmount [[],[],[1,3,1]]) (patternEdgeCount [[],[],[1,3,1]]) [] := certificate_300_checked

theorem certificate_301_checked : certificate_301.Valid 11 6 10 certificate_301_q certificate_301_edges 4 2 [] := by decide +kernel
theorem certificate_301_valid : certificate_301.Valid 11 6 (patternOrder [[],[],[2],[2]]) (patternClique [[],[],[2],[2]]) (patternEdges [[],[],[2],[2]]) (patternAmount [[],[],[2],[2]]) (patternEdgeCount [[],[],[2],[2]]) [] := certificate_301_checked

theorem certificate_302_checked : certificate_302.Valid 11 6 11 certificate_302_q certificate_302_edges 5 2 [] := by decide +kernel
theorem certificate_302_valid : certificate_302.Valid 11 6 (patternOrder [[],[],[2],[3]]) (patternClique [[],[],[2],[3]]) (patternEdges [[],[],[2],[3]]) (patternAmount [[],[],[2],[3]]) (patternEdgeCount [[],[],[2],[3]]) [] := certificate_302_checked

theorem certificate_303_checked : certificate_303.Valid 11 6 11 certificate_303_q certificate_303_edges 5 3 [] := by decide +kernel
theorem certificate_303_valid : certificate_303.Valid 11 6 (patternOrder [[],[],[2,1,2]]) (patternClique [[],[],[2,1,2]]) (patternEdges [[],[],[2,1,2]]) (patternAmount [[],[],[2,1,2]]) (patternEdgeCount [[],[],[2,1,2]]) [] := certificate_303_checked

theorem certificate_304_checked : certificate_304.Valid 11 6 9 certificate_304_q certificate_304_edges 3 3 [] := by decide +kernel
theorem certificate_304_valid : certificate_304.Valid 11 6 (patternOrder [[],[1],[1,1]]) (patternClique [[],[1],[1,1]]) (patternEdges [[],[1],[1,1]]) (patternAmount [[],[1],[1,1]]) (patternEdgeCount [[],[1],[1,1]]) [] := certificate_304_checked

theorem certificate_305_checked : certificate_305.Valid 11 6 10 certificate_305_q certificate_305_edges 4 3 [] := by decide +kernel
theorem certificate_305_valid : certificate_305.Valid 11 6 (patternOrder [[],[1],[1,2]]) (patternClique [[],[1],[1,2]]) (patternEdges [[],[1],[1,2]]) (patternAmount [[],[1],[1,2]]) (patternEdgeCount [[],[1],[1,2]]) [] := certificate_305_checked

theorem certificate_306_checked : certificate_306.Valid 11 6 11 certificate_306_q certificate_306_edges 5 3 [] := by decide +kernel
theorem certificate_306_valid : certificate_306.Valid 11 6 (patternOrder [[],[1],[1,3]]) (patternClique [[],[1],[1,3]]) (patternEdges [[],[1],[1,3]]) (patternAmount [[],[1],[1,3]]) (patternEdgeCount [[],[1],[1,3]]) [] := certificate_306_checked

theorem certificate_307_checked : certificate_307.Valid 11 6 11 certificate_307_q certificate_307_edges 5 3 [] := by decide +kernel
theorem certificate_307_valid : certificate_307.Valid 11 6 (patternOrder [[],[1],[2,2]]) (patternClique [[],[1],[2,2]]) (patternEdges [[],[1],[2,2]]) (patternAmount [[],[1],[2,2]]) (patternEdgeCount [[],[1],[2,2]]) [] := certificate_307_checked

theorem certificate_308_checked : certificate_308.Valid 11 6 10 certificate_308_q certificate_308_edges 4 3 [] := by decide +kernel
theorem certificate_308_valid : certificate_308.Valid 11 6 (patternOrder [[],[1,1],[2]]) (patternClique [[],[1,1],[2]]) (patternEdges [[],[1,1],[2]]) (patternAmount [[],[1,1],[2]]) (patternEdgeCount [[],[1,1],[2]]) [] := certificate_308_checked

theorem certificate_309_checked : certificate_309.Valid 11 6 11 certificate_309_q certificate_309_edges 5 3 [] := by decide +kernel
theorem certificate_309_valid : certificate_309.Valid 11 6 (patternOrder [[],[1,1],[3]]) (patternClique [[],[1,1],[3]]) (patternEdges [[],[1,1],[3]]) (patternAmount [[],[1,1],[3]]) (patternEdgeCount [[],[1,1],[3]]) [] := certificate_309_checked

theorem certificate_310_checked : certificate_310.Valid 11 6 10 certificate_310_q certificate_310_edges 4 4 [] := by decide +kernel
theorem certificate_310_valid : certificate_310.Valid 11 6 (patternOrder [[],[1,1,1,1]]) (patternClique [[],[1,1,1,1]]) (patternEdges [[],[1,1,1,1]]) (patternAmount [[],[1,1,1,1]]) (patternEdgeCount [[],[1,1,1,1]]) [] := certificate_310_checked

theorem certificate_311_checked : certificate_311.Valid 11 6 11 certificate_311_q certificate_311_edges 5 4 [] := by decide +kernel
theorem certificate_311_valid : certificate_311.Valid 11 6 (patternOrder [[],[1,1,1,2]]) (patternClique [[],[1,1,1,2]]) (patternEdges [[],[1,1,1,2]]) (patternAmount [[],[1,1,1,2]]) (patternEdgeCount [[],[1,1,1,2]]) [] := certificate_311_checked

theorem certificate_312_checked : certificate_312.Valid 11 6 11 certificate_312_q certificate_312_edges 5 4 [] := by decide +kernel
theorem certificate_312_valid : certificate_312.Valid 11 6 (patternOrder [[],[1,1,2,1]]) (patternClique [[],[1,1,2,1]]) (patternEdges [[],[1,1,2,1]]) (patternAmount [[],[1,1,2,1]]) (patternEdgeCount [[],[1,1,2,1]]) [] := certificate_312_checked

theorem certificate_313_checked : certificate_313.Valid 11 6 11 certificate_313_q certificate_313_edges 5 3 [] := by decide +kernel
theorem certificate_313_valid : certificate_313.Valid 11 6 (patternOrder [[],[1,2],[2]]) (patternClique [[],[1,2],[2]]) (patternEdges [[],[1,2],[2]]) (patternAmount [[],[1,2],[2]]) (patternEdgeCount [[],[1,2],[2]]) [] := certificate_313_checked

theorem certificate_314_checked : certificate_314.Valid 11 6 9 certificate_314_q certificate_314_edges 3 3 [] := by decide +kernel
theorem certificate_314_valid : certificate_314.Valid 11 6 (patternOrder [[1],[1],[1]]) (patternClique [[1],[1],[1]]) (patternEdges [[1],[1],[1]]) (patternAmount [[1],[1],[1]]) (patternEdgeCount [[1],[1],[1]]) [] := certificate_314_checked

theorem certificate_315_checked : certificate_315.Valid 11 6 10 certificate_315_q certificate_315_edges 4 3 [] := by decide +kernel
theorem certificate_315_valid : certificate_315.Valid 11 6 (patternOrder [[1],[1],[2]]) (patternClique [[1],[1],[2]]) (patternEdges [[1],[1],[2]]) (patternAmount [[1],[1],[2]]) (patternEdgeCount [[1],[1],[2]]) [] := certificate_315_checked

theorem certificate_316_checked : certificate_316.Valid 11 6 11 certificate_316_q certificate_316_edges 5 3 [] := by decide +kernel
theorem certificate_316_valid : certificate_316.Valid 11 6 (patternOrder [[1],[1],[3]]) (patternClique [[1],[1],[3]]) (patternEdges [[1],[1],[3]]) (patternAmount [[1],[1],[3]]) (patternEdgeCount [[1],[1],[3]]) [] := certificate_316_checked

theorem certificate_317_checked : certificate_317.Valid 11 6 10 certificate_317_q certificate_317_edges 4 4 [] := by decide +kernel
theorem certificate_317_valid : certificate_317.Valid 11 6 (patternOrder [[1],[1,1,1]]) (patternClique [[1],[1,1,1]]) (patternEdges [[1],[1,1,1]]) (patternAmount [[1],[1,1,1]]) (patternEdgeCount [[1],[1,1,1]]) [] := certificate_317_checked

theorem certificate_318_checked : certificate_318.Valid 11 6 11 certificate_318_q certificate_318_edges 5 4 [] := by decide +kernel
theorem certificate_318_valid : certificate_318.Valid 11 6 (patternOrder [[1],[1,1,2]]) (patternClique [[1],[1,1,2]]) (patternEdges [[1],[1,1,2]]) (patternAmount [[1],[1,1,2]]) (patternEdgeCount [[1],[1,1,2]]) [] := certificate_318_checked

theorem certificate_319_checked : certificate_319.Valid 11 6 11 certificate_319_q certificate_319_edges 5 4 [] := by decide +kernel
theorem certificate_319_valid : certificate_319.Valid 11 6 (patternOrder [[1],[1,2,1]]) (patternClique [[1],[1,2,1]]) (patternEdges [[1],[1,2,1]]) (patternAmount [[1],[1,2,1]]) (patternEdgeCount [[1],[1,2,1]]) [] := certificate_319_checked

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

theorem certificate_320_checked : certificate_320.Valid 11 6 11 certificate_320_q certificate_320_edges 5 3 [] := by decide +kernel
theorem certificate_320_valid : certificate_320.Valid 11 6 (patternOrder [[1],[2],[2]]) (patternClique [[1],[2],[2]]) (patternEdges [[1],[2],[2]]) (patternAmount [[1],[2],[2]]) (patternEdgeCount [[1],[2],[2]]) [] := certificate_320_checked

theorem certificate_321_checked : certificate_321.Valid 11 6 10 certificate_321_q certificate_321_edges 4 4 [] := by decide +kernel
theorem certificate_321_valid : certificate_321.Valid 11 6 (patternOrder [[1,1],[1,1]]) (patternClique [[1,1],[1,1]]) (patternEdges [[1,1],[1,1]]) (patternAmount [[1,1],[1,1]]) (patternEdgeCount [[1,1],[1,1]]) [] := certificate_321_checked

theorem certificate_322_checked : certificate_322.Valid 11 6 11 certificate_322_q certificate_322_edges 5 4 [] := by decide +kernel
theorem certificate_322_valid : certificate_322.Valid 11 6 (patternOrder [[1,1],[1,2]]) (patternClique [[1,1],[1,2]]) (patternEdges [[1,1],[1,2]]) (patternAmount [[1,1],[1,2]]) (patternEdgeCount [[1,1],[1,2]]) [] := certificate_322_checked

theorem certificate_323_checked : certificate_323.Valid 11 6 11 certificate_323_q certificate_323_edges 5 4 [] := by decide +kernel
theorem certificate_323_valid : certificate_323.Valid 11 6 (patternOrder [[1,1,1],[2]]) (patternClique [[1,1,1],[2]]) (patternEdges [[1,1,1],[2]]) (patternAmount [[1,1,1],[2]]) (patternEdgeCount [[1,1,1],[2]]) [] := certificate_323_checked

theorem certificate_324_checked : certificate_324.Valid 11 6 11 certificate_324_q certificate_324_edges 5 5 [] := by decide +kernel
theorem certificate_324_valid : certificate_324.Valid 11 6 (patternOrder [[1,1,1,1,1]]) (patternClique [[1,1,1,1,1]]) (patternEdges [[1,1,1,1,1]]) (patternAmount [[1,1,1,1,1]]) (patternEdgeCount [[1,1,1,1,1]]) [] := certificate_324_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns11x6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem patterns_11_6_0_verified : ∀ D ∈ patterns_11_6_0, PatternVerified 11 6 D := by

  simp only [patterns_11_6_0, List.forall_mem_cons]

  exact ⟨⟨certificate_279, certificate_279_valid⟩, ⟨⟨certificate_280, certificate_280_valid⟩, ⟨⟨certificate_281, certificate_281_valid⟩, ⟨⟨certificate_282, certificate_282_valid⟩, ⟨⟨certificate_283, certificate_283_valid⟩, ⟨⟨certificate_284, certificate_284_valid⟩, ⟨⟨certificate_285, certificate_285_valid⟩, ⟨⟨certificate_286, certificate_286_valid⟩, ⟨⟨certificate_287, certificate_287_valid⟩, ⟨⟨certificate_288, certificate_288_valid⟩, ⟨⟨certificate_289, certificate_289_valid⟩, ⟨⟨certificate_290, certificate_290_valid⟩, ⟨⟨certificate_291, certificate_291_valid⟩, ⟨⟨certificate_292, certificate_292_valid⟩, ⟨⟨certificate_293, certificate_293_valid⟩, ⟨⟨certificate_294, certificate_294_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem patterns_11_6_1_verified : ∀ D ∈ patterns_11_6_1, PatternVerified 11 6 D := by

  simp only [patterns_11_6_1, List.forall_mem_cons]

  exact ⟨⟨certificate_295, certificate_295_valid⟩, ⟨⟨certificate_296, certificate_296_valid⟩, ⟨⟨certificate_297, certificate_297_valid⟩, ⟨⟨certificate_298, certificate_298_valid⟩, ⟨⟨certificate_299, certificate_299_valid⟩, ⟨⟨certificate_300, certificate_300_valid⟩, ⟨⟨certificate_301, certificate_301_valid⟩, ⟨⟨certificate_302, certificate_302_valid⟩, ⟨⟨certificate_303, certificate_303_valid⟩, ⟨⟨certificate_304, certificate_304_valid⟩, ⟨⟨certificate_305, certificate_305_valid⟩, ⟨⟨certificate_306, certificate_306_valid⟩, ⟨⟨certificate_307, certificate_307_valid⟩, ⟨⟨certificate_308, certificate_308_valid⟩, ⟨⟨certificate_309, certificate_309_valid⟩, ⟨⟨certificate_310, certificate_310_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem patterns_11_6_2_verified : ∀ D ∈ patterns_11_6_2, PatternVerified 11 6 D := by

  simp only [patterns_11_6_2, List.forall_mem_cons]

  exact ⟨⟨certificate_311, certificate_311_valid⟩, ⟨⟨certificate_312, certificate_312_valid⟩, ⟨⟨certificate_313, certificate_313_valid⟩, ⟨⟨certificate_314, certificate_314_valid⟩, ⟨⟨certificate_315, certificate_315_valid⟩, ⟨⟨certificate_316, certificate_316_valid⟩, ⟨⟨certificate_317, certificate_317_valid⟩, ⟨⟨certificate_318, certificate_318_valid⟩, ⟨⟨certificate_319, certificate_319_valid⟩, ⟨⟨certificate_320, certificate_320_valid⟩, ⟨⟨certificate_321, certificate_321_valid⟩, ⟨⟨certificate_322, certificate_322_valid⟩, ⟨⟨certificate_323, certificate_323_valid⟩, ⟨⟨certificate_324, certificate_324_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem patterns_11_6_verified : ∀ D ∈ patterns_11_6, PatternVerified 11 6 D := by

  simp only [patterns_11_6, List.forall_mem_append]

  exact ⟨patterns_11_6_0_verified, ⟨patterns_11_6_1_verified, ⟨patterns_11_6_2_verified, by simp⟩⟩⟩

theorem patterns_11_6_coverage : patternChoices 6 5 [] = patterns_11_6 := by decide +kernel

theorem finite_patterns_11_6_oai : ∀ D ∈ patternChoices 6 (11-6) [], PatternVerified 11 6 D := by

  rw [patterns_11_6_coverage]

  exact patterns_11_6_verified

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.finite_patterns_11_6_oai := @OAI.CycleClique.finite_patterns_11_6_oai
