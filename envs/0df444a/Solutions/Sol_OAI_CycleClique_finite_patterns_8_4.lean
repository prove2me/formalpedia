-- Prove2me | solution 1 for OAI.CycleClique.finite_patterns_8_4
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T21:03:37.941704+00:00
-- url     : https://prove2.me/submissions/207ff81c-730c-43c2-815a-7398044d387d

import Mathlib
import Definitions.Def_OAIQ107D132
import Definitions.Def_OAIQ107D133

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates002
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_47_checked : certificate_47.Valid 8 4 4 certificate_47_q certificate_47_edges 0 0 [] := by decide +kernel
theorem certificate_47_valid : certificate_47.Valid 8 4 (patternOrder [[],[],[],[]]) (patternClique [[],[],[],[]]) (patternEdges [[],[],[],[]]) (patternAmount [[],[],[],[]]) (patternEdgeCount [[],[],[],[]]) [] := certificate_47_checked

theorem certificate_48_checked : certificate_48.Valid 8 4 5 certificate_48_q certificate_48_edges 1 1 [] := by decide +kernel
theorem certificate_48_valid : certificate_48.Valid 8 4 (patternOrder [[],[],[1]]) (patternClique [[],[],[1]]) (patternEdges [[],[],[1]]) (patternAmount [[],[],[1]]) (patternEdgeCount [[],[],[1]]) [] := certificate_48_checked

theorem certificate_49_checked : certificate_49.Valid 8 4 6 certificate_49_q certificate_49_edges 2 1 [] := by decide +kernel
theorem certificate_49_valid : certificate_49.Valid 8 4 (patternOrder [[],[],[2]]) (patternClique [[],[],[2]]) (patternEdges [[],[],[2]]) (patternAmount [[],[],[2]]) (patternEdgeCount [[],[],[2]]) [] := certificate_49_checked

theorem certificate_50_part_6_checked : certificate_50_part_6.Valid 8 4 7 certificate_50_q certificate_50_part_6_E 3 1 certificate_50_part_6_M := by exact ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩, by decide +kernel⟩

theorem certificate_50_part_5_checked : certificate_50_part_5.Valid 8 4 7 certificate_50_q certificate_50_part_5_E 3 1 certificate_50_part_5_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_50_part_6_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_50_part_4_checked : certificate_50_part_4.Valid 8 4 7 certificate_50_q certificate_50_part_4_E 3 1 certificate_50_part_4_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_50_part_5_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_50_part_3_checked : certificate_50_part_3.Valid 8 4 7 certificate_50_q certificate_50_part_3_E 3 1 certificate_50_part_3_M := by exact ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_50_part_4_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_50_part_2_checked : certificate_50_part_2.Valid 8 4 7 certificate_50_q certificate_50_part_2_E 3 1 certificate_50_part_2_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_50_part_3_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_50_part_1_checked : certificate_50_part_1.Valid 8 4 7 certificate_50_q certificate_50_part_1_E 3 1 certificate_50_part_1_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_50_part_2_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_50_checked : certificate_50.Valid 8 4 7 certificate_50_q certificate_50_E 3 1 certificate_50_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_50_part_1_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_50_valid : certificate_50.Valid 8 4 (patternOrder [[],[],[3]]) (patternClique [[],[],[3]]) (patternEdges [[],[],[3]]) (patternAmount [[],[],[3]]) (patternEdgeCount [[],[],[3]]) [] := certificate_50_checked

theorem certificate_51_part_3_checked : certificate_51_part_3.Valid 8 4 8 certificate_51_q certificate_51_part_3_E 4 1 certificate_51_part_3_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem certificate_51_part_5_checked : certificate_51_part_5.Valid 8 4 9 certificate_51_q certificate_51_part_5_E 4 1 certificate_51_part_5_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩⟩⟩

theorem certificate_51_part_8_checked : certificate_51_part_8.Valid 8 4 9 certificate_51_q certificate_51_part_8_E 4 1 certificate_51_part_8_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem certificate_51_part_10_checked : certificate_51_part_10.Valid 8 4 8 certificate_51_q certificate_51_part_10_E 4 1 certificate_51_part_10_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem certificate_51_part_12_checked : certificate_51_part_12.Valid 8 4 9 certificate_51_q certificate_51_part_12_E 4 1 certificate_51_part_12_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩⟩

theorem certificate_51_part_11_checked : certificate_51_part_11.Valid 8 4 8 certificate_51_q certificate_51_part_11_E 4 1 certificate_51_part_11_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_51_part_12_checked⟩⟩⟩⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩⟩⟩

theorem certificate_51_part_9_checked : certificate_51_part_9.Valid 8 4 8 certificate_51_q certificate_51_part_9_E 4 1 certificate_51_part_9_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_51_part_10_checked⟩⟩⟩⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_51_part_11_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_51_part_7_checked : certificate_51_part_7.Valid 8 4 8 certificate_51_q certificate_51_part_7_E 4 1 certificate_51_part_7_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_51_part_8_checked⟩⟩⟩⟩⟩⟩, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_51_part_9_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_51_part_6_checked : certificate_51_part_6.Valid 8 4 8 certificate_51_q certificate_51_part_6_E 4 1 certificate_51_part_6_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_51_part_7_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_51_part_4_checked : certificate_51_part_4.Valid 8 4 8 certificate_51_q certificate_51_part_4_E 4 1 certificate_51_part_4_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_51_part_5_checked⟩⟩⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_51_part_6_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_51_part_2_checked : certificate_51_part_2.Valid 8 4 8 certificate_51_q certificate_51_part_2_E 4 1 certificate_51_part_2_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_51_part_3_checked⟩⟩⟩⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_51_part_4_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_51_part_1_checked : certificate_51_part_1.Valid 8 4 8 certificate_51_q certificate_51_part_1_E 4 1 certificate_51_part_1_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_51_part_2_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_51_checked : certificate_51.Valid 8 4 8 certificate_51_q certificate_51_E 4 1 certificate_51_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_51_part_1_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_51_valid : certificate_51.Valid 8 4 (patternOrder [[],[],[4]]) (patternClique [[],[],[4]]) (patternEdges [[],[],[4]]) (patternAmount [[],[],[4]]) (patternEdgeCount [[],[],[4]]) [] := certificate_51_checked

theorem certificate_52_checked : certificate_52.Valid 8 4 6 certificate_52_q certificate_52_edges 2 2 [] := by decide +kernel
theorem certificate_52_valid : certificate_52.Valid 8 4 (patternOrder [[],[1,1]]) (patternClique [[],[1,1]]) (patternEdges [[],[1,1]]) (patternAmount [[],[1,1]]) (patternEdgeCount [[],[1,1]]) [] := certificate_52_checked

theorem certificate_53_checked : certificate_53.Valid 8 4 7 certificate_53_q certificate_53_edges 3 2 [] := by decide +kernel
theorem certificate_53_valid : certificate_53.Valid 8 4 (patternOrder [[],[1,2]]) (patternClique [[],[1,2]]) (patternEdges [[],[1,2]]) (patternAmount [[],[1,2]]) (patternEdgeCount [[],[1,2]]) [] := certificate_53_checked

theorem certificate_54_checked : certificate_54.Valid 8 4 8 certificate_54_q certificate_54_edges 4 2 [] := by decide +kernel
theorem certificate_54_valid : certificate_54.Valid 8 4 (patternOrder [[],[1,3]]) (patternClique [[],[1,3]]) (patternEdges [[],[1,3]]) (patternAmount [[],[1,3]]) (patternEdgeCount [[],[1,3]]) [] := certificate_54_checked

theorem certificate_55_checked : certificate_55.Valid 8 4 8 certificate_55_q certificate_55_edges 4 2 [] := by decide +kernel
theorem certificate_55_valid : certificate_55.Valid 8 4 (patternOrder [[],[2,2]]) (patternClique [[],[2,2]]) (patternEdges [[],[2,2]]) (patternAmount [[],[2,2]]) (patternEdgeCount [[],[2,2]]) [] := certificate_55_checked

theorem certificate_56_checked : certificate_56.Valid 8 4 6 certificate_56_q certificate_56_edges 2 2 [] := by decide +kernel
theorem certificate_56_valid : certificate_56.Valid 8 4 (patternOrder [[1],[1]]) (patternClique [[1],[1]]) (patternEdges [[1],[1]]) (patternAmount [[1],[1]]) (patternEdgeCount [[1],[1]]) [] := certificate_56_checked

theorem certificate_57_checked : certificate_57.Valid 8 4 7 certificate_57_q certificate_57_edges 3 2 [] := by decide +kernel
theorem certificate_57_valid : certificate_57.Valid 8 4 (patternOrder [[1],[2]]) (patternClique [[1],[2]]) (patternEdges [[1],[2]]) (patternAmount [[1],[2]]) (patternEdgeCount [[1],[2]]) [] := certificate_57_checked

theorem certificate_58_part_3_checked : certificate_58_part_3.Valid 8 4 8 certificate_58_q certificate_58_part_3_E 4 2 certificate_58_part_3_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem certificate_58_part_6_checked : certificate_58_part_6.Valid 8 4 8 certificate_58_q certificate_58_part_6_E 4 2 certificate_58_part_6_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩

theorem certificate_58_part_9_checked : certificate_58_part_9.Valid 8 4 8 certificate_58_q certificate_58_part_9_E 4 2 certificate_58_part_9_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩, by decide +kernel⟩⟩⟩⟩

theorem certificate_58_part_8_checked : certificate_58_part_8.Valid 8 4 8 certificate_58_q certificate_58_part_8_E 4 2 certificate_58_part_8_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_58_part_9_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_58_part_7_checked : certificate_58_part_7.Valid 8 4 8 certificate_58_q certificate_58_part_7_E 4 2 certificate_58_part_7_M := by exact ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_58_part_8_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_58_part_5_checked : certificate_58_part_5.Valid 8 4 8 certificate_58_q certificate_58_part_5_E 4 2 certificate_58_part_5_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, certificate_58_part_6_checked, certificate_58_part_7_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_58_part_4_checked : certificate_58_part_4.Valid 8 4 8 certificate_58_q certificate_58_part_4_E 4 2 certificate_58_part_4_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_58_part_5_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_58_part_2_checked : certificate_58_part_2.Valid 8 4 8 certificate_58_q certificate_58_part_2_E 4 2 certificate_58_part_2_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, certificate_58_part_3_checked, certificate_58_part_4_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_58_part_1_checked : certificate_58_part_1.Valid 8 4 8 certificate_58_q certificate_58_part_1_E 4 2 certificate_58_part_1_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_58_part_2_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_58_checked : certificate_58.Valid 8 4 8 certificate_58_q certificate_58_E 4 2 certificate_58_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_58_part_1_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_58_valid : certificate_58.Valid 8 4 (patternOrder [[1],[3]]) (patternClique [[1],[3]]) (patternEdges [[1],[3]]) (patternAmount [[1],[3]]) (patternEdgeCount [[1],[3]]) [] := certificate_58_checked

theorem certificate_59_checked : certificate_59.Valid 8 4 7 certificate_59_q certificate_59_edges 3 3 [] := by decide +kernel
theorem certificate_59_valid : certificate_59.Valid 8 4 (patternOrder [[1,1,1]]) (patternClique [[1,1,1]]) (patternEdges [[1,1,1]]) (patternAmount [[1,1,1]]) (patternEdgeCount [[1,1,1]]) [] := certificate_59_checked

theorem certificate_60_checked : certificate_60.Valid 8 4 8 certificate_60_q certificate_60_edges 4 3 [] := by decide +kernel
theorem certificate_60_valid : certificate_60.Valid 8 4 (patternOrder [[1,1,2]]) (patternClique [[1,1,2]]) (patternEdges [[1,1,2]]) (patternAmount [[1,1,2]]) (patternEdgeCount [[1,1,2]]) [] := certificate_60_checked

theorem certificate_61_checked : certificate_61.Valid 8 4 8 certificate_61_q certificate_61_edges 4 3 [] := by decide +kernel
theorem certificate_61_valid : certificate_61.Valid 8 4 (patternOrder [[1,2,1]]) (patternClique [[1,2,1]]) (patternEdges [[1,2,1]]) (patternAmount [[1,2,1]]) (patternEdgeCount [[1,2,1]]) [] := certificate_61_checked

theorem certificate_62_checked : certificate_62.Valid 8 4 8 certificate_62_q certificate_62_edges 4 2 [] := by decide +kernel
theorem certificate_62_valid : certificate_62.Valid 8 4 (patternOrder [[2],[2]]) (patternClique [[2],[2]]) (patternEdges [[2],[2]]) (patternAmount [[2],[2]]) (patternEdgeCount [[2],[2]]) [] := certificate_62_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns8x4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem patterns_8_4_0_verified : ∀ D ∈ patterns_8_4_0, PatternVerified 8 4 D := by

  simp only [patterns_8_4_0, List.forall_mem_cons]

  exact ⟨⟨certificate_47, certificate_47_valid⟩, ⟨⟨certificate_48, certificate_48_valid⟩, ⟨⟨certificate_49, certificate_49_valid⟩, ⟨⟨certificate_50, certificate_50_valid⟩, ⟨⟨certificate_51, certificate_51_valid⟩, ⟨⟨certificate_52, certificate_52_valid⟩, ⟨⟨certificate_53, certificate_53_valid⟩, ⟨⟨certificate_54, certificate_54_valid⟩, ⟨⟨certificate_55, certificate_55_valid⟩, ⟨⟨certificate_56, certificate_56_valid⟩, ⟨⟨certificate_57, certificate_57_valid⟩, ⟨⟨certificate_58, certificate_58_valid⟩, ⟨⟨certificate_59, certificate_59_valid⟩, ⟨⟨certificate_60, certificate_60_valid⟩, ⟨⟨certificate_61, certificate_61_valid⟩, ⟨⟨certificate_62, certificate_62_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem patterns_8_4_verified : ∀ D ∈ patterns_8_4, PatternVerified 8 4 D := by

  simp only [patterns_8_4, List.forall_mem_append]

  exact ⟨patterns_8_4_0_verified, by simp⟩

theorem patterns_8_4_coverage : patternChoices 4 4 [] = patterns_8_4 := by decide +kernel

theorem finite_patterns_8_4_oai : ∀ D ∈ patternChoices 4 (8-4) [], PatternVerified 8 4 D := by

  rw [patterns_8_4_coverage]

  exact patterns_8_4_verified

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.finite_patterns_8_4_oai := @OAI.CycleClique.finite_patterns_8_4_oai
