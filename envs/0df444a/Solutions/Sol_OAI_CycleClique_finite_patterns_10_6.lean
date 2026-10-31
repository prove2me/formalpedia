-- Prove2me | solution 1 for OAI.CycleClique.finite_patterns_10_6
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T19:56:42.731643+00:00
-- url     : https://prove2.me/submissions/ea230854-23af-4101-966d-d0ced5b34ce2

import Mathlib
import Definitions.Def_OAIQ107D129
import Definitions.Def_OAIQ107D130
import Definitions.Def_OAIQ107D133

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates006
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_179_checked : certificate_179.Valid 10 6 6 certificate_179_q certificate_179_edges 0 0 [] := by decide +kernel
theorem certificate_179_valid : certificate_179.Valid 10 6 (patternOrder [[],[],[],[],[],[]]) (patternClique [[],[],[],[],[],[]]) (patternEdges [[],[],[],[],[],[]]) (patternAmount [[],[],[],[],[],[]]) (patternEdgeCount [[],[],[],[],[],[]]) [] := certificate_179_checked

theorem certificate_180_checked : certificate_180.Valid 10 6 7 certificate_180_q certificate_180_edges 1 1 [] := by decide +kernel
theorem certificate_180_valid : certificate_180.Valid 10 6 (patternOrder [[],[],[],[],[1]]) (patternClique [[],[],[],[],[1]]) (patternEdges [[],[],[],[],[1]]) (patternAmount [[],[],[],[],[1]]) (patternEdgeCount [[],[],[],[],[1]]) [] := certificate_180_checked

theorem certificate_181_checked : certificate_181.Valid 10 6 8 certificate_181_q certificate_181_edges 2 1 [] := by decide +kernel
theorem certificate_181_valid : certificate_181.Valid 10 6 (patternOrder [[],[],[],[],[2]]) (patternClique [[],[],[],[],[2]]) (patternEdges [[],[],[],[],[2]]) (patternAmount [[],[],[],[],[2]]) (patternEdgeCount [[],[],[],[],[2]]) [] := certificate_181_checked

theorem certificate_182_checked : certificate_182.Valid 10 6 9 certificate_182_q certificate_182_edges 3 1 [] := by decide +kernel
theorem certificate_182_valid : certificate_182.Valid 10 6 (patternOrder [[],[],[],[],[3]]) (patternClique [[],[],[],[],[3]]) (patternEdges [[],[],[],[],[3]]) (patternAmount [[],[],[],[],[3]]) (patternEdgeCount [[],[],[],[],[3]]) [] := certificate_182_checked

theorem certificate_183_part_6_checked : certificate_183_part_6.Valid 10 6 10 certificate_183_q certificate_183_part_6_E 4 1 certificate_183_part_6_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩⟩⟩

theorem certificate_183_part_8_checked : certificate_183_part_8.Valid 10 6 10 certificate_183_q certificate_183_part_8_E 4 1 certificate_183_part_8_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩

theorem certificate_183_part_10_checked : certificate_183_part_10.Valid 10 6 11 certificate_183_q certificate_183_part_10_E 4 1 certificate_183_part_10_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩

theorem certificate_183_part_9_checked : certificate_183_part_9.Valid 10 6 11 certificate_183_q certificate_183_part_9_E 4 1 certificate_183_part_9_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_183_part_10_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_183_part_12_checked : certificate_183_part_12.Valid 10 6 10 certificate_183_q certificate_183_part_12_E 4 1 certificate_183_part_12_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩

theorem certificate_183_part_13_checked : certificate_183_part_13.Valid 10 6 10 certificate_183_q certificate_183_part_13_E 4 1 certificate_183_part_13_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩⟩⟩

theorem certificate_183_part_14_checked : certificate_183_part_14.Valid 10 6 10 certificate_183_q certificate_183_part_14_E 4 1 certificate_183_part_14_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩⟩⟩

theorem certificate_183_part_15_checked : certificate_183_part_15.Valid 10 6 10 certificate_183_q certificate_183_part_15_E 4 1 certificate_183_part_15_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_183_part_16_checked : certificate_183_part_16.Valid 10 6 10 certificate_183_q certificate_183_part_16_E 4 1 certificate_183_part_16_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_183_part_18_checked : certificate_183_part_18.Valid 10 6 10 certificate_183_q certificate_183_part_18_E 4 1 certificate_183_part_18_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

theorem certificate_183_part_17_checked : certificate_183_part_17.Valid 10 6 10 certificate_183_q certificate_183_part_17_E 4 1 certificate_183_part_17_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_183_part_18_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_183_part_20_checked : certificate_183_part_20.Valid 10 6 10 certificate_183_q certificate_183_part_20_E 4 1 certificate_183_part_20_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩

theorem certificate_183_part_24_checked : certificate_183_part_24.Valid 10 6 11 certificate_183_q certificate_183_part_24_E 4 1 certificate_183_part_24_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

theorem certificate_183_part_23_checked : certificate_183_part_23.Valid 10 6 11 certificate_183_q certificate_183_part_23_E 4 1 certificate_183_part_23_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_183_part_24_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_183_part_22_checked : certificate_183_part_22.Valid 10 6 11 certificate_183_q certificate_183_part_22_E 4 1 certificate_183_part_22_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_183_part_23_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_183_part_26_checked : certificate_183_part_26.Valid 10 6 10 certificate_183_q certificate_183_part_26_E 4 1 certificate_183_part_26_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩⟩

theorem certificate_183_part_25_checked : certificate_183_part_25.Valid 10 6 10 certificate_183_q certificate_183_part_25_E 4 1 certificate_183_part_25_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_183_part_26_checked⟩⟩⟩⟩, by decide +kernel⟩⟩⟩⟩

theorem certificate_183_part_21_checked : certificate_183_part_21.Valid 10 6 10 certificate_183_q certificate_183_part_21_E 4 1 certificate_183_part_21_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_183_part_22_checked⟩⟩⟩⟩⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_183_part_25_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_183_part_19_checked : certificate_183_part_19.Valid 10 6 10 certificate_183_q certificate_183_part_19_E 4 1 certificate_183_part_19_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_183_part_20_checked⟩⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_183_part_21_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_183_part_11_checked : certificate_183_part_11.Valid 10 6 10 certificate_183_q certificate_183_part_11_E 4 1 certificate_183_part_11_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_183_part_12_checked⟩⟩⟩⟩⟩, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_183_part_13_checked⟩⟩⟩⟩, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_183_part_14_checked⟩⟩⟩, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_183_part_15_checked⟩⟩, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_183_part_16_checked⟩, ⟨by decide +kernel, by decide +kernel, certificate_183_part_17_checked, certificate_183_part_19_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_183_part_7_checked : certificate_183_part_7.Valid 10 6 10 certificate_183_q certificate_183_part_7_E 4 1 certificate_183_part_7_M := by exact ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_183_part_8_checked⟩⟩⟩⟩⟩⟩⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_183_part_9_checked⟩⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_183_part_11_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_183_part_5_checked : certificate_183_part_5.Valid 10 6 10 certificate_183_q certificate_183_part_5_E 4 1 certificate_183_part_5_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_183_part_6_checked⟩⟩⟩⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_183_part_7_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_183_part_4_checked : certificate_183_part_4.Valid 10 6 10 certificate_183_q certificate_183_part_4_E 4 1 certificate_183_part_4_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_183_part_5_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_183_part_3_checked : certificate_183_part_3.Valid 10 6 10 certificate_183_q certificate_183_part_3_E 4 1 certificate_183_part_3_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_183_part_4_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_183_part_2_checked : certificate_183_part_2.Valid 10 6 10 certificate_183_q certificate_183_part_2_E 4 1 certificate_183_part_2_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_183_part_3_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_183_part_1_checked : certificate_183_part_1.Valid 10 6 10 certificate_183_q certificate_183_part_1_E 4 1 certificate_183_part_1_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_183_part_2_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_183_checked : certificate_183.Valid 10 6 10 certificate_183_q certificate_183_E 4 1 certificate_183_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_183_part_1_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_183_valid : certificate_183.Valid 10 6 (patternOrder [[],[],[],[],[4]]) (patternClique [[],[],[],[],[4]]) (patternEdges [[],[],[],[],[4]]) (patternAmount [[],[],[],[],[4]]) (patternEdgeCount [[],[],[],[],[4]]) [] := certificate_183_checked

theorem certificate_184_checked : certificate_184.Valid 10 6 8 certificate_184_q certificate_184_edges 2 2 [] := by decide +kernel
theorem certificate_184_valid : certificate_184.Valid 10 6 (patternOrder [[],[],[],[1,1]]) (patternClique [[],[],[],[1,1]]) (patternEdges [[],[],[],[1,1]]) (patternAmount [[],[],[],[1,1]]) (patternEdgeCount [[],[],[],[1,1]]) [] := certificate_184_checked

theorem certificate_185_checked : certificate_185.Valid 10 6 9 certificate_185_q certificate_185_edges 3 2 [] := by decide +kernel
theorem certificate_185_valid : certificate_185.Valid 10 6 (patternOrder [[],[],[],[1,2]]) (patternClique [[],[],[],[1,2]]) (patternEdges [[],[],[],[1,2]]) (patternAmount [[],[],[],[1,2]]) (patternEdgeCount [[],[],[],[1,2]]) [] := certificate_185_checked

theorem certificate_186_checked : certificate_186.Valid 10 6 10 certificate_186_q certificate_186_edges 4 2 [] := by decide +kernel
theorem certificate_186_valid : certificate_186.Valid 10 6 (patternOrder [[],[],[],[1,3]]) (patternClique [[],[],[],[1,3]]) (patternEdges [[],[],[],[1,3]]) (patternAmount [[],[],[],[1,3]]) (patternEdgeCount [[],[],[],[1,3]]) [] := certificate_186_checked

theorem certificate_187_checked : certificate_187.Valid 10 6 10 certificate_187_q certificate_187_edges 4 2 [] := by decide +kernel
theorem certificate_187_valid : certificate_187.Valid 10 6 (patternOrder [[],[],[],[2,2]]) (patternClique [[],[],[],[2,2]]) (patternEdges [[],[],[],[2,2]]) (patternAmount [[],[],[],[2,2]]) (patternEdgeCount [[],[],[],[2,2]]) [] := certificate_187_checked

theorem certificate_188_checked : certificate_188.Valid 10 6 8 certificate_188_q certificate_188_edges 2 2 [] := by decide +kernel
theorem certificate_188_valid : certificate_188.Valid 10 6 (patternOrder [[],[],[1],[1]]) (patternClique [[],[],[1],[1]]) (patternEdges [[],[],[1],[1]]) (patternAmount [[],[],[1],[1]]) (patternEdgeCount [[],[],[1],[1]]) [] := certificate_188_checked

theorem certificate_189_checked : certificate_189.Valid 10 6 9 certificate_189_q certificate_189_edges 3 2 [] := by decide +kernel
theorem certificate_189_valid : certificate_189.Valid 10 6 (patternOrder [[],[],[1],[2]]) (patternClique [[],[],[1],[2]]) (patternEdges [[],[],[1],[2]]) (patternAmount [[],[],[1],[2]]) (patternEdgeCount [[],[],[1],[2]]) [] := certificate_189_checked

theorem certificate_190_checked : certificate_190.Valid 10 6 10 certificate_190_q certificate_190_edges 4 2 [] := by decide +kernel
theorem certificate_190_valid : certificate_190.Valid 10 6 (patternOrder [[],[],[1],[3]]) (patternClique [[],[],[1],[3]]) (patternEdges [[],[],[1],[3]]) (patternAmount [[],[],[1],[3]]) (patternEdgeCount [[],[],[1],[3]]) [] := certificate_190_checked

theorem certificate_191_checked : certificate_191.Valid 10 6 9 certificate_191_q certificate_191_edges 3 3 [] := by decide +kernel
theorem certificate_191_valid : certificate_191.Valid 10 6 (patternOrder [[],[],[1,1,1]]) (patternClique [[],[],[1,1,1]]) (patternEdges [[],[],[1,1,1]]) (patternAmount [[],[],[1,1,1]]) (patternEdgeCount [[],[],[1,1,1]]) [] := certificate_191_checked

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

theorem certificate_192_checked : certificate_192.Valid 10 6 10 certificate_192_q certificate_192_edges 4 3 [] := by decide +kernel
theorem certificate_192_valid : certificate_192.Valid 10 6 (patternOrder [[],[],[1,1,2]]) (patternClique [[],[],[1,1,2]]) (patternEdges [[],[],[1,1,2]]) (patternAmount [[],[],[1,1,2]]) (patternEdgeCount [[],[],[1,1,2]]) [] := certificate_192_checked

theorem certificate_193_checked : certificate_193.Valid 10 6 10 certificate_193_q certificate_193_edges 4 3 [] := by decide +kernel
theorem certificate_193_valid : certificate_193.Valid 10 6 (patternOrder [[],[],[1,2,1]]) (patternClique [[],[],[1,2,1]]) (patternEdges [[],[],[1,2,1]]) (patternAmount [[],[],[1,2,1]]) (patternEdgeCount [[],[],[1,2,1]]) [] := certificate_193_checked

theorem certificate_194_checked : certificate_194.Valid 10 6 10 certificate_194_q certificate_194_edges 4 2 [] := by decide +kernel
theorem certificate_194_valid : certificate_194.Valid 10 6 (patternOrder [[],[],[2],[2]]) (patternClique [[],[],[2],[2]]) (patternEdges [[],[],[2],[2]]) (patternAmount [[],[],[2],[2]]) (patternEdgeCount [[],[],[2],[2]]) [] := certificate_194_checked

theorem certificate_195_checked : certificate_195.Valid 10 6 9 certificate_195_q certificate_195_edges 3 3 [] := by decide +kernel
theorem certificate_195_valid : certificate_195.Valid 10 6 (patternOrder [[],[1],[1,1]]) (patternClique [[],[1],[1,1]]) (patternEdges [[],[1],[1,1]]) (patternAmount [[],[1],[1,1]]) (patternEdgeCount [[],[1],[1,1]]) [] := certificate_195_checked

theorem certificate_196_checked : certificate_196.Valid 10 6 10 certificate_196_q certificate_196_edges 4 3 [] := by decide +kernel
theorem certificate_196_valid : certificate_196.Valid 10 6 (patternOrder [[],[1],[1,2]]) (patternClique [[],[1],[1,2]]) (patternEdges [[],[1],[1,2]]) (patternAmount [[],[1],[1,2]]) (patternEdgeCount [[],[1],[1,2]]) [] := certificate_196_checked

theorem certificate_197_checked : certificate_197.Valid 10 6 10 certificate_197_q certificate_197_edges 4 3 [] := by decide +kernel
theorem certificate_197_valid : certificate_197.Valid 10 6 (patternOrder [[],[1,1],[2]]) (patternClique [[],[1,1],[2]]) (patternEdges [[],[1,1],[2]]) (patternAmount [[],[1,1],[2]]) (patternEdgeCount [[],[1,1],[2]]) [] := certificate_197_checked

theorem certificate_198_checked : certificate_198.Valid 10 6 10 certificate_198_q certificate_198_edges 4 4 [] := by decide +kernel
theorem certificate_198_valid : certificate_198.Valid 10 6 (patternOrder [[],[1,1,1,1]]) (patternClique [[],[1,1,1,1]]) (patternEdges [[],[1,1,1,1]]) (patternAmount [[],[1,1,1,1]]) (patternEdgeCount [[],[1,1,1,1]]) [] := certificate_198_checked

theorem certificate_199_checked : certificate_199.Valid 10 6 9 certificate_199_q certificate_199_edges 3 3 [] := by decide +kernel
theorem certificate_199_valid : certificate_199.Valid 10 6 (patternOrder [[1],[1],[1]]) (patternClique [[1],[1],[1]]) (patternEdges [[1],[1],[1]]) (patternAmount [[1],[1],[1]]) (patternEdgeCount [[1],[1],[1]]) [] := certificate_199_checked

theorem certificate_200_checked : certificate_200.Valid 10 6 10 certificate_200_q certificate_200_edges 4 3 [] := by decide +kernel
theorem certificate_200_valid : certificate_200.Valid 10 6 (patternOrder [[1],[1],[2]]) (patternClique [[1],[1],[2]]) (patternEdges [[1],[1],[2]]) (patternAmount [[1],[1],[2]]) (patternEdgeCount [[1],[1],[2]]) [] := certificate_200_checked

theorem certificate_201_checked : certificate_201.Valid 10 6 10 certificate_201_q certificate_201_edges 4 4 [] := by decide +kernel
theorem certificate_201_valid : certificate_201.Valid 10 6 (patternOrder [[1],[1,1,1]]) (patternClique [[1],[1,1,1]]) (patternEdges [[1],[1,1,1]]) (patternAmount [[1],[1,1,1]]) (patternEdgeCount [[1],[1,1,1]]) [] := certificate_201_checked

theorem certificate_202_checked : certificate_202.Valid 10 6 10 certificate_202_q certificate_202_edges 4 4 [] := by decide +kernel
theorem certificate_202_valid : certificate_202.Valid 10 6 (patternOrder [[1,1],[1,1]]) (patternClique [[1,1],[1,1]]) (patternEdges [[1,1],[1,1]]) (patternAmount [[1,1],[1,1]]) (patternEdgeCount [[1,1],[1,1]]) [] := certificate_202_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns10x6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem patterns_10_6_0_verified : ∀ D ∈ patterns_10_6_0, PatternVerified 10 6 D := by

  simp only [patterns_10_6_0, List.forall_mem_cons]

  exact ⟨⟨certificate_179, certificate_179_valid⟩, ⟨⟨certificate_180, certificate_180_valid⟩, ⟨⟨certificate_181, certificate_181_valid⟩, ⟨⟨certificate_182, certificate_182_valid⟩, ⟨⟨certificate_183, certificate_183_valid⟩, ⟨⟨certificate_184, certificate_184_valid⟩, ⟨⟨certificate_185, certificate_185_valid⟩, ⟨⟨certificate_186, certificate_186_valid⟩, ⟨⟨certificate_187, certificate_187_valid⟩, ⟨⟨certificate_188, certificate_188_valid⟩, ⟨⟨certificate_189, certificate_189_valid⟩, ⟨⟨certificate_190, certificate_190_valid⟩, ⟨⟨certificate_191, certificate_191_valid⟩, ⟨⟨certificate_192, certificate_192_valid⟩, ⟨⟨certificate_193, certificate_193_valid⟩, ⟨⟨certificate_194, certificate_194_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem patterns_10_6_1_verified : ∀ D ∈ patterns_10_6_1, PatternVerified 10 6 D := by

  simp only [patterns_10_6_1, List.forall_mem_cons]

  exact ⟨⟨certificate_195, certificate_195_valid⟩, ⟨⟨certificate_196, certificate_196_valid⟩, ⟨⟨certificate_197, certificate_197_valid⟩, ⟨⟨certificate_198, certificate_198_valid⟩, ⟨⟨certificate_199, certificate_199_valid⟩, ⟨⟨certificate_200, certificate_200_valid⟩, ⟨⟨certificate_201, certificate_201_valid⟩, ⟨⟨certificate_202, certificate_202_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩

theorem patterns_10_6_verified : ∀ D ∈ patterns_10_6, PatternVerified 10 6 D := by

  simp only [patterns_10_6, List.forall_mem_append]

  exact ⟨patterns_10_6_0_verified, ⟨patterns_10_6_1_verified, by simp⟩⟩

theorem patterns_10_6_coverage : patternChoices 6 4 [] = patterns_10_6 := by decide +kernel

theorem finite_patterns_10_6_oai : ∀ D ∈ patternChoices 6 (10-6) [], PatternVerified 10 6 D := by

  rw [patterns_10_6_coverage]

  exact patterns_10_6_verified

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.finite_patterns_10_6_oai := @OAI.CycleClique.finite_patterns_10_6_oai
