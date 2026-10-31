-- Prove2me | solution 1 for OAI.CycleClique.finite_patterns_13_6
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T20:10:20.53899+00:00
-- url     : https://prove2.me/submissions/c33431e6-8c0b-4759-9f1e-ea68da8460f0

import Mathlib
import Definitions.Def_OAIQ107D133
import Theorems.Thm_OAI_CycleClique_patterns_13_6_0_verified
import Theorems.Thm_OAI_CycleClique_patterns_13_6_1_verified
import Theorems.Thm_OAI_CycleClique_patterns_13_6_3_verified

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates018
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_557_checked : certificate_557.Valid 13 6 11 certificate_557_q certificate_557_edges 5 3 [] := by decide +kernel
theorem certificate_557_valid : certificate_557.Valid 13 6 (patternOrder [[],[],[1,2,2]]) (patternClique [[],[],[1,2,2]]) (patternEdges [[],[],[1,2,2]]) (patternAmount [[],[],[1,2,2]]) (patternEdgeCount [[],[],[1,2,2]]) [] := certificate_557_checked

theorem certificate_558_checked : certificate_558.Valid 13 6 12 certificate_558_q certificate_558_edges 6 3 [] := by decide +kernel
theorem certificate_558_valid : certificate_558.Valid 13 6 (patternOrder [[],[],[1,2,3]]) (patternClique [[],[],[1,2,3]]) (patternEdges [[],[],[1,2,3]]) (patternAmount [[],[],[1,2,3]]) (patternEdgeCount [[],[],[1,2,3]]) [] := certificate_558_checked

theorem certificate_559_checked : certificate_559.Valid 13 6 13 certificate_559_q certificate_559_edges 7 3 [] := by decide +kernel
theorem certificate_559_valid : certificate_559.Valid 13 6 (patternOrder [[],[],[1,2,4]]) (patternClique [[],[],[1,2,4]]) (patternEdges [[],[],[1,2,4]]) (patternAmount [[],[],[1,2,4]]) (patternEdgeCount [[],[],[1,2,4]]) [] := certificate_559_checked

theorem certificate_560_checked : certificate_560.Valid 13 6 11 certificate_560_q certificate_560_edges 5 3 [] := by decide +kernel
theorem certificate_560_valid : certificate_560.Valid 13 6 (patternOrder [[],[],[1,3,1]]) (patternClique [[],[],[1,3,1]]) (patternEdges [[],[],[1,3,1]]) (patternAmount [[],[],[1,3,1]]) (patternEdgeCount [[],[],[1,3,1]]) [] := certificate_560_checked

theorem certificate_561_checked : certificate_561.Valid 13 6 12 certificate_561_q certificate_561_edges 6 3 [] := by decide +kernel
theorem certificate_561_valid : certificate_561.Valid 13 6 (patternOrder [[],[],[1,3,2]]) (patternClique [[],[],[1,3,2]]) (patternEdges [[],[],[1,3,2]]) (patternAmount [[],[],[1,3,2]]) (patternEdgeCount [[],[],[1,3,2]]) [] := certificate_561_checked

theorem certificate_562_checked : certificate_562.Valid 13 6 13 certificate_562_q certificate_562_edges 7 3 [] := by decide +kernel
theorem certificate_562_valid : certificate_562.Valid 13 6 (patternOrder [[],[],[1,3,3]]) (patternClique [[],[],[1,3,3]]) (patternEdges [[],[],[1,3,3]]) (patternAmount [[],[],[1,3,3]]) (patternEdgeCount [[],[],[1,3,3]]) [] := certificate_562_checked

theorem certificate_563_checked : certificate_563.Valid 13 6 12 certificate_563_q certificate_563_edges 6 3 [] := by decide +kernel
theorem certificate_563_valid : certificate_563.Valid 13 6 (patternOrder [[],[],[1,4,1]]) (patternClique [[],[],[1,4,1]]) (patternEdges [[],[],[1,4,1]]) (patternAmount [[],[],[1,4,1]]) (patternEdgeCount [[],[],[1,4,1]]) [] := certificate_563_checked

theorem certificate_564_checked : certificate_564.Valid 13 6 13 certificate_564_q certificate_564_edges 7 3 [] := by decide +kernel
theorem certificate_564_valid : certificate_564.Valid 13 6 (patternOrder [[],[],[1,4,2]]) (patternClique [[],[],[1,4,2]]) (patternEdges [[],[],[1,4,2]]) (patternAmount [[],[],[1,4,2]]) (patternEdgeCount [[],[],[1,4,2]]) [] := certificate_564_checked

theorem certificate_565_checked : certificate_565.Valid 13 6 13 certificate_565_q certificate_565_edges 7 3 [] := by decide +kernel
theorem certificate_565_valid : certificate_565.Valid 13 6 (patternOrder [[],[],[1,5,1]]) (patternClique [[],[],[1,5,1]]) (patternEdges [[],[],[1,5,1]]) (patternAmount [[],[],[1,5,1]]) (patternEdgeCount [[],[],[1,5,1]]) [] := certificate_565_checked

theorem certificate_566_checked : certificate_566.Valid 13 6 10 certificate_566_q certificate_566_edges 4 2 [] := by decide +kernel
theorem certificate_566_valid : certificate_566.Valid 13 6 (patternOrder [[],[],[2],[2]]) (patternClique [[],[],[2],[2]]) (patternEdges [[],[],[2],[2]]) (patternAmount [[],[],[2],[2]]) (patternEdgeCount [[],[],[2],[2]]) [] := certificate_566_checked

theorem certificate_567_checked : certificate_567.Valid 13 6 11 certificate_567_q certificate_567_edges 5 2 [] := by decide +kernel
theorem certificate_567_valid : certificate_567.Valid 13 6 (patternOrder [[],[],[2],[3]]) (patternClique [[],[],[2],[3]]) (patternEdges [[],[],[2],[3]]) (patternAmount [[],[],[2],[3]]) (patternEdgeCount [[],[],[2],[3]]) [] := certificate_567_checked

theorem certificate_568_checked : certificate_568.Valid 13 6 12 certificate_568_q certificate_568_edges 6 2 [] := by decide +kernel
theorem certificate_568_valid : certificate_568.Valid 13 6 (patternOrder [[],[],[2],[4]]) (patternClique [[],[],[2],[4]]) (patternEdges [[],[],[2],[4]]) (patternAmount [[],[],[2],[4]]) (patternEdgeCount [[],[],[2],[4]]) [] := certificate_568_checked

theorem certificate_569_part_11_checked : certificate_569_part_11.Valid 13 6 13 certificate_569_q certificate_569_part_11_E 7 2 certificate_569_part_11_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩⟩

theorem certificate_569_part_17_checked : certificate_569_part_17.Valid 13 6 13 certificate_569_q certificate_569_part_17_E 7 2 certificate_569_part_17_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem certificate_569_part_20_checked : certificate_569_part_20.Valid 13 6 14 certificate_569_q certificate_569_part_20_E 7 2 certificate_569_part_20_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem certificate_569_part_21_checked : certificate_569_part_21.Valid 13 6 13 certificate_569_q certificate_569_part_21_E 7 2 certificate_569_part_21_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem certificate_569_part_22_checked : certificate_569_part_22.Valid 13 6 13 certificate_569_q certificate_569_part_22_E 7 2 certificate_569_part_22_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem certificate_569_part_25_checked : certificate_569_part_25.Valid 13 6 13 certificate_569_q certificate_569_part_25_E 7 2 certificate_569_part_25_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩

theorem certificate_569_part_26_checked : certificate_569_part_26.Valid 13 6 13 certificate_569_q certificate_569_part_26_E 7 2 certificate_569_part_26_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩

theorem certificate_569_part_28_checked : certificate_569_part_28.Valid 13 6 13 certificate_569_q certificate_569_part_28_E 7 2 certificate_569_part_28_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩

theorem certificate_569_part_29_checked : certificate_569_part_29.Valid 13 6 13 certificate_569_q certificate_569_part_29_E 7 2 certificate_569_part_29_M := by exact ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩, by decide +kernel⟩⟩⟩

theorem certificate_569_part_27_checked : certificate_569_part_27.Valid 13 6 13 certificate_569_q certificate_569_part_27_E 7 2 certificate_569_part_27_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_569_part_28_checked⟩⟩⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_569_part_29_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_569_part_24_checked : certificate_569_part_24.Valid 13 6 13 certificate_569_q certificate_569_part_24_E 7 2 certificate_569_part_24_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_569_part_25_checked⟩, ⟨by decide +kernel, by decide +kernel, certificate_569_part_26_checked, certificate_569_part_27_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_569_part_23_checked : certificate_569_part_23.Valid 13 6 13 certificate_569_q certificate_569_part_23_E 7 2 certificate_569_part_23_M := by exact ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_569_part_24_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_569_part_19_checked : certificate_569_part_19.Valid 13 6 13 certificate_569_q certificate_569_part_19_E 7 2 certificate_569_part_19_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_569_part_20_checked⟩⟩⟩⟩⟩⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_569_part_21_checked⟩, ⟨by decide +kernel, by decide +kernel, certificate_569_part_22_checked, certificate_569_part_23_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_569_part_18_checked : certificate_569_part_18.Valid 13 6 13 certificate_569_q certificate_569_part_18_E 7 2 certificate_569_part_18_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_569_part_19_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_569_part_16_checked : certificate_569_part_16.Valid 13 6 13 certificate_569_q certificate_569_part_16_E 7 2 certificate_569_part_16_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_569_part_17_checked⟩⟩⟩⟩, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_569_part_18_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_569_part_15_checked : certificate_569_part_15.Valid 13 6 13 certificate_569_q certificate_569_part_15_E 7 2 certificate_569_part_15_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_569_part_16_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_569_part_14_checked : certificate_569_part_14.Valid 13 6 13 certificate_569_q certificate_569_part_14_E 7 2 certificate_569_part_14_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_569_part_15_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_569_part_13_checked : certificate_569_part_13.Valid 13 6 13 certificate_569_q certificate_569_part_13_E 7 2 certificate_569_part_13_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_569_part_14_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_569_part_12_checked : certificate_569_part_12.Valid 13 6 13 certificate_569_q certificate_569_part_12_E 7 2 certificate_569_part_12_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_569_part_13_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_569_part_10_checked : certificate_569_part_10.Valid 13 6 13 certificate_569_q certificate_569_part_10_E 7 2 certificate_569_part_10_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, certificate_569_part_11_checked, certificate_569_part_12_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_569_part_9_checked : certificate_569_part_9.Valid 13 6 13 certificate_569_q certificate_569_part_9_E 7 2 certificate_569_part_9_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_569_part_10_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_569_part_8_checked : certificate_569_part_8.Valid 13 6 13 certificate_569_q certificate_569_part_8_E 7 2 certificate_569_part_8_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_569_part_9_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_569_part_7_checked : certificate_569_part_7.Valid 13 6 13 certificate_569_q certificate_569_part_7_E 7 2 certificate_569_part_7_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_569_part_8_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_569_part_6_checked : certificate_569_part_6.Valid 13 6 13 certificate_569_q certificate_569_part_6_E 7 2 certificate_569_part_6_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_569_part_7_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_569_part_5_checked : certificate_569_part_5.Valid 13 6 13 certificate_569_q certificate_569_part_5_E 7 2 certificate_569_part_5_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_569_part_6_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_569_part_4_checked : certificate_569_part_4.Valid 13 6 13 certificate_569_q certificate_569_part_4_E 7 2 certificate_569_part_4_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_569_part_5_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_569_part_3_checked : certificate_569_part_3.Valid 13 6 13 certificate_569_q certificate_569_part_3_E 7 2 certificate_569_part_3_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_569_part_4_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_569_part_2_checked : certificate_569_part_2.Valid 13 6 13 certificate_569_q certificate_569_part_2_E 7 2 certificate_569_part_2_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_569_part_3_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_569_part_1_checked : certificate_569_part_1.Valid 13 6 13 certificate_569_q certificate_569_part_1_E 7 2 certificate_569_part_1_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_569_part_2_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_569_checked : certificate_569.Valid 13 6 13 certificate_569_q certificate_569_E 7 2 certificate_569_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_569_part_1_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_569_valid : certificate_569.Valid 13 6 (patternOrder [[],[],[2],[5]]) (patternClique [[],[],[2],[5]]) (patternEdges [[],[],[2],[5]]) (patternAmount [[],[],[2],[5]]) (patternEdgeCount [[],[],[2],[5]]) [] := certificate_569_checked

theorem certificate_570_checked : certificate_570.Valid 13 6 11 certificate_570_q certificate_570_edges 5 3 [] := by decide +kernel
theorem certificate_570_valid : certificate_570.Valid 13 6 (patternOrder [[],[],[2,1,2]]) (patternClique [[],[],[2,1,2]]) (patternEdges [[],[],[2,1,2]]) (patternAmount [[],[],[2,1,2]]) (patternEdgeCount [[],[],[2,1,2]]) [] := certificate_570_checked

theorem certificate_571_checked : certificate_571.Valid 13 6 12 certificate_571_q certificate_571_edges 6 3 [] := by decide +kernel
theorem certificate_571_valid : certificate_571.Valid 13 6 (patternOrder [[],[],[2,1,3]]) (patternClique [[],[],[2,1,3]]) (patternEdges [[],[],[2,1,3]]) (patternAmount [[],[],[2,1,3]]) (patternEdgeCount [[],[],[2,1,3]]) [] := certificate_571_checked

theorem certificate_572_checked : certificate_572.Valid 13 6 13 certificate_572_q certificate_572_edges 7 3 [] := by decide +kernel
theorem certificate_572_valid : certificate_572.Valid 13 6 (patternOrder [[],[],[2,1,4]]) (patternClique [[],[],[2,1,4]]) (patternEdges [[],[],[2,1,4]]) (patternAmount [[],[],[2,1,4]]) (patternEdgeCount [[],[],[2,1,4]]) [] := certificate_572_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates019
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_589_checked : certificate_589.Valid 13 6 11 certificate_589_q certificate_589_edges 5 3 [] := by decide +kernel
theorem certificate_589_valid : certificate_589.Valid 13 6 (patternOrder [[],[1,1],[3]]) (patternClique [[],[1,1],[3]]) (patternEdges [[],[1,1],[3]]) (patternAmount [[],[1,1],[3]]) (patternEdgeCount [[],[1,1],[3]]) [] := certificate_589_checked

theorem certificate_590_checked : certificate_590.Valid 13 6 12 certificate_590_q certificate_590_edges 6 3 [] := by decide +kernel
theorem certificate_590_valid : certificate_590.Valid 13 6 (patternOrder [[],[1,1],[4]]) (patternClique [[],[1,1],[4]]) (patternEdges [[],[1,1],[4]]) (patternAmount [[],[1,1],[4]]) (patternEdgeCount [[],[1,1],[4]]) [] := certificate_590_checked

theorem certificate_591_checked : certificate_591.Valid 13 6 13 certificate_591_q certificate_591_edges 7 3 [] := by decide +kernel
theorem certificate_591_valid : certificate_591.Valid 13 6 (patternOrder [[],[1,1],[5]]) (patternClique [[],[1,1],[5]]) (patternEdges [[],[1,1],[5]]) (patternAmount [[],[1,1],[5]]) (patternEdgeCount [[],[1,1],[5]]) [] := certificate_591_checked

theorem certificate_592_checked : certificate_592.Valid 13 6 10 certificate_592_q certificate_592_edges 4 4 [] := by decide +kernel
theorem certificate_592_valid : certificate_592.Valid 13 6 (patternOrder [[],[1,1,1,1]]) (patternClique [[],[1,1,1,1]]) (patternEdges [[],[1,1,1,1]]) (patternAmount [[],[1,1,1,1]]) (patternEdgeCount [[],[1,1,1,1]]) [] := certificate_592_checked

theorem certificate_593_checked : certificate_593.Valid 13 6 11 certificate_593_q certificate_593_edges 5 4 [] := by decide +kernel
theorem certificate_593_valid : certificate_593.Valid 13 6 (patternOrder [[],[1,1,1,2]]) (patternClique [[],[1,1,1,2]]) (patternEdges [[],[1,1,1,2]]) (patternAmount [[],[1,1,1,2]]) (patternEdgeCount [[],[1,1,1,2]]) [] := certificate_593_checked

theorem certificate_594_checked : certificate_594.Valid 13 6 12 certificate_594_q certificate_594_edges 6 4 [] := by decide +kernel
theorem certificate_594_valid : certificate_594.Valid 13 6 (patternOrder [[],[1,1,1,3]]) (patternClique [[],[1,1,1,3]]) (patternEdges [[],[1,1,1,3]]) (patternAmount [[],[1,1,1,3]]) (patternEdgeCount [[],[1,1,1,3]]) [] := certificate_594_checked

theorem certificate_595_checked : certificate_595.Valid 13 6 13 certificate_595_q certificate_595_edges 7 4 [] := by decide +kernel
theorem certificate_595_valid : certificate_595.Valid 13 6 (patternOrder [[],[1,1,1,4]]) (patternClique [[],[1,1,1,4]]) (patternEdges [[],[1,1,1,4]]) (patternAmount [[],[1,1,1,4]]) (patternEdgeCount [[],[1,1,1,4]]) [] := certificate_595_checked

theorem certificate_596_checked : certificate_596.Valid 13 6 11 certificate_596_q certificate_596_edges 5 4 [] := by decide +kernel
theorem certificate_596_valid : certificate_596.Valid 13 6 (patternOrder [[],[1,1,2,1]]) (patternClique [[],[1,1,2,1]]) (patternEdges [[],[1,1,2,1]]) (patternAmount [[],[1,1,2,1]]) (patternEdgeCount [[],[1,1,2,1]]) [] := certificate_596_checked

theorem certificate_597_checked : certificate_597.Valid 13 6 12 certificate_597_q certificate_597_edges 6 4 [] := by decide +kernel
theorem certificate_597_valid : certificate_597.Valid 13 6 (patternOrder [[],[1,1,2,2]]) (patternClique [[],[1,1,2,2]]) (patternEdges [[],[1,1,2,2]]) (patternAmount [[],[1,1,2,2]]) (patternEdgeCount [[],[1,1,2,2]]) [] := certificate_597_checked

theorem certificate_598_checked : certificate_598.Valid 13 6 13 certificate_598_q certificate_598_edges 7 4 [] := by decide +kernel
theorem certificate_598_valid : certificate_598.Valid 13 6 (patternOrder [[],[1,1,2,3]]) (patternClique [[],[1,1,2,3]]) (patternEdges [[],[1,1,2,3]]) (patternAmount [[],[1,1,2,3]]) (patternEdgeCount [[],[1,1,2,3]]) [] := certificate_598_checked

theorem certificate_599_checked : certificate_599.Valid 13 6 12 certificate_599_q certificate_599_edges 6 4 [] := by decide +kernel
theorem certificate_599_valid : certificate_599.Valid 13 6 (patternOrder [[],[1,1,3,1]]) (patternClique [[],[1,1,3,1]]) (patternEdges [[],[1,1,3,1]]) (patternAmount [[],[1,1,3,1]]) (patternEdgeCount [[],[1,1,3,1]]) [] := certificate_599_checked

theorem certificate_600_checked : certificate_600.Valid 13 6 13 certificate_600_q certificate_600_edges 7 4 [] := by decide +kernel
theorem certificate_600_valid : certificate_600.Valid 13 6 (patternOrder [[],[1,1,3,2]]) (patternClique [[],[1,1,3,2]]) (patternEdges [[],[1,1,3,2]]) (patternAmount [[],[1,1,3,2]]) (patternEdgeCount [[],[1,1,3,2]]) [] := certificate_600_checked

theorem certificate_601_checked : certificate_601.Valid 13 6 13 certificate_601_q certificate_601_edges 7 4 [] := by decide +kernel
theorem certificate_601_valid : certificate_601.Valid 13 6 (patternOrder [[],[1,1,4,1]]) (patternClique [[],[1,1,4,1]]) (patternEdges [[],[1,1,4,1]]) (patternAmount [[],[1,1,4,1]]) (patternEdgeCount [[],[1,1,4,1]]) [] := certificate_601_checked

theorem certificate_602_checked : certificate_602.Valid 13 6 11 certificate_602_q certificate_602_edges 5 3 [] := by decide +kernel
theorem certificate_602_valid : certificate_602.Valid 13 6 (patternOrder [[],[1,2],[2]]) (patternClique [[],[1,2],[2]]) (patternEdges [[],[1,2],[2]]) (patternAmount [[],[1,2],[2]]) (patternEdgeCount [[],[1,2],[2]]) [] := certificate_602_checked

theorem certificate_603_checked : certificate_603.Valid 13 6 12 certificate_603_q certificate_603_edges 6 3 [] := by decide +kernel
theorem certificate_603_valid : certificate_603.Valid 13 6 (patternOrder [[],[1,2],[3]]) (patternClique [[],[1,2],[3]]) (patternEdges [[],[1,2],[3]]) (patternAmount [[],[1,2],[3]]) (patternEdgeCount [[],[1,2],[3]]) [] := certificate_603_checked

theorem certificate_604_checked : certificate_604.Valid 13 6 13 certificate_604_q certificate_604_edges 7 3 [] := by decide +kernel
theorem certificate_604_valid : certificate_604.Valid 13 6 (patternOrder [[],[1,2],[4]]) (patternClique [[],[1,2],[4]]) (patternEdges [[],[1,2],[4]]) (patternAmount [[],[1,2],[4]]) (patternEdgeCount [[],[1,2],[4]]) [] := certificate_604_checked

theorem certificate_605_checked : certificate_605.Valid 13 6 12 certificate_605_q certificate_605_edges 6 4 [] := by decide +kernel
theorem certificate_605_valid : certificate_605.Valid 13 6 (patternOrder [[],[1,2,1,2]]) (patternClique [[],[1,2,1,2]]) (patternEdges [[],[1,2,1,2]]) (patternAmount [[],[1,2,1,2]]) (patternEdgeCount [[],[1,2,1,2]]) [] := certificate_605_checked

theorem certificate_606_checked : certificate_606.Valid 13 6 13 certificate_606_q certificate_606_edges 7 4 [] := by decide +kernel
theorem certificate_606_valid : certificate_606.Valid 13 6 (patternOrder [[],[1,2,1,3]]) (patternClique [[],[1,2,1,3]]) (patternEdges [[],[1,2,1,3]]) (patternAmount [[],[1,2,1,3]]) (patternEdgeCount [[],[1,2,1,3]]) [] := certificate_606_checked

theorem certificate_607_checked : certificate_607.Valid 13 6 12 certificate_607_q certificate_607_edges 6 4 [] := by decide +kernel
theorem certificate_607_valid : certificate_607.Valid 13 6 (patternOrder [[],[1,2,2,1]]) (patternClique [[],[1,2,2,1]]) (patternEdges [[],[1,2,2,1]]) (patternAmount [[],[1,2,2,1]]) (patternEdgeCount [[],[1,2,2,1]]) [] := certificate_607_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates020
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_608_checked : certificate_608.Valid 13 6 13 certificate_608_q certificate_608_edges 7 4 [] := by decide +kernel
theorem certificate_608_valid : certificate_608.Valid 13 6 (patternOrder [[],[1,2,2,2]]) (patternClique [[],[1,2,2,2]]) (patternEdges [[],[1,2,2,2]]) (patternAmount [[],[1,2,2,2]]) (patternEdgeCount [[],[1,2,2,2]]) [] := certificate_608_checked

theorem certificate_609_checked : certificate_609.Valid 13 6 13 certificate_609_q certificate_609_edges 7 4 [] := by decide +kernel
theorem certificate_609_valid : certificate_609.Valid 13 6 (patternOrder [[],[1,2,3,1]]) (patternClique [[],[1,2,3,1]]) (patternEdges [[],[1,2,3,1]]) (patternAmount [[],[1,2,3,1]]) (patternEdgeCount [[],[1,2,3,1]]) [] := certificate_609_checked

theorem certificate_610_checked : certificate_610.Valid 13 6 12 certificate_610_q certificate_610_edges 6 3 [] := by decide +kernel
theorem certificate_610_valid : certificate_610.Valid 13 6 (patternOrder [[],[1,3],[2]]) (patternClique [[],[1,3],[2]]) (patternEdges [[],[1,3],[2]]) (patternAmount [[],[1,3],[2]]) (patternEdgeCount [[],[1,3],[2]]) [] := certificate_610_checked

theorem certificate_611_checked : certificate_611.Valid 13 6 13 certificate_611_q certificate_611_edges 7 3 [] := by decide +kernel
theorem certificate_611_valid : certificate_611.Valid 13 6 (patternOrder [[],[1,3],[3]]) (patternClique [[],[1,3],[3]]) (patternEdges [[],[1,3],[3]]) (patternAmount [[],[1,3],[3]]) (patternEdgeCount [[],[1,3],[3]]) [] := certificate_611_checked

theorem certificate_612_checked : certificate_612.Valid 13 6 13 certificate_612_q certificate_612_edges 7 4 [] := by decide +kernel
theorem certificate_612_valid : certificate_612.Valid 13 6 (patternOrder [[],[1,3,1,2]]) (patternClique [[],[1,3,1,2]]) (patternEdges [[],[1,3,1,2]]) (patternAmount [[],[1,3,1,2]]) (patternEdgeCount [[],[1,3,1,2]]) [] := certificate_612_checked

theorem certificate_613_checked : certificate_613.Valid 13 6 13 certificate_613_q certificate_613_edges 7 3 [] := by decide +kernel
theorem certificate_613_valid : certificate_613.Valid 13 6 (patternOrder [[],[1,4],[2]]) (patternClique [[],[1,4],[2]]) (patternEdges [[],[1,4],[2]]) (patternAmount [[],[1,4],[2]]) (patternEdgeCount [[],[1,4],[2]]) [] := certificate_613_checked

theorem certificate_614_checked : certificate_614.Valid 13 6 12 certificate_614_q certificate_614_edges 6 3 [] := by decide +kernel
theorem certificate_614_valid : certificate_614.Valid 13 6 (patternOrder [[],[2],[2,2]]) (patternClique [[],[2],[2,2]]) (patternEdges [[],[2],[2,2]]) (patternAmount [[],[2],[2,2]]) (patternEdgeCount [[],[2],[2,2]]) [] := certificate_614_checked

theorem certificate_615_checked : certificate_615.Valid 13 6 13 certificate_615_q certificate_615_edges 7 3 [] := by decide +kernel
theorem certificate_615_valid : certificate_615.Valid 13 6 (patternOrder [[],[2],[2,3]]) (patternClique [[],[2],[2,3]]) (patternEdges [[],[2],[2,3]]) (patternAmount [[],[2],[2,3]]) (patternEdgeCount [[],[2],[2,3]]) [] := certificate_615_checked

theorem certificate_616_checked : certificate_616.Valid 13 6 12 certificate_616_q certificate_616_edges 6 4 [] := by decide +kernel
theorem certificate_616_valid : certificate_616.Valid 13 6 (patternOrder [[],[2,1,1,2]]) (patternClique [[],[2,1,1,2]]) (patternEdges [[],[2,1,1,2]]) (patternAmount [[],[2,1,1,2]]) (patternEdgeCount [[],[2,1,1,2]]) [] := certificate_616_checked

theorem certificate_617_checked : certificate_617.Valid 13 6 13 certificate_617_q certificate_617_edges 7 4 [] := by decide +kernel
theorem certificate_617_valid : certificate_617.Valid 13 6 (patternOrder [[],[2,1,1,3]]) (patternClique [[],[2,1,1,3]]) (patternEdges [[],[2,1,1,3]]) (patternAmount [[],[2,1,1,3]]) (patternEdgeCount [[],[2,1,1,3]]) [] := certificate_617_checked

theorem certificate_618_checked : certificate_618.Valid 13 6 13 certificate_618_q certificate_618_edges 7 4 [] := by decide +kernel
theorem certificate_618_valid : certificate_618.Valid 13 6 (patternOrder [[],[2,1,2,2]]) (patternClique [[],[2,1,2,2]]) (patternEdges [[],[2,1,2,2]]) (patternAmount [[],[2,1,2,2]]) (patternEdgeCount [[],[2,1,2,2]]) [] := certificate_618_checked

theorem certificate_619_checked : certificate_619.Valid 13 6 13 certificate_619_q certificate_619_edges 7 3 [] := by decide +kernel
theorem certificate_619_valid : certificate_619.Valid 13 6 (patternOrder [[],[2,2],[3]]) (patternClique [[],[2,2],[3]]) (patternEdges [[],[2,2],[3]]) (patternAmount [[],[2,2],[3]]) (patternEdgeCount [[],[2,2],[3]]) [] := certificate_619_checked

theorem certificate_620_checked : certificate_620.Valid 13 6 9 certificate_620_q certificate_620_edges 3 3 [] := by decide +kernel
theorem certificate_620_valid : certificate_620.Valid 13 6 (patternOrder [[1],[1],[1]]) (patternClique [[1],[1],[1]]) (patternEdges [[1],[1],[1]]) (patternAmount [[1],[1],[1]]) (patternEdgeCount [[1],[1],[1]]) [] := certificate_620_checked

theorem certificate_621_checked : certificate_621.Valid 13 6 10 certificate_621_q certificate_621_edges 4 3 [] := by decide +kernel
theorem certificate_621_valid : certificate_621.Valid 13 6 (patternOrder [[1],[1],[2]]) (patternClique [[1],[1],[2]]) (patternEdges [[1],[1],[2]]) (patternAmount [[1],[1],[2]]) (patternEdgeCount [[1],[1],[2]]) [] := certificate_621_checked

theorem certificate_622_checked : certificate_622.Valid 13 6 11 certificate_622_q certificate_622_edges 5 3 [] := by decide +kernel
theorem certificate_622_valid : certificate_622.Valid 13 6 (patternOrder [[1],[1],[3]]) (patternClique [[1],[1],[3]]) (patternEdges [[1],[1],[3]]) (patternAmount [[1],[1],[3]]) (patternEdgeCount [[1],[1],[3]]) [] := certificate_622_checked

theorem certificate_623_checked : certificate_623.Valid 13 6 12 certificate_623_q certificate_623_edges 6 3 [] := by decide +kernel
theorem certificate_623_valid : certificate_623.Valid 13 6 (patternOrder [[1],[1],[4]]) (patternClique [[1],[1],[4]]) (patternEdges [[1],[1],[4]]) (patternAmount [[1],[1],[4]]) (patternEdgeCount [[1],[1],[4]]) [] := certificate_623_checked

theorem certificate_624_checked : certificate_624.Valid 13 6 13 certificate_624_q certificate_624_edges 7 3 [] := by decide +kernel
theorem certificate_624_valid : certificate_624.Valid 13 6 (patternOrder [[1],[1],[5]]) (patternClique [[1],[1],[5]]) (patternEdges [[1],[1],[5]]) (patternAmount [[1],[1],[5]]) (patternEdgeCount [[1],[1],[5]]) [] := certificate_624_checked

theorem certificate_625_checked : certificate_625.Valid 13 6 10 certificate_625_q certificate_625_edges 4 4 [] := by decide +kernel
theorem certificate_625_valid : certificate_625.Valid 13 6 (patternOrder [[1],[1,1,1]]) (patternClique [[1],[1,1,1]]) (patternEdges [[1],[1,1,1]]) (patternAmount [[1],[1,1,1]]) (patternEdgeCount [[1],[1,1,1]]) [] := certificate_625_checked

theorem certificate_626_checked : certificate_626.Valid 13 6 11 certificate_626_q certificate_626_edges 5 4 [] := by decide +kernel
theorem certificate_626_valid : certificate_626.Valid 13 6 (patternOrder [[1],[1,1,2]]) (patternClique [[1],[1,1,2]]) (patternEdges [[1],[1,1,2]]) (patternAmount [[1],[1,1,2]]) (patternEdgeCount [[1],[1,1,2]]) [] := certificate_626_checked

theorem certificate_627_checked : certificate_627.Valid 13 6 12 certificate_627_q certificate_627_edges 6 4 [] := by decide +kernel
theorem certificate_627_valid : certificate_627.Valid 13 6 (patternOrder [[1],[1,1,3]]) (patternClique [[1],[1,1,3]]) (patternEdges [[1],[1,1,3]]) (patternAmount [[1],[1,1,3]]) (patternEdgeCount [[1],[1,1,3]]) [] := certificate_627_checked

theorem certificate_628_checked : certificate_628.Valid 13 6 13 certificate_628_q certificate_628_edges 7 4 [] := by decide +kernel
theorem certificate_628_valid : certificate_628.Valid 13 6 (patternOrder [[1],[1,1,4]]) (patternClique [[1],[1,1,4]]) (patternEdges [[1],[1,1,4]]) (patternAmount [[1],[1,1,4]]) (patternEdgeCount [[1],[1,1,4]]) [] := certificate_628_checked

theorem certificate_629_checked : certificate_629.Valid 13 6 11 certificate_629_q certificate_629_edges 5 4 [] := by decide +kernel
theorem certificate_629_valid : certificate_629.Valid 13 6 (patternOrder [[1],[1,2,1]]) (patternClique [[1],[1,2,1]]) (patternEdges [[1],[1,2,1]]) (patternAmount [[1],[1,2,1]]) (patternEdgeCount [[1],[1,2,1]]) [] := certificate_629_checked

theorem certificate_630_checked : certificate_630.Valid 13 6 12 certificate_630_q certificate_630_edges 6 4 [] := by decide +kernel
theorem certificate_630_valid : certificate_630.Valid 13 6 (patternOrder [[1],[1,2,2]]) (patternClique [[1],[1,2,2]]) (patternEdges [[1],[1,2,2]]) (patternAmount [[1],[1,2,2]]) (patternEdgeCount [[1],[1,2,2]]) [] := certificate_630_checked

theorem certificate_631_checked : certificate_631.Valid 13 6 13 certificate_631_q certificate_631_edges 7 4 [] := by decide +kernel
theorem certificate_631_valid : certificate_631.Valid 13 6 (patternOrder [[1],[1,2,3]]) (patternClique [[1],[1,2,3]]) (patternEdges [[1],[1,2,3]]) (patternAmount [[1],[1,2,3]]) (patternEdgeCount [[1],[1,2,3]]) [] := certificate_631_checked

theorem certificate_632_checked : certificate_632.Valid 13 6 12 certificate_632_q certificate_632_edges 6 4 [] := by decide +kernel
theorem certificate_632_valid : certificate_632.Valid 13 6 (patternOrder [[1],[1,3,1]]) (patternClique [[1],[1,3,1]]) (patternEdges [[1],[1,3,1]]) (patternAmount [[1],[1,3,1]]) (patternEdgeCount [[1],[1,3,1]]) [] := certificate_632_checked

theorem certificate_633_checked : certificate_633.Valid 13 6 13 certificate_633_q certificate_633_edges 7 4 [] := by decide +kernel
theorem certificate_633_valid : certificate_633.Valid 13 6 (patternOrder [[1],[1,3,2]]) (patternClique [[1],[1,3,2]]) (patternEdges [[1],[1,3,2]]) (patternAmount [[1],[1,3,2]]) (patternEdgeCount [[1],[1,3,2]]) [] := certificate_633_checked

theorem certificate_634_checked : certificate_634.Valid 13 6 13 certificate_634_q certificate_634_edges 7 4 [] := by decide +kernel
theorem certificate_634_valid : certificate_634.Valid 13 6 (patternOrder [[1],[1,4,1]]) (patternClique [[1],[1,4,1]]) (patternEdges [[1],[1,4,1]]) (patternAmount [[1],[1,4,1]]) (patternEdgeCount [[1],[1,4,1]]) [] := certificate_634_checked

theorem certificate_635_checked : certificate_635.Valid 13 6 11 certificate_635_q certificate_635_edges 5 3 [] := by decide +kernel
theorem certificate_635_valid : certificate_635.Valid 13 6 (patternOrder [[1],[2],[2]]) (patternClique [[1],[2],[2]]) (patternEdges [[1],[2],[2]]) (patternAmount [[1],[2],[2]]) (patternEdgeCount [[1],[2],[2]]) [] := certificate_635_checked

theorem certificate_636_checked : certificate_636.Valid 13 6 12 certificate_636_q certificate_636_edges 6 3 [] := by decide +kernel
theorem certificate_636_valid : certificate_636.Valid 13 6 (patternOrder [[1],[2],[3]]) (patternClique [[1],[2],[3]]) (patternEdges [[1],[2],[3]]) (patternAmount [[1],[2],[3]]) (patternEdgeCount [[1],[2],[3]]) [] := certificate_636_checked

theorem certificate_637_checked : certificate_637.Valid 13 6 13 certificate_637_q certificate_637_edges 7 3 [] := by decide +kernel
theorem certificate_637_valid : certificate_637.Valid 13 6 (patternOrder [[1],[2],[4]]) (patternClique [[1],[2],[4]]) (patternEdges [[1],[2],[4]]) (patternAmount [[1],[2],[4]]) (patternEdgeCount [[1],[2],[4]]) [] := certificate_637_checked

theorem certificate_638_checked : certificate_638.Valid 13 6 12 certificate_638_q certificate_638_edges 6 4 [] := by decide +kernel
theorem certificate_638_valid : certificate_638.Valid 13 6 (patternOrder [[1],[2,1,2]]) (patternClique [[1],[2,1,2]]) (patternEdges [[1],[2,1,2]]) (patternAmount [[1],[2,1,2]]) (patternEdgeCount [[1],[2,1,2]]) [] := certificate_638_checked

theorem certificate_639_checked : certificate_639.Valid 13 6 13 certificate_639_q certificate_639_edges 7 4 [] := by decide +kernel
theorem certificate_639_valid : certificate_639.Valid 13 6 (patternOrder [[1],[2,1,3]]) (patternClique [[1],[2,1,3]]) (patternEdges [[1],[2,1,3]]) (patternAmount [[1],[2,1,3]]) (patternEdgeCount [[1],[2,1,3]]) [] := certificate_639_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates021
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_640_checked : certificate_640.Valid 13 6 13 certificate_640_q certificate_640_edges 7 4 [] := by decide +kernel
theorem certificate_640_valid : certificate_640.Valid 13 6 (patternOrder [[1],[2,2,2]]) (patternClique [[1],[2,2,2]]) (patternEdges [[1],[2,2,2]]) (patternAmount [[1],[2,2,2]]) (patternEdgeCount [[1],[2,2,2]]) [] := certificate_640_checked

theorem certificate_641_checked : certificate_641.Valid 13 6 13 certificate_641_q certificate_641_edges 7 3 [] := by decide +kernel
theorem certificate_641_valid : certificate_641.Valid 13 6 (patternOrder [[1],[3],[3]]) (patternClique [[1],[3],[3]]) (patternEdges [[1],[3],[3]]) (patternAmount [[1],[3],[3]]) (patternEdgeCount [[1],[3],[3]]) [] := certificate_641_checked

theorem certificate_642_checked : certificate_642.Valid 13 6 10 certificate_642_q certificate_642_edges 4 4 [] := by decide +kernel
theorem certificate_642_valid : certificate_642.Valid 13 6 (patternOrder [[1,1],[1,1]]) (patternClique [[1,1],[1,1]]) (patternEdges [[1,1],[1,1]]) (patternAmount [[1,1],[1,1]]) (patternEdgeCount [[1,1],[1,1]]) [] := certificate_642_checked

theorem certificate_643_checked : certificate_643.Valid 13 6 11 certificate_643_q certificate_643_edges 5 4 [] := by decide +kernel
theorem certificate_643_valid : certificate_643.Valid 13 6 (patternOrder [[1,1],[1,2]]) (patternClique [[1,1],[1,2]]) (patternEdges [[1,1],[1,2]]) (patternAmount [[1,1],[1,2]]) (patternEdgeCount [[1,1],[1,2]]) [] := certificate_643_checked

theorem certificate_644_checked : certificate_644.Valid 13 6 12 certificate_644_q certificate_644_edges 6 4 [] := by decide +kernel
theorem certificate_644_valid : certificate_644.Valid 13 6 (patternOrder [[1,1],[1,3]]) (patternClique [[1,1],[1,3]]) (patternEdges [[1,1],[1,3]]) (patternAmount [[1,1],[1,3]]) (patternEdgeCount [[1,1],[1,3]]) [] := certificate_644_checked

theorem certificate_645_checked : certificate_645.Valid 13 6 13 certificate_645_q certificate_645_edges 7 4 [] := by decide +kernel
theorem certificate_645_valid : certificate_645.Valid 13 6 (patternOrder [[1,1],[1,4]]) (patternClique [[1,1],[1,4]]) (patternEdges [[1,1],[1,4]]) (patternAmount [[1,1],[1,4]]) (patternEdgeCount [[1,1],[1,4]]) [] := certificate_645_checked

theorem certificate_646_checked : certificate_646.Valid 13 6 12 certificate_646_q certificate_646_edges 6 4 [] := by decide +kernel
theorem certificate_646_valid : certificate_646.Valid 13 6 (patternOrder [[1,1],[2,2]]) (patternClique [[1,1],[2,2]]) (patternEdges [[1,1],[2,2]]) (patternAmount [[1,1],[2,2]]) (patternEdgeCount [[1,1],[2,2]]) [] := certificate_646_checked

theorem certificate_647_checked : certificate_647.Valid 13 6 13 certificate_647_q certificate_647_edges 7 4 [] := by decide +kernel
theorem certificate_647_valid : certificate_647.Valid 13 6 (patternOrder [[1,1],[2,3]]) (patternClique [[1,1],[2,3]]) (patternEdges [[1,1],[2,3]]) (patternAmount [[1,1],[2,3]]) (patternEdgeCount [[1,1],[2,3]]) [] := certificate_647_checked

theorem certificate_648_checked : certificate_648.Valid 13 6 11 certificate_648_q certificate_648_edges 5 4 [] := by decide +kernel
theorem certificate_648_valid : certificate_648.Valid 13 6 (patternOrder [[1,1,1],[2]]) (patternClique [[1,1,1],[2]]) (patternEdges [[1,1,1],[2]]) (patternAmount [[1,1,1],[2]]) (patternEdgeCount [[1,1,1],[2]]) [] := certificate_648_checked

theorem certificate_649_checked : certificate_649.Valid 13 6 12 certificate_649_q certificate_649_edges 6 4 [] := by decide +kernel
theorem certificate_649_valid : certificate_649.Valid 13 6 (patternOrder [[1,1,1],[3]]) (patternClique [[1,1,1],[3]]) (patternEdges [[1,1,1],[3]]) (patternAmount [[1,1,1],[3]]) (patternEdgeCount [[1,1,1],[3]]) [] := certificate_649_checked

theorem certificate_650_checked : certificate_650.Valid 13 6 13 certificate_650_q certificate_650_edges 7 4 [] := by decide +kernel
theorem certificate_650_valid : certificate_650.Valid 13 6 (patternOrder [[1,1,1],[4]]) (patternClique [[1,1,1],[4]]) (patternEdges [[1,1,1],[4]]) (patternAmount [[1,1,1],[4]]) (patternEdgeCount [[1,1,1],[4]]) [] := certificate_650_checked

theorem certificate_651_checked : certificate_651.Valid 13 6 11 certificate_651_q certificate_651_edges 5 5 [] := by decide +kernel
theorem certificate_651_valid : certificate_651.Valid 13 6 (patternOrder [[1,1,1,1,1]]) (patternClique [[1,1,1,1,1]]) (patternEdges [[1,1,1,1,1]]) (patternAmount [[1,1,1,1,1]]) (patternEdgeCount [[1,1,1,1,1]]) [] := certificate_651_checked

theorem certificate_652_checked : certificate_652.Valid 13 6 12 certificate_652_q certificate_652_edges 6 5 [] := by decide +kernel
theorem certificate_652_valid : certificate_652.Valid 13 6 (patternOrder [[1,1,1,1,2]]) (patternClique [[1,1,1,1,2]]) (patternEdges [[1,1,1,1,2]]) (patternAmount [[1,1,1,1,2]]) (patternEdgeCount [[1,1,1,1,2]]) [] := certificate_652_checked

theorem certificate_653_checked : certificate_653.Valid 13 6 13 certificate_653_q certificate_653_edges 7 5 [] := by decide +kernel
theorem certificate_653_valid : certificate_653.Valid 13 6 (patternOrder [[1,1,1,1,3]]) (patternClique [[1,1,1,1,3]]) (patternEdges [[1,1,1,1,3]]) (patternAmount [[1,1,1,1,3]]) (patternEdgeCount [[1,1,1,1,3]]) [] := certificate_653_checked

theorem certificate_654_checked : certificate_654.Valid 13 6 12 certificate_654_q certificate_654_edges 6 5 [] := by decide +kernel
theorem certificate_654_valid : certificate_654.Valid 13 6 (patternOrder [[1,1,1,2,1]]) (patternClique [[1,1,1,2,1]]) (patternEdges [[1,1,1,2,1]]) (patternAmount [[1,1,1,2,1]]) (patternEdgeCount [[1,1,1,2,1]]) [] := certificate_654_checked

theorem certificate_655_checked : certificate_655.Valid 13 6 13 certificate_655_q certificate_655_edges 7 5 [] := by decide +kernel
theorem certificate_655_valid : certificate_655.Valid 13 6 (patternOrder [[1,1,1,2,2]]) (patternClique [[1,1,1,2,2]]) (patternEdges [[1,1,1,2,2]]) (patternAmount [[1,1,1,2,2]]) (patternEdgeCount [[1,1,1,2,2]]) [] := certificate_655_checked

theorem certificate_656_checked : certificate_656.Valid 13 6 13 certificate_656_q certificate_656_edges 7 5 [] := by decide +kernel
theorem certificate_656_valid : certificate_656.Valid 13 6 (patternOrder [[1,1,1,3,1]]) (patternClique [[1,1,1,3,1]]) (patternEdges [[1,1,1,3,1]]) (patternAmount [[1,1,1,3,1]]) (patternEdgeCount [[1,1,1,3,1]]) [] := certificate_656_checked

theorem certificate_657_checked : certificate_657.Valid 13 6 12 certificate_657_q certificate_657_edges 6 4 [] := by decide +kernel
theorem certificate_657_valid : certificate_657.Valid 13 6 (patternOrder [[1,1,2],[2]]) (patternClique [[1,1,2],[2]]) (patternEdges [[1,1,2],[2]]) (patternAmount [[1,1,2],[2]]) (patternEdgeCount [[1,1,2],[2]]) [] := certificate_657_checked

theorem certificate_658_checked : certificate_658.Valid 13 6 13 certificate_658_q certificate_658_edges 7 4 [] := by decide +kernel
theorem certificate_658_valid : certificate_658.Valid 13 6 (patternOrder [[1,1,2],[3]]) (patternClique [[1,1,2],[3]]) (patternEdges [[1,1,2],[3]]) (patternAmount [[1,1,2],[3]]) (patternEdgeCount [[1,1,2],[3]]) [] := certificate_658_checked

theorem certificate_659_checked : certificate_659.Valid 13 6 12 certificate_659_q certificate_659_edges 6 5 [] := by decide +kernel
theorem certificate_659_valid : certificate_659.Valid 13 6 (patternOrder [[1,1,2,1,1]]) (patternClique [[1,1,2,1,1]]) (patternEdges [[1,1,2,1,1]]) (patternAmount [[1,1,2,1,1]]) (patternEdgeCount [[1,1,2,1,1]]) [] := certificate_659_checked

theorem certificate_660_checked : certificate_660.Valid 13 6 13 certificate_660_q certificate_660_edges 7 5 [] := by decide +kernel
theorem certificate_660_valid : certificate_660.Valid 13 6 (patternOrder [[1,1,2,1,2]]) (patternClique [[1,1,2,1,2]]) (patternEdges [[1,1,2,1,2]]) (patternAmount [[1,1,2,1,2]]) (patternEdgeCount [[1,1,2,1,2]]) [] := certificate_660_checked

theorem certificate_661_checked : certificate_661.Valid 13 6 13 certificate_661_q certificate_661_edges 7 5 [] := by decide +kernel
theorem certificate_661_valid : certificate_661.Valid 13 6 (patternOrder [[1,1,2,2,1]]) (patternClique [[1,1,2,2,1]]) (patternEdges [[1,1,2,2,1]]) (patternAmount [[1,1,2,2,1]]) (patternEdgeCount [[1,1,2,2,1]]) [] := certificate_661_checked

theorem certificate_662_checked : certificate_662.Valid 13 6 13 certificate_662_q certificate_662_edges 7 4 [] := by decide +kernel
theorem certificate_662_valid : certificate_662.Valid 13 6 (patternOrder [[1,1,3],[2]]) (patternClique [[1,1,3],[2]]) (patternEdges [[1,1,3],[2]]) (patternAmount [[1,1,3],[2]]) (patternEdgeCount [[1,1,3],[2]]) [] := certificate_662_checked

theorem certificate_663_checked : certificate_663.Valid 13 6 13 certificate_663_q certificate_663_edges 7 5 [] := by decide +kernel
theorem certificate_663_valid : certificate_663.Valid 13 6 (patternOrder [[1,1,3,1,1]]) (patternClique [[1,1,3,1,1]]) (patternEdges [[1,1,3,1,1]]) (patternAmount [[1,1,3,1,1]]) (patternEdgeCount [[1,1,3,1,1]]) [] := certificate_663_checked

theorem certificate_664_checked : certificate_664.Valid 13 6 12 certificate_664_q certificate_664_edges 6 4 [] := by decide +kernel
theorem certificate_664_valid : certificate_664.Valid 13 6 (patternOrder [[1,2],[1,2]]) (patternClique [[1,2],[1,2]]) (patternEdges [[1,2],[1,2]]) (patternAmount [[1,2],[1,2]]) (patternEdgeCount [[1,2],[1,2]]) [] := certificate_664_checked

theorem certificate_665_checked : certificate_665.Valid 13 6 13 certificate_665_q certificate_665_edges 7 4 [] := by decide +kernel
theorem certificate_665_valid : certificate_665.Valid 13 6 (patternOrder [[1,2],[1,3]]) (patternClique [[1,2],[1,3]]) (patternEdges [[1,2],[1,3]]) (patternAmount [[1,2],[1,3]]) (patternEdgeCount [[1,2],[1,3]]) [] := certificate_665_checked

theorem certificate_666_checked : certificate_666.Valid 13 6 13 certificate_666_q certificate_666_edges 7 4 [] := by decide +kernel
theorem certificate_666_valid : certificate_666.Valid 13 6 (patternOrder [[1,2],[2,2]]) (patternClique [[1,2],[2,2]]) (patternEdges [[1,2],[2,2]]) (patternAmount [[1,2],[2,2]]) (patternEdgeCount [[1,2],[2,2]]) [] := certificate_666_checked

theorem certificate_667_checked : certificate_667.Valid 13 6 12 certificate_667_q certificate_667_edges 6 4 [] := by decide +kernel
theorem certificate_667_valid : certificate_667.Valid 13 6 (patternOrder [[1,2,1],[2]]) (patternClique [[1,2,1],[2]]) (patternEdges [[1,2,1],[2]]) (patternAmount [[1,2,1],[2]]) (patternEdgeCount [[1,2,1],[2]]) [] := certificate_667_checked

theorem certificate_668_checked : certificate_668.Valid 13 6 13 certificate_668_q certificate_668_edges 7 4 [] := by decide +kernel
theorem certificate_668_valid : certificate_668.Valid 13 6 (patternOrder [[1,2,1],[3]]) (patternClique [[1,2,1],[3]]) (patternEdges [[1,2,1],[3]]) (patternAmount [[1,2,1],[3]]) (patternEdgeCount [[1,2,1],[3]]) [] := certificate_668_checked

theorem certificate_669_checked : certificate_669.Valid 13 6 13 certificate_669_q certificate_669_edges 7 5 [] := by decide +kernel
theorem certificate_669_valid : certificate_669.Valid 13 6 (patternOrder [[1,2,1,1,2]]) (patternClique [[1,2,1,1,2]]) (patternEdges [[1,2,1,1,2]]) (patternAmount [[1,2,1,1,2]]) (patternEdgeCount [[1,2,1,1,2]]) [] := certificate_669_checked

theorem certificate_670_checked : certificate_670.Valid 13 6 13 certificate_670_q certificate_670_edges 7 5 [] := by decide +kernel
theorem certificate_670_valid : certificate_670.Valid 13 6 (patternOrder [[1,2,1,2,1]]) (patternClique [[1,2,1,2,1]]) (patternEdges [[1,2,1,2,1]]) (patternAmount [[1,2,1,2,1]]) (patternEdgeCount [[1,2,1,2,1]]) [] := certificate_670_checked

theorem certificate_671_checked : certificate_671.Valid 13 6 13 certificate_671_q certificate_671_edges 7 4 [] := by decide +kernel
theorem certificate_671_valid : certificate_671.Valid 13 6 (patternOrder [[1,2,2],[2]]) (patternClique [[1,2,2],[2]]) (patternEdges [[1,2,2],[2]]) (patternAmount [[1,2,2],[2]]) (patternEdgeCount [[1,2,2],[2]]) [] := certificate_671_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates022
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_672_checked : certificate_672.Valid 13 6 13 certificate_672_q certificate_672_edges 7 4 [] := by decide +kernel
theorem certificate_672_valid : certificate_672.Valid 13 6 (patternOrder [[1,3,1],[2]]) (patternClique [[1,3,1],[2]]) (patternEdges [[1,3,1],[2]]) (patternAmount [[1,3,1],[2]]) (patternEdgeCount [[1,3,1],[2]]) [] := certificate_672_checked

theorem certificate_673_checked : certificate_673.Valid 13 6 12 certificate_673_q certificate_673_edges 6 3 [] := by decide +kernel
theorem certificate_673_valid : certificate_673.Valid 13 6 (patternOrder [[2],[2],[2]]) (patternClique [[2],[2],[2]]) (patternEdges [[2],[2],[2]]) (patternAmount [[2],[2],[2]]) (patternEdgeCount [[2],[2],[2]]) [] := certificate_673_checked

theorem certificate_674_checked : certificate_674.Valid 13 6 13 certificate_674_q certificate_674_edges 7 3 [] := by decide +kernel
theorem certificate_674_valid : certificate_674.Valid 13 6 (patternOrder [[2],[2],[3]]) (patternClique [[2],[2],[3]]) (patternEdges [[2],[2],[3]]) (patternAmount [[2],[2],[3]]) (patternEdgeCount [[2],[2],[3]]) [] := certificate_674_checked

theorem certificate_675_checked : certificate_675.Valid 13 6 13 certificate_675_q certificate_675_edges 7 4 [] := by decide +kernel
theorem certificate_675_valid : certificate_675.Valid 13 6 (patternOrder [[2],[2,1,2]]) (patternClique [[2],[2,1,2]]) (patternEdges [[2],[2,1,2]]) (patternAmount [[2],[2,1,2]]) (patternEdgeCount [[2],[2,1,2]]) [] := certificate_675_checked

theorem certificate_676_checked : certificate_676.Valid 13 6 13 certificate_676_q certificate_676_edges 7 5 [] := by decide +kernel
theorem certificate_676_valid : certificate_676.Valid 13 6 (patternOrder [[2,1,1,1,2]]) (patternClique [[2,1,1,1,2]]) (patternEdges [[2,1,1,1,2]]) (patternAmount [[2,1,1,1,2]]) (patternEdgeCount [[2,1,1,1,2]]) [] := certificate_676_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns13x6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem patterns_13_6_2_verified : ∀ D ∈ patterns_13_6_2, PatternVerified 13 6 D := by

  simp only [patterns_13_6_2, List.forall_mem_cons]

  exact ⟨⟨certificate_557, certificate_557_valid⟩, ⟨⟨certificate_558, certificate_558_valid⟩, ⟨⟨certificate_559, certificate_559_valid⟩, ⟨⟨certificate_560, certificate_560_valid⟩, ⟨⟨certificate_561, certificate_561_valid⟩, ⟨⟨certificate_562, certificate_562_valid⟩, ⟨⟨certificate_563, certificate_563_valid⟩, ⟨⟨certificate_564, certificate_564_valid⟩, ⟨⟨certificate_565, certificate_565_valid⟩, ⟨⟨certificate_566, certificate_566_valid⟩, ⟨⟨certificate_567, certificate_567_valid⟩, ⟨⟨certificate_568, certificate_568_valid⟩, ⟨⟨certificate_569, certificate_569_valid⟩, ⟨⟨certificate_570, certificate_570_valid⟩, ⟨⟨certificate_571, certificate_571_valid⟩, ⟨⟨certificate_572, certificate_572_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem patterns_13_6_4_verified : ∀ D ∈ patterns_13_6_4, PatternVerified 13 6 D := by

  simp only [patterns_13_6_4, List.forall_mem_cons]

  exact ⟨⟨certificate_589, certificate_589_valid⟩, ⟨⟨certificate_590, certificate_590_valid⟩, ⟨⟨certificate_591, certificate_591_valid⟩, ⟨⟨certificate_592, certificate_592_valid⟩, ⟨⟨certificate_593, certificate_593_valid⟩, ⟨⟨certificate_594, certificate_594_valid⟩, ⟨⟨certificate_595, certificate_595_valid⟩, ⟨⟨certificate_596, certificate_596_valid⟩, ⟨⟨certificate_597, certificate_597_valid⟩, ⟨⟨certificate_598, certificate_598_valid⟩, ⟨⟨certificate_599, certificate_599_valid⟩, ⟨⟨certificate_600, certificate_600_valid⟩, ⟨⟨certificate_601, certificate_601_valid⟩, ⟨⟨certificate_602, certificate_602_valid⟩, ⟨⟨certificate_603, certificate_603_valid⟩, ⟨⟨certificate_604, certificate_604_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem patterns_13_6_5_verified : ∀ D ∈ patterns_13_6_5, PatternVerified 13 6 D := by

  simp only [patterns_13_6_5, List.forall_mem_cons]

  exact ⟨⟨certificate_605, certificate_605_valid⟩, ⟨⟨certificate_606, certificate_606_valid⟩, ⟨⟨certificate_607, certificate_607_valid⟩, ⟨⟨certificate_608, certificate_608_valid⟩, ⟨⟨certificate_609, certificate_609_valid⟩, ⟨⟨certificate_610, certificate_610_valid⟩, ⟨⟨certificate_611, certificate_611_valid⟩, ⟨⟨certificate_612, certificate_612_valid⟩, ⟨⟨certificate_613, certificate_613_valid⟩, ⟨⟨certificate_614, certificate_614_valid⟩, ⟨⟨certificate_615, certificate_615_valid⟩, ⟨⟨certificate_616, certificate_616_valid⟩, ⟨⟨certificate_617, certificate_617_valid⟩, ⟨⟨certificate_618, certificate_618_valid⟩, ⟨⟨certificate_619, certificate_619_valid⟩, ⟨⟨certificate_620, certificate_620_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem patterns_13_6_6_verified : ∀ D ∈ patterns_13_6_6, PatternVerified 13 6 D := by

  simp only [patterns_13_6_6, List.forall_mem_cons]

  exact ⟨⟨certificate_621, certificate_621_valid⟩, ⟨⟨certificate_622, certificate_622_valid⟩, ⟨⟨certificate_623, certificate_623_valid⟩, ⟨⟨certificate_624, certificate_624_valid⟩, ⟨⟨certificate_625, certificate_625_valid⟩, ⟨⟨certificate_626, certificate_626_valid⟩, ⟨⟨certificate_627, certificate_627_valid⟩, ⟨⟨certificate_628, certificate_628_valid⟩, ⟨⟨certificate_629, certificate_629_valid⟩, ⟨⟨certificate_630, certificate_630_valid⟩, ⟨⟨certificate_631, certificate_631_valid⟩, ⟨⟨certificate_632, certificate_632_valid⟩, ⟨⟨certificate_633, certificate_633_valid⟩, ⟨⟨certificate_634, certificate_634_valid⟩, ⟨⟨certificate_635, certificate_635_valid⟩, ⟨⟨certificate_636, certificate_636_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem patterns_13_6_7_verified : ∀ D ∈ patterns_13_6_7, PatternVerified 13 6 D := by

  simp only [patterns_13_6_7, List.forall_mem_cons]

  exact ⟨⟨certificate_637, certificate_637_valid⟩, ⟨⟨certificate_638, certificate_638_valid⟩, ⟨⟨certificate_639, certificate_639_valid⟩, ⟨⟨certificate_640, certificate_640_valid⟩, ⟨⟨certificate_641, certificate_641_valid⟩, ⟨⟨certificate_642, certificate_642_valid⟩, ⟨⟨certificate_643, certificate_643_valid⟩, ⟨⟨certificate_644, certificate_644_valid⟩, ⟨⟨certificate_645, certificate_645_valid⟩, ⟨⟨certificate_646, certificate_646_valid⟩, ⟨⟨certificate_647, certificate_647_valid⟩, ⟨⟨certificate_648, certificate_648_valid⟩, ⟨⟨certificate_649, certificate_649_valid⟩, ⟨⟨certificate_650, certificate_650_valid⟩, ⟨⟨certificate_651, certificate_651_valid⟩, ⟨⟨certificate_652, certificate_652_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem patterns_13_6_8_verified : ∀ D ∈ patterns_13_6_8, PatternVerified 13 6 D := by

  simp only [patterns_13_6_8, List.forall_mem_cons]

  exact ⟨⟨certificate_653, certificate_653_valid⟩, ⟨⟨certificate_654, certificate_654_valid⟩, ⟨⟨certificate_655, certificate_655_valid⟩, ⟨⟨certificate_656, certificate_656_valid⟩, ⟨⟨certificate_657, certificate_657_valid⟩, ⟨⟨certificate_658, certificate_658_valid⟩, ⟨⟨certificate_659, certificate_659_valid⟩, ⟨⟨certificate_660, certificate_660_valid⟩, ⟨⟨certificate_661, certificate_661_valid⟩, ⟨⟨certificate_662, certificate_662_valid⟩, ⟨⟨certificate_663, certificate_663_valid⟩, ⟨⟨certificate_664, certificate_664_valid⟩, ⟨⟨certificate_665, certificate_665_valid⟩, ⟨⟨certificate_666, certificate_666_valid⟩, ⟨⟨certificate_667, certificate_667_valid⟩, ⟨⟨certificate_668, certificate_668_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem patterns_13_6_9_verified : ∀ D ∈ patterns_13_6_9, PatternVerified 13 6 D := by

  simp only [patterns_13_6_9, List.forall_mem_cons]

  exact ⟨⟨certificate_669, certificate_669_valid⟩, ⟨⟨certificate_670, certificate_670_valid⟩, ⟨⟨certificate_671, certificate_671_valid⟩, ⟨⟨certificate_672, certificate_672_valid⟩, ⟨⟨certificate_673, certificate_673_valid⟩, ⟨⟨certificate_674, certificate_674_valid⟩, ⟨⟨certificate_675, certificate_675_valid⟩, ⟨⟨certificate_676, certificate_676_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩

theorem patterns_13_6_verified : ∀ D ∈ patterns_13_6, PatternVerified 13 6 D := by

  simp only [patterns_13_6, List.forall_mem_append]

  exact ⟨patterns_13_6_0_verified, ⟨patterns_13_6_1_verified, ⟨patterns_13_6_2_verified, ⟨patterns_13_6_3_verified, ⟨patterns_13_6_4_verified, ⟨patterns_13_6_5_verified, ⟨patterns_13_6_6_verified, ⟨patterns_13_6_7_verified, ⟨patterns_13_6_8_verified, ⟨patterns_13_6_9_verified, by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem patterns_13_6_coverage : patternChoices 6 7 [] = patterns_13_6 := by decide +kernel

theorem finite_patterns_13_6_oai : ∀ D ∈ patternChoices 6 (13-6) [], PatternVerified 13 6 D := by

  rw [patterns_13_6_coverage]

  exact patterns_13_6_verified

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.finite_patterns_13_6_oai := @OAI.CycleClique.finite_patterns_13_6_oai
