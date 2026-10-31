-- Prove2me | solution 1 for OAI.CycleClique.finite_patterns_6_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T20:55:44.983095+00:00
-- url     : https://prove2.me/submissions/db629789-3726-4996-9689-b080a8b3db5c

import Mathlib
import Definitions.Def_OAIQ107D126
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

theorem certificate_7_checked : certificate_7.Valid 6 3 3 certificate_7_q certificate_7_edges 0 0 [] := by decide +kernel
theorem certificate_7_valid : certificate_7.Valid 6 3 (patternOrder [[],[],[]]) (patternClique [[],[],[]]) (patternEdges [[],[],[]]) (patternAmount [[],[],[]]) (patternEdgeCount [[],[],[]]) [] := certificate_7_checked

theorem certificate_8_checked : certificate_8.Valid 6 3 4 certificate_8_q certificate_8_edges 1 1 [] := by decide +kernel
theorem certificate_8_valid : certificate_8.Valid 6 3 (patternOrder [[],[1]]) (patternClique [[],[1]]) (patternEdges [[],[1]]) (patternAmount [[],[1]]) (patternEdgeCount [[],[1]]) [] := certificate_8_checked

theorem certificate_9_part_3_checked : certificate_9_part_3.Valid 6 3 5 certificate_9_q certificate_9_part_3_E 2 1 certificate_9_part_3_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩⟩⟩

theorem certificate_9_part_2_checked : certificate_9_part_2.Valid 6 3 5 certificate_9_q certificate_9_part_2_E 2 1 certificate_9_part_2_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_9_part_3_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_9_part_1_checked : certificate_9_part_1.Valid 6 3 5 certificate_9_q certificate_9_part_1_E 2 1 certificate_9_part_1_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_9_part_2_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_9_checked : certificate_9.Valid 6 3 5 certificate_9_q certificate_9_E 2 1 certificate_9_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_9_part_1_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_9_valid : certificate_9.Valid 6 3 (patternOrder [[],[2]]) (patternClique [[],[2]]) (patternEdges [[],[2]]) (patternAmount [[],[2]]) (patternEdgeCount [[],[2]]) [] := certificate_9_checked

theorem certificate_10_part_2_checked : certificate_10_part_2.Valid 6 3 7 certificate_10_q certificate_10_part_2_E 3 1 certificate_10_part_2_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

theorem certificate_10_part_4_checked : certificate_10_part_4.Valid 6 3 7 certificate_10_q certificate_10_part_4_E 3 1 certificate_10_part_4_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩

theorem certificate_10_part_5_checked : certificate_10_part_5.Valid 6 3 6 certificate_10_q certificate_10_part_5_E 3 1 certificate_10_part_5_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

theorem certificate_10_part_7_checked : certificate_10_part_7.Valid 6 3 6 certificate_10_q certificate_10_part_7_E 3 1 certificate_10_part_7_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩

theorem certificate_10_part_8_checked : certificate_10_part_8.Valid 6 3 7 certificate_10_q certificate_10_part_8_E 3 1 certificate_10_part_8_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩⟩⟩

theorem certificate_10_part_10_checked : certificate_10_part_10.Valid 6 3 6 certificate_10_q certificate_10_part_10_E 3 1 certificate_10_part_10_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem certificate_10_part_12_checked : certificate_10_part_12.Valid 6 3 7 certificate_10_q certificate_10_part_12_E 3 1 certificate_10_part_12_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩⟩

theorem certificate_10_part_13_checked : certificate_10_part_13.Valid 6 3 7 certificate_10_q certificate_10_part_13_E 3 1 certificate_10_part_13_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩⟩⟩

theorem certificate_10_part_11_checked : certificate_10_part_11.Valid 6 3 6 certificate_10_q certificate_10_part_11_E 3 1 certificate_10_part_11_M := by exact ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_10_part_12_checked⟩⟩⟩⟩⟩⟩⟩, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_10_part_13_checked⟩⟩⟩⟩⟩⟩, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩, by decide +kernel⟩⟩⟩⟩

theorem certificate_10_part_9_checked : certificate_10_part_9.Valid 6 3 6 certificate_10_q certificate_10_part_9_E 3 1 certificate_10_part_9_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩, ⟨by decide +kernel, by decide +kernel, certificate_10_part_10_checked, certificate_10_part_11_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_10_part_6_checked : certificate_10_part_6.Valid 6 3 6 certificate_10_q certificate_10_part_6_E 3 1 certificate_10_part_6_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_10_part_7_checked⟩⟩⟩, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_10_part_8_checked⟩⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_10_part_9_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_10_part_3_checked : certificate_10_part_3.Valid 6 3 6 certificate_10_q certificate_10_part_3_E 3 1 certificate_10_part_3_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_10_part_4_checked⟩⟩⟩⟩⟩⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_10_part_5_checked⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_10_part_6_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_10_part_1_checked : certificate_10_part_1.Valid 6 3 6 certificate_10_q certificate_10_part_1_E 3 1 certificate_10_part_1_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_10_part_2_checked⟩⟩⟩⟩, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_10_part_3_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_10_checked : certificate_10.Valid 6 3 6 certificate_10_q certificate_10_E 3 1 certificate_10_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_10_part_1_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_10_valid : certificate_10.Valid 6 3 (patternOrder [[],[3]]) (patternClique [[],[3]]) (patternEdges [[],[3]]) (patternAmount [[],[3]]) (patternEdgeCount [[],[3]]) [] := certificate_10_checked

theorem certificate_11_part_1_checked : certificate_11_part_1.Valid 6 3 5 certificate_11_q certificate_11_part_1_E 2 2 certificate_11_part_1_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩⟩⟩⟩⟩

theorem certificate_11_checked : certificate_11.Valid 6 3 5 certificate_11_q certificate_11_E 2 2 certificate_11_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_11_part_1_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_11_valid : certificate_11.Valid 6 3 (patternOrder [[1,1]]) (patternClique [[1,1]]) (patternEdges [[1,1]]) (patternAmount [[1,1]]) (patternEdgeCount [[1,1]]) [] := certificate_11_checked

theorem certificate_12_part_2_checked : certificate_12_part_2.Valid 6 3 6 certificate_12_q certificate_12_part_2_E 3 2 certificate_12_part_2_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem certificate_12_part_1_checked : certificate_12_part_1.Valid 6 3 6 certificate_12_q certificate_12_part_1_E 3 2 certificate_12_part_1_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_12_part_2_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_12_checked : certificate_12.Valid 6 3 6 certificate_12_q certificate_12_E 3 2 certificate_12_M := by exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨by decide +kernel, by decide +kernel, by decide +kernel, certificate_12_part_1_checked⟩⟩⟩⟩⟩⟩⟩⟩

theorem certificate_12_valid : certificate_12.Valid 6 3 (patternOrder [[1,2]]) (patternClique [[1,2]]) (patternEdges [[1,2]]) (patternAmount [[1,2]]) (patternEdgeCount [[1,2]]) [] := certificate_12_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns6x3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem patterns_6_3_0_verified : ∀ D ∈ patterns_6_3_0, PatternVerified 6 3 D := by

  simp only [patterns_6_3_0, List.forall_mem_cons]

  exact ⟨⟨certificate_7, certificate_7_valid⟩, ⟨⟨certificate_8, certificate_8_valid⟩, ⟨⟨certificate_9, certificate_9_valid⟩, ⟨⟨certificate_10, certificate_10_valid⟩, ⟨⟨certificate_11, certificate_11_valid⟩, ⟨⟨certificate_12, certificate_12_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩

theorem patterns_6_3_verified : ∀ D ∈ patterns_6_3, PatternVerified 6 3 D := by

  simp only [patterns_6_3, List.forall_mem_append]

  exact ⟨patterns_6_3_0_verified, by simp⟩

theorem patterns_6_3_coverage : patternChoices 3 3 [] = patterns_6_3 := by decide +kernel

theorem finite_patterns_6_3_oai : ∀ D ∈ patternChoices 3 (6-3) [], PatternVerified 6 3 D := by

  rw [patterns_6_3_coverage]

  exact patterns_6_3_verified

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.finite_patterns_6_3_oai := @OAI.CycleClique.finite_patterns_6_3_oai
