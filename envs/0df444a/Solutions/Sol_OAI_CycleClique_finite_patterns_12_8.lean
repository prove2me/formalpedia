-- Prove2me | solution 1 for OAI.CycleClique.finite_patterns_12_8
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T20:08:26.608466+00:00
-- url     : https://prove2.me/submissions/5a0796ae-89f8-4cdf-8708-9b3d593fd41e

import Mathlib
import Definitions.Def_OAIQ107D133

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates016
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_499_checked : certificate_499.Valid 12 8 8 certificate_499_q certificate_499_edges 0 0 [] := by decide +kernel
theorem certificate_499_valid : certificate_499.Valid 12 8 (patternOrder [[],[],[],[],[],[],[],[]]) (patternClique [[],[],[],[],[],[],[],[]]) (patternEdges [[],[],[],[],[],[],[],[]]) (patternAmount [[],[],[],[],[],[],[],[]]) (patternEdgeCount [[],[],[],[],[],[],[],[]]) [] := certificate_499_checked

theorem certificate_500_checked : certificate_500.Valid 12 8 9 certificate_500_q certificate_500_edges 1 1 [] := by decide +kernel
theorem certificate_500_valid : certificate_500.Valid 12 8 (patternOrder [[],[],[],[],[],[],[1]]) (patternClique [[],[],[],[],[],[],[1]]) (patternEdges [[],[],[],[],[],[],[1]]) (patternAmount [[],[],[],[],[],[],[1]]) (patternEdgeCount [[],[],[],[],[],[],[1]]) [] := certificate_500_checked

theorem certificate_501_checked : certificate_501.Valid 12 8 10 certificate_501_q certificate_501_edges 2 1 [] := by decide +kernel
theorem certificate_501_valid : certificate_501.Valid 12 8 (patternOrder [[],[],[],[],[],[],[2]]) (patternClique [[],[],[],[],[],[],[2]]) (patternEdges [[],[],[],[],[],[],[2]]) (patternAmount [[],[],[],[],[],[],[2]]) (patternEdgeCount [[],[],[],[],[],[],[2]]) [] := certificate_501_checked

theorem certificate_502_checked : certificate_502.Valid 12 8 11 certificate_502_q certificate_502_edges 3 1 [] := by decide +kernel
theorem certificate_502_valid : certificate_502.Valid 12 8 (patternOrder [[],[],[],[],[],[],[3]]) (patternClique [[],[],[],[],[],[],[3]]) (patternEdges [[],[],[],[],[],[],[3]]) (patternAmount [[],[],[],[],[],[],[3]]) (patternEdgeCount [[],[],[],[],[],[],[3]]) [] := certificate_502_checked

theorem certificate_503_checked : certificate_503.Valid 12 8 12 certificate_503_q certificate_503_edges 4 1 [] := by decide +kernel
theorem certificate_503_valid : certificate_503.Valid 12 8 (patternOrder [[],[],[],[],[],[],[4]]) (patternClique [[],[],[],[],[],[],[4]]) (patternEdges [[],[],[],[],[],[],[4]]) (patternAmount [[],[],[],[],[],[],[4]]) (patternEdgeCount [[],[],[],[],[],[],[4]]) [] := certificate_503_checked

theorem certificate_504_checked : certificate_504.Valid 12 8 10 certificate_504_q certificate_504_edges 2 2 [] := by decide +kernel
theorem certificate_504_valid : certificate_504.Valid 12 8 (patternOrder [[],[],[],[],[],[1,1]]) (patternClique [[],[],[],[],[],[1,1]]) (patternEdges [[],[],[],[],[],[1,1]]) (patternAmount [[],[],[],[],[],[1,1]]) (patternEdgeCount [[],[],[],[],[],[1,1]]) [] := certificate_504_checked

theorem certificate_505_checked : certificate_505.Valid 12 8 11 certificate_505_q certificate_505_edges 3 2 [] := by decide +kernel
theorem certificate_505_valid : certificate_505.Valid 12 8 (patternOrder [[],[],[],[],[],[1,2]]) (patternClique [[],[],[],[],[],[1,2]]) (patternEdges [[],[],[],[],[],[1,2]]) (patternAmount [[],[],[],[],[],[1,2]]) (patternEdgeCount [[],[],[],[],[],[1,2]]) [] := certificate_505_checked

theorem certificate_506_checked : certificate_506.Valid 12 8 12 certificate_506_q certificate_506_edges 4 2 [] := by decide +kernel
theorem certificate_506_valid : certificate_506.Valid 12 8 (patternOrder [[],[],[],[],[],[1,3]]) (patternClique [[],[],[],[],[],[1,3]]) (patternEdges [[],[],[],[],[],[1,3]]) (patternAmount [[],[],[],[],[],[1,3]]) (patternEdgeCount [[],[],[],[],[],[1,3]]) [] := certificate_506_checked

theorem certificate_507_checked : certificate_507.Valid 12 8 12 certificate_507_q certificate_507_edges 4 2 [] := by decide +kernel
theorem certificate_507_valid : certificate_507.Valid 12 8 (patternOrder [[],[],[],[],[],[2,2]]) (patternClique [[],[],[],[],[],[2,2]]) (patternEdges [[],[],[],[],[],[2,2]]) (patternAmount [[],[],[],[],[],[2,2]]) (patternEdgeCount [[],[],[],[],[],[2,2]]) [] := certificate_507_checked

theorem certificate_508_checked : certificate_508.Valid 12 8 10 certificate_508_q certificate_508_edges 2 2 [] := by decide +kernel
theorem certificate_508_valid : certificate_508.Valid 12 8 (patternOrder [[],[],[],[],[1],[1]]) (patternClique [[],[],[],[],[1],[1]]) (patternEdges [[],[],[],[],[1],[1]]) (patternAmount [[],[],[],[],[1],[1]]) (patternEdgeCount [[],[],[],[],[1],[1]]) [] := certificate_508_checked

theorem certificate_509_checked : certificate_509.Valid 12 8 11 certificate_509_q certificate_509_edges 3 2 [] := by decide +kernel
theorem certificate_509_valid : certificate_509.Valid 12 8 (patternOrder [[],[],[],[],[1],[2]]) (patternClique [[],[],[],[],[1],[2]]) (patternEdges [[],[],[],[],[1],[2]]) (patternAmount [[],[],[],[],[1],[2]]) (patternEdgeCount [[],[],[],[],[1],[2]]) [] := certificate_509_checked

theorem certificate_510_checked : certificate_510.Valid 12 8 12 certificate_510_q certificate_510_edges 4 2 [] := by decide +kernel
theorem certificate_510_valid : certificate_510.Valid 12 8 (patternOrder [[],[],[],[],[1],[3]]) (patternClique [[],[],[],[],[1],[3]]) (patternEdges [[],[],[],[],[1],[3]]) (patternAmount [[],[],[],[],[1],[3]]) (patternEdgeCount [[],[],[],[],[1],[3]]) [] := certificate_510_checked

theorem certificate_511_checked : certificate_511.Valid 12 8 11 certificate_511_q certificate_511_edges 3 3 [] := by decide +kernel
theorem certificate_511_valid : certificate_511.Valid 12 8 (patternOrder [[],[],[],[],[1,1,1]]) (patternClique [[],[],[],[],[1,1,1]]) (patternEdges [[],[],[],[],[1,1,1]]) (patternAmount [[],[],[],[],[1,1,1]]) (patternEdgeCount [[],[],[],[],[1,1,1]]) [] := certificate_511_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates017
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_512_checked : certificate_512.Valid 12 8 12 certificate_512_q certificate_512_edges 4 3 [] := by decide +kernel
theorem certificate_512_valid : certificate_512.Valid 12 8 (patternOrder [[],[],[],[],[1,1,2]]) (patternClique [[],[],[],[],[1,1,2]]) (patternEdges [[],[],[],[],[1,1,2]]) (patternAmount [[],[],[],[],[1,1,2]]) (patternEdgeCount [[],[],[],[],[1,1,2]]) [] := certificate_512_checked

theorem certificate_513_checked : certificate_513.Valid 12 8 12 certificate_513_q certificate_513_edges 4 3 [] := by decide +kernel
theorem certificate_513_valid : certificate_513.Valid 12 8 (patternOrder [[],[],[],[],[1,2,1]]) (patternClique [[],[],[],[],[1,2,1]]) (patternEdges [[],[],[],[],[1,2,1]]) (patternAmount [[],[],[],[],[1,2,1]]) (patternEdgeCount [[],[],[],[],[1,2,1]]) [] := certificate_513_checked

theorem certificate_514_checked : certificate_514.Valid 12 8 12 certificate_514_q certificate_514_edges 4 2 [] := by decide +kernel
theorem certificate_514_valid : certificate_514.Valid 12 8 (patternOrder [[],[],[],[],[2],[2]]) (patternClique [[],[],[],[],[2],[2]]) (patternEdges [[],[],[],[],[2],[2]]) (patternAmount [[],[],[],[],[2],[2]]) (patternEdgeCount [[],[],[],[],[2],[2]]) [] := certificate_514_checked

theorem certificate_515_checked : certificate_515.Valid 12 8 11 certificate_515_q certificate_515_edges 3 3 [] := by decide +kernel
theorem certificate_515_valid : certificate_515.Valid 12 8 (patternOrder [[],[],[],[1],[1,1]]) (patternClique [[],[],[],[1],[1,1]]) (patternEdges [[],[],[],[1],[1,1]]) (patternAmount [[],[],[],[1],[1,1]]) (patternEdgeCount [[],[],[],[1],[1,1]]) [] := certificate_515_checked

theorem certificate_516_checked : certificate_516.Valid 12 8 12 certificate_516_q certificate_516_edges 4 3 [] := by decide +kernel
theorem certificate_516_valid : certificate_516.Valid 12 8 (patternOrder [[],[],[],[1],[1,2]]) (patternClique [[],[],[],[1],[1,2]]) (patternEdges [[],[],[],[1],[1,2]]) (patternAmount [[],[],[],[1],[1,2]]) (patternEdgeCount [[],[],[],[1],[1,2]]) [] := certificate_516_checked

theorem certificate_517_checked : certificate_517.Valid 12 8 12 certificate_517_q certificate_517_edges 4 3 [] := by decide +kernel
theorem certificate_517_valid : certificate_517.Valid 12 8 (patternOrder [[],[],[],[1,1],[2]]) (patternClique [[],[],[],[1,1],[2]]) (patternEdges [[],[],[],[1,1],[2]]) (patternAmount [[],[],[],[1,1],[2]]) (patternEdgeCount [[],[],[],[1,1],[2]]) [] := certificate_517_checked

theorem certificate_518_checked : certificate_518.Valid 12 8 12 certificate_518_q certificate_518_edges 4 4 [] := by decide +kernel
theorem certificate_518_valid : certificate_518.Valid 12 8 (patternOrder [[],[],[],[1,1,1,1]]) (patternClique [[],[],[],[1,1,1,1]]) (patternEdges [[],[],[],[1,1,1,1]]) (patternAmount [[],[],[],[1,1,1,1]]) (patternEdgeCount [[],[],[],[1,1,1,1]]) [] := certificate_518_checked

theorem certificate_519_checked : certificate_519.Valid 12 8 11 certificate_519_q certificate_519_edges 3 3 [] := by decide +kernel
theorem certificate_519_valid : certificate_519.Valid 12 8 (patternOrder [[],[],[1],[1],[1]]) (patternClique [[],[],[1],[1],[1]]) (patternEdges [[],[],[1],[1],[1]]) (patternAmount [[],[],[1],[1],[1]]) (patternEdgeCount [[],[],[1],[1],[1]]) [] := certificate_519_checked

theorem certificate_520_checked : certificate_520.Valid 12 8 12 certificate_520_q certificate_520_edges 4 3 [] := by decide +kernel
theorem certificate_520_valid : certificate_520.Valid 12 8 (patternOrder [[],[],[1],[1],[2]]) (patternClique [[],[],[1],[1],[2]]) (patternEdges [[],[],[1],[1],[2]]) (patternAmount [[],[],[1],[1],[2]]) (patternEdgeCount [[],[],[1],[1],[2]]) [] := certificate_520_checked

theorem certificate_521_checked : certificate_521.Valid 12 8 12 certificate_521_q certificate_521_edges 4 4 [] := by decide +kernel
theorem certificate_521_valid : certificate_521.Valid 12 8 (patternOrder [[],[],[1],[1,1,1]]) (patternClique [[],[],[1],[1,1,1]]) (patternEdges [[],[],[1],[1,1,1]]) (patternAmount [[],[],[1],[1,1,1]]) (patternEdgeCount [[],[],[1],[1,1,1]]) [] := certificate_521_checked

theorem certificate_522_checked : certificate_522.Valid 12 8 12 certificate_522_q certificate_522_edges 4 4 [] := by decide +kernel
theorem certificate_522_valid : certificate_522.Valid 12 8 (patternOrder [[],[],[1,1],[1,1]]) (patternClique [[],[],[1,1],[1,1]]) (patternEdges [[],[],[1,1],[1,1]]) (patternAmount [[],[],[1,1],[1,1]]) (patternEdgeCount [[],[],[1,1],[1,1]]) [] := certificate_522_checked

theorem certificate_523_checked : certificate_523.Valid 12 8 12 certificate_523_q certificate_523_edges 4 4 [] := by decide +kernel
theorem certificate_523_valid : certificate_523.Valid 12 8 (patternOrder [[],[1],[1],[1,1]]) (patternClique [[],[1],[1],[1,1]]) (patternEdges [[],[1],[1],[1,1]]) (patternAmount [[],[1],[1],[1,1]]) (patternEdgeCount [[],[1],[1],[1,1]]) [] := certificate_523_checked

theorem certificate_524_checked : certificate_524.Valid 12 8 12 certificate_524_q certificate_524_edges 4 4 [] := by decide +kernel
theorem certificate_524_valid : certificate_524.Valid 12 8 (patternOrder [[1],[1],[1],[1]]) (patternClique [[1],[1],[1],[1]]) (patternEdges [[1],[1],[1],[1]]) (patternAmount [[1],[1],[1],[1]]) (patternEdgeCount [[1],[1],[1],[1]]) [] := certificate_524_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns12x8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem patterns_12_8_0_verified : ∀ D ∈ patterns_12_8_0, PatternVerified 12 8 D := by

  simp only [patterns_12_8_0, List.forall_mem_cons]

  exact ⟨⟨certificate_499, certificate_499_valid⟩, ⟨⟨certificate_500, certificate_500_valid⟩, ⟨⟨certificate_501, certificate_501_valid⟩, ⟨⟨certificate_502, certificate_502_valid⟩, ⟨⟨certificate_503, certificate_503_valid⟩, ⟨⟨certificate_504, certificate_504_valid⟩, ⟨⟨certificate_505, certificate_505_valid⟩, ⟨⟨certificate_506, certificate_506_valid⟩, ⟨⟨certificate_507, certificate_507_valid⟩, ⟨⟨certificate_508, certificate_508_valid⟩, ⟨⟨certificate_509, certificate_509_valid⟩, ⟨⟨certificate_510, certificate_510_valid⟩, ⟨⟨certificate_511, certificate_511_valid⟩, ⟨⟨certificate_512, certificate_512_valid⟩, ⟨⟨certificate_513, certificate_513_valid⟩, ⟨⟨certificate_514, certificate_514_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem patterns_12_8_1_verified : ∀ D ∈ patterns_12_8_1, PatternVerified 12 8 D := by

  simp only [patterns_12_8_1, List.forall_mem_cons]

  exact ⟨⟨certificate_515, certificate_515_valid⟩, ⟨⟨certificate_516, certificate_516_valid⟩, ⟨⟨certificate_517, certificate_517_valid⟩, ⟨⟨certificate_518, certificate_518_valid⟩, ⟨⟨certificate_519, certificate_519_valid⟩, ⟨⟨certificate_520, certificate_520_valid⟩, ⟨⟨certificate_521, certificate_521_valid⟩, ⟨⟨certificate_522, certificate_522_valid⟩, ⟨⟨certificate_523, certificate_523_valid⟩, ⟨⟨certificate_524, certificate_524_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem patterns_12_8_verified : ∀ D ∈ patterns_12_8, PatternVerified 12 8 D := by

  simp only [patterns_12_8, List.forall_mem_append]

  exact ⟨patterns_12_8_0_verified, ⟨patterns_12_8_1_verified, by simp⟩⟩

theorem patterns_12_8_coverage : patternChoices 8 4 [] = patterns_12_8 := by decide +kernel

theorem finite_patterns_12_8_oai : ∀ D ∈ patternChoices 8 (12-8) [], PatternVerified 12 8 D := by

  rw [patterns_12_8_coverage]

  exact patterns_12_8_verified

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.finite_patterns_12_8_oai := @OAI.CycleClique.finite_patterns_12_8_oai
