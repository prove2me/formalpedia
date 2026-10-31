-- Prove2me | solution 1 for OAI.CycleClique.finite_patterns_11_7
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T20:03:12.218995+00:00
-- url     : https://prove2.me/submissions/54f04e15-a53f-4c0e-aedf-a44f510b75ca

import Mathlib
import Definitions.Def_OAIQ107D105
import Definitions.Def_OAIQ107D133

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates011
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_325_checked : certificate_325.Valid 11 7 7 certificate_325_q certificate_325_edges 0 0 [] := by decide +kernel
theorem certificate_325_valid : certificate_325.Valid 11 7 (patternOrder [[],[],[],[],[],[],[]]) (patternClique [[],[],[],[],[],[],[]]) (patternEdges [[],[],[],[],[],[],[]]) (patternAmount [[],[],[],[],[],[],[]]) (patternEdgeCount [[],[],[],[],[],[],[]]) [] := certificate_325_checked

theorem certificate_326_checked : certificate_326.Valid 11 7 8 certificate_326_q certificate_326_edges 1 1 [] := by decide +kernel
theorem certificate_326_valid : certificate_326.Valid 11 7 (patternOrder [[],[],[],[],[],[1]]) (patternClique [[],[],[],[],[],[1]]) (patternEdges [[],[],[],[],[],[1]]) (patternAmount [[],[],[],[],[],[1]]) (patternEdgeCount [[],[],[],[],[],[1]]) [] := certificate_326_checked

theorem certificate_327_checked : certificate_327.Valid 11 7 9 certificate_327_q certificate_327_edges 2 1 [] := by decide +kernel
theorem certificate_327_valid : certificate_327.Valid 11 7 (patternOrder [[],[],[],[],[],[2]]) (patternClique [[],[],[],[],[],[2]]) (patternEdges [[],[],[],[],[],[2]]) (patternAmount [[],[],[],[],[],[2]]) (patternEdgeCount [[],[],[],[],[],[2]]) [] := certificate_327_checked

theorem certificate_328_checked : certificate_328.Valid 11 7 10 certificate_328_q certificate_328_edges 3 1 [] := by decide +kernel
theorem certificate_328_valid : certificate_328.Valid 11 7 (patternOrder [[],[],[],[],[],[3]]) (patternClique [[],[],[],[],[],[3]]) (patternEdges [[],[],[],[],[],[3]]) (patternAmount [[],[],[],[],[],[3]]) (patternEdgeCount [[],[],[],[],[],[3]]) [] := certificate_328_checked

theorem certificate_329_checked : certificate_329.Valid 11 7 11 certificate_329_q certificate_329_edges 4 1 [] := by decide +kernel
theorem certificate_329_valid : certificate_329.Valid 11 7 (patternOrder [[],[],[],[],[],[4]]) (patternClique [[],[],[],[],[],[4]]) (patternEdges [[],[],[],[],[],[4]]) (patternAmount [[],[],[],[],[],[4]]) (patternEdgeCount [[],[],[],[],[],[4]]) [] := certificate_329_checked

theorem certificate_330_checked : certificate_330.Valid 11 7 9 certificate_330_q certificate_330_edges 2 2 [] := by decide +kernel
theorem certificate_330_valid : certificate_330.Valid 11 7 (patternOrder [[],[],[],[],[1,1]]) (patternClique [[],[],[],[],[1,1]]) (patternEdges [[],[],[],[],[1,1]]) (patternAmount [[],[],[],[],[1,1]]) (patternEdgeCount [[],[],[],[],[1,1]]) [] := certificate_330_checked

theorem certificate_331_checked : certificate_331.Valid 11 7 10 certificate_331_q certificate_331_edges 3 2 [] := by decide +kernel
theorem certificate_331_valid : certificate_331.Valid 11 7 (patternOrder [[],[],[],[],[1,2]]) (patternClique [[],[],[],[],[1,2]]) (patternEdges [[],[],[],[],[1,2]]) (patternAmount [[],[],[],[],[1,2]]) (patternEdgeCount [[],[],[],[],[1,2]]) [] := certificate_331_checked

theorem certificate_332_checked : certificate_332.Valid 11 7 11 certificate_332_q certificate_332_edges 4 2 [] := by decide +kernel
theorem certificate_332_valid : certificate_332.Valid 11 7 (patternOrder [[],[],[],[],[1,3]]) (patternClique [[],[],[],[],[1,3]]) (patternEdges [[],[],[],[],[1,3]]) (patternAmount [[],[],[],[],[1,3]]) (patternEdgeCount [[],[],[],[],[1,3]]) [] := certificate_332_checked

theorem certificate_333_checked : certificate_333.Valid 11 7 11 certificate_333_q certificate_333_edges 4 2 [] := by decide +kernel
theorem certificate_333_valid : certificate_333.Valid 11 7 (patternOrder [[],[],[],[],[2,2]]) (patternClique [[],[],[],[],[2,2]]) (patternEdges [[],[],[],[],[2,2]]) (patternAmount [[],[],[],[],[2,2]]) (patternEdgeCount [[],[],[],[],[2,2]]) [] := certificate_333_checked

theorem certificate_334_checked : certificate_334.Valid 11 7 9 certificate_334_q certificate_334_edges 2 2 [] := by decide +kernel
theorem certificate_334_valid : certificate_334.Valid 11 7 (patternOrder [[],[],[],[1],[1]]) (patternClique [[],[],[],[1],[1]]) (patternEdges [[],[],[],[1],[1]]) (patternAmount [[],[],[],[1],[1]]) (patternEdgeCount [[],[],[],[1],[1]]) [] := certificate_334_checked

theorem certificate_335_checked : certificate_335.Valid 11 7 10 certificate_335_q certificate_335_edges 3 2 [] := by decide +kernel
theorem certificate_335_valid : certificate_335.Valid 11 7 (patternOrder [[],[],[],[1],[2]]) (patternClique [[],[],[],[1],[2]]) (patternEdges [[],[],[],[1],[2]]) (patternAmount [[],[],[],[1],[2]]) (patternEdgeCount [[],[],[],[1],[2]]) [] := certificate_335_checked

theorem certificate_336_checked : certificate_336.Valid 11 7 11 certificate_336_q certificate_336_edges 4 2 [] := by decide +kernel
theorem certificate_336_valid : certificate_336.Valid 11 7 (patternOrder [[],[],[],[1],[3]]) (patternClique [[],[],[],[1],[3]]) (patternEdges [[],[],[],[1],[3]]) (patternAmount [[],[],[],[1],[3]]) (patternEdgeCount [[],[],[],[1],[3]]) [] := certificate_336_checked

theorem certificate_337_checked : certificate_337.Valid 11 7 10 certificate_337_q certificate_337_edges 3 3 [] := by decide +kernel
theorem certificate_337_valid : certificate_337.Valid 11 7 (patternOrder [[],[],[],[1,1,1]]) (patternClique [[],[],[],[1,1,1]]) (patternEdges [[],[],[],[1,1,1]]) (patternAmount [[],[],[],[1,1,1]]) (patternEdgeCount [[],[],[],[1,1,1]]) [] := certificate_337_checked

theorem certificate_338_checked : certificate_338.Valid 11 7 11 certificate_338_q certificate_338_edges 4 3 [] := by decide +kernel
theorem certificate_338_valid : certificate_338.Valid 11 7 (patternOrder [[],[],[],[1,1,2]]) (patternClique [[],[],[],[1,1,2]]) (patternEdges [[],[],[],[1,1,2]]) (patternAmount [[],[],[],[1,1,2]]) (patternEdgeCount [[],[],[],[1,1,2]]) [] := certificate_338_checked

theorem certificate_339_checked : certificate_339.Valid 11 7 11 certificate_339_q certificate_339_edges 4 3 [] := by decide +kernel
theorem certificate_339_valid : certificate_339.Valid 11 7 (patternOrder [[],[],[],[1,2,1]]) (patternClique [[],[],[],[1,2,1]]) (patternEdges [[],[],[],[1,2,1]]) (patternAmount [[],[],[],[1,2,1]]) (patternEdgeCount [[],[],[],[1,2,1]]) [] := certificate_339_checked

theorem certificate_340_checked : certificate_340.Valid 11 7 11 certificate_340_q certificate_340_edges 4 2 [] := by decide +kernel
theorem certificate_340_valid : certificate_340.Valid 11 7 (patternOrder [[],[],[],[2],[2]]) (patternClique [[],[],[],[2],[2]]) (patternEdges [[],[],[],[2],[2]]) (patternAmount [[],[],[],[2],[2]]) (patternEdgeCount [[],[],[],[2],[2]]) [] := certificate_340_checked

theorem certificate_341_checked : certificate_341.Valid 11 7 10 certificate_341_q certificate_341_edges 3 3 [] := by decide +kernel
theorem certificate_341_valid : certificate_341.Valid 11 7 (patternOrder [[],[],[1],[1,1]]) (patternClique [[],[],[1],[1,1]]) (patternEdges [[],[],[1],[1,1]]) (patternAmount [[],[],[1],[1,1]]) (patternEdgeCount [[],[],[1],[1,1]]) [] := certificate_341_checked

theorem certificate_342_checked : certificate_342.Valid 11 7 11 certificate_342_q certificate_342_edges 4 3 [] := by decide +kernel
theorem certificate_342_valid : certificate_342.Valid 11 7 (patternOrder [[],[],[1],[1,2]]) (patternClique [[],[],[1],[1,2]]) (patternEdges [[],[],[1],[1,2]]) (patternAmount [[],[],[1],[1,2]]) (patternEdgeCount [[],[],[1],[1,2]]) [] := certificate_342_checked

theorem certificate_343_checked : certificate_343.Valid 11 7 11 certificate_343_q certificate_343_edges 4 3 [] := by decide +kernel
theorem certificate_343_valid : certificate_343.Valid 11 7 (patternOrder [[],[],[1,1],[2]]) (patternClique [[],[],[1,1],[2]]) (patternEdges [[],[],[1,1],[2]]) (patternAmount [[],[],[1,1],[2]]) (patternEdgeCount [[],[],[1,1],[2]]) [] := certificate_343_checked

theorem certificate_344_checked : certificate_344.Valid 11 7 11 certificate_344_q certificate_344_edges 4 4 [] := by decide +kernel
theorem certificate_344_valid : certificate_344.Valid 11 7 (patternOrder [[],[],[1,1,1,1]]) (patternClique [[],[],[1,1,1,1]]) (patternEdges [[],[],[1,1,1,1]]) (patternAmount [[],[],[1,1,1,1]]) (patternEdgeCount [[],[],[1,1,1,1]]) [] := certificate_344_checked

theorem certificate_345_checked : certificate_345.Valid 11 7 10 certificate_345_q certificate_345_edges 3 3 [] := by decide +kernel
theorem certificate_345_valid : certificate_345.Valid 11 7 (patternOrder [[],[1],[1],[1]]) (patternClique [[],[1],[1],[1]]) (patternEdges [[],[1],[1],[1]]) (patternAmount [[],[1],[1],[1]]) (patternEdgeCount [[],[1],[1],[1]]) [] := certificate_345_checked

theorem certificate_346_checked : certificate_346.Valid 11 7 11 certificate_346_q certificate_346_edges 4 3 [] := by decide +kernel
theorem certificate_346_valid : certificate_346.Valid 11 7 (patternOrder [[],[1],[1],[2]]) (patternClique [[],[1],[1],[2]]) (patternEdges [[],[1],[1],[2]]) (patternAmount [[],[1],[1],[2]]) (patternEdgeCount [[],[1],[1],[2]]) [] := certificate_346_checked

theorem certificate_347_checked : certificate_347.Valid 11 7 11 certificate_347_q certificate_347_edges 4 4 [] := by decide +kernel
theorem certificate_347_valid : certificate_347.Valid 11 7 (patternOrder [[],[1],[1,1,1]]) (patternClique [[],[1],[1,1,1]]) (patternEdges [[],[1],[1,1,1]]) (patternAmount [[],[1],[1,1,1]]) (patternEdgeCount [[],[1],[1,1,1]]) [] := certificate_347_checked

theorem certificate_348_checked : certificate_348.Valid 11 7 11 certificate_348_q certificate_348_edges 4 4 [] := by decide +kernel
theorem certificate_348_valid : certificate_348.Valid 11 7 (patternOrder [[],[1,1],[1,1]]) (patternClique [[],[1,1],[1,1]]) (patternEdges [[],[1,1],[1,1]]) (patternAmount [[],[1,1],[1,1]]) (patternEdgeCount [[],[1,1],[1,1]]) [] := certificate_348_checked

theorem certificate_349_checked : certificate_349.Valid 11 7 11 certificate_349_q certificate_349_edges 4 4 [] := by decide +kernel
theorem certificate_349_valid : certificate_349.Valid 11 7 (patternOrder [[1],[1],[1,1]]) (patternClique [[1],[1],[1,1]]) (patternEdges [[1],[1],[1,1]]) (patternAmount [[1],[1],[1,1]]) (patternEdgeCount [[1],[1],[1,1]]) [] := certificate_349_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns11x7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem patterns_11_7_0_verified : ∀ D ∈ patterns_11_7_0, PatternVerified 11 7 D := by

  simp only [patterns_11_7_0, List.forall_mem_cons]

  exact ⟨⟨certificate_325, certificate_325_valid⟩, ⟨⟨certificate_326, certificate_326_valid⟩, ⟨⟨certificate_327, certificate_327_valid⟩, ⟨⟨certificate_328, certificate_328_valid⟩, ⟨⟨certificate_329, certificate_329_valid⟩, ⟨⟨certificate_330, certificate_330_valid⟩, ⟨⟨certificate_331, certificate_331_valid⟩, ⟨⟨certificate_332, certificate_332_valid⟩, ⟨⟨certificate_333, certificate_333_valid⟩, ⟨⟨certificate_334, certificate_334_valid⟩, ⟨⟨certificate_335, certificate_335_valid⟩, ⟨⟨certificate_336, certificate_336_valid⟩, ⟨⟨certificate_337, certificate_337_valid⟩, ⟨⟨certificate_338, certificate_338_valid⟩, ⟨⟨certificate_339, certificate_339_valid⟩, ⟨⟨certificate_340, certificate_340_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem patterns_11_7_1_verified : ∀ D ∈ patterns_11_7_1, PatternVerified 11 7 D := by

  simp only [patterns_11_7_1, List.forall_mem_cons]

  exact ⟨⟨certificate_341, certificate_341_valid⟩, ⟨⟨certificate_342, certificate_342_valid⟩, ⟨⟨certificate_343, certificate_343_valid⟩, ⟨⟨certificate_344, certificate_344_valid⟩, ⟨⟨certificate_345, certificate_345_valid⟩, ⟨⟨certificate_346, certificate_346_valid⟩, ⟨⟨certificate_347, certificate_347_valid⟩, ⟨⟨certificate_348, certificate_348_valid⟩, ⟨⟨certificate_349, certificate_349_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem patterns_11_7_verified : ∀ D ∈ patterns_11_7, PatternVerified 11 7 D := by

  simp only [patterns_11_7, List.forall_mem_append]

  exact ⟨patterns_11_7_0_verified, ⟨patterns_11_7_1_verified, by simp⟩⟩

theorem patterns_11_7_coverage : patternChoices 7 4 [] = patterns_11_7 := by decide +kernel

theorem finite_patterns_11_7_oai : ∀ D ∈ patternChoices 7 (11-7) [], PatternVerified 11 7 D := by

  rw [patterns_11_7_coverage]

  exact patterns_11_7_verified

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.finite_patterns_11_7_oai := @OAI.CycleClique.finite_patterns_11_7_oai
