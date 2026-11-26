-- Prove2me | solution 1 for GlobalTheory.polyGrading_natCast
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T13:28:46.584856+00:00
-- url     : https://prove2.me/submissions/bd1cb428-8d30-44d7-a4b2-89be3dd4e1f7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_XSmulMemWeightedHomogeneousSubmodule
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_WeightAddLeOfMemSupportDividedContraction
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsGradedMapLinearCombination
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open DirectSum MvPolynomial
noncomputable section
open GlobalTheory
open GradedHilbert
variable (ι : Type*) (R : Type*) [CommRing R]
variable {ι R}
variable (ι R)

theorem solution (d : ℕ) : polyGrading ι R d = homogeneousSubmodule ι R d := by
  ext p
  rw [mem_polyGrading_natCast, mem_homogeneousSubmodule]
