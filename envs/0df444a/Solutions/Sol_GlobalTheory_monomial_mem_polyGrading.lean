-- Prove2me | solution 1 for GlobalTheory.monomial_mem_polyGrading
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:22:27.287035+00:00
-- url     : https://prove2.me/submissions/ff1dd91a-4ae0-4c0f-8e8b-72415f7c5e6a

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
namespace GlobalTheory
theorem _root_.solution (a : ι →₀ ℕ) (r : R) :
    monomial a r ∈ polyGrading ι R (a.degree : ℤ) :=
  mem_polyGrading_natCast.2 (isHomogeneous_monomial r rfl)
end GlobalTheory
