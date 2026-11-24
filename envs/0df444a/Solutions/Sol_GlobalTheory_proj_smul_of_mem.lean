-- Prove2me | solution 1 for GlobalTheory.proj_smul_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:36:09.940088+00:00
-- url     : https://prove2.me/submissions/5572d642-f03d-49e4-a0f2-c81acdb17641

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_XSmulMemWeightedHomogeneousSubmodule
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_WeightAddLeOfMemSupportDividedContraction
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsGradedMapLinearCombination
import Theorems.Thm_GlobalTheory_proj_grShift
import Theorems.Thm_GlobalTheory_isGradedMap_lsmul

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
variable {ι : Type*} {R : Type*} [CommRing R]
  {M : Type*} [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
  {N : Type*} [AddCommGroup N] [Module R N] [Module (MvPolynomial ι R) N]
  {P : Type*} [AddCommGroup P] [Module R P] [Module (MvPolynomial ι R) P]
variable [IsScalarTower R (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) N]
namespace GlobalTheory
theorem _root_.solution (ℳ : ℤ → Submodule R M) [Decomposition ℳ] [PolyGradedSMul ι ℳ]
    {p : MvPolynomial ι R} {d : ℤ} (hp : p ∈ polyGrading ι R d) (n : ℤ) (m : M) :
    proj ℳ (n + d) (p • m) = p • proj ℳ n m := by
  rw [← proj_grShift]
  exact (isGradedMap_lsmul ℳ hp).proj_apply n m
end GlobalTheory
