-- Prove2me | solution 1 for GlobalTheory.polyGradedSMul_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:41:08.597378+00:00
-- url     : https://prove2.me/submissions/3a422ee9-3dbe-460f-af6d-8e6dbe9d6f24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_XSmulMemWeightedHomogeneousSubmodule
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_WeightAddLeOfMemSupportDividedContraction
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsGradedMapLinearCombination
import Theorems.Thm_GlobalTheory_X_smul_mem_gr

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
namespace GlobalTheory
theorem _root_.solution [IsScalarTower R (MvPolynomial ι R) M] (ℳ : ℤ → Submodule R M) :
    PolyGradedSMul ι ℳ ↔
      ∀ (i : ι) (n : ℤ), ∀ m ∈ ℳ n, (X i : MvPolynomial ι R) • m ∈ ℳ (n + 1) :=
  ⟨fun _ => X_smul_mem_gr ℳ, polyGradedSMul_of_X_smul_mem ℳ⟩
end GlobalTheory
