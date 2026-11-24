-- Prove2me | solution 1 for GlobalTheory.EigFlat.exact_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:24:53.156156+00:00
-- url     : https://prove2.me/submissions/ea3e592c-1154-448f-b1e6-71bb0fa63dc7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_CommonEigenvectorsFlatBaseChange
import Theorems.Thm_GlobalTheory_EigFlat_piScalarRight_lTensor_vecMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix TensorProduct
open GlobalTheory
open GlobalTheory.EigFlat
variable {A : Type} [CommRing A]
namespace GlobalTheory.EigFlat
theorem _root_.solution {a b c : Type} [Fintype a] [Fintype b] [Fintype c] [DecidableEq a]
    [DecidableEq b] [DecidableEq c] (U : Matrix a b A) (H : Matrix b c A)
    (B : Type) [CommRing B] [Algebra A B] :
    Function.Exact (LinearMap.lTensor B U.vecMulLinear) (LinearMap.lTensor B H.vecMulLinear) ↔
      ∀ w : b → B, w ᵥ* H.map (algebraMap A B) = 0 ↔
        ∃ cf : a → B, cf ᵥ* U.map (algebraMap A B) = w := by
  constructor
  · intro h w
    obtain ⟨y, rfl⟩ := (TensorProduct.piScalarRight A B B b).surjective w
    rw [← piScalarRight_lTensor_vecMul, LinearEquiv.map_eq_zero_iff, h y]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨_, (piScalarRight_lTensor_vecMul U B x).symm⟩
    · rintro ⟨cf, hcf⟩
      obtain ⟨x, rfl⟩ := (TensorProduct.piScalarRight A B B a).surjective cf
      rw [← piScalarRight_lTensor_vecMul] at hcf
      exact ⟨x, (TensorProduct.piScalarRight A B B b).injective hcf⟩
  · intro h y
    rw [← (TensorProduct.piScalarRight A B B c).map_eq_zero_iff, piScalarRight_lTensor_vecMul, h]
    constructor
    · rintro ⟨cf, hcf⟩
      obtain ⟨x, rfl⟩ := (TensorProduct.piScalarRight A B B a).surjective cf
      rw [← piScalarRight_lTensor_vecMul] at hcf
      exact ⟨x, (TensorProduct.piScalarRight A B B b).injective hcf⟩
    · rintro ⟨x, rfl⟩
      exact ⟨_, (piScalarRight_lTensor_vecMul U B x).symm⟩
end GlobalTheory.EigFlat
