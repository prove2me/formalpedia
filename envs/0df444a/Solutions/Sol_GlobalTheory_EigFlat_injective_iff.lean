-- Prove2me | solution 1 for GlobalTheory.EigFlat.injective_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:24:55.849363+00:00
-- url     : https://prove2.me/submissions/68f42b3b-9003-4e3c-80fa-575f115ad46d

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
theorem _root_.solution {a b : Type} [Fintype a] [Fintype b] [DecidableEq a]
    [DecidableEq b] (U : Matrix a b A) (B : Type) [CommRing B] [Algebra A B] :
    Function.Injective (LinearMap.lTensor B U.vecMulLinear) ↔
      Function.Injective (fun cf : a → B => cf ᵥ* U.map (algebraMap A B)) := by
  have h : (TensorProduct.piScalarRight A B B b) ∘ (LinearMap.lTensor B U.vecMulLinear)
      = (fun cf : a → B => cf ᵥ* U.map (algebraMap A B)) ∘ (TensorProduct.piScalarRight A B B a) :=
    funext fun x => piScalarRight_lTensor_vecMul U B x
  rw [← Function.Injective.of_comp_iff (TensorProduct.piScalarRight A B B b).injective, h,
    Function.Injective.of_comp_iff' _ (TensorProduct.piScalarRight A B B a).bijective]
end GlobalTheory.EigFlat
