-- Prove2me | solution 1 for GlobalTheory.T.bijective_of_lTensor_bijective_of_flat_family
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:12:58.877724+00:00
-- url     : https://prove2.me/submissions/592e04b1-853e-4805-9be3-3ed66ac1cb3a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BijectiveOfLTensorFlatFamily
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BijectiveOfLTensorFlatFamilyStatement
import Theorems.Thm_GlobalTheory_bijective_of_lTensor_flat_family


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R : Type) [CommRing R] (N N' : Type) [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N'] (f : N →ₗ[R] N') (J : Type) (B : J → Type) [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)], (∀ i, Module.Flat R (B i)) → (∀ m : Ideal R, m.IsMaximal → ∃ i, Ideal.map (algebraMap R (B i)) m ≠ ⊤) → (∀ i, Function.Bijective (LinearMap.lTensor (B i) f)) → Function.Bijective f := by
  first | exact @GlobalTheory.bijective_of_lTensor_flat_family | exact GlobalTheory.bijective_of_lTensor_flat_family | (intros; apply GlobalTheory.bijective_of_lTensor_flat_family <;> assumption)
end _root_.GlobalTheory.T
