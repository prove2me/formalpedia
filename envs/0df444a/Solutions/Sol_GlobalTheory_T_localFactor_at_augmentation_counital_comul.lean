-- Prove2me | solution 1 for GlobalTheory.T.localFactor_at_augmentation_counital_comul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:25:32.664541+00:00
-- url     : https://prove2.me/submissions/7392f56d-332e-4ca5-bf26-8ab6393c8117

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocalFactorAtAugmentationCounitalComul
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocalFactorAtAugmentationCounitalComulStatement
import Theorems.Thm_GlobalTheory_localFactor_counital_descends


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k A : Type) [Field k] [CommRing A] [Algebra k A] [Module.Finite k A] (ε : A →ₐ[k] k) (Δ : A →ₐ[k] A ⊗[k] A), ((∀ a : A, TensorProduct.lid k A (LinearMap.rTensor A ε.toLinearMap (Δ a)) = a) ∧ (∀ a : A, TensorProduct.rid k A (LinearMap.lTensor A ε.toLinearMap (Δ a)) = a)) → ∃ e : A, ε e = 1 ∧ IsIdempotentElem e ∧ ∃ (ε' : (A ⧸ Ideal.span {1 - e}) →ₐ[k] k) (Δ' : (A ⧸ Ideal.span {1 - e}) →ₐ[k] (A ⧸ Ideal.span {1 - e}) ⊗[k] (A ⧸ Ideal.span {1 - e})), ((∀ a : (A ⧸ Ideal.span {1 - e}), TensorProduct.lid k (A ⧸ Ideal.span {1 - e}) (LinearMap.rTensor (A ⧸ Ideal.span {1 - e}) ε'.toLinearMap (Δ' a)) = a) ∧ (∀ a : (A ⧸ Ideal.span {1 - e}), TensorProduct.rid k (A ⧸ Ideal.span {1 - e}) (LinearMap.lTensor (A ⧸ Ideal.span {1 - e}) ε'.toLinearMap (Δ' a)) = a)) ∧ IsNilpotent (RingHom.ker ε') := by
  first | exact @GlobalTheory.localFactor_counital_descends | exact GlobalTheory.localFactor_counital_descends | (intros; apply GlobalTheory.localFactor_counital_descends <;> assumption)
end _root_.GlobalTheory.T
