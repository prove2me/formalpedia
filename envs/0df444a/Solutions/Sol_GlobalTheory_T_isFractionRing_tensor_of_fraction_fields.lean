-- Prove2me | solution 1 for GlobalTheory.T.isFractionRing_tensor_of_fraction_fields
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:33:38.332617+00:00
-- url     : https://prove2.me/submissions/414aac8b-c6ea-4724-976c-4f2af54255c1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsFractionRingTensorOfFractionFields
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsFractionRingTensorOfFractionFieldsStatement
import Theorems.Thm_GlobalTheory_tensor_fractionRing_of_tensor


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
theorem _root_.solution : ∀ {k R B K κ L : Type} [Field k] [CommRing R] [CommRing B] [Field K] [Field κ]
    [Field L] [Algebra k R] [Algebra k B] [Algebra k K] [Algebra k κ] [Algebra R K] [Algebra B κ]
    [IsScalarTower k R K] [IsScalarTower k B κ] [IsFractionRing R K] [IsFractionRing B κ]
    [Algebra (K ⊗[k] κ) L] [IsFractionRing (K ⊗[k] κ) L],
    Function.Injective ((algebraMap (K ⊗[k] κ) L).comp (Algebra.TensorProduct.map
      (IsScalarTower.toAlgHom k R K) (IsScalarTower.toAlgHom k B κ)).toRingHom) ∧
    ∀ z : L, ∃ x y : R ⊗[k] B,
      (algebraMap (K ⊗[k] κ) L).comp (Algebra.TensorProduct.map
        (IsScalarTower.toAlgHom k R K) (IsScalarTower.toAlgHom k B κ)).toRingHom y ≠ 0 ∧
      z * (algebraMap (K ⊗[k] κ) L).comp (Algebra.TensorProduct.map
        (IsScalarTower.toAlgHom k R K) (IsScalarTower.toAlgHom k B κ)).toRingHom y =
      (algebraMap (K ⊗[k] κ) L).comp (Algebra.TensorProduct.map
        (IsScalarTower.toAlgHom k R K) (IsScalarTower.toAlgHom k B κ)).toRingHom x := by
  first | exact @GlobalTheory.tensor_fractionRing_of_tensor | exact GlobalTheory.tensor_fractionRing_of_tensor | (intros; apply GlobalTheory.tensor_fractionRing_of_tensor <;> assumption)
end _root_.GlobalTheory.T
