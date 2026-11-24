-- Prove2me | solution 1 for GlobalTheory.exists_isIdempotentElem_tmul_one_eq_of_smooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:42:40.22516+00:00
-- url     : https://prove2.me/submissions/0bd19d6c-2b9b-4881-bdaa-168c37878e0e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsIntegralOfIsIdempotentElem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIdempotentTmulOneEqOfSmoothAlgebra
import Theorems.Thm_GlobalTheory_IdempotentTensorOne_exists_idempotent_tmul_one_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (R A : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [CommRing A] [Algebra R A],
      Algebra.Smooth R A → ∀ ε : A ⊗[R] FractionRing R, IsIdempotentElem ε →
        ∃ a : A, IsIdempotentElem a ∧ a ⊗ₜ[R] (1 : FractionRing R) = ε := by
  first
  | exact @_root_.GlobalTheory.IdempotentTensorOne.exists_idempotent_tmul_one_eq
  | exact _root_.GlobalTheory.IdempotentTensorOne.exists_idempotent_tmul_one_eq
  | (apply _root_.GlobalTheory.IdempotentTensorOne.exists_idempotent_tmul_one_eq <;> assumption)
  | (intros; apply _root_.GlobalTheory.IdempotentTensorOne.exists_idempotent_tmul_one_eq <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IdempotentTensorOne.exists_idempotent_tmul_one_eq <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IdempotentTensorOne.exists_idempotent_tmul_one_eq ..)
end GlobalTheory
