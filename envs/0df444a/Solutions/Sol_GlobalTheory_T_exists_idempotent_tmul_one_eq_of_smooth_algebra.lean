-- Prove2me | solution 1 for GlobalTheory.T.exists_idempotent_tmul_one_eq_of_smooth_algebra
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:53:05.394993+00:00
-- url     : https://prove2.me/submissions/ab0f3374-3b5d-4190-b04e-39223e963694

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIdempotentTmulOneEqOfSmoothAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIdempotentTmulOneEqOfSmoothAlgebraStatement
import Theorems.Thm_GlobalTheory_exists_isIdempotentElem_tmul_one_eq_of_smooth


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R A : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [CommRing A] [Algebra R A], Algebra.Smooth R A → ∀ ε : A ⊗[R] FractionRing R, IsIdempotentElem ε → ∃ a : A, IsIdempotentElem a ∧ a ⊗ₜ[R] (1 : FractionRing R) = ε := by
  first | exact @GlobalTheory.exists_isIdempotentElem_tmul_one_eq_of_smooth | exact GlobalTheory.exists_isIdempotentElem_tmul_one_eq_of_smooth | (intros; apply GlobalTheory.exists_isIdempotentElem_tmul_one_eq_of_smooth <;> assumption)
end _root_.GlobalTheory.T
