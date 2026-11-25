-- Prove2me | solution 1 for GlobalTheory.T.exists_left_inverse_of_fibrewise_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:18:09.239535+00:00
-- url     : https://prove2.me/submissions/1d96adf4-9c9d-4351-ba2a-33fe82f1fc8b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsLeftInverseOfFibrewiseInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsLeftInverseOfFibrewiseInjectiveStatement
import Theorems.Thm_GlobalTheory_matrix_exists_left_inverse_of_forall_field


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R : Type) [CommRing R] (m n : ℕ) (Q : Matrix (Fin m) (Fin n) R), (∀ (K : Type) [Field K] (φ : R →+* K), Function.Injective (Q.map φ).mulVec) → ∃ Q' : Matrix (Fin n) (Fin m) R, Q' * Q = 1 := by
  first | exact @GlobalTheory.matrix_exists_left_inverse_of_forall_field | exact GlobalTheory.matrix_exists_left_inverse_of_forall_field | (intros; apply GlobalTheory.matrix_exists_left_inverse_of_forall_field <;> assumption)
end _root_.GlobalTheory.T
