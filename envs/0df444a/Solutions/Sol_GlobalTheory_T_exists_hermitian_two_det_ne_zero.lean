-- Prove2me | solution 1 for GlobalTheory.T.exists_hermitian_two_det_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:19:44.343522+00:00
-- url     : https://prove2.me/submissions/95234941-4f43-42e5-8425-20416b91a898

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsHermitianDetNeZeroTwo
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsHermitianDetNeZeroTwoStatement
import Theorems.Thm_GlobalTheory_exists_hermitian_det_ne_zero_two


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
theorem _root_.solution : ∀ (E κ : Type) [Field E] [CharZero E] [Field κ] (σ : E →+* E) (φ : E →+* κ) (δ : E), δ ≠ 0 → σ δ = -δ → ∀ (n : ℕ) (c d y c' d' y' : Matrix (Fin n) (Fin n) κ), (c * y + d).det ≠ 0 → (c' * y' + d').det ≠ 0 → ∃ x : Matrix (Fin n) (Fin n) E, x.map σ = x.transpose ∧ (c * x.map φ + d).det ≠ 0 ∧ (c' * x.transpose.map φ + d').det ≠ 0 := by
  first | exact @GlobalTheory.exists_hermitian_det_ne_zero_two | exact GlobalTheory.exists_hermitian_det_ne_zero_two | (intros; apply GlobalTheory.exists_hermitian_det_ne_zero_two <;> assumption)
end _root_.GlobalTheory.T
