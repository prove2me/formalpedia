-- Prove2me | solution 1 for GlobalTheory.T.matrixGaussSum_mul_dual_eq_card_pow_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:28:54.068989+00:00
-- url     : https://prove2.me/submissions/beb50880-7d6d-4c62-a493-b8c0f4c93f3e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MatrixGaussSumMulDualEqCardPowSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MatrixGaussSumMulDualEqCardPowSqStatement
import Theorems.Thm_GlobalTheory_matrixGaussSum_mul_dual_eq_card_pow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k : Type) [Field k] [Fintype k] [DecidableEq k] (R : Type) [CommRing R] [IsDomain R] (ψ : AddChar k R) (ξ : kˣ →* Rˣ) (r : ℕ), ψ.IsPrimitive → ξ ≠ 1 → (∑ x : GL (Fin r) k, (((ξ (Matrix.GeneralLinearGroup.det x))⁻¹ : Rˣ) : R) * ψ (Matrix.trace (1 * (x : Matrix (Fin r) (Fin r) k)))) * (∑ x : GL (Fin r) k, (((ξ⁻¹ (Matrix.GeneralLinearGroup.det x))⁻¹ : Rˣ) : R) * ψ⁻¹ (Matrix.trace (1 * (x : Matrix (Fin r) (Fin r) k)))) = (Fintype.card k : R) ^ (r ^ 2) := by
  first | exact @GlobalTheory.matrixGaussSum_mul_dual_eq_card_pow | exact GlobalTheory.matrixGaussSum_mul_dual_eq_card_pow | (intros; apply GlobalTheory.matrixGaussSum_mul_dual_eq_card_pow <;> assumption)
end _root_.GlobalTheory.T
