-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RealPlace.eq_diagonal_of_upperTriangular_of_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:57:45.591798+00:00
-- url     : https://prove2.me/submissions/200f7a16-1497-425c-a57b-ee427d650dff

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_EqDiagonalOfUpperTriangularOfUnitary

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RealPlace
namespace GlobalTheory.CompanionTheory.RealPlace
theorem _root_.solution {r : ℕ} (B : Matrix (Fin r) (Fin r) ℂ)
    (hB : B.BlockTriangular id) (hBB : Bᴴ * B = 1) : B = diagonal (fun i => B i i) := by
  have hinv : B⁻¹ = Bᴴ := Matrix.inv_eq_left_inv hBB
  haveI : Invertible B := Matrix.invertibleOfIsUnitDet B (Matrix.isUnit_det_of_left_inverse hBB)
  have hT : B⁻¹.BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hB
  rw [hinv] at hT
  ext i j
  rcases lt_trichotomy i j with h | rfl | h
  · have h1 : Bᴴ j i = 0 := hT h
    rw [Matrix.conjTranspose_apply, star_eq_zero] at h1
    rw [h1, Matrix.diagonal_apply_ne _ (ne_of_lt h)]
  · simp
  · rw [hB h, Matrix.diagonal_apply_ne _ (ne_of_gt h)]
end GlobalTheory.CompanionTheory.RealPlace
