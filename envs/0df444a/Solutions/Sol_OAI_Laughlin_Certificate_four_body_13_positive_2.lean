-- Prove2me | solution 2 for OAI.Laughlin.Certificate.four_body_13_positive
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T12:31:09.127855+00:00
-- url     : https://prove2.me/submissions/088156d1-5e6a-48a8-a06a-fc16d353be48

import Mathlib
import Definitions.Def_OAIQ047L000
import Theorems.Thm_OAI_Laughlin_Certificate_error_13

namespace OAI
namespace Laughlin.Certificate
open scoped Matrix
theorem fb_hZ : gramRational 13 = candidateZ_13 := by decide +kernel
theorem fb_hL : compressedRational 13 = lower_13 * Matrix.diagonal pivots_13 * lower_13.transpose := by
  unfold compressedRational middleRational
  rw [error_13, fb_hZ]
  decide +kernel

lemma psd_of_ldl {n : ℕ} (A L : Matrix (Fin n) (Fin n) ℚ) (p : Fin n → ℚ)
    (h : A = L * Matrix.diagonal p * L.transpose) (hp : ∀ i, 0 ≤ p i) :
    (A.map (Rat.castHom ℝ)).PosSemidef := by
  subst h
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.diagonal_map (map_zero _), Matrix.transpose_map]
  have hd : (Matrix.diagonal (fun i => (Rat.castHom ℝ) (p i))).PosSemidef :=
    Matrix.PosSemidef.diagonal (fun i => by simpa using hp i)
  have := hd.mul_mul_conjTranspose_same (L.map (Rat.castHom ℝ))
  have hc : (L.map (Rat.castHom ℝ))ᴴ = (L.map (Rat.castHom ℝ))ᵀ := by
    ext i j; simp [Matrix.conjTranspose_apply]
  rw [hc] at this
  simpa using this

theorem _root_.solution :
    ((compressedRational 13).map (Rat.castHom ℝ)).PosSemidef :=
  psd_of_ldl _ _ _ fb_hL (by decide +kernel)
end Laughlin.Certificate
end OAI
