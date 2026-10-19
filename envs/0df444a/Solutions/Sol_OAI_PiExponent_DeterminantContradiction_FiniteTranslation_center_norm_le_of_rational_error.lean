-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.FiniteTranslation.center_norm_le_of_rational_error
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T17:38:47.913998+00:00
-- url     : https://prove2.me/submissions/df0b4aa9-9ede-4375-9e03-07f7e222423d

import Definitions.Def_OAI_PiExponent_FiniteActualTranslation

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem solution
    {nu : ℝ} (p : ℤ) (q k K : ℕ) (hnu : 0 ≤ nu)
    (hq : 0 < q) (hk : k ≤ K)
    (herr : |Real.pi - (p : ℝ) / (q : ℝ)| ≤ (q : ℝ) ^ (-nu)) :
    ‖((k : ℂ) *
      (2 * Complex.I * (p : ℂ) / (q : ℂ) -
        2 * (Real.pi : ℂ) * Complex.I))‖ ≤
      2 * (K : ℝ) * (q : ℝ) ^ (-nu) := by
  let e : ℝ := (p : ℝ) / (q : ℝ) - Real.pi
  have herror : |e| ≤ (q : ℝ) ^ (-nu) := by
    dsimp [e]
    simpa [abs_sub_comm] using herr
  have hfactor :
      2 * Complex.I * (p : ℂ) / (q : ℂ) -
          2 * (Real.pi : ℂ) * Complex.I =
        (2 * Complex.I) * (e : ℂ) := by
    dsimp [e]
    push_cast
    ring
  have hnorm :
      ‖((k : ℂ) *
        (2 * Complex.I * (p : ℂ) / (q : ℂ) -
          2 * (Real.pi : ℂ) * Complex.I))‖ =
        2 * (k : ℝ) * |e| := by
    rw [hfactor]
    simp [norm_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
    ring
  rw [hnorm]
  have hkreal : (k : ℝ) ≤ K := by exact_mod_cast hk
  calc
    2 * (k : ℝ) * |e| ≤ 2 * (K : ℝ) * |e| := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hkreal (by norm_num)) (abs_nonneg e)
    _ ≤ 2 * (K : ℝ) * (q : ℝ) ^ (-nu) := by
      exact mul_le_mul_of_nonneg_left herror (by positivity)