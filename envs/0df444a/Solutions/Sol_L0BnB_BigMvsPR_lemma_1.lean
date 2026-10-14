-- Prove2me | solution 1 for L0BnB.BigMvsPR.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T02:06:48.580995+00:00
-- url     : https://prove2.me/submissions/ce8ca7de-a57d-455a-9c8e-80de0d6657ea

import Definitions.Def_L0BnB_BigMvsPR_Penalties
import Mathlib

open L0BnB.BigMvsPR L0BnB.Reduced

theorem solution (lam0 lam2 M : ℝ) (hlam0 : 0 < lam0) (hlam2 : 0 < lam2) (hM : 0 < M)
    (hMlarge : Real.sqrt (lam0 / lam2) ≤ M) :
    ∀ b : ℝ, -M ≤ b → b ≤ M → 0 ≤ tGap lam0 lam2 M b := by
  intro b hb₁ hb₂
  let r := Real.sqrt (lam2 / lam0)
  have hr : 0 < r := Real.sqrt_pos_of_pos (div_pos hlam2 hlam0)
  have hr2 : lam0 * r^2 = lam2 := by
    dsimp [r]
    rw [Real.sq_sqrt (div_nonneg hlam2.le hlam0.le)]
    field_simp
  have hsr : Real.sqrt (lam0 / lam2) * r = 1 := by
    dsimp [r]
    rw [← Real.sqrt_mul (div_nonneg hlam0.le hlam2.le)]
    rw [show lam0 / lam2 * (lam2 / lam0) = 1 by field_simp]
    norm_num
  have hMr : 1 ≤ M * r := by
    nlinarith [mul_le_mul_of_nonneg_right hMlarge hr.le]
  have hcoef : lam0 / M ≤ lam0 * r := by
    apply (div_le_iff₀ hM).mpr
    nlinarith [mul_le_mul_of_nonneg_left hMr hlam0.le]
  have habs : |b| ≤ M := abs_le.mpr ⟨hb₁, hb₂⟩
  have hpen : lam0 / M * |b| ≤ lam0 := by
    have h := mul_le_mul_of_nonneg_left ((div_le_one hM).mpr habs) hlam0.le
    calc
      _ = lam0 * (|b| / M) := by ring
      _ ≤ lam0 * 1 := h
      _ = lam0 := by ring
  by_cases hs : |b * r| ≤ 1
  · have has : |b| * r ≤ 1 := by simpa [abs_mul, abs_of_pos hr] using hs
    have hq : lam2 * b^2 ≤ lam0 * r * |b| := by
      calc
        lam2 * b^2 = (lam0 * (|b| * r)) * (|b| * r) := by
          rw [← hr2, ← sq_abs b]
          ring
        _ ≤ (lam0 * (|b| * r)) * 1 :=
          mul_le_mul_of_nonneg_left has (mul_nonneg hlam0.le (mul_nonneg (abs_nonneg _) hr.le))
        _ = lam0 * r * |b| := by ring
    have hp := mul_le_mul_of_nonneg_right hcoef (abs_nonneg b)
    change 0 ≤ 2 * lam0 * reverseHuber (b*r) - lam0 / M * |b| - lam2*b^2
    rw [reverseHuber, if_pos hs, abs_mul, abs_of_pos hr]
    nlinarith [hp, hq]
  · have hq : lam0 * (b*r)^2 = lam2*b^2 := by
      calc
        _ = (lam0*r^2)*b^2 := by ring
        _ = _ := by rw [hr2]
    change 0 ≤ 2 * lam0 * reverseHuber (b*r) - lam0 / M * |b| - lam2*b^2
    rw [reverseHuber, if_neg hs]
    nlinarith [hq, hpen]
