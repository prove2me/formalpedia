-- Prove2me | solution 1 for HessianDamping.IGAHDSC.inner_grad_le
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T03:43:40.367772+00:00
-- url     : https://prove2.me/submissions/3e803644-3a03-4a1c-8e1d-7f8a8b8ddee0

import Mathlib
import Definitions.Def_HessianDamping_IGAHDSC_Setting

set_option autoImplicit false

open HessianDamping.IGAHDSC

theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (f : H → ℝ) (hfC1 : ContDiff ℝ 1 f)
    (L : ℝ) (hL : 0 < L)
    (hLip : ∀ u w : H, ‖gradient f u - gradient f w‖ ≤ L * ‖u - w‖)
    (xstar : H) (hxstar : ∀ y : H, f xstar ≤ f y)
    (x : ℕ → H) (k : ℕ) (hk : 1 ≤ k) :
    inner ℝ (gradient f (x k)) (x k - xstar) =
      inner ℝ (gradient f (x k) - gradient f xstar) (x k - xstar) ∧
    inner ℝ (gradient f (x k)) (x k - xstar) ≤ L * ‖x k - xstar‖ ^ 2 ∧
      L * ‖x k - xstar‖ ^ 2 ≤
        2 * L * ‖x (k + 1) - xstar‖ ^ 2 +
          2 * L * ‖x (k + 1) - x k‖ ^ 2 := by
  have hg0 : gradient f xstar = 0 := by
    have hmin : IsLocalMin f xstar := Filter.Eventually.of_forall hxstar
    have h := hmin.fderiv_eq_zero
    unfold gradient
    rw [h]
    simp
  refine ⟨?_, ?_, ?_⟩
  · rw [hg0, sub_zero]
  · calc inner ℝ (gradient f (x k)) (x k - xstar)
        ≤ ‖gradient f (x k)‖ * ‖x k - xstar‖ := real_inner_le_norm _ _
      _ = ‖gradient f (x k) - gradient f xstar‖ * ‖x k - xstar‖ := by rw [hg0, sub_zero]
      _ ≤ L * ‖x k - xstar‖ * ‖x k - xstar‖ :=
          mul_le_mul_of_nonneg_right (hLip (x k) xstar) (norm_nonneg _)
      _ = L * ‖x k - xstar‖ ^ 2 := by ring
  · have e : x k - xstar = (x (k + 1) - xstar) - (x (k + 1) - x k) := by abel
    have key : ‖x k - xstar‖ ^ 2 ≤ 2 * ‖x (k + 1) - xstar‖ ^ 2 + 2 * ‖x (k + 1) - x k‖ ^ 2 := by
      rw [e]
      have h1 := norm_sub_le (x (k + 1) - xstar) (x (k + 1) - x k)
      have h0 := norm_nonneg (x (k + 1) - xstar - (x (k + 1) - x k))
      nlinarith [sq_nonneg (‖x (k + 1) - xstar‖ - ‖x (k + 1) - x k‖)]
    nlinarith [mul_le_mul_of_nonneg_left key hL.le]
