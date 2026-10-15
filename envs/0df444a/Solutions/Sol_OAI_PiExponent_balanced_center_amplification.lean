-- Prove2me | solution 1 for OAI.PiExponent.balanced_center_amplification
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-14T09:06:50.10658+00:00
-- url     : https://prove2.me/submissions/57db8948-bcd8-4336-b675-99cb67fd0642

import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.Order
import Theorems.Thm_OAI_PiExponent_ratio_base_below_quadratic
import Theorems.Thm_OAI_PiExponent_exp_beats_affine_after
import Theorems.Thm_OAI_PiExponent_balanced_center_window_ratio

theorem solution
    (theta : ℚ) (A p q : ℝ)
    (htheta : 0 < theta) (htheta_one : theta < 1)
    (hA : 0 < A) (hquadratic : A ^ 2 < (theta : ℝ)) :
    ∃ m K : ℕ,
      0 < m ∧ 0 < K ∧
      (K : ℝ) ^ 2 * (theta : ℝ) ^ m < 1 ∧
      p * (m : ℝ) + q <
        (K : ℝ) * (theta : ℝ) ^ m /
          (((m : ℝ) + 1) * A ^ m) := by
  obtain ⟨R, hR, hRsq⟩ :=
    OAI.PiExponent.ratio_base_below_quadratic theta A htheta hA hquadratic
  obtain ⟨M, hM⟩ :=
    OAI.PiExponent.balanced_center_window_ratio theta A R htheta htheta_one
      hA hquadratic hR hRsq
  obtain ⟨m, hmM, hmpos, hlinear⟩ :=
    OAI.PiExponent.exp_beats_affine_after R p q hR M
  obtain ⟨K, hK, hwindow, hcenter⟩ := hM m hmM
  exact ⟨m, K, hmpos, hK, hwindow, lt_trans hlinear hcenter⟩