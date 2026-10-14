-- Prove2me | solution 1 for OAI.PiExponent.balanced_center_window_ratio
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-14T09:26:16.112514+00:00
-- url     : https://prove2.me/submissions/f323450c-2522-4535-bcb1-3d67c5702636
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Theorems.Thm_OAI_PiExponent_eventually_integer_geometric_window
import Theorems.Thm_OAI_PiExponent_window_lower_ratio_of_scaled_power

theorem solution
    (theta : ℚ) (A R : ℝ)
    (htheta : 0 < theta) (htheta_one : theta < 1)
    (hA : 0 < A) (hquadratic : A ^ 2 < (theta : ℝ))
    (hR : 1 < R)
    (hRsq : R ^ 2 < (theta : ℝ) / A ^ 2) :
    ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
      ∃ K : ℕ, 0 < K ∧
        (K : ℝ) ^ 2 * (theta : ℝ) ^ m < 1 ∧
        R ^ m / (8 * ((m : ℝ) + 1)) <
          ((K : ℝ) * (theta : ℝ) ^ m) /
            (((m : ℝ) + 1) * A ^ m) := by
  have htheta_pos : (0 : ℝ) < (theta : ℝ) := by
    exact_mod_cast htheta
  have htheta_lt : (theta : ℝ) < 1 := by
    exact_mod_cast htheta_one
  have hA_sq_pos : 0 < A ^ 2 := sq_pos_of_pos hA
  have hbase_sq : R ^ 2 * A ^ 2 < (theta : ℝ) :=
    (lt_div_iff₀ hA_sq_pos).mp hRsq
  have hbase_pos : 0 < R * A / (theta : ℝ) :=
    div_pos (mul_pos (by linarith) hA) htheta_pos
  have hgap : (R * A / (theta : ℝ)) ^ 2 * (theta : ℝ) < 1 := by
    calc
      (R * A / (theta : ℝ)) ^ 2 * (theta : ℝ) =
          (R ^ 2 * A ^ 2) / (theta : ℝ) := by
        field_simp [ne_of_gt htheta_pos]
      _ < 1 := (div_lt_one htheta_pos).2 hbase_sq
  obtain ⟨M, hM⟩ :=
    OAI.PiExponent.eventually_integer_geometric_window
      (theta : ℝ) (R * A / (theta : ℝ))
      htheta_pos htheta_lt hbase_pos hgap
  refine ⟨M, fun m hm => ?_⟩
  obtain ⟨K, hK, hKupper, hKlower⟩ := hM m hm
  refine ⟨K, hK, hKupper, ?_⟩
  exact OAI.PiExponent.window_lower_ratio_of_scaled_power
    (theta : ℝ) A R m K htheta_pos hA hKlower