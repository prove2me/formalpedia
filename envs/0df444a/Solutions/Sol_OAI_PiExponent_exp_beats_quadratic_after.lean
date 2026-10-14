-- Prove2me | solution 1 for OAI.PiExponent.exp_beats_quadratic_after
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-14T09:44:26.919488+00:00
-- url     : https://prove2.me/submissions/470b2fa8-5f84-4856-a7db-044d7b7ebd4e

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Filter
open scoped Topology

theorem solution
    (R C : ℝ) (hR : 1 < R) (M : ℕ) (hC : 0 < C) :
    ∃ m : ℕ, M ≤ m ∧ C * ((m : ℝ) + 1) ^ 2 < R ^ m := by
  have hlim : Tendsto
      (fun n : ℕ => (4 * C) * ((n : ℝ) ^ 2 / R ^ n)) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_const_div_const_pow_of_one_lt 2 hR).const_mul (4 * C)
  have hsmall : ∀ᶠ n : ℕ in atTop,
      (4 * C) * ((n : ℝ) ^ 2 / R ^ n) < 1 :=
    hlim.eventually (gt_mem_nhds (show (0 : ℝ) < 1 from zero_lt_one))
  obtain ⟨m, ⟨⟨hmSmall, hmM⟩, hmOne⟩⟩ :=
    ((hsmall.and (eventually_ge_atTop M)).and
      (eventually_ge_atTop (1 : ℕ))).exists
  have hmOneR : (1 : ℝ) ≤ (m : ℝ) := Nat.one_le_cast.mpr hmOne
  have hquad : ((m : ℝ) + 1) ^ 2 ≤ 4 * (m : ℝ) ^ 2 := by
    nlinarith only [hmOneR, sq_nonneg ((m : ℝ) - 1)]
  have hRpow : 0 < R ^ m := pow_pos (lt_trans zero_lt_one hR) m
  have hbound : (4 * C) * (m : ℝ) ^ 2 < R ^ m := by
    apply (div_lt_one hRpow).mp
    simpa only [mul_div_assoc] using hmSmall
  refine ⟨m, hmM, ?_⟩
  calc
    C * ((m : ℝ) + 1) ^ 2 ≤ C * (4 * (m : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hquad hC.le
    _ = (4 * C) * (m : ℝ) ^ 2 := by ring
    _ < R ^ m := hbound
