-- Prove2me | solution 1 for OAI.ExpBound.norm_tsum_exp_le_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:30:33.763963+00:00
-- url     : https://prove2.me/submissions/11e51dae-ef36-4416-9702-218d1f965978

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinCoordinates
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_ExponentialSmoothing
import Theorems.Thm_OAI_ExpBound_exp_neg_le_half

set_option autoImplicit false
open OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open OAI.ExpBound
namespace OAI.ExpBound
theorem _root_.solution
    (a : ℕ → ℂ) (ha0 : a 0 = 0)
    (ha : ∀ n, ‖a n‖ ≤ 1)
    (t : ℝ) (ht : 1 ≤ t)
    (hsum : Summable (fun n : ℕ => a n * Real.exp (-(n : ℝ) * t))) :
    ‖∑' n : ℕ, a n * Real.exp (-(n : ℝ) * t)‖ ≤
      2 * Real.exp (-t) := by
  let r : ℝ := Real.exp (-t)
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hrhalf : r ≤ (1 : ℝ) / 2 := exp_neg_le_half ht
  have hbound (n : ℕ) :
      ‖a (n + 1) * (Real.exp (-(↑(n + 1) : ℝ) * t) : ℂ)‖ ≤
        r * ((1 : ℝ) / 2) ^ n := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    have hexp : Real.exp (-(↑(n + 1) : ℝ) * t) = r ^ (n + 1) := by
      dsimp [r]
      rw [show -(↑(n + 1) : ℝ) * t = (↑(n + 1) : ℝ) * (-t) by ring,
        Real.exp_nat_mul]
    rw [hexp, pow_succ]
    calc
      ‖a (n + 1)‖ * (r ^ n * r) ≤
          1 * (r ^ n * r) := by gcongr; exact ha _
      _ ≤ r * ((1 : ℝ) / 2) ^ n := by
        have hp : r ^ n ≤ ((1 : ℝ) / 2) ^ n := pow_le_pow_left₀ hr0 hrhalf _
        nlinarith [mul_nonneg (sub_nonneg.mpr hp) hr0]
  have hbdsum : Summable (fun n : ℕ => r * ((1 : ℝ) / 2) ^ n) :=
    (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 : ℝ) / 2 < 1)).mul_left r
  have hshift :
      (∑' n : ℕ, a n * Real.exp (-(n : ℝ) * t)) =
        ∑' n : ℕ, a (n + 1) * Real.exp (-(↑(n + 1) : ℝ) * t) := by
    have h := hsum.sum_add_tsum_nat_add 1
    simpa [ha0] using h.symm
  rw [hshift]
  have hnormsum : Summable (fun n : ℕ =>
      ‖a (n + 1) * (Real.exp (-(↑(n + 1) : ℝ) * t) : ℂ)‖) :=
    hbdsum.of_nonneg_of_le (fun _ => norm_nonneg _) hbound
  calc
    ‖∑' n : ℕ, a (n + 1) * Real.exp (-(↑(n + 1) : ℝ) * t)‖ ≤
        ∑' n : ℕ,
          ‖a (n + 1) * (Real.exp (-(↑(n + 1) : ℝ) * t) : ℂ)‖ :=
      norm_tsum_le_tsum_norm hnormsum
    _ ≤ ∑' n : ℕ, r * ((1 : ℝ) / 2) ^ n :=
      hnormsum.tsum_le_tsum hbound hbdsum
    _ = 2 * Real.exp (-t) := by
      rw [tsum_mul_left, tsum_geometric_two]
      dsimp [r]
      ring
end OAI.ExpBound
