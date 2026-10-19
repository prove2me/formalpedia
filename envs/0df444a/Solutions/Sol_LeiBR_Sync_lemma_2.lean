-- Prove2me | solution 1 for LeiBR.Sync.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-18T19:38:06.487991+00:00
-- url     : https://prove2.me/submissions/a3453065-e04e-4e46-b6e5-7dac65bd14de

import Mathlib
set_option autoImplicit false


theorem solution (c q D : ℝ) (hc0 : 0 < c) (hc1 : c < 1) (hcq : c < q) (hq1 : q < 1)
    (hD : 1 / (Real.exp 1 * Real.log (q / c)) ≤ D) (z : ℝ) (hz : 0 ≤ z) :
    z * c ^ z ≤ D * q ^ z := by
  have hq0 : 0 < q := hc0.trans hcq
  have ha : 0 < Real.log (q / c) := Real.log_pos (by rw [one_lt_div hc0]; exact hcq)
  set a := Real.log (q / c) with ha_def
  have key : c ^ z = q ^ z * Real.exp (-(a * z)) := by
    rw [Real.rpow_def_of_pos hc0, Real.rpow_def_of_pos hq0, ← Real.exp_add, ha_def,
      Real.log_div hq0.ne' hc0.ne']
    congr 1
    ring
  have h1 : a * z ≤ Real.exp (a * z - 1) := by
    have := Real.add_one_le_exp (a * z - 1)
    linarith
  have h3 : Real.exp (-(a * z)) * Real.exp 1 * (a * z) ≤ 1 := by
    have hp : 0 < Real.exp (-(a * z)) * Real.exp 1 := by positivity
    calc Real.exp (-(a * z)) * Real.exp 1 * (a * z)
        ≤ Real.exp (-(a * z)) * Real.exp 1 * Real.exp (a * z - 1) :=
          mul_le_mul_of_nonneg_left h1 hp.le
      _ = 1 := by
          rw [← Real.exp_add, ← Real.exp_add]
          simp
  have h2 : z * Real.exp (-(a * z)) ≤ 1 / (Real.exp 1 * a) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [h3]
  have hqz : 0 < q ^ z := Real.rpow_pos_of_pos hq0 z
  rw [key]
  calc z * (q ^ z * Real.exp (-(a * z))) = (z * Real.exp (-(a * z))) * q ^ z := by ring
    _ ≤ D * q ^ z := mul_le_mul_of_nonneg_right (h2.trans hD) hqz.le

