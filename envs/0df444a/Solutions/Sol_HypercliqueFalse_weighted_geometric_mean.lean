-- Prove2me | solution 1 for HypercliqueFalse.weighted_geometric_mean
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T09:29:02.726529+00:00
-- url     : https://prove2.me/submissions/55899c7e-dc73-4829-9c6a-f8a98e9fa71d

import Mathlib

set_option autoImplicit false
namespace HypercliqueFalse

theorem weighted_geometric_mean (a b c ε : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hε : 0 < ε) (hε2 : ε ≤ 2) :
    min (min (a * b * c ^ (1 - ε)) (a ^ (1 - ε) * b * c ^ 2)) (a * b ^ (1 - ε) * c ^ 2) ≤
        (a * b) ^ (1 - ε ^ 2 / 8) * c ^ (1 - 3 * ε / 4 + ε ^ 2 / 4) ∧
      (a * b) ^ (1 - ε ^ 2 / 8) * c ^ (1 - 3 * ε / 4 + ε ^ 2 / 4) ≤
        (a * b * c) ^ (1 - ε ^ 2 / 8) := by
  have a0 : 0 < a := by linarith
  have b0 : 0 < b := by linarith
  have c0 : 0 < c := by linarith
  constructor
  · set X := a * b * c ^ (1 - ε) with hX
    set Y := a ^ (1 - ε) * b * c ^ 2 with hY
    set Z := a * b ^ (1 - ε) * c ^ 2 with hZ
    have X0 : 0 < X := by positivity
    have Y0 : 0 < Y := by positivity
    have Z0 : 0 < Z := by positivity
    set M := min (min X Y) Z with hM
    have M0 : 0 < M := lt_min (lt_min X0 Y0) Z0
    have hMX : M ≤ X := le_trans (min_le_left _ _) (min_le_left _ _)
    have hMY : M ≤ Y := le_trans (min_le_left _ _) (min_le_right _ _)
    have hMZ : M ≤ Z := min_le_right _ _
    have lX : Real.log X = Real.log a + Real.log b + (1 - ε) * Real.log c := by
      rw [hX, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_rpow c0]
    have lY : Real.log Y = (1 - ε) * Real.log a + Real.log b + 2 * Real.log c := by
      rw [hY, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_rpow a0, Real.log_pow]; push_cast; ring
    have lZ : Real.log Z = Real.log a + (1 - ε) * Real.log b + 2 * Real.log c := by
      rw [hZ, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_rpow b0, Real.log_pow]; push_cast; ring
    have lR : Real.log ((a * b) ^ (1 - ε ^ 2 / 8) * c ^ (1 - 3 * ε / 4 + ε ^ 2 / 4)) =
        (1 - ε ^ 2 / 8) * (Real.log a + Real.log b) + (1 - 3 * ε / 4 + ε ^ 2 / 4) * Real.log c := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow (by positivity),
        Real.log_rpow c0, Real.log_mul (by positivity) (by positivity)]
    have h1 := Real.log_le_log M0 hMX
    have h2 := Real.log_le_log M0 hMY
    have h3 := Real.log_le_log M0 hMZ
    rw [← Real.log_le_log_iff M0 (by positivity), lR]
    have w1 : 0 ≤ 1 - ε / 4 := by linarith
    have w2 : 0 ≤ ε / 8 := by linarith
    have key : Real.log M = (1 - ε / 4) * Real.log M + ε / 8 * Real.log M + ε / 8 * Real.log M := by ring
    rw [key]
    have e1 := mul_le_mul_of_nonneg_left h1 w1
    have e2 := mul_le_mul_of_nonneg_left h2 w2
    have e3 := mul_le_mul_of_nonneg_left h3 w2
    rw [lX] at e1; rw [lY] at e2; rw [lZ] at e3
    nlinarith
  · rw [Real.mul_rpow (x := a * b) (y := c) (by positivity) (by positivity)]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Real.rpow_le_rpow_of_exponent_le hc (by nlinarith)

end HypercliqueFalse

theorem solution (a b c ε : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hε : 0 < ε) (hε2 : ε ≤ 2) :
    min (min (a * b * c ^ (1 - ε)) (a ^ (1 - ε) * b * c ^ 2)) (a * b ^ (1 - ε) * c ^ 2) ≤
        (a * b) ^ (1 - ε ^ 2 / 8) * c ^ (1 - 3 * ε / 4 + ε ^ 2 / 4) ∧
      (a * b) ^ (1 - ε ^ 2 / 8) * c ^ (1 - 3 * ε / 4 + ε ^ 2 / 4) ≤
        (a * b * c) ^ (1 - ε ^ 2 / 8) :=
  HypercliqueFalse.weighted_geometric_mean a b c ε ha hb hc hε hε2
