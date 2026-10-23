-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.separation_constant_budget
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-22T21:51:33.444453+00:00
-- url     : https://prove2.me/submissions/75b23438-c34f-45a0-a96e-c96270b18adb

import Definitions.Def_OAI_PiExponent_AdmissibleDeterminantParameters

open OAI.PiExponent

theorem solution (m : Nat) (sigma : Rat)
    (hm : 1 ≤ m) (hsigma : 0 < (sigma : Real)) :
    0 < interpolationSeparationConstant m sigma ∧
      (m : Real) ^ 2 / interpolationSeparationConstant m sigma ≤ (sigma : Real) := by
  let M : Real := (m : Real) + 2
  let S : Real := (sigma : Real)
  let B : Real := 1 + M / S
  have hmR : 1 ≤ (m : Real) := by exact_mod_cast hm
  have hM : 1 ≤ M := by dsimp [M]; linarith
  have hMge : (m : Real) ≤ M := by dsimp [M]; linarith
  have hS : 0 < S := hsigma
  have hB : 1 ≤ B := by
    dsimp [B]
    have : 0 ≤ M / S := div_nonneg (by dsimp [M]; linarith) (le_of_lt hS)
    linarith
  have hMpow : M ^ 2 ≤ M ^ (m + 2) := by
    rw [show m + 2 = 2 + m by omega, pow_add]
    calc
      M ^ 2 = M ^ 2 * 1 := by ring
      _ ≤ M ^ 2 * M ^ m := by
        gcongr
        exact one_le_pow₀ hM
  have hBpow : B ^ 2 ≤ B ^ (m + 2) := by
    rw [show m + 2 = 2 + m by omega, pow_add]
    calc
      B ^ 2 = B ^ 2 * 1 := by ring
      _ ≤ B ^ 2 * B ^ m := by
        gcongr
        exact one_le_pow₀ hB
  have hCbound : 2 * M ^ 2 * B ^ 2 ≤ interpolationSeparationConstant m sigma := by
    change 2 * M ^ 2 * B ^ 2 ≤
      2 * M ^ (m + 2) * B ^ (m + 2)
    calc
      2 * M ^ 2 * B ^ 2 ≤ 2 * M ^ (m + 2) * B ^ 2 := by
        apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul_of_nonneg_left hMpow (by norm_num)
        · positivity
      _ ≤ 2 * M ^ (m + 2) * B ^ (m + 2) := by
        exact mul_le_mul_of_nonneg_left hBpow (by positivity)
  have hCpos : 0 < interpolationSeparationConstant m sigma := by
    unfold interpolationSeparationConstant
    positivity
  have hsum : 0 ≤ S + (M ^ 2) / S := by positivity
  have hparent : 2 * M ≤ S + 2 * M + (M ^ 2) / S := by linarith
  have hmul := mul_le_mul_of_nonneg_left hparent (sq_nonneg M)
  have hsq : (m : Real) ^ 2 ≤ M ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hMge)
      (add_nonneg (by positivity : 0 ≤ (m : Real)) (by positivity : 0 ≤ M))]
  have hM2le : M ^ 2 ≤ 2 * M ^ 3 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr (show 1 ≤ 2 * M by linarith [hM]))
      (sq_nonneg M)]
  have hEq : S * (2 * M ^ 2 * B ^ 2) = 2 * M ^ 2 * (S + 2 * M + M ^ 2 / S) := by
    dsimp [B]
    field_simp [ne_of_gt hS]
    ring
  have htarget : (m : Real) ^ 2 ≤ S * (2 * M ^ 2 * B ^ 2) := by
    rw [hEq]
    nlinarith [hsq, hM2le, hmul]
  have hscaled := mul_le_mul_of_nonneg_left hCbound (le_of_lt hS)
  constructor
  · exact hCpos
  · rw [div_le_iff₀ hCpos]
    dsimp [S] at hscaled htarget ⊢
    exact le_trans htarget hscaled
