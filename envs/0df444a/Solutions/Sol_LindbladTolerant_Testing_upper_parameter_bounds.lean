-- Prove2me | solution 1 for LindbladTolerant.Testing.upper_parameter_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:02:04.638584+00:00
-- url     : https://prove2.me/submissions/ac0f1b0b-1f4c-4709-a857-3b481728b9e6

import Definitions.Def_LindbladTolerant_Testing_algorithm

set_option autoImplicit false
open scoped ComplexOrder
noncomputable section
open scoped BigOperators Matrix
open LindbladTolerant.Testing

theorem solution (k : ℕ) (hk : 1 ≤ k)
    (hC : 1 ≤ copyConstant k) :
    0 < upperConstant k ∧
    ∀ eps1 eps2 : ℝ, 0 ≤ eps1 → eps1 < eps2 →
      0 < totalTime k eps1 eps2 ∧
      totalTime k eps1 eps2 ≤ upperConstant k * eps2 / (eps2-eps1)^2 ∧
      ∀ {M : ℕ} (f : Fin M → Bool),
        eps2 / (2 * qConstant k) < (successCount f : ℝ) / totalTime k eps1 eps2 →
        (successCount f : ℝ) / totalTime k eps1 eps2 < 2*eps2 →
        retainedCount k eps1 eps2 ≤ successCount f := by
  have hfb : 0 ≤ functionalBound k := by
    unfold functionalBound
    positivity
  have hq0 : 0 ≤ qConstant k := Real.sqrt_nonneg _
  have hq2 : (qConstant k)^2 = 1 + functionalBound k := by
    rw [qConstant, Real.sq_sqrt]
    linarith
  have hq : 1 ≤ qConstant k := by nlinarith
  have hqpos : 0 < qConstant k := lt_of_lt_of_le zero_lt_one hq
  have hA : 0 < upperConstant k := by
    unfold upperConstant
    nlinarith
  refine ⟨hA, ?_⟩
  intro eps1 eps2 he1 he12
  have he2 : 0 < eps2 := lt_of_le_of_lt he1 he12
  have hDelta : 0 < eps2-eps1 := sub_pos.mpr he12
  have hd : 0 < testAccuracy eps1 eps2 := by
    unfold testAccuracy
    positivity
  have hdle : testAccuracy eps1 eps2 ≤ 1/32 := by
    unfold testAccuracy
    rw [div_le_iff₀ (by positivity : 0 < (32:ℝ)*eps2)]
    nlinarith
  have hx : 0 < copyConstant k * (testAccuracy eps1 eps2)⁻¹^2 := by
    have hi : 0 < (testAccuracy eps1 eps2)⁻¹ := inv_pos.mpr hd
    positivity
  have hR : 0 < retainedCount k eps1 eps2 := by
    unfold retainedCount
    exact Nat.ceil_pos.mpr hx
  have hR0 : (0:ℝ) ≤ (retainedCount k eps1 eps2 : ℝ) := by positivity
  have hT : 0 < totalTime k eps1 eps2 := by
    unfold totalTime
    have hRpos : (0:ℝ) < (retainedCount k eps1 eps2 : ℝ) := by exact_mod_cast hR
    exact div_pos (mul_pos (mul_pos (by norm_num) (sq_pos_of_pos hqpos)) hRpos) he2
  have hi : (1:ℝ) ≤ (testAccuracy eps1 eps2)⁻¹ := by
    rw [one_le_inv₀ hd]
    linarith
  have hx1 : (1:ℝ) ≤ (testAccuracy eps1 eps2)⁻¹^2 := by
    nlinarith [sq_nonneg ((testAccuracy eps1 eps2)⁻¹ - 1)]
  have hceil : (retainedCount k eps1 eps2 : ℝ) <
      copyConstant k * (testAccuracy eps1 eps2)⁻¹^2 + 1 := by
    exact Nat.ceil_lt_add_one hx.le
  have hRle : (retainedCount k eps1 eps2 : ℝ) ≤
      (copyConstant k+1) * (testAccuracy eps1 eps2)⁻¹^2 := by
    nlinarith
  have htime : totalTime k eps1 eps2 ≤
      upperConstant k * eps2 / (eps2-eps1)^2 := by
    calc
      totalTime k eps1 eps2 ≤
          32 * (qConstant k)^2 *
            ((copyConstant k+1) * (testAccuracy eps1 eps2)⁻¹^2) / eps2 := by
        unfold totalTime
        gcongr
      _ = upperConstant k * eps2 / (eps2-eps1)^2 := by
        unfold upperConstant testAccuracy
        field_simp
        ring
  refine ⟨hT, htime, ?_⟩
  intro M f hlow _hhigh
  by_contra hnot
  have hKlt : (successCount f : ℝ) < (retainedCount k eps1 eps2 : ℝ) := by
    exact_mod_cast Nat.lt_of_not_ge hnot
  have hraw := (div_lt_div_iff₀ (by positivity : 0 < (2:ℝ)*qConstant k) hT).mp hlow
  have hid : totalTime k eps1 eps2 * eps2 =
      32 * (qConstant k)^2 * (retainedCount k eps1 eps2 : ℝ) := by
    unfold totalTime
    field_simp
  have hlarge : 16 * qConstant k * (retainedCount k eps1 eps2 : ℝ) <
      (successCount f : ℝ) := by
    nlinarith [hid]
  have hRlarge : (retainedCount k eps1 eps2 : ℝ) ≤
      16 * qConstant k * (retainedCount k eps1 eps2 : ℝ) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hq) hR0]
  linarith
