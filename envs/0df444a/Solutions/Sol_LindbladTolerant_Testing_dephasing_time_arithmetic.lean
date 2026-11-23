-- Prove2me | solution 1 for LindbladTolerant.Testing.dephasing_time_arithmetic
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-23T03:10:36.067964+00:00
-- url     : https://prove2.me/submissions/c4071c1a-ac29-4a81-b95c-10a45af5d568

import Definitions.Def_LindbladTolerant_Testing_lower_bound_model

set_option autoImplicit false
open scoped ComplexOrder
noncomputable section
open scoped BigOperators Matrix ENNReal
namespace LindbladTolerant.Testing


theorem dephasing_time_arithmetic (eps1 eps2 T gamma0 gamma1 : ℝ)
    (heps1 : 0 ≤ eps1) (heps12 : eps1 < eps2) (hT : 0 ≤ T)
    (hgamma0 : gamma0 = eps1 / Real.sqrt 2)
    (hgamma1 : gamma1 = eps2 / Real.sqrt 2)
    (hsep : (1/3 : ℝ) ≤ poissonTV (gamma0 * T) (gamma1 * T))
    (hhell : poissonTV (gamma0 * T) (gamma1 * T) ≤
      Real.sqrt (1 - Real.exp (-(Real.sqrt (gamma1 * T) - Real.sqrt (gamma0 * T))^2))) :
    lowerConstant * (Real.sqrt eps2 + Real.sqrt eps1)^2 / (eps2-eps1)^2 ≤ T ∧
    lowerConstant * eps2 / (eps2-eps1)^2 ≤ T := by
  have hs1 := Real.sqrt_nonneg eps1
  have hs2 := Real.sqrt_nonneg eps2
  have hsq1 : Real.sqrt eps1 ^ 2 = eps1 := Real.sq_sqrt heps1
  have hsq2 : Real.sqrt eps2 ^ 2 = eps2 := Real.sq_sqrt (by linarith)
  have hlt : Real.sqrt eps1 < Real.sqrt eps2 := Real.sqrt_lt_sqrt heps1 heps12
  have hr2 : 0 < Real.sqrt 2 := by positivity
  have hc : Real.sqrt (T / Real.sqrt 2) ^ 2 = T / Real.sqrt 2 := Real.sq_sqrt (by positivity)
  have hg0 : Real.sqrt (gamma0 * T) = Real.sqrt (T / Real.sqrt 2) * Real.sqrt eps1 := by
    rw [hgamma0, show eps1 / Real.sqrt 2 * T = (T / Real.sqrt 2) * eps1 by ring,
      Real.sqrt_mul (by positivity)]
  have hg1 : Real.sqrt (gamma1 * T) = Real.sqrt (T / Real.sqrt 2) * Real.sqrt eps2 := by
    rw [hgamma1, show eps2 / Real.sqrt 2 * T = (T / Real.sqrt 2) * eps2 by ring,
      Real.sqrt_mul (by positivity)]
  have hD : (Real.sqrt (gamma1 * T) - Real.sqrt (gamma0 * T)) ^ 2 =
      T / Real.sqrt 2 * (Real.sqrt eps2 - Real.sqrt eps1) ^ 2 := by
    rw [hg0, hg1]; linear_combination (Real.sqrt eps2 - Real.sqrt eps1) ^ 2 * hc
  have h19 : (1/3 : ℝ) ^ 2 ≤ 1 - Real.exp (-(Real.sqrt (gamma1 * T) - Real.sqrt (gamma0 * T)) ^ 2) :=
    (Real.le_sqrt' (by norm_num)).mp (hsep.trans hhell)
  rw [hD] at h19
  have he : Real.exp (-(T / Real.sqrt 2 * (Real.sqrt eps2 - Real.sqrt eps1) ^ 2)) ≤ 8 / 9 := by
    have : (1/3 : ℝ) ^ 2 = 1 / 9 := by norm_num
    linarith
  have hlog : -(T / Real.sqrt 2 * (Real.sqrt eps2 - Real.sqrt eps1) ^ 2) ≤ Real.log (8 / 9) := by
    rw [← Real.log_exp (-(T / Real.sqrt 2 * (Real.sqrt eps2 - Real.sqrt eps1) ^ 2))]
    exact Real.log_le_log (Real.exp_pos _) he
  have hl89 : Real.log (8 / 9) = - Real.log (9 / 8) := by
    rw [show (8 / 9 : ℝ) = (9 / 8)⁻¹ by norm_num, Real.log_inv]
  have key : Real.sqrt 2 * Real.log (9 / 8) ≤ T * (Real.sqrt eps2 - Real.sqrt eps1) ^ 2 := by
    have h3 : Real.log (9 / 8) ≤ T / Real.sqrt 2 * (Real.sqrt eps2 - Real.sqrt eps1) ^ 2 := by linarith
    have h4 := mul_le_mul_of_nonneg_left h3 hr2.le
    have h5 : Real.sqrt 2 * (T / Real.sqrt 2 * (Real.sqrt eps2 - Real.sqrt eps1) ^ 2) =
        T * (Real.sqrt eps2 - Real.sqrt eps1) ^ 2 := by field_simp
    linarith
  have hdiff : eps2 - eps1 = (Real.sqrt eps2 - Real.sqrt eps1) * (Real.sqrt eps2 + Real.sqrt eps1) := by
    have : (Real.sqrt eps2 - Real.sqrt eps1) * (Real.sqrt eps2 + Real.sqrt eps1) =
      Real.sqrt eps2 ^ 2 - Real.sqrt eps1 ^ 2 := by ring
    rw [this, hsq1, hsq2]
  have hpos : 0 < eps2 - eps1 := by linarith
  have hL : 0 ≤ lowerConstant := by
    unfold lowerConstant; exact mul_nonneg hr2.le (Real.log_nonneg (by norm_num))
  have first : lowerConstant * (Real.sqrt eps2 + Real.sqrt eps1) ^ 2 / (eps2 - eps1) ^ 2 ≤ T := by
    rw [div_le_iff₀ (by positivity)]
    unfold lowerConstant
    rw [hdiff]
    calc Real.sqrt 2 * Real.log (9 / 8) * (Real.sqrt eps2 + Real.sqrt eps1) ^ 2
        = (Real.sqrt 2 * Real.log (9 / 8)) * (Real.sqrt eps2 + Real.sqrt eps1) ^ 2 := by ring
      _ ≤ (T * (Real.sqrt eps2 - Real.sqrt eps1) ^ 2) * (Real.sqrt eps2 + Real.sqrt eps1) ^ 2 :=
          mul_le_mul_of_nonneg_right key (sq_nonneg _)
      _ = _ := by ring
  refine ⟨first, le_trans ?_ first⟩
  refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hL) (sq_nonneg _)
  nlinarith


end LindbladTolerant.Testing

end

open LindbladTolerant.Testing in
theorem solution (eps1 eps2 T gamma0 gamma1 : ℝ)
    (heps1 : 0 ≤ eps1) (heps12 : eps1 < eps2) (hT : 0 ≤ T)
    (hgamma0 : gamma0 = eps1 / Real.sqrt 2)
    (hgamma1 : gamma1 = eps2 / Real.sqrt 2)
    (hsep : (1/3 : ℝ) ≤ poissonTV (gamma0 * T) (gamma1 * T))
    (hhell : poissonTV (gamma0 * T) (gamma1 * T) ≤
      Real.sqrt (1 - Real.exp (-(Real.sqrt (gamma1 * T) - Real.sqrt (gamma0 * T))^2))) :
    lowerConstant * (Real.sqrt eps2 + Real.sqrt eps1)^2 / (eps2-eps1)^2 ≤ T ∧
    lowerConstant * eps2 / (eps2-eps1)^2 ≤ T :=
  LindbladTolerant.Testing.dephasing_time_arithmetic eps1 eps2 T gamma0 gamma1 heps1 heps12 hT hgamma0 hgamma1 hsep hhell
