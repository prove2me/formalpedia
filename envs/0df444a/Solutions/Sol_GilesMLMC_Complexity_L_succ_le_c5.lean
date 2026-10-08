-- Prove2me | solution 1 for GilesMLMC.Complexity.L_succ_le_c5
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T19:44:21.544042+00:00
-- url     : https://prove2.me/submissions/d7ed558c-50d0-48e9-a9ae-1cc046f09e27

import Definitions.Def_GilesMLMC_Complexity_Choices
open GilesMLMC.Complexity

theorem solution
    (M : ℕ) (hM : 2 ≤ M) (T : ℝ) (hT : 0 < T)
    (α c₁ ε : ℝ) (hα : 0 < α) (hc₁ : 0 < c₁) (hε : 0 < ε) (hε1 : ε < Real.exp (-1)) :
    ((Lchoice M T α c₁ ε : ℤ) : ℝ) + 1 ≤ c₅ M T α c₁ * Real.log ε⁻¹ := by
  have hm : 1 < (M : ℝ) := by exact_mod_cast (show 1 < M by omega)
  have hd : 0 < α * Real.log (M : ℝ) := mul_pos hα (Real.log_pos hm)
  have hs : 0 < Real.sqrt 2 * c₁ * T ^ α := by positivity
  have he : 1 < Real.log ε⁻¹ := by
    have h := Real.log_lt_log hε hε1
    rw [Real.log_exp] at h
    rw [Real.log_inv]; linarith
  have hh : Real.log (Real.sqrt 2 * c₁ * T ^ α * ε⁻¹) /
      (α * Real.log (M : ℝ)) =
      Real.log (Real.sqrt 2 * c₁ * T ^ α) / (α * Real.log (M : ℝ)) +
      Real.log ε⁻¹ / (α * Real.log (M : ℝ)) := by
    rw [Real.log_mul hs.ne' (inv_ne_zero hε.ne'), add_div]
  have hc := Int.ceil_lt_add_one (Real.log (Real.sqrt 2 * c₁ * T ^ α * ε⁻¹) / (α * Real.log (M : ℝ)))
  change (Lchoice M T α c₁ ε : ℝ) < _ at hc
  rw [hh] at hc
  have hp : 0 ≤ max 0 (Real.log (Real.sqrt 2 * c₁ * T ^ α) / (α * Real.log (M : ℝ))) := le_max_left _ _
  have hb := le_max_right (0 : ℝ) (Real.log (Real.sqrt 2 * c₁ * T ^ α) / (α * Real.log (M : ℝ)))
  have hmul := mul_le_mul_of_nonneg_left he.le hp
  unfold c₅
  simp only [add_mul, one_div, div_eq_mul_inv] at *
  nlinarith

#print axioms solution
