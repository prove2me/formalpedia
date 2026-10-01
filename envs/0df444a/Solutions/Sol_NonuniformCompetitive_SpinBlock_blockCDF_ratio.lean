-- Prove2me | solution 1 for NonuniformCompetitive.SpinBlock.blockCDF_ratio
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T14:29:03.145423+00:00
-- url     : https://prove2.me/submissions/51f2c156-8c94-40f5-890d-d04211638f20

import Definitions.Def_NonuniformCompetitive_SpinBlock_blockCDF

open NonuniformCompetitive.SpinBlock MeasureTheory Set
open scoped Interval
namespace SpinProof

theorem denom_pos : 0 < Real.exp 1-1 := by
  have := Real.one_lt_exp_iff.mpr (show (0:ℝ)<1 by norm_num)
  linarith

theorem cdf_continuous (C : ℝ) (hC : 0 < C) : Continuous (blockCDF C) := by
  apply continuous_if_le continuous_id continuous_const (by fun_prop) continuous_const.continuousOn
  intro x hx
  change x=C at hx
  subst x
  simp [hC.ne',denom_pos.ne']

theorem cdf_integral_low (C τ : ℝ) (hC : 0 < C) (hτ : 0 ≤ τ) (hτC : τ ≤ C) :
    ∫ t in (0:ℝ)..τ, (1-blockCDF C t) =
      Real.exp 1/(Real.exp 1-1)*τ-C*(Real.exp (τ/C)-1)/(Real.exp 1-1) := by
  let F : ℝ → ℝ := fun t => Real.exp 1/(Real.exp 1-1)*t-C*(Real.exp (t/C)-1)/(Real.exp 1-1)
  have hd (t : ℝ) : HasDerivAt F (1-(Real.exp (t/C)-1)/(Real.exp 1-1)) t := by
    have h := ((hasDerivAt_id t).div_const C).exp
    have hh := ((hasDerivAt_id t).const_mul (Real.exp 1/(Real.exp 1-1))).sub
      (((h.sub_const 1).const_mul C).div_const (Real.exp 1-1))
    simp only [id_eq,mul_one] at hh
    convert hh using 1 <;> try rfl
    all_goals field_simp [hC.ne',denom_pos.ne'] <;> ring
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t (_ : t ∈ uIcc (0:ℝ) τ) => hd t)
    (show IntervalIntegrable (fun t => 1-(Real.exp (t/C)-1)/(Real.exp 1-1)) volume 0 τ from
      (by fun_prop : Continuous (fun t : ℝ => 1-(Real.exp (t/C)-1)/(Real.exp 1-1))).intervalIntegrable _ _)
  calc
    _ = ∫ t in (0:ℝ)..τ, (1-(Real.exp (t/C)-1)/(Real.exp 1-1)) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hτ] at ht
      simp [blockCDF,le_trans ht.2 hτC]
    _ = _ := by simpa [F] using he

theorem cdf_ratio (C τ : ℝ) (hC : 0 < C) (hτ : 0 ≤ τ) :
    blockCDF C τ*C + ∫ t in (0:ℝ)..τ, (1-blockCDF C t) =
      Real.exp 1/(Real.exp 1-1)*min τ C := by
  by_cases ht : τ ≤ C
  · rw [min_eq_left ht,cdf_integral_low C τ hC hτ ht]
    simp only [blockCDF,if_pos ht]
    ring
  · have hCt : C ≤ τ := le_of_lt (not_le.mp ht)
    have hcont : Continuous (fun t => 1-blockCDF C t) := continuous_const.sub (cdf_continuous C hC)
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable 0 C) (hcont.intervalIntegrable C τ)]
    have hi : ∫ t in C..τ, (1-blockCDF C t) = 0 := by
      apply intervalIntegral.integral_zero_ae
      filter_upwards with t
      intro hmem
      rw [uIoc_of_le hCt] at hmem
      simp [blockCDF,not_le.mpr hmem.1]
    rw [hi,cdf_integral_low C C hC hC.le le_rfl,min_eq_right hCt]
    simp [blockCDF,ht,hC.ne']
    field_simp [denom_pos.ne']
    ring

end SpinProof

open NonuniformCompetitive.SpinBlock
theorem solution (C : ℝ) (hC : 0 < C) (τ : ℝ) (hτ : 0 ≤ τ) :
    blockCDF C τ*C + ∫ t in (0:ℝ)..τ, (1-blockCDF C t) ≤
      Real.exp 1/(Real.exp 1-1)*min τ C :=
  (SpinProof.cdf_ratio C τ hC hτ).le
