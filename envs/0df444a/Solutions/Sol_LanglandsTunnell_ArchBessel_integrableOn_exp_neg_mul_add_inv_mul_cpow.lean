-- Prove2me | solution 1 for LanglandsTunnell.ArchBessel.integrableOn_exp_neg_mul_add_inv_mul_cpow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/2eaad221-4da0-5df3-adae-6bd94552c049

import Mathlib.Analysis.MellinTransform
import Definitions.Def_LanglandsTunnell_ArchBessel
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_ArchBessel_integrableOn_exp_neg_mul_add_inv_mul_cpow

set_option autoImplicit false

open LanglandsTunnell.ArchBessel

theorem solution (ν : ℂ) (x : ℝ) (hx : 0 < x) :
    MeasureTheory.IntegrableOn
      (fun t : ℝ => (Real.exp (-(x * (t + t⁻¹) / 2)) : ℂ) * ((t : ℂ) ^ (ν - 1))) (Set.Ioi 0) := by
  set a : ℝ := ν.re with ha

  set m : ℕ := ⌈-a⌉₊ + 1 with hm
  have hma : -1 < (m : ℝ) + a - 1 := by
    rw [hm]; have := Nat.le_ceil (-a); push_cast; linarith
  have hx2 : 0 < x / 2 := by linarith

  set C : ℝ := (m.factorial : ℝ) * (2 / x) ^ m with hC
  have hC0 : 0 ≤ C := by positivity
  have hg : MeasureTheory.IntegrableOn (fun t : ℝ => C * (t ^ ((m : ℝ) + a - 1) * Real.exp (-(x / 2) * t ^ (1 : ℝ)))) (Set.Ioi 0) :=
    (integrableOn_rpow_mul_exp_neg_mul_rpow hma one_pos hx2).const_mul C

  have hcont : ContinuousOn (fun t : ℝ => (Real.exp (-(x * (t + t⁻¹) / 2)) : ℂ) * ((t : ℂ) ^ (ν - 1))) (Set.Ioi 0) := by
    intro t ht
    have ht0 : t ≠ 0 := (ne_of_gt ht)
    refine ContinuousAt.continuousWithinAt ?_
    refine ContinuousAt.mul ?_ (Complex.continuousAt_ofReal_cpow_const t (ν - 1) (Or.inr ht0))
    refine Complex.continuous_ofReal.continuousAt.comp ?_
    refine Real.continuous_exp.continuousAt.comp ?_
    exact ((continuousAt_const.mul (continuousAt_id.add (continuousAt_inv₀ ht0))).div_const _).neg
  rw [MeasureTheory.IntegrableOn]
  refine MeasureTheory.Integrable.mono' hg.integrable (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
  refine Filter.Eventually.of_forall fun t (ht : t ∈ Set.Ioi (0 : ℝ)) => ?_
  have ht' : 0 < t := ht

  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Real.abs_exp, Complex.norm_cpow_eq_rpow_re_of_pos ht',
    Complex.sub_re, Complex.one_re, ← ha, Real.rpow_one]

  have hsplit : Real.exp (-(x * (t + t⁻¹) / 2)) = Real.exp (-(x / 2) * t) * Real.exp (-((x / 2) / t)) := by
    rw [← Real.exp_add]; congr 1; field_simp; ring
  have hu : 0 < (x / 2) / t := by positivity
  have hsing : Real.exp (-((x / 2) / t)) ≤ (m.factorial : ℝ) * (2 / x) ^ m * t ^ m := by
    have h1 := Real.pow_div_factorial_le_exp ((x / 2) / t) hu.le m
    have hfac : (0 : ℝ) < m.factorial := by positivity
    rw [div_le_iff₀ hfac] at h1
    rw [Real.exp_neg, inv_le_iff_one_le_mul₀ (Real.exp_pos _)]

    have h2 : ((x / 2) / t) ^ m * ((2 / x) ^ m * t ^ m) = 1 := by
      rw [← mul_pow, ← mul_pow]; rw [show (x / 2) / t * (2 / x * t) = 1 by field_simp]; simp
    calc (1 : ℝ) = ((x / 2) / t) ^ m * ((2 / x) ^ m * t ^ m) := h2.symm
      _ ≤ (Real.exp ((x / 2) / t) * m.factorial) * ((2 / x) ^ m * t ^ m) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = (m.factorial : ℝ) * (2 / x) ^ m * t ^ m * Real.exp ((x / 2) / t) := by ring
  have hpow : t ^ m * t ^ (a - 1) = t ^ ((m : ℝ) + a - 1) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add ht']; congr 1; ring
  rw [hsplit]
  calc Real.exp (-(x / 2) * t) * Real.exp (-((x / 2) / t)) * t ^ (a - 1)
      ≤ Real.exp (-(x / 2) * t) * ((m.factorial : ℝ) * (2 / x) ^ m * t ^ m) * t ^ (a - 1) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsing (Real.exp_pos _).le) ?_
        exact Real.rpow_nonneg ht'.le _
    _ = C * ((t ^ m * t ^ (a - 1)) * Real.exp (-(x / 2) * t)) := by rw [hC]; ring
    _ = C * (t ^ ((m : ℝ) + a - 1) * Real.exp (-(x / 2) * t)) := by rw [hpow]

end S_LanglandsTunnell_ArchBessel_integrableOn_exp_neg_mul_add_inv_mul_cpow
end P2MW
export P2MW.S_LanglandsTunnell_ArchBessel_integrableOn_exp_neg_mul_add_inv_mul_cpow (solution)
