-- Prove2me | solution 1 for Kyprianou.Ch05.positiveDeficitSquaredDensityInjective
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T13:06:44.073475+00:00
-- url     : https://prove2.me/submissions/a210e619-864d-49f2-8ca2-4ed2aa27a911

import Mathlib
import Theorems.Thm_AvramDividend_Classical_withDensity_injective_of_everywhere_pos_finite
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    (mu nu : Measure Real)
    (hm : mu (Set.Iic (0 : Real)) = 0)
    (hn : nu (Set.Iic (0 : Real)) = 0)
    (heq : mu.withDensity (fun x => ENNReal.ofReal ((1 - Real.exp (-x)) ^ 2)) =
      nu.withDensity (fun x => ENNReal.ofReal ((1 - Real.exp (-x)) ^ 2))) :
    mu = nu := by
  let f (x : Real) := ENNReal.ofReal ((1 - Real.exp (-x))^2)
  let g (x : Real) := if 0 < x then f x else 1
  have hg : Measurable g := by
    exact Measurable.ite measurableSet_Ioi (by fun_prop) measurable_const
  have hpos (x : Real) : g x ≠ 0 := by
    by_cases hx : 0 < x
    · have he : Real.exp (-x) < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hx)
      simp only [g, if_pos hx, f]
      exact (ENNReal.ofReal_pos.mpr (sq_pos_of_pos (sub_pos.mpr he))).ne'
    · simp [g, hx]
  have htop (x : Real) : g x ≠ ⊤ := by
    by_cases hx : 0 < x <;> simp [g, hx, f]
  have hp (rho : Measure Real) (h : rho (Set.Iic (0 : Real)) = 0) :
      rho.withDensity g = rho.withDensity f := by
    apply withDensity_congr_ae
    have ha : ∀ᵐ x ∂rho, 0 < x := by
      rw [ae_iff]
      convert h using 2
      ext x
      simp
    filter_upwards [ha] with x hx
    simp [g, hx]
  exact AvramDividend.Classical.withDensity_injective_of_everywhere_pos_finite
    mu nu g hg hpos htop ((hp mu hm).trans (heq.trans (hp nu hn).symm))
