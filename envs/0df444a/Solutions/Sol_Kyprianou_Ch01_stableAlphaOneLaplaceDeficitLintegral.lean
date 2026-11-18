-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaOneLaplaceDeficitLintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T09:31:50.292943+00:00
-- url     : https://prove2.me/submissions/798fe532-f14f-4d8e-b747-314b6b862f37

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneLaplaceCosineDeficit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Real Set
open scoped ENNReal
set_option autoImplicit false
/-! The positive Laplace-cosine-deficit kernel as an extended nonnegative integral. -/
theorem solution
    (a : ℝ) (ha : 0 < a) :
    (∫⁻ x in Set.Ioi (0 : ℝ),
      ENNReal.ofReal (a * Real.exp (-(a * x)) * (1 - Real.cos x))) =
      ENNReal.ofReal ((1 + a ^ 2)⁻¹) := by
  have hExp : IntegrableOn
      (fun x : ℝ => Real.exp (-(a * x))) (Ioi (0 : ℝ)) := by
    simpa only [neg_mul] using
      (integrableOn_exp_mul_Ioi (a := -a) (by linarith) 0)
  have hDom : IntegrableOn
      (fun x : ℝ => (2 * a) * Real.exp (-(a * x)))
      (Ioi (0 : ℝ)) := hExp.const_mul (2 * a)
  have hge (x : ℝ) :
      0 ≤ a * Real.exp (-(a * x)) * (1 - Real.cos x) := by
    exact mul_nonneg (mul_nonneg ha.le (Real.exp_pos _).le)
      (sub_nonneg.mpr (Real.cos_le_one x))
  have hInt : IntegrableOn
      (fun x : ℝ => a * Real.exp (-(a * x)) * (1 - Real.cos x))
      (Ioi (0 : ℝ)) := by
    apply hDom.mono'
    · have hm : Measurable
        (fun x : ℝ => a * Real.exp (-(a * x)) * (1 - Real.cos x)) := by
        fun_prop
      exact hm.aestronglyMeasurable
    · filter_upwards [] with x
      rw [Real.norm_eq_abs, abs_of_nonneg (hge x)]

      calc
        a * Real.exp (-(a * x)) * (1 - Real.cos x) ≤
            (a * Real.exp (-(a * x))) * 2 :=
          mul_le_mul_of_nonneg_left
            (by linarith [Real.neg_one_le_cos x])
            (mul_nonneg ha.le (Real.exp_pos _).le)
        _ = (2 * a) * Real.exp (-(a * x)) := by ring
  have hn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun x : ℝ => a * Real.exp (-(a * x)) * (1 - Real.cos x)) := by
    filter_upwards [] with x
    exact hge x
  calc
    (∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal
      (a * Real.exp (-(a * x)) * (1 - Real.cos x))) =
      ENNReal.ofReal (∫ x in Ioi (0 : ℝ),
        a * Real.exp (-(a * x)) * (1 - Real.cos x)) :=
          (ofReal_integral_eq_lintegral_ofReal hInt hn).symm
    _ = ENNReal.ofReal ((1 + a ^ 2)⁻¹) := by
      rw [Kyprianou.Ch01.stableAlphaOneLaplaceCosineDeficit a ha]
