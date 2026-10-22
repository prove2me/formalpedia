-- Prove2me | solution 1 for JHolomorphic.lintegral_ball_segment_le
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-21T20:11:18.610657+00:00
-- url     : https://prove2.me/submissions/bf408f3a-f204-44ca-8214-e4ce10b86d39

import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic



namespace JHolomorphic

open MeasureTheory Metric Filter
open scoped ENNReal

/-- Averages of a nonnegative function over the translates `z + t a`, `t ∈ (0, 1]`, integrated over
`B(c, r)`, are bounded by its integral over `B(c, r + ‖a‖)`. -/
theorem lintegral_ball_segment_le_aux (H : ℂ → ℝ≥0∞) (hH : Measurable H) (a c : ℂ) (r : ℝ) :
    ∫⁻ z in ball c r, ∫⁻ t in Set.Ioc (0:ℝ) 1, H (z + (t:ℂ) * a) ≤
      ∫⁻ w in ball c (r + ‖a‖), H w := by
  have hprod : AEMeasurable (Function.uncurry fun z (t : ℝ) => H (z + (t:ℂ) * a))
      ((volume.restrict (ball c r)).prod (volume.restrict (Set.Ioc (0:ℝ) 1))) :=
    (hH.comp (measurable_fst.add
      ((Complex.measurable_ofReal.comp measurable_snd).mul measurable_const))).aemeasurable
  rw [lintegral_lintegral_swap hprod]
  have hvol : volume (Set.Ioc (0:ℝ) 1) = 1 := by simp
  calc ∫⁻ t in Set.Ioc (0:ℝ) 1, ∫⁻ z in ball c r, H (z + (t:ℂ) * a)
      ≤ ∫⁻ t in Set.Ioc (0:ℝ) 1, ∫⁻ w in ball c (r + ‖a‖), H w := by
        refine setLIntegral_mono' measurableSet_Ioc fun t ht => ?_
        have hmp := measurePreserving_add_right (volume : Measure ℂ) ((t:ℂ) * a)
        have hsub : ball c r ⊆ (· + (t:ℂ) * a) ⁻¹' ball c (r + ‖a‖) := by
          intro z hz
          simp only [Set.mem_preimage, mem_ball] at hz ⊢
          have hta : ‖(t:ℂ) * a‖ ≤ ‖a‖ := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht.1]
            exact mul_le_of_le_one_left (norm_nonneg _) ht.2
          calc dist (z + (t:ℂ) * a) c ≤ dist z c + ‖(t:ℂ) * a‖ := by
                rw [dist_eq_norm, dist_eq_norm, add_sub_right_comm]; exact norm_add_le _ _
            _ < r + ‖a‖ := by linarith
        calc ∫⁻ z in ball c r, H (z + (t:ℂ) * a)
            ≤ ∫⁻ z in (· + (t:ℂ) * a) ⁻¹' ball c (r + ‖a‖), H (z + (t:ℂ) * a) :=
              lintegral_mono_set hsub
          _ = ∫⁻ w in ball c (r + ‖a‖), H w :=
              hmp.setLIntegral_comp_preimage measurableSet_ball hH
    _ = ∫⁻ w in ball c (r + ‖a‖), H w := by
        rw [setLIntegral_const, hvol, mul_one]

end JHolomorphic

open JHolomorphic

open MeasureTheory Metric
open scoped ENNReal

theorem solution (H : ℂ → ℝ≥0∞) (hH : Measurable H) (a c : ℂ) (r : ℝ) :
    ∫⁻ z in ball c r, ∫⁻ t in Set.Ioc (0:ℝ) 1, H (z + (t:ℂ) * a) ≤
      ∫⁻ w in ball c (r + ‖a‖), H w :=
  lintegral_ball_segment_le_aux H hH a c r
