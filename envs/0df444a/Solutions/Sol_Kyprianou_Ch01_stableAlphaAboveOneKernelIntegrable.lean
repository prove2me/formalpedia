-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaAboveOneKernelIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T00:32:03.642009+00:00
-- url     : https://prove2.me/submissions/b0177b41-128c-4f71-a3a3-3dacfebe0795

import Mathlib
import Mathlib.Tactic.FunProp
import Theorems.Thm_Kyprianou_Ch01_stableGammaPowerEnvelopeIntegrable
import Theorems.Thm_Kyprianou_Ch01_stableAlphaAboveOneKernelEnvelopeBound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Complex Real Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Stable compensated Fourier kernel integrability by a sharp two-power majorant. -/
theorem solution (alpha : ℝ) (ha1 : 1 < alpha) (ha2 : alpha < 2) :
    IntegrableOn
      (fun r : ℝ =>
        (Complex.exp (Complex.I * (r : ℂ)) - 1 -
          Complex.I * (r : ℂ)) /
            ((((r : ℝ) ^ (alpha + 1)) : ℝ) : ℂ))
      (Set.Ioi (0 : ℝ)) := by
  have henv0 := Kyprianou.Ch01.stableGammaPowerEnvelopeIntegrable
    (alpha - 1) (1 / 2) (by linarith) (by linarith)
      (by norm_num : (0 : ℝ) < 1 / 2)
  have henv : IntegrableOn
      (fun r : ℝ => if r ≤ 1 then r ^ (1 - alpha)
        else 2 * r ^ (-alpha)) (Set.Ioi (0 : ℝ)) := by
    have hscaled : IntegrableOn
        (fun r : ℝ => 2 * (if r ≤ 1 then
          (1 / 2 : ℝ) * r ^ (-(alpha - 1))
          else r ^ (-(alpha - 1) - 1)))
        (Set.Ioi (0 : ℝ)) := henv0.const_mul 2
    refine hscaled.congr_fun (fun r hr => ?_) measurableSet_Ioi
    by_cases h : r ≤ 1
    · simp [h, show -(alpha - 1) = 1 - alpha by ring]
    · simp [h, show -(alpha - 1) - 1 = -alpha by ring]
  apply Integrable.mono' henv
  · have hnum : Continuous
        (fun r : ℝ =>
          Complex.exp (Complex.I * (r : ℂ)) - 1 -
            Complex.I * (r : ℂ)) := by fun_prop
    have hreal : ContinuousOn
        (fun r : ℝ => r ^ (alpha + 1)) (Set.Ioi (0 : ℝ)) :=
      continuousOn_id.rpow_const
        (fun r hr => Or.inl (ne_of_gt hr))
    have hden : ContinuousOn
        (fun r : ℝ => (((r ^ (alpha + 1) : ℝ)) : ℂ))
        (Set.Ioi (0 : ℝ)) :=
      Complex.continuous_ofReal.comp_continuousOn hreal
    have hcon : ContinuousOn
        (fun r : ℝ =>
          (Complex.exp (Complex.I * (r : ℂ)) - 1 -
            Complex.I * (r : ℂ)) /
              ((((r : ℝ) ^ (alpha + 1)) : ℝ) : ℂ))
        (Set.Ioi (0 : ℝ)) :=
      hnum.continuousOn.div hden
        (fun r hr => by
          exact_mod_cast
            (Real.rpow_pos_of_pos hr (alpha + 1)).ne')
    exact hcon.aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact Kyprianou.Ch01.stableAlphaAboveOneKernelEnvelopeBound alpha r hr
