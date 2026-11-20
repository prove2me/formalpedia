-- Prove2me | solution 1 for Kyprianou.Ch01.stableAboveOneTailComplexIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T23:43:51.408222+00:00
-- url     : https://prove2.me/submissions/41f96d7c-ebc8-41ea-9867-080b6b9abb7c

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableAlphaAboveOneLargeJumpPowerIntegrable
open MeasureTheory Set Real Complex
set_option autoImplicit false

theorem solution
    (alpha : ℝ) (ha1 : 1 < alpha) (ha2 : alpha < 2) :
    IntegrableOn
      (fun r : ℝ => if r < 1 then (0 : ℂ) else
        (((r ^ (-alpha) : ℝ) : ℂ)))
      (Set.Ioi (0 : ℝ)) := by
  have hreal :=
    Kyprianou.Ch01.stableAlphaAboveOneLargeJumpPowerIntegrable
      alpha ha1 ha2
  have hcomplex : IntegrableOn
      (fun r : ℝ => (((r ^ (-alpha) : ℝ) : ℂ)))
      (Set.Ioi (1 : ℝ)) := by
    simpa only [IntegrableOn, Complex.ofRealCLM_apply] using
      Complex.ofRealCLM.integrable_comp hreal
  have hci : IntegrableOn
      (fun r : ℝ => (((r ^ (-alpha) : ℝ) : ℂ)))
      (Set.Ici (1 : ℝ)) :=
    hcomplex.congr_set_ae
      (MeasureTheory.Ioi_ae_eq_Ici (μ := volume)).symm
  have hrest : Integrable
      (fun r : ℝ => (((r ^ (-alpha) : ℝ) : ℂ)))
      ((volume.restrict (Set.Ioi (0 : ℝ))).restrict
        (Set.Ici (1 : ℝ))) := by
    rw [Measure.restrict_restrict measurableSet_Ici]
    have hset : Set.Ici (1 : ℝ) ∩ Set.Ioi (0 : ℝ) =
        Set.Ici (1 : ℝ) := by
      ext r
      simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ici]
      constructor
      · intro h; exact h.1
      · intro h; exact ⟨h, lt_of_lt_of_le zero_lt_one h⟩
    rw [hset]
    exact hci
  have hind :
      Integrable
        ((Set.Ici (1 : ℝ)).indicator
          (fun r : ℝ => (((r ^ (-alpha) : ℝ) : ℂ))))
        (volume.restrict (Set.Ioi (0 : ℝ))) :=
    (integrable_indicator_iff measurableSet_Ici).2 hrest
  apply (IntegrableOn.congr_fun hind ?_ measurableSet_Ioi)
  intro r hr
  by_cases h : r < 1
  · simp [Set.indicator, h, Set.mem_Ici, le_of_lt h]
  · simp [Set.indicator, h, Set.mem_Ici, le_of_not_gt h]
