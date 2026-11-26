-- Prove2me | solution 1 for Kyprianou.Ch05.subordinator_zero_of_unitLaplace
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T16:19:24.47354+00:00
-- url     : https://prove2.me/submissions/b9ef8488-8530-4866-9921-5ab7e2566581

import Definitions.Def_Kyprianou_Ch05_ExponentialPassageMoments
import Mathlib
import Theorems.Thm_Kyprianou_Ch01_aeEqOneOfIntegrableLeOneMeanOneV1
import Theorems.Thm_Kyprianou_Ch05_levyCoordinateMeasurableCompletion
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_Kyprianou_Ch05_WeakPassageObservables
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05
open Classical
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y : NNReal → Omega → Real)
    (hLevy : ProbabilityTheory.IsLevyProcess Y P)
    (hMono : ∀ᵐ w ∂P, Monotone (fun t : NNReal => Y t w))
    (beta : Real) (hb : 0 < beta)
    (hMean : ∀ n : ℕ, (∫ w, Real.exp (-beta * Y (n : NNReal) w) ∂P) = 1) :
    ∀ᵐ w ∂P, ∀ t : NNReal, Y t w = 0 := by
  have hN (n : ℕ) : ∀ᵐ w ∂P, Y (n : NNReal) w = 0 := by
    have hc : NullMeasurable (Y (n : NNReal)) P :=
      levyCoordinateMeasurableCompletion P Y hLevy (n : NNReal)
    let f (w : Omega) := Real.exp (-beta * Y (n : NNReal) w)
    have hle : ∀ᵐ w ∂P, f w ≤ 1 := by
      filter_upwards [hMono] with w hw
      have hz := hw (show 0 ≤ (n : NNReal) from bot_le)
      change Y 0 w ≤ Y (n : NNReal) w at hz
      rw [hLevy.start_zero] at hz
      exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr hb.le) hz)
    have hi : Integrable f P := by
      apply (integrable_const (1 : Real)).mono'
        (Real.continuous_exp.measurable.comp_aemeasurable
          (aemeasurable_const.mul hc.aemeasurable)).aestronglyMeasurable
      filter_upwards [hle] with w hw
      simpa [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le, f] using hw
    filter_upwards [Kyprianou.Ch01.aeEqOneOfIntegrableLeOneMeanOneV1 P f hi hle
      (hMean n)] with w hw
    have he : -beta * Y (n : NNReal) w = 0 := Real.exp_injective (hw.trans Real.exp_zero.symm)
    exact (mul_eq_zero.mp he).resolve_left (neg_ne_zero.mpr hb.ne')
  have hAll : ∀ᵐ w ∂P, ∀ n : ℕ, Y (n : NNReal) w = 0 := ae_all_iff.mpr hN
  filter_upwards [hAll, hMono] with w hw hm t
  obtain ⟨n, hn⟩ := exists_nat_ge t
  apply le_antisymm
  · exact (hm hn).trans (hw n).le
  · have h := hm (show 0 ≤ t from bot_le)
    change Y 0 w ≤ Y t w at h
    simpa [hLevy.start_zero] using h
