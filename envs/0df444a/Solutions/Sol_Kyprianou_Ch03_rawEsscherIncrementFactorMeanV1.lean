-- Prove2me | solution 1 for Kyprianou.Ch03.rawEsscherIncrementFactorMeanV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T23:14:09.769906+00:00
-- url     : https://prove2.me/submissions/9ea3e6f3-b75f-4dc7-a916-42b63cf2dd0d

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_EsscherDensity
import Definitions.Def_PerfCorrMSQ_NaturalFiltration

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch03

theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : NNReal → Ω → ℝ) (hX : IsLevyProcess X P)
    (beta : ℝ) (hm : ∀ t, Measurable (X t)) (k : ℝ)
    (hunit : ∀ t : NNReal, Integrable (esscherDensity X beta k t) P ∧
      (∫ w, esscherDensity X beta k t w ∂P) = 1)
    (s t : NNReal) (hst : s ≤ t) :
    (∫⁻ w, ENNReal.ofReal (Real.exp (beta * (X t w - X s w) -
      k * ((t - s : NNReal) : ℝ))) ∂P) = 1 := by
  let Z : NNReal → Ω → ℝ≥0∞ := fun u w => ENNReal.ofReal (esscherDensity X beta k u w)
  let W : ℝ → ℝ≥0∞ := fun y => ENNReal.ofReal (Real.exp (beta * y - k * ((t - s : NNReal) : ℝ)))
  have hW : Measurable W := by fun_prop
  have hstat := hX.stationary_increments s (t - s)
  rw [add_tsub_cancel_of_le hst] at hstat
  change IdentDistrib (fun w => X t w - X s w) (fun w => X (t - s) w - X 0 w) P P at hstat
  simp only [hX.start_zero, sub_zero] at hstat
  have hWI : ∫⁻ w, W (X t w - X s w) ∂P = 1 := by
    change ∫⁻ w, (W ∘ fun w => X t w - X s w) w ∂P = 1
    rw [(hstat.comp hW).lintegral_eq]
    change ∫⁻ w, Z (t - s) w ∂P = 1
    rw [← ofReal_integral_eq_lintegral_ofReal (hunit (t - s)).1
      (ae_of_all _ fun w => (Real.exp_pos _).le), (hunit (t - s)).2, ENNReal.ofReal_one]
  exact hWI
