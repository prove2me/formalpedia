-- Prove2me | solution 1 for Kyprianou.Ch03.nonnegativeIndicatorIntegralOfRealV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T23:14:47.517396+00:00
-- url     : https://prove2.me/submissions/19b470e7-f919-4f6b-97c4-336df95dbb39

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
    (P : Measure Ω) (f : Ω → ℝ) (A : Set Ω)
    (hA : MeasurableSet A) (hi : Integrable f P) (hn : ∀ w, 0 ≤ f w) :
    ENNReal.ofReal (∫ w, A.indicator f w ∂P) =
      ∫⁻ w, A.indicator (fun w => ENNReal.ofReal (f w)) w ∂P := by
  rw [ofReal_integral_eq_lintegral_ofReal (hi.indicator hA)
    (ae_of_all _ fun w => Set.indicator_nonneg (fun x _ => hn x) w)]
  apply lintegral_congr
  intro w
  by_cases hw : w ∈ A <;> simp [hw]
