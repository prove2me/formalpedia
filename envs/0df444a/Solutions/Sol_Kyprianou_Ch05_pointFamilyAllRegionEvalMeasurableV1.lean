-- Prove2me | solution 1 for Kyprianou.Ch05.pointFamilyAllRegionEvalMeasurableV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T15:52:24.366733+00:00
-- url     : https://prove2.me/submissions/9f2b2b34-fe94-4f82-9191-043ce6a23c5c

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonFiltration
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    {Ω E : Type} [MeasurableSpace E]
    (m : Measure E) [SigmaFinite m]
    (K : ℕ → Ω → ℕ) (Z : ℕ → ℕ → Ω → E)
    (R C : Set E) (hC : MeasurableSet C) (hCR : C ⊆ R) :
    Measurable[prmEvalSigma K Z m R]
      (fun w => poissonRandomMeasure K Z w C) := by
  let D : ℕ → Set E := fun n => C ∩ spanningSets m n
  have hD : Monotone D := fun i j hij => fun x hx => ⟨hx.1, spanningSets_mono (μ := m) hij hx.2⟩
  have hU : (⋃ n, D n) = C := by
    simp only [D,← inter_iUnion,iUnion_spanningSets,inter_univ]
  have hEq (w : Ω) : poissonRandomMeasure K Z w C =
      ⨆ n, poissonRandomMeasure K Z w (D n) := by
    rw [← hU]
    exact hD.measure_iUnion
  simp_rw [hEq]
  apply Measurable.iSup
  intro n
  exact measurable_prmEvalSigma_apply (hC.inter (measurableSet_spanningSets m n))
    (inter_subset_left.trans hCR)
    ((measure_mono inter_subset_right).trans_lt (measure_spanningSets_lt_top m n))
