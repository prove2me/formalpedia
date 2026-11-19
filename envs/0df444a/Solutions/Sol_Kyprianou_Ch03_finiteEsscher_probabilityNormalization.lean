-- Prove2me | solution 1 for Kyprianou.Ch03.finiteEsscher_probabilityNormalization
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T15:41:17.289099+00:00
-- url     : https://prove2.me/submissions/24518882-765d-40a7-8eb6-7387da6f1ed7

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Definitions.Def_Kyprianou_Ch03_EsscherDensity
import Theorems.Thm_AppliedSDE_SarkkaSolin_unit_mean_density_is_probability
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou.Ch03

theorem solution
{Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal → Omega → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hNatural : IsCompletedNaturalFiltration P X F)
    (beta k : ℝ)
    (hDensity : ∀ t : NNReal,
      Integrable (esscherDensity X beta k t) P ∧
      (∫ omega, esscherDensity X beta k t omega ∂P) = 1)
    (hConsistent : ∀ s t : NNReal, s ≤ t →
      ∀ A : Set Omega, MeasurableSet[F s] A →
        (∫ omega, Set.indicator A (esscherDensity X beta k t) omega ∂P) =
        (∫ omega, Set.indicator A (esscherDensity X beta k s) omega ∂P)) :
    (∀ t : NNReal,
      P.withDensity (fun omega =>
        ENNReal.ofReal (esscherDensity X beta k t omega)) Set.univ = 1) := by
  intro t
  have hZ (omega : Omega) :
      0 ≤ esscherDensity X beta k t omega :=
    (Real.exp_pos _).le
  haveI hProb : IsProbabilityMeasure
      (P.withDensity (fun omega : Omega =>
        ENNReal.ofReal (esscherDensity X beta k t omega))) :=
    AppliedSDE.SarkkaSolin.unit_mean_density_is_probability P
      (esscherDensity X beta k t) (hDensity t).1 hZ (hDensity t).2
  exact measure_univ
