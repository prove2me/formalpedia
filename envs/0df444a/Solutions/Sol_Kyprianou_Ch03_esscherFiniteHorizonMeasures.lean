-- Prove2me | solution 1 for Kyprianou.Ch03.esscherFiniteHorizonMeasures
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T14:58:42.384218+00:00
-- url     : https://prove2.me/submissions/031a7084-3601-4044-81fb-b5c87218afbe

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Definitions.Def_Kyprianou_Ch03_EsscherDensity
import Theorems.Thm_Kyprianou_Ch03_finiteEsscher_probabilityNormalization
import Theorems.Thm_Kyprianou_Ch03_finiteEsscher_finiteTimeConsistency
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
        ENNReal.ofReal (esscherDensity X beta k t omega)) Set.univ = 1) ∧
    (∀ s t : NNReal, s ≤ t →
      ∀ A : Set Omega, MeasurableSet[F s] A →
        (P.withDensity (fun omega =>
          ENNReal.ofReal (esscherDensity X beta k s omega))) A =
        (P.withDensity (fun omega =>
          ENNReal.ofReal (esscherDensity X beta k t omega))) A) := by
  exact ⟨
    Kyprianou.Ch03.finiteEsscher_probabilityNormalization P F X hX hNatural beta k hDensity hConsistent,
    Kyprianou.Ch03.finiteEsscher_finiteTimeConsistency P F X hX hNatural beta k hDensity hConsistent
  ⟩

