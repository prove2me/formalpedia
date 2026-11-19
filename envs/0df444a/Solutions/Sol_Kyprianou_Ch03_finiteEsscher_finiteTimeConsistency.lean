-- Prove2me | solution 1 for Kyprianou.Ch03.finiteEsscher_finiteTimeConsistency
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T15:51:36.402165+00:00
-- url     : https://prove2.me/submissions/1b9a67a2-9339-408b-9579-9e172a5e9b91

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Definitions.Def_Kyprianou_Ch03_EsscherDensity
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
    (∀ s t : NNReal, s ≤ t →
      ∀ A : Set Omega, MeasurableSet[F s] A →
        (P.withDensity (fun omega =>
          ENNReal.ofReal (esscherDensity X beta k s omega))) A =
        (P.withDensity (fun omega =>
          ENNReal.ofReal (esscherDensity X beta k t omega))) A) := by
  refine fun s t hst A hA => ?_
  have hA0 : MeasurableSet A := (F.le s) A hA
  have hbridge (u : NNReal) :
      (P.withDensity (fun omega : Omega =>
        ENNReal.ofReal (esscherDensity X beta k u omega))) A =
      ENNReal.ofReal (∫ omega, Set.indicator A
        (esscherDensity X beta k u) omega ∂P) := by
    have hpos : ∀ omega : Omega,
        0 ≤ esscherDensity X beta k u omega := by
      intro omega
      exact (Real.exp_pos _).le
    rw [withDensity_apply _ hA0]
    rw [← ofReal_integral_eq_lintegral_ofReal
      ((hDensity u).1.integrableOn)
      (Filter.Eventually.of_forall hpos)]
    congr 1
    exact (integral_indicator hA0).symm
  calc
    (P.withDensity (fun omega : Omega =>
      ENNReal.ofReal (esscherDensity X beta k s omega))) A =
        ENNReal.ofReal (∫ omega, Set.indicator A
          (esscherDensity X beta k s) omega ∂P) := hbridge s
    _ = ENNReal.ofReal (∫ omega, Set.indicator A
          (esscherDensity X beta k t) omega ∂P) := by
      exact congrArg ENNReal.ofReal (hConsistent s t hst A hA).symm
    _ = (P.withDensity (fun omega : Omega =>
          ENNReal.ofReal (esscherDensity X beta k t omega))) A :=
      (hbridge t).symm

