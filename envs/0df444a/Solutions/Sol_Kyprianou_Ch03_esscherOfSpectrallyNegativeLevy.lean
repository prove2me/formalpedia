-- Prove2me | solution 1 for Kyprianou.Ch03.esscherOfSpectrallyNegativeLevy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T15:13:09.854601+00:00
-- url     : https://prove2.me/submissions/3cc8e37c-4d92-4217-b763-92cbef0e22b1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EsscherDensity
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Theorems.Thm_Kyprianou_Ch03_esscherSpectralWitness_constructed
import Theorems.Thm_Kyprianou_Ch03_esscherSpectralWitness_property1
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch03

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P Q : Measure Omega) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hNatural : IsCompletedNaturalFiltration P L.X F)
    (beta : Real) (hBeta : 0 <= beta)
    (hEsscher : forall (t : NNReal) (A : Set Omega),
      MeasurableSet[F t] A ->
      Q A =
        ENNReal.ofReal
          (∫ omega, Set.indicator A
            (fun omega : Omega =>
              esscherDensity L.X beta (L.ψ beta) t omega)
            omega ∂P)) :
    exists (Lbeta : AvramDividend.Classical.SpectrallyNegativeLevy Q F),
      Lbeta.X = L.X ∧
      Lbeta.σ = L.σ ∧
      Lbeta.ν = L.ν.withDensity
        (fun x : Real => ENNReal.ofReal (Real.exp (beta * x))) ∧
      Lbeta.c = L.c + beta * L.σ ^ 2 +
        (∫ x in {x : Real | abs x < 1},
          (Real.exp (beta * x) - 1) * x ∂L.ν) ∧
      forall theta : Real, -beta <= theta ->
        Lbeta.ψ theta = L.ψ (theta + beta) - L.ψ beta := by
  rcases Kyprianou.Ch03.esscherSpectralWitness_constructed P Q F L hNatural beta hBeta hEsscher with ⟨Lbeta, h1, h2, h3, h4⟩
  have hparams : (Lbeta.X = L.X ∧ Lbeta.σ = L.σ ∧ Lbeta.ν = L.ν.withDensity
        (fun x : Real => ENNReal.ofReal (Real.exp (beta * x))) ∧ Lbeta.c = L.c + beta * L.σ ^ 2 +
        (∫ x in {x : Real | abs x < 1},
          (Real.exp (beta * x) - 1) * x ∂L.ν)) := ⟨h1, h2, h3, h4⟩
  refine ⟨Lbeta, h1, h2, h3, h4, ?_⟩
  · exact Kyprianou.Ch03.esscherSpectralWitness_property1 P Q F L hNatural beta hBeta hEsscher Lbeta hparams

