-- Prove2me | solution 1 for Kyprianou.Ch04.limitingDrawdown_nonpositiveMeanClassification
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T00:47:16.346864+00:00
-- url     : https://prove2.me/submissions/19a28350-a972-4abd-b834-62622ba7f30e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_Kyprianou_Ch03_exercise35LaplaceExponentRegularity
import Theorems.Thm_Kyprianou_Ch04_nonpositiveSecantSlopeIff
import Theorems.Thm_Kyprianou_Ch04_nonpositiveSlopeLowerUnbounded
import Theorems.Thm_Kyprianou_Ch04_infimumLimitSupport
import Theorems.Thm_Kyprianou_Ch04_limitingDrawdown_positiveMeanClassification
open MeasureTheory AvramDividend.Classical Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hNotNegativeSubordinator :
      ¬ (∀ᵐ omega : Omega ∂P, Antitone (fun t : NNReal => L.X t omega))) :
    let nonnegativeSlope : Real :=
      max 0 (sInf ((fun theta : Real => L.ψ theta / theta) '' Set.Ioi 0))
    let meanNonpositive : Prop :=
      forall epsilon : Real, 0 < epsilon ->
        exists theta : Real, 0 < theta ∧ L.ψ theta < epsilon * theta
    (meanNonpositive ↔
      (P {omega : Omega | ¬ BddBelow (Set.range (fun t : NNReal => L.X t omega))}).toReal = 1) := by
  intro m mean
  let : IsProbabilityMeasure P := L.isProbability
  obtain ⟨hzero,_,hconv,_,_⟩ := Kyprianou.Ch03.exercise35LaplaceExponentRegularity P F L
  have hiff : mean ↔ m = 0 := Kyprianou.Ch04.nonpositiveSecantSlopeIff L.ψ hconv hzero
  let B : Set Omega := {w | BddBelow (range (fun t : NNReal => L.X t w))}
  have hBm : MeasurableSet B := (Kyprianou.Ch04.infimumLimitSupport P F L 1 (by norm_num)).1
  have hcomp : P Bᶜ = 1 - P B := by
    rw [measure_compl hBm (measure_ne_top P B),measure_univ]
  change mean ↔ (P Bᶜ).toReal = 1
  constructor
  · intro h
    have hB := Kyprianou.Ch04.nonpositiveSlopeLowerUnbounded P F L hNotNegativeSubordinator (hiff.1 h)
    rw [hcomp,hB,tsub_zero,ENNReal.toReal_one]
  · intro h
    by_contra hn
    have hp : (P B).toReal = 1 := Kyprianou.Ch04.limitingDrawdown_positiveMeanClassification P F L hNotNegativeSubordinator hn
    have hp' := ENNReal.ofReal_toReal (measure_ne_top P B)
    rw [hp,ENNReal.ofReal_one] at hp'
    rw [hcomp,← hp',tsub_self,ENNReal.toReal_zero] at h
    norm_num at h
