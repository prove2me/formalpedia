-- Prove2me | solution 1 for Kyprianou.Ch04.limitingDrawdown_positiveMeanClassification
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T00:47:16.644775+00:00
-- url     : https://prove2.me/submissions/010b2a8d-0700-49d5-973d-f324a9279504

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_Kyprianou_Ch03_exercise35LaplaceExponentRegularity
import Theorems.Thm_Kyprianou_Ch04_nonpositiveSecantSlopeIff
import Theorems.Thm_Kyprianou_Ch04_zeroSlopeOfPositiveRoot
import Theorems.Thm_Kyprianou_Ch04_nonSingularInfimumTransform
import Theorems.Thm_Kyprianou_Ch04_infimumLimitSupport
import Theorems.Thm_Kyprianou_Ch04_positiveSecantProbabilityFull
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
    (¬ meanNonpositive →
      (P {omega : Omega | BddBelow (Set.range (fun t : NNReal => L.X t omega))}).toReal = 1) := by
  intro m mean hmean
  let : IsProbabilityMeasure P := L.isProbability
  obtain ⟨hzero,_,hconv,_,_⟩ := Kyprianou.Ch03.exercise35LaplaceExponentRegularity P F L
  have hiff : mean ↔ m = 0 := Kyprianou.Ch04.nonpositiveSecantSlopeIff L.ψ hconv hzero
  have hm : 0 < m := lt_of_le_of_ne (le_max_left _ _) (fun e => hmean (hiff.2 e.symm))
  let B : Set Omega := {w | BddBelow (range (fun t : NNReal => L.X t w))}
  have hB : P B ≤ 1 := by simpa using (measure_mono (μ := P) (subset_univ B))
  have hp1 : (P B).toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top hB
  apply Kyprianou.Ch04.positiveSecantProbabilityFull L.ψ (P B).toReal ENNReal.toReal_nonneg hp1 hm
  intro beta hb
  have hn : L.ψ beta ≠ 0 := fun hz => hm.ne' (Kyprianou.Ch04.zeroSlopeOfPositiveRoot L.ψ beta hb hz)
  have hlim := Kyprianou.Ch04.nonSingularInfimumTransform P F L hNotNegativeSubordinator beta hb hn
  exact (Kyprianou.Ch04.infimumLimitSupport P F L beta hb).2.1 _ hlim
