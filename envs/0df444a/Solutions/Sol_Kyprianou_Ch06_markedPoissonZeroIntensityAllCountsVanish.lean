-- Prove2me | solution 1 for Kyprianou.Ch06.markedPoissonZeroIntensityAllCountsVanish
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T07:50:32.639174+00:00
-- url     : https://prove2.me/submissions/a7ff0298-ad0c-489e-9216-11ebe16b6c1b

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_markedPoissonMarginalCountLaw
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (n : Measure E) (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (A : Set E) (hA : MeasurableSet A) (hZero : n A = 0) :
  ∀ᵐ omega ∂P, ∀ t : NNReal, N omega t A = 0 := by
  have hnat : ∀ m : Nat, ∀ᵐ omega ∂P,
      N omega (m : NNReal) A = 0 := by
    intro m
    have hfinite : n A < ⊤ := by simp [hZero]
    have hprob : P {omega | N omega (m : NNReal) A = 0} = 1 := by
      have h := Kyprianou.Ch06.markedPoissonMarginalCountLaw
        P n N hPPP (m : NNReal) A hA hfinite 0
      simpa [hZero, ProbabilityTheory.poissonMeasure_singleton] using h
    have hmeas : MeasurableSet {omega | N omega (m : NNReal) A = 0} := by
      have hnmeas := hPPP.1 (m : NNReal) A hA
      exact hnmeas (measurableSet_singleton 0)
    exact (MeasureTheory.mem_ae_iff_prob_eq_one hmeas).2 hprob
  have hnatall : ∀ᵐ omega ∂P,
      ∀ m : Nat, N omega (m : NNReal) A = 0 := by
    exact ae_all_iff.mpr hnat
  filter_upwards [hnatall, hPPP.2.1] with omega hz hm
  intro t
  obtain ⟨m, hlt⟩ := exists_nat_gt t
  have hle : N omega t A ≤ N omega (m : NNReal) A :=
    hm.2.2 A (le_of_lt hlt)
  exact Nat.eq_zero_of_le_zero (by simpa [hz m] using hle)
