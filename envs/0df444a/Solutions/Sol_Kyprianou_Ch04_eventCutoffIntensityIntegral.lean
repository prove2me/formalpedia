-- Prove2me | solution 1 for Kyprianou.Ch04.eventCutoffIntensityIntegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T23:09:24.155075+00:00
-- url     : https://prove2.me/submissions/917e778e-752f-4b96-8d7d-281d2580ca1a

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
open MeasureTheory Filter LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch04
open scoped Classical

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (levyMeasure : Measure Real) [SigmaFinite levyMeasure]
    (phi : Real -> Real -> Omega -> Real)
    (u t : NNReal) (A : Set Omega) (hA : MeasurableSet A) :
    (∫⁻ omega, (∫⁻ s in Set.Icc (0 : Real) (t : Real),
      (∫⁻ x, ENNReal.ofReal (if (u : Real) < s ∧ omega ∈ A then phi s x omega else 0)
        ∂levyMeasure) ∂volume) ∂P) =
    (∫⁻ omega in A, (∫⁻ s in Set.Ioc (u : Real) (t : Real),
      (∫⁻ x, ENNReal.ofReal (phi s x omega) ∂levyMeasure) ∂volume) ∂P) := by
  classical
  rw [← lintegral_indicator hA]
  apply lintegral_congr
  intro omega
  by_cases hω : omega ∈ A
  · rw [Set.indicator_of_mem hω]
    have hset : Set.Ioi (u : Real) ∩ Set.Icc (0 : Real) (t : Real) =
        Set.Ioc (u : Real) (t : Real) := by
      ext s
      simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Icc, Set.mem_Ioc]
      have hu : (0 : Real) ≤ (u : Real) := NNReal.coe_nonneg u
      constructor
      · exact fun h => ⟨h.1, h.2.2⟩
      · exact fun h => ⟨h.1, le_trans hu h.1.le, h.2⟩
    calc
      _ = ∫⁻ s in Set.Icc (0 : Real) (t : Real),
          (Set.Ioi (u : Real)).indicator
            (fun s => ∫⁻ x, ENNReal.ofReal (phi s x omega) ∂levyMeasure) s ∂volume := by
        apply lintegral_congr
        intro s
        by_cases hs : (u : Real) < s <;> simp [Set.indicator, hs, hω]
      _ = _ := by
        rw [lintegral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi, hset]
  · simp [hω]
