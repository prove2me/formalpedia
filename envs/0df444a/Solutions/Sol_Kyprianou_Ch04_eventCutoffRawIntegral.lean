-- Prove2me | solution 1 for Kyprianou.Ch04.eventCutoffRawIntegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T23:09:11.841015+00:00
-- url     : https://prove2.me/submissions/7228b436-6fe5-4f36-9fd5-ff27bc736a02

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
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0,0,0} P levyMeasure)
    (phi : Real -> Real -> Omega -> Real)
    (u t : NNReal) (A : Set Omega) (hA : MeasurableSet A) :
    (∫⁻ omega, (∫⁻ z in Set.Icc (0 : Real) (t : Real) ×ˢ Set.univ,
      ENNReal.ofReal (if (u : Real) < z.1 ∧ omega ∈ A then phi z.1 z.2 omega else 0)
      ∂(N.N omega)) ∂P) =
    (∫⁻ omega in A, (∫⁻ z in Set.Ioc (u : Real) (t : Real) ×ˢ Set.univ,
      ENNReal.ofReal (phi z.1 z.2 omega) ∂(N.N omega)) ∂P) := by
  classical
  rw [← lintegral_indicator hA]
  apply lintegral_congr
  intro omega
  by_cases hω : omega ∈ A
  · rw [Set.indicator_of_mem hω]
    let B : Set (Real × Real) := Set.Ioi (u : Real) ×ˢ Set.univ
    have hB : MeasurableSet B := measurableSet_Ioi.prod MeasurableSet.univ
    have hset : B ∩ (Set.Icc (0 : Real) (t : Real) ×ˢ Set.univ) =
        Set.Ioc (u : Real) (t : Real) ×ˢ Set.univ := by
      ext z
      simp only [B, Set.mem_inter_iff, Set.mem_prod, Set.mem_univ, and_true, Set.mem_Ioi, Set.mem_Icc, Set.mem_Ioc]
      have hu : (0 : Real) ≤ (u : Real) := NNReal.coe_nonneg u
      constructor
      · exact fun h => ⟨h.1, h.2.2⟩
      · exact fun h => ⟨h.1, le_trans hu h.1.le, h.2⟩
    calc
      _ = ∫⁻ z in Set.Icc (0 : Real) (t : Real) ×ˢ Set.univ,
          B.indicator (fun z => ENNReal.ofReal (phi z.1 z.2 omega)) z ∂(N.N omega) := by
        apply lintegral_congr
        intro z
        by_cases hz : (u : Real) < z.1 <;> simp [B, Set.indicator, hz, hω]
      _ = _ := by rw [lintegral_indicator hB, Measure.restrict_restrict hB, hset]
  · simp [hω]
