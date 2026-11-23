-- Prove2me | solution 2 for Kyprianou.Ch02.prmFiniteWindowDiracLawV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T10:46:15.955699+00:00
-- url     : https://prove2.me/submissions/158ed83d-b6e6-4bcd-9213-c8c22bafdaa3

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch02_prmFiniteRegionAllMeasurableCountNatV1
import Theorems.Thm_Kyprianou_Ch02_integerValuedFiniteDiracV1

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B) (hfinite : ν B < ⊤) :
    ∀ᵐ ω ∂P, ∀ T : ℕ, ∃ s : Finset (ℝ × ℝ),
      (N.N ω).restrict (Set.Ioc (0 : ℝ) (T : ℝ) ×ˢ B) =
        ∑ p ∈ s, ((N.N ω).restrict (Set.Ioc (0 : ℝ) (T : ℝ) ×ˢ B)) {p} • Measure.dirac p := by
  rw [ae_all_iff]
  intro T
  let R : Set (ℝ × ℝ) := Set.Ioc (0 : ℝ) (T : ℝ) ×ˢ B
  have hR : MeasurableSet R := measurableSet_Ioc.prod hB
  have hRfin : LevyStochCalc.Poisson.referenceIntensity ν R ≠ ⊤ := by
    have hvalue : LevyStochCalc.Poisson.referenceIntensity ν R =
        ENNReal.ofReal (T : ℝ) * ν B := by
      rw [LevyStochCalc.Poisson.referenceIntensity, Measure.prod_prod,
        Measure.restrict_apply measurableSet_Ioc]
      congr 1
      have hset : Set.Ioc (0 : ℝ) (T : ℝ) ∩ Set.Ici (0 : ℝ) =
          Set.Ioc (0 : ℝ) (T : ℝ) := by
        ext x
        simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ici,
          and_iff_left_iff_imp]
        exact fun h => h.1.le
      rw [hset, Real.volume_Ioc, sub_zero]
    rw [hvalue]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfinite.ne
  filter_upwards [
    Kyprianou.Ch02.prmFiniteRegionAllMeasurableCountNatV1
      P ν N R hR hRfin] with ω hω
  have hInt : LevyStochCalc.Probability.IsIntegerValued
      ((N.N ω).restrict R) := by
    intro A hA
    rw [Measure.restrict_apply hA]
    exact hω A hA
  obtain ⟨s, hs⟩ :=
    Kyprianou.Ch02.integerValuedFiniteDiracV1 ((N.N ω).restrict R) hInt
  exact ⟨s, hs⟩
