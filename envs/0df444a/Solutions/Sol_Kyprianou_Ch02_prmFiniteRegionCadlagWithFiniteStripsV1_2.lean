-- Prove2me | solution 2 for Kyprianou.Ch02.prmFiniteRegionCadlagWithFiniteStripsV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T10:53:40.935359+00:00
-- url     : https://prove2.me/submissions/7af78b13-75b2-402b-a373-3bc612fb7915

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch02_prmFiniteRegionAllMeasurableCountNatV1
import Theorems.Thm_Kyprianou_Ch02_integerValuedFiniteSupportV1
import Theorems.Thm_Kyprianou_Ch02_finiteRegionPoissonCadlagFromFiniteSupportV2

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B) (hfinite : ν B < ⊤)
    (hCount : ∀ᵐ ω ∂P, ∀ n : ℕ, ∃ k : ℕ,
      N.N ω (Set.Ico (n : ℝ) (n + 1) ×ˢ B) = k) :
    ∀ᵐ ω ∂P, IsCadlag (fun (t : ℝ≥0) =>
      ∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B), z.2 ∂(N.N ω)) := by
  have hSupport : ∀ᵐ ω ∂P, ∀ T : ℕ, ∃ s : Finset (ℝ × ℝ),
      N.N ω ((Set.Ioc (0 : ℝ) (T : ℝ) ×ˢ B) \ (s : Set (ℝ × ℝ))) = 0 := by
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
      Kyprianou.Ch02.integerValuedFiniteSupportV1
        ((N.N ω).restrict R) hInt
    refine ⟨s, ?_⟩
    rw [MeasureTheory.ae_iff, Measure.restrict_apply] at hs
    · rw [← hs]
      congr 1
      ext p
      simp [R, and_comm]
    · exact s.measurableSet.compl
  exact Kyprianou.Ch02.finiteRegionPoissonCadlagFromFiniteSupportV2
    P ν N B hB hfinite hSupport
