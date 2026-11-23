-- Prove2me | solution 1 for Kyprianou.Ch02.prmFiniteIntensityWindowSimpleMarkIntegralTendstoV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T14:16:21.646748+00:00
-- url     : https://prove2.me/submissions/04ba38e5-5074-4252-bc8e-c92f0707ef5d

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Theorems.Thm_Kyprianou_Ch02_prmFiniteRegionAllMeasurableCountNatV1
import Theorems.Thm_Kyprianou_Ch02_integerValuedFiniteDiracV1
import Theorems.Thm_Kyprianou_Ch02_finiteDiracMarkIntegralTendstoV1

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
set_option autoImplicit false

/-- Finite-intensity Poisson windows admit finite atomic integration on one conull event. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (R : Set (ℝ × ℝ)) (hRm : MeasurableSet R)
    (hRfin : LevyStochCalc.Poisson.referenceIntensity ν R ≠ ⊤)
    (f : ℕ → SimpleFunc ℝ ℝ)
    (hf : ∀ x : ℝ, Tendsto (fun n => f n x) atTop (𝓝 x)) :
    ∀ᵐ ω ∂P,
      Tendsto (fun n => ∫ z in R, f n z.2 ∂(N.N ω))
        atTop (𝓝 (∫ z in R, z.2 ∂(N.N ω))) := by
  filter_upwards
    [Kyprianou.Ch02.prmFiniteRegionAllMeasurableCountNatV1
      P ν N R hRm hRfin] with ω hω
  have hint : LevyStochCalc.Probability.IsIntegerValued
      ((N.N ω).restrict R) := by
    intro A hA
    rw [Measure.restrict_apply hA]
    exact hω A hA
  obtain ⟨s, hs⟩ :=
    Kyprianou.Ch02.integerValuedFiniteDiracV1
      ((N.N ω).restrict R) hint
  have hcoef : ∀ p ∈ s, ((N.N ω).restrict R) {p} ≠ ⊤ := by
    intro p hp
    obtain ⟨n, hn⟩ := hint {p} (measurableSet_singleton p)
    rw [hn]
    exact ENNReal.natCast_ne_top n
  exact Kyprianou.Ch02.finiteDiracMarkIntegralTendstoV1
    ((N.N ω).restrict R) s
      (fun p => ((N.N ω).restrict R) {p}) hcoef hs
      (fun n x => f n x) hf
