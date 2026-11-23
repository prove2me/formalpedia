-- Prove2me | solution 1 for Kyprianou.Ch02.prmFiniteSimpleMarkIntegralAEFibreSumKLSV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T18:18:17.834934+00:00
-- url     : https://prove2.me/submissions/6f73d794-df0c-4432-97e1-63d001465def

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Theorems.Thm_Kyprianou_Ch02_prmFiniteRegionAllMeasurableCountNatV1
import Theorems.Thm_Kyprianou_Ch02_prmFiniteSimpleMarkIntegralFibreSumV1
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
set_option autoImplicit false

/-- Integrability and finite fibres follow simultaneously on the finite-count event. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (R : Set (ℝ × ℝ)) (hRm : MeasurableSet R)
    (hRfin : LevyStochCalc.Poisson.referenceIntensity ν R ≠ ⊤)
    (f : SimpleFunc ℝ ℝ) :
    ∀ᵐ ω ∂P, (∫ z in R, f z.2 ∂(N.N ω)) =
      ∑ x ∈ f.range,
        (N.N ω (R ∩ {z : ℝ × ℝ | f z.2 = x})).toReal * x := by
  filter_upwards
    [Kyprianou.Ch02.prmFiniteRegionAllMeasurableCountNatV1
      P ν N R hRm hRfin] with ω hω
  obtain ⟨n, hn⟩ := hω Set.univ MeasurableSet.univ
  have hcount : N.N ω R = (n : ℝ≥0∞) := by
    simpa only [Set.univ_inter] using hn
  have hfin : N.N ω R < ⊤ := by
    rw [hcount]
    exact ENNReal.natCast_lt_top n
  exact Kyprianou.Ch02.prmFiniteSimpleMarkIntegralFibreSumV1
    P ν N R hRm f ω hfin
