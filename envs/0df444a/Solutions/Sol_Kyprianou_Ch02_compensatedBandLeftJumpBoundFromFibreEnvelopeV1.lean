-- Prove2me | solution 1 for Kyprianou.Ch02.compensatedBandLeftJumpBoundFromFibreEnvelopeV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:01:27.940679+00:00
-- url     : https://prove2.me/submissions/e16a94b4-ab13-4552-bc60-21461f6ea623

import Theorems.Thm_Kyprianou_Ch02_compensatedBandLeftJumpEqualsFibreIntegralV1
import Theorems.Thm_Kyprianou_Ch02_markedFibreIntegralBoundFromEnvelopeV1
import Mathlib
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (e : ℝ) (he : 0 < e) (he1 : e < 1)
    (T : ℝ≥0) (ω : Ω) (c : ℝ) (hc : 0 ≤ c)
    (hfinite : N.N ω (Set.Ioc (0 : ℝ) (T : ℝ) ×ˢ
        {x : ℝ | e ≤ |x| ∧ |x| < 1}) < ⊤)
    (henvelope : N.N ω (Set.Ioc (0 : ℝ) (T : ℝ) ×ˢ
        {x : ℝ | c < |x| ∧ |x| < 1}) = 0)
    (hfibre : ∀ t : ℝ≥0, 0 < t → t ≤ T →
      N.N ω ({(t : ℝ)} ×ˢ {x : ℝ | e ≤ |x| ∧ |x| < 1}) ≤ 1)
    (t : ℝ≥0) (ht : 0 < t) (htT : t ≤ T) :
    ∃ l : ℝ,
      Tendsto (fun s => Kyprianou.compensatedSmallJumpBand P ν N e s ω)
        (nhdsWithin t (Set.Iio t)) (nhds l) ∧
      |Kyprianou.compensatedSmallJumpBand P ν N e t ω - l| ≤ c := by
  let B : Set ℝ := {x | e ≤ |x| ∧ |x| < 1}
  have hB : MeasurableSet B := (measurableSet_le measurable_const continuous_abs.measurable).inter
    (measurableSet_lt continuous_abs.measurable measurable_const)
  obtain ⟨l, hl, hj⟩ := Kyprianou.Ch02.compensatedBandLeftJumpEqualsFibreIntegralV1
    P ν N e T ω hfinite t ht htT
  refine ⟨l, hl, ?_⟩
  rw [hj]
  exact Kyprianou.Ch02.markedFibreIntegralBoundFromEnvelopeV1
    (N.N ω) B hB (fun _ hx => hx.2) T t ht htT c hc henvelope (hfibre t ht htT)
