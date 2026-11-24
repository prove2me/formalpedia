-- Prove2me | solution 1 for Kyprianou.Ch02.compensatedBandLeftJumpEqualsFibreIntegralV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:03:16.74684+00:00
-- url     : https://prove2.me/submissions/24c693bb-3c02-4c5d-9e71-e0408afb1cc5

import Theorems.Thm_Kyprianou_Ch02_finiteMarkedWindowLeftLimitV1
import Theorems.Thm_Kyprianou_Ch02_finiteMarkedWindowIntegralSplitV1
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
    (e : ℝ) (T : ℝ≥0) (ω : Ω)
    (hfinite : N.N ω (Set.Ioc (0 : ℝ) (T : ℝ) ×ˢ
        {x : ℝ | e ≤ |x| ∧ |x| < 1}) < ⊤)
    (t : ℝ≥0) (ht : 0 < t) (htT : t ≤ T) :
    ∃ l : ℝ,
      Tendsto (fun s => Kyprianou.compensatedSmallJumpBand P ν N e s ω)
        (nhdsWithin t (Set.Iio t)) (nhds l) ∧
      Kyprianou.compensatedSmallJumpBand P ν N e t ω - l =
        ∫ z in ({(t : ℝ)} ×ˢ {x : ℝ | e ≤ |x| ∧ |x| < 1}), z.2 ∂(N.N ω) := by
  let B : Set ℝ := {x | e ≤ |x| ∧ |x| < 1}
  let μ := N.N ω
  let d : ℝ := ∫ x in B, x ∂ν
  have hB : MeasurableSet B := (measurableSet_le measurable_const continuous_abs.measurable).inter
    (measurableSet_lt continuous_abs.measurable measurable_const)
  have hsmall : B ⊆ {x : ℝ | |x| < 1} := fun _ hx => hx.2
  have hconv := Kyprianou.Ch02.finiteMarkedWindowLeftLimitV1 μ B hB hsmall T t htT hfinite
  have hd : Tendsto (fun s : ℝ≥0 => (s : ℝ) * d)
      (nhdsWithin t (Set.Iio t)) (nhds ((t : ℝ) * d)) :=
    ((NNReal.continuous_coe.mul continuous_const).tendsto t).mono_left nhdsWithin_le_nhds
  refine ⟨(∫ z in (Set.Ioo (0 : ℝ) (t : ℝ) ×ˢ B), z.2 ∂μ) - (t : ℝ) * d, ?_, ?_⟩
  · exact hconv.sub hd
  · change (∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B), z.2 ∂μ) - (t : ℝ) * d -
      ((∫ z in (Set.Ioo (0 : ℝ) (t : ℝ) ×ˢ B), z.2 ∂μ) - (t : ℝ) * d) = _
    rw [Kyprianou.Ch02.finiteMarkedWindowIntegralSplitV1 μ B hB hsmall T t htT hfinite ht]
    ring
