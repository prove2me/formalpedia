-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45CutoffStateRegularV5
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:00:50.92499+00:00
-- url     : https://prove2.me/submissions/1cbb0fe5-c798-43f2-8097-c20854d94716

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_LeanLevy_Levy_LevyMeasure
import Theorems.Thm_Kyprianou_Ch02_prmMarkedIntegralMeasurableAmbientV1
import Theorems.Thm_Kyprianou_Ch04_actualCutoffAffineStepsV1
import Theorems.Thm_Kyprianou_Ch02_finiteRegionStepSumCadlagNNRealV1
open MeasureTheory Filter Set Topology ProbabilityTheory LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false
/-- Physical finite-cutoff states have measurable coordinates and a.e. right-continuous paths. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν] (hν : IsLevyMeasure ν)
    (N : PoissonRandomMeasure.{0,0,0} P ν) (X L X2 Y : NNReal → Ω → ℝ)
    (b e : ℝ) (he : 0 < e)
    (hN : ∀ᵐ w ∂P, N.N w = Kyprianou.Ch04.pathJumpMeasure X L w)
    (h2 : ∀ t w, X2 t w = b * (t : ℝ) +
      ∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | 1 ≤ |x|}, z.2 ∂(N.N w))
    (hY : ∀ t w, Y t w = X2 t w +
      (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | e < |x| ∧ |x| < 1}, z.2 ∂(N.N w)) -
      (t : ℝ) * ∫ x in {x : ℝ | e < |x| ∧ |x| < 1}, x ∂ν) :
    (∀ t, AEMeasurable (Y t) P) ∧
      (∀ᵐ w ∂P, ∀ t, ContinuousWithinAt (fun s => Y s w) (Ici t) t) := by
  constructor
  · intro t
    have hl := Kyprianou.Ch02.prmMarkedIntegralMeasurableAmbientV1 P ν N
      (Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | 1 ≤ |x|})
      (measurableSet_Icc.prod (measurableSet_le measurable_const measurable_id.abs))
    have hs := Kyprianou.Ch02.prmMarkedIntegralMeasurableAmbientV1 P ν N
      (Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | e < |x| ∧ |x| < 1})
      (measurableSet_Icc.prod ((measurableSet_lt measurable_const measurable_id.abs).inter
        (measurableSet_lt measurable_id.abs measurable_const)))
    have h2m : Measurable (X2 t) := by
      rw [funext (h2 t)]
      exact measurable_const.add hl
    rw [funext (hY t)]
    exact ((h2m.add hs).sub measurable_const).aemeasurable
  · filter_upwards [Kyprianou.Ch04.actualCutoffAffineStepsV1
      P ν hν N X L X2 Y b e he hN h2 hY] with w hw
    intro t
    obtain ⟨m,hm⟩ := exists_nat_gt t
    obtain ⟨S,R,a,d,h⟩ := hw m
    let c := b - ∫ x in {x : ℝ | e < |x| ∧ |x| < 1}, x ∂ν
    let V (s : NNReal) := ∑ p ∈ S, if p.1 ≤ (s : ℝ) then a p else 0
    let W (s : NNReal) := ∑ p ∈ R, if p.1 ≤ (s : ℝ) then d p else 0
    let U (s : NNReal) := c * (s : ℝ) + V s + W s
    have hv := (Kyprianou.Ch02.finiteRegionStepSumCadlagNNRealV1 S a t).1
    have hw' := (Kyprianou.Ch02.finiteRegionStepSumCadlagNNRealV1 R d t).1
    have hd : ContinuousWithinAt (fun s : NNReal => c * (s : ℝ)) (Ici t) t :=
      (continuous_const.mul NNReal.continuous_coe).continuousWithinAt
    have hc : ContinuousWithinAt U (Ici t) t := (hd.add hv).add hw'
    have hEq : (fun s => Y s w) =ᶠ[nhdsWithin t (Ici t)] U := by
      filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hm)] with s hs
      exact (h s hs.le).2
    change Tendsto (fun s => Y s w) (nhdsWithin t (Ici t)) (nhds (Y t w))
    rw [show Y t w = U t from (h t hm.le).2]
    exact hc.congr' hEq.symm
