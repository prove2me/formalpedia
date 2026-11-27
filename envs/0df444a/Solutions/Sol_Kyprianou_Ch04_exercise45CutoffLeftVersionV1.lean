-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45CutoffLeftVersionV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-27T00:20:26.239224+00:00
-- url     : https://prove2.me/submissions/396e99bd-c41c-4578-a575-779bc4dc65f1

import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_5CertificationV3
import Theorems.Thm_Kyprianou_Ch04_actualCutoffAffineStepsV1
import Theorems.Thm_Kyprianou_Ch02_finiteRegionStepSumCadlagNNRealV1
open MeasureTheory ProbabilityTheory Filter Set LevyStochCalc.Poisson
open scoped NNReal ENNReal Classical
set_option autoImplicit false

/-- A physical finite cutoff admits a left-limit version on the original space. -/
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
    ∃ Yleft : NNReal → Ω → ℝ, ∀ᵐ w ∂P, ∀ t : NNReal, 0 < t →
      Tendsto (fun s => Y s w) (nhdsWithin t (Iio t)) (nhds (Yleft t w)) := by
  let Yleft (t : NNReal) (w : Ω) :=
    if h : ∃ l : ℝ, Tendsto (fun s => Y s w) (nhdsWithin t (Iio t)) (nhds l)
    then Classical.choose h else 0
  refine ⟨Yleft,?_⟩
  filter_upwards [Kyprianou.Ch04.actualCutoffAffineStepsV1 P ν hν N X L X2 Y
    b e he hN h2 hY] with w hw
  intro t ht
  obtain ⟨m,hm⟩ := exists_nat_gt t
  obtain ⟨S,R,a,d,h⟩ := hw m
  let c := b - ∫ x in {x : ℝ | e < |x| ∧ |x| < 1}, x ∂ν
  let V (s : NNReal) := ∑ p ∈ S, if p.1 ≤ (s : ℝ) then a p else 0
  let W (s : NNReal) := ∑ p ∈ R, if p.1 ≤ (s : ℝ) then d p else 0
  let U (s : NNReal) := c * (s : ℝ) + V s + W s
  obtain ⟨v,hv⟩ := (Kyprianou.Ch02.finiteRegionStepSumCadlagNNRealV1 S a t).2
  obtain ⟨q,hq⟩ := (Kyprianou.Ch02.finiteRegionStepSumCadlagNNRealV1 R d t).2
  have hd : Tendsto (fun s : NNReal => c * (s : ℝ))
      (nhdsWithin t (Iio t)) (nhds (c * (t : ℝ))) :=
    ((continuous_const.mul NNReal.continuous_coe).continuousAt.tendsto).mono_left
      nhdsWithin_le_nhds
  have hU : Tendsto U (nhdsWithin t (Iio t)) (nhds (c * (t : ℝ) + v + q)) :=
    (hd.add hv).add hq
  have hEq : (fun s => Y s w) =ᶠ[nhdsWithin t (Iio t)] U := by
    filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hm)] with s hs
    exact (h s hs.le).2
  have hex : ∃ l : ℝ, Tendsto (fun s => Y s w) (nhdsWithin t (Iio t)) (nhds l) :=
    ⟨_,hU.congr' hEq.symm⟩
  simpa only [Yleft,dif_pos hex] using Classical.choose_spec hex
