-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45PhysicalLargeRightV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-27T00:33:32.406211+00:00
-- url     : https://prove2.me/submissions/db3d322e-c3fe-49a3-92ae-4241158c567f

import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_5CertificationV3
import Theorems.Thm_Kyprianou_Ch04_actualCutoffAffineStepsV1
import Theorems.Thm_Kyprianou_Ch02_finiteRegionStepSumCadlagNNRealV1
open MeasureTheory ProbabilityTheory Filter Set LevyStochCalc.Poisson
open scoped NNReal ENNReal Classical
set_option autoImplicit false

/-- The physical large jump and drift process is right-continuous almost surely. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν] (hν : IsLevyMeasure ν)
    (N : PoissonRandomMeasure.{0,0,0} P ν) (X L : NNReal → Ω → ℝ)
    (b : ℝ) (hN : ∀ᵐ w ∂P, N.N w = Kyprianou.Ch04.pathJumpMeasure X L w) :
    let V : NNReal → Ω → ℝ := fun t w => b * (t : ℝ) +
      ∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | 1 ≤ |x|}, z.2 ∂(N.N w)
    ∀ᵐ w ∂P, ∀ t, ContinuousWithinAt (fun s => V s w) (Ici t) t := by
  intro V
  let e : ℝ := 1 / 2
  let Y (t : NNReal) (w : Ω) := V t w +
    (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | e < |x| ∧ |x| < 1}, z.2 ∂(N.N w)) -
    (t : ℝ) * ∫ x in {x : ℝ | e < |x| ∧ |x| < 1}, x ∂ν
  filter_upwards [Kyprianou.Ch04.actualCutoffAffineStepsV1 P ν hν N X L V Y b e
    (by norm_num [e]) hN (fun _ _ => rfl) (fun _ _ => rfl)] with w hw
  intro t
  obtain ⟨n,hn⟩ := exists_nat_gt t
  obtain ⟨S,R,a,c,h⟩ := hw n
  let U (s : NNReal) := b * (s : ℝ) + ∑ p ∈ S, if p.1 ≤ (s : ℝ) then a p else 0
  have hu : ContinuousWithinAt U (Ici t) t :=
    (continuous_const.mul NNReal.continuous_coe).continuousWithinAt.add
      (Kyprianou.Ch02.finiteRegionStepSumCadlagNNRealV1 S a t).1
  have he : (fun s => V s w) =ᶠ[nhdsWithin t (Ici t)] U := by
    filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hn)] with s hs
    exact (h s hs.le).1
  exact hu.congr_of_eventuallyEq he (h t hn.le).1
