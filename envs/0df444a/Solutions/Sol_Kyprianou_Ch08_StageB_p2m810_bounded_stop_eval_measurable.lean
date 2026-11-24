-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m810_bounded_stop_eval_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T21:59:38.236159+00:00
-- url     : https://prove2.me/submissions/9139be24-7171-4d26-b843-b109646b1a0d

import Theorems.Thm_LevyStochCalc_Probability_progressivelyMeasurable_of_rightContinuous
import Mathlib.Probability.Process.Stopping
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.Instances.NNReal.Lemmas
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω] (F : Filtration ℝ≥0 mΩ)
    (X : ℝ≥0 → Ω → ℝ)
    (hadapt : ∀ t, Measurable[F t] (X t))
    (hrc : ∀ ω t, ContinuousWithinAt (fun s => X s ω) (Ici t) t)
    (τ : Ω → ℝ≥0) (hτ : IsStoppingTime F (fun ω => (τ ω : WithTop ℝ≥0)))
    (s : ℝ≥0) (hb : ∀ ω, τ ω ≤ s) :
    Measurable[F s] (fun ω => X (τ ω) ω) := by
  let G : Filtration ℝ mΩ :=
    ⟨fun r => F (Real.toNNReal r),fun _ _ h => F.mono (Real.toNNReal_mono h),
      fun r => F.le (Real.toNNReal r)⟩
  let V : ℝ → Ω → ℝ := fun r ω => X (Real.toNNReal r) ω
  have hV (ω : Ω) (r : ℝ) :
      Tendsto (fun u => V u ω) (nhdsWithin r (Ioi r)) (𝓝 (V r ω)) := by
    have hm : MapsTo Real.toNNReal (Ioi r) (Ici (Real.toNNReal r)) :=
      fun _ hu => Real.toNNReal_mono hu.le
    exact (hrc ω (Real.toNNReal r)).comp
      continuous_real_toNNReal.continuousWithinAt hm
  have hp := LevyStochCalc.Probability.progressivelyMeasurable_of_rightContinuous
    (ℱ := G) (X := V) (fun r => hadapt (Real.toNNReal r)) hV
  have ht : Measurable[F s] (fun ω => (τ ω : WithTop ℝ≥0)) :=
    hτ.measurable.mono (hτ.measurableSpace_le_of_le_const
      (fun ω => WithTop.coe_le_coe.mpr (hb ω))) le_rfl
  have ht' : Measurable[F s] τ := by
    simpa only [WithTop.untopD_coe] using Measurable.untopD 0 ht
  have hh := hp (s : ℝ)
  change @StronglyMeasurable (Ω × ℝ) ℝ _
    (@Prod.instMeasurableSpace Ω ℝ (G (s : ℝ)) inferInstance)
    (fun p => (Iic (s : ℝ)).indicator (fun u => V u p.1) p.2) at hh
  have he : G (s : ℝ) = F s := by simp [G,Real.toNNReal_coe]
  rw [he] at hh
  letI : MeasurableSpace Ω := F s
  have hpair : Measurable (fun ω : Ω => (ω,(τ ω : ℝ))) :=
    measurable_id.prodMk (NNReal.continuous_coe.measurable.comp ht')
  have hh' := hh.measurable.comp hpair
  convert hh' using 1
  funext ω
  change X (τ ω) ω = (Iic (s : ℝ)).indicator (fun u => V u ω) (τ ω : ℝ)
  rw [indicator_of_mem (show (τ ω : ℝ) ∈ Iic (s : ℝ) from hb ω)]
  simp [V,Real.toNNReal_coe]
