-- Prove2me | solution 1 for Kyprianou.Ch02.normaliseBrownianMotionZeroAtOriginV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T21:52:29.562191+00:00
-- url     : https://prove2.me/submissions/cdadccd3-5d22-49d7-b03c-49332ba07790

import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Mathlib
import Theorems.Thm_Kyprianou_Ch02_brownianNormalisedPastFutureIndependentV1
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch02_IndependentComponents
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false


theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (B : LevyStochCalc.Brownian.BrownianMotion P) :
    ∃ B' : LevyStochCalc.Brownian.BrownianMotion P,
      ∀ (t : ℝ) (ω : Ω),
        B'.W t ω = B.W t ω - B.W 0 ω  := by
  let W' : ℝ → Ω → ℝ := fun t ω => B.W t ω - B.W 0 ω
  have hW0 : ∀ ω : Ω, W' 0 ω = 0 := by
    intro ω
    simp [W']
  have hmeas : ∀ t, Measurable (W' t) := by
    intro t
    exact (B.measurable_eval t).sub (B.measurable_eval 0)
  have hjoint : Measurable (Function.uncurry W') := by
    have heq : Function.uncurry W' =
        (Function.uncurry B.W) -
          (fun z : ℝ × Ω => B.W 0 z.2) := by
      funext z
      rfl
    rw [heq]
    exact B.joint_measurable.sub
      ((B.measurable_eval 0).comp measurable_snd)
  have hincr : ∀ {s t : ℝ} (hs : 0 ≤ s) (hst : s < t),
      P.map (fun ω => W' t ω - W' s ω) =
        gaussianReal 0 ⟨t - s, by linarith⟩ := by
    intro s t hs hst
    have heq : (fun ω => W' t ω - W' s ω) =
        (fun ω => B.W t ω - B.W s ω) := by
      funext ω
      simp only [W']
      ring
    rw [heq]
    exact B.increment_gaussian hs hst
  have hpath : ∀ᵐ ω ∂P, Continuous (fun t : ℝ => W' t ω) := by
    filter_upwards [B.continuous_paths] with ω hw
    exact hw.sub continuous_const
  have hneg : ∀ s : ℝ, s < 0 → ∀ᵐ ω ∂P, W' s ω = 0 := by
    intro s hs
    filter_upwards [B.negative_zero s hs, B.initial_zero] with ω hz hzero
    simp [W', hz, hzero]
  have hInd : ∀ {s t : ℝ}, 0 ≤ s → s < t →
      Indep
        (⨆ j ∈ Set.Iic s, MeasurableSpace.comap (W' j) inferInstance)
        (MeasurableSpace.comap (fun ω => W' t ω - W' s ω) inferInstance)
        P := by
    intro s t hs hst
    exact Kyprianou.Ch02.brownianNormalisedPastFutureIndependentV1
      P B hs hst
  refine ⟨{
    W := W'
    measurable_eval := hmeas
    joint_measurable := hjoint
    initial_zero := Filter.Eventually.of_forall hW0
    increment_gaussian := hincr
    continuous_paths := hpath
    negative_zero := hneg
    joint_increment_independent := hInd
  }, ?_⟩
  intro t ω
  rfl
