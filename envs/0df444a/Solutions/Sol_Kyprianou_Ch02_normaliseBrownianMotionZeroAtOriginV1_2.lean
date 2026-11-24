-- Prove2me | solution 2 for Kyprianou.Ch02.normaliseBrownianMotionZeroAtOriginV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T21:53:25.218496+00:00
-- url     : https://prove2.me/submissions/cd7a661c-851e-4ea3-b4e9-5b34b1432e6a

import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch02_IndependentComponents
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou Kyprianou.Ch02

theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (B : LevyStochCalc.Brownian.BrownianMotion P) :
    ∃ B' : LevyStochCalc.Brownian.BrownianMotion P,
      ∀ (t : ℝ) (ω : Ω),
        B'.W t ω = B.W t ω - B.W 0 ω := by
  let origM : MeasurableSpace Ω := inferInstance
  let W' : ℝ → Ω → ℝ := fun t ω => B.W t ω - B.W 0 ω
  let B' : LevyStochCalc.Brownian.BrownianMotion P := {
    W := W'
    measurable_eval := fun t =>
      (B.measurable_eval t).sub (B.measurable_eval 0)
    joint_measurable := by
      change Measurable (fun p : ℝ × Ω => B.W p.1 p.2 - B.W 0 p.2)
      exact B.joint_measurable.sub ((B.measurable_eval 0).comp measurable_snd)
    initial_zero := by
      filter_upwards [] with ω
      dsimp [W']
      ring
    increment_gaussian := by
      intro s t hs hst
      have hinc : (fun ω => W' t ω - W' s ω) =
          (fun ω => B.W t ω - B.W s ω) := by
        funext ω
        dsimp [W']
        ring
      rw [hinc]
      exact B.increment_gaussian hs hst
    continuous_paths := by
      filter_upwards [B.continuous_paths] with ω hc
      exact hc.sub continuous_const
    negative_zero := by
      intro s hs
      filter_upwards [B.negative_zero s hs, B.initial_zero] with ω hneg hzero
      dsimp [W']
      rw [hneg, hzero]
      ring
    joint_increment_independent := by
      intro s t hs hst
      let V : ℝ → Ω → ℝ := B.W
      let Past : MeasurableSpace Ω :=
        ⨆ j ∈ Set.Iic s, MeasurableSpace.comap (V j) inferInstance
      have hPast (j : ℝ) (hj : j ≤ s) :
          MeasurableSpace.comap (V j) inferInstance ≤ Past := by
        exact le_iSup_of_le j (le_iSup_of_le (by simpa using hj) le_rfl)
      have hsub :
          (⨆ j ∈ Set.Iic s, MeasurableSpace.comap (W' j) inferInstance) ≤ Past := by
        apply iSup_le
        intro j
        apply iSup_le
        intro hj
        letI : MeasurableSpace Ω := Past
        have hjM : Measurable (V j) :=
          measurable_iff_comap_le.mpr (hPast j hj)
        have h0M : Measurable (V 0) :=
          measurable_iff_comap_le.mpr (hPast 0 hs)
        exact measurable_iff_comap_le.mp (hjM.sub h0M)
      letI : MeasurableSpace Ω := origM
      have hinc : (fun ω => W' t ω - W' s ω) =
          (fun ω => B.W t ω - B.W s ω) := by
        funext ω
        change (B.W t ω - B.W 0 ω) -
          (B.W s ω - B.W 0 ω) = B.W t ω - B.W s ω
        ring
      rw [hinc]
      exact ProbabilityTheory.indep_of_indep_of_le_left
        (B.joint_increment_independent hs hst) hsub
  }
  refine ⟨B', ?_⟩
  intro t ω
  rfl
