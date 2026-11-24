-- Prove2me | solution 3 for Kyprianou.Ch02.normaliseBrownianMotionZeroAtOriginV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T21:55:09.961555+00:00
-- url     : https://prove2.me/submissions/d63b91b7-1e0f-4d81-99a3-50afd039435e

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

open Kyprianou.Ch02

theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (B : LevyStochCalc.Brownian.BrownianMotion P) :
    ∃ B' : LevyStochCalc.Brownian.BrownianMotion P,
      ∀ (t : ℝ) (ω : Ω),
        B'.W t ω = B.W t ω - B.W 0 ω := by
  classical
  let W' : ℝ → Ω → ℝ := fun t ω => B.W t ω - B.W 0 ω
  have hm : ∀ t : ℝ, Measurable (W' t) := by
    intro t
    exact (B.measurable_eval t).sub (B.measurable_eval 0)
  have hjoint : Measurable (Function.uncurry W') := by
    change Measurable (fun p : ℝ × Ω => B.W p.1 p.2 - B.W 0 p.2)
    exact B.joint_measurable.sub
      ((B.measurable_eval 0).comp measurable_snd)
  have hinc (s t : ℝ) :
      (fun ω => W' t ω - W' s ω) =
        (fun ω => B.W t ω - B.W s ω) := by
    funext ω
    simp only [W']
    ring
  have hind : ∀ {s t : ℝ}, 0 ≤ s → s < t →
      Indep (⨆ j ∈ Set.Iic s,
        MeasurableSpace.comap (W' j) inferInstance)
        (MeasurableSpace.comap (fun ω => W' t ω - W' s ω) inferInstance) P := by
    intro s t hs hst
    have hOrig := B.joint_increment_independent hs hst
    let path : ℝ → Ω → ℝ := B.W
    let mHist : MeasurableSpace Ω :=
      ⨆ j ∈ Set.Iic s, MeasurableSpace.comap (path j) inferInstance
    have hmeas (j : ℝ) (hj : j ∈ Set.Iic s) :
        @Measurable Ω ℝ mHist inferInstance (path j) := by
      apply Measurable.of_comap_le
      exact le_iSup_of_le j (le_iSup_of_le hj le_rfl)
    have hhist : (⨆ j ∈ Set.Iic s,
        MeasurableSpace.comap (W' j) inferInstance) ≤ mHist := by
      apply iSup_le
      intro j
      apply iSup_le
      intro hj
      change MeasurableSpace.comap
        (fun ω => path j ω - path 0 ω) inferInstance ≤ mHist
      exact ((hmeas j hj).sub
        (hmeas 0 (Set.mem_Iic.mpr hs))).comap_le
    rw [hinc s t]
    exact indep_of_indep_of_le_left hOrig hhist
  refine ⟨{
    W := W'
    measurable_eval := hm
    joint_measurable := hjoint
    initial_zero := Filter.Eventually.of_forall (fun ω => sub_self (B.W 0 ω))
    increment_gaussian := ?_
    continuous_paths := ?_
    negative_zero := ?_
    joint_increment_independent := hind
  }, ?_⟩
  · intro s t hs hst
    rw [hinc s t]
    exact B.increment_gaussian hs hst
  · filter_upwards [B.continuous_paths] with ω hω
    exact hω.sub continuous_const
  · intro s hs
    filter_upwards [B.negative_zero s hs, B.initial_zero] with ω hn hz
    simp only [W', hn, hz, sub_self]
  · intro t ω
    rfl
