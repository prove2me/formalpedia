-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m810_restart_kernel_pointwise_exponential
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T21:48:36.917444+00:00
-- url     : https://prove2.me/submissions/63b8ed26-dc37-4730-94c3-75f8a4a7cc7a

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_finite_lower_crossing_value
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℝ≥0 → Ω → ℝ) (ω : Ω) (q y θ K : ℝ)
    (hrc : ∀ t, ContinuousWithinAt (fun s => X s ω) (Ici t) t)
    (hminus : ∀ x : ℝ, x ≤ 0 →
      (∫ η, discountedAt q (lastExitShifted X x η) ∂P) = K * Real.exp (θ*x)) :
    WithTop.recTopCoe (0 : ℝ) (fun t : ℝ≥0 =>
      Real.exp (-q * (t : ℝ)) *
        (∫ η, discountedAt q (lastExitShifted X (y + X t ω) η) ∂P))
      (tauMinus (shifted X y) 0 ω) = K * downOvershootTilt X q θ y ω := by
  by_cases ht : tauMinus (shifted X y) 0 ω = ⊤
  · simp [ht,downOvershootTilt]
  · obtain ⟨t,ht⟩ := WithTop.ne_top_iff_exists.mp ht
    have hn : y + X t ω ≤ 0 :=
      p2m810_finite_lower_crossing_value Ω (shifted X y) ω 0 t
        (continuousWithinAt_const.add (hrc t)) ht.symm
    unfold downOvershootTilt
    rw [← ht]
    simp only [WithTop.recTopCoe_coe, hminus _ hn, Real.exp_add]
    ring
