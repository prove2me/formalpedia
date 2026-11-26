-- Prove2me | solution 1 for Kyprianou.Ch04.exercise49DenseRightEqualityV4
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T16:06:44.916669+00:00
-- url     : https://prove2.me/submissions/6f531eea-fabb-4bc5-8e7d-583900037aa6

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch04_exercise41DenseRightHitV4
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch04
open scoped NNReal ENNReal BigOperators Classical Topology
variable {Ω : Type} [MeasurableSpace Ω]
theorem solution (x y : NNReal → ℝ) (q : ℕ → NNReal) (hq : DenseRange q)
    (hx : ∀ s, ContinuousWithinAt x (Ici s) s)
    (hy : ∀ s, ContinuousWithinAt y (Ici s) s)
    (he : ∀ k, x (q k) = y (q k)) : x = y := by
  funext s
  by_contra hne
  have hpos : 0 < |x s - y s| := abs_pos.mpr (sub_ne_zero.mpr hne)
  have hr : ContinuousWithinAt (fun t => x t - y t - (x s - y s)) (Ici s) s :=
    ((hx s).sub (hy s)).sub continuousWithinAt_const
  obtain ⟨k,_,_,hk⟩ := exercise41DenseRightHitV4
    (fun t => x t - y t - (x s - y s)) q hq s ((s : ℝ)+1)
    |x s - y s| (by linarith) hpos hr (by ring)
  rw [he k, sub_self, zero_sub, abs_neg] at hk
  exact (lt_irrefl _) hk
