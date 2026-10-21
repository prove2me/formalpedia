-- Prove2me | solution 1 for ModernOnlineLearning.Reductions.lemma_12_2_zero_mem
-- status  : ACCEPTED   (prove)
-- author  : @suzukasan
-- created : 2026-10-20T17:34:46.639977+00:00
-- url     : https://prove2.me/submissions/592315f5-f3d0-4fc0-9b26-761f06900c26

import Definitions.Def_ModernOnlineLearning_Reductions_Setting

set_option autoImplicit false
open ModernOnlineLearning.Reductions

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (V : Set E) (hV : V.Nonempty)
    (hclosed : IsClosed V) (hconv : Convex ℝ V) (x : E) (hx : x ∈ V) :
    IsSubgradient (distance V) x (0 : E →L[ℝ] ℝ) := by
  intro y
  have hz : distance V x = 0 := Metric.infDist_zero_of_mem hx
  change distance V x + (0 : E →L[ℝ] ℝ) (y-x) ≤ distance V y
  rw [hz, ContinuousLinearMap.zero_apply, zero_add]
  exact Metric.infDist_nonneg

