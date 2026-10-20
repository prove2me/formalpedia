-- Prove2me | solution 1 for OAI.LipschitzCounterexample.FreeSpace.linearize_unique
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T19:43:42.614984+00:00
-- url     : https://prove2.me/submissions/8303b4dc-46a8-4bcc-9580-a1e55d658028

import Mathlib
import Definitions.Def_LipschitzEquivalence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FreeSpace

open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.FreeSpace
universe uM uF
open scoped NNReal ENNReal
variable (M : Type uM) [MetricSpace M] [Zero M]
variable {M}
variable {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable (D : M → F) {K : ℝ≥0} (hD : LipschitzWith K D) (h0 : D 0 = 0)
include hD h0
variable [CompleteSpace F]


theorem solution (T : Space M →L[ℝ] F) (hT : ∀ x, T (point x) = D x) :
    linearize D = T := by
  have hd := dense_combinations (M := M)
  apply DFunLike.coe_injective
  refine hd.equalizer (linearize D).continuous T.continuous (funext fun a => ?_)
  simp only [Function.comp_apply]
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | single x r => simp [Finsupp.linearCombination_single, linearize_point D hD h0, hT]

