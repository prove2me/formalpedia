-- Prove2me | solution 1 for GlobalTheory.continuous_prod_ofFn_curves
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:13:48.249974+00:00
-- url     : https://prove2.me/submissions/6a5d89b2-6e91-4d00-9dac-0be4f1c197c3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SqIntervalIntegralLeMulIntervalIntegralSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SobolevIteratedOneParameterSubgroups

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (N : ℕ) (c : Fin N → ℝ → G) (hc : ∀ i, Continuous (c i)) :
    Continuous fun t : Fin N → ℝ => (List.ofFn fun i => c i (t i)).prod := by
  induction N with
  | zero =>
    simp only [List.ofFn_zero, List.prod_nil]
    exact continuous_const
  | succ n ih =>
    simp only [List.ofFn_succ, List.prod_cons]
    exact ((hc 0).comp (continuous_apply 0)).mul
      ((ih (fun i => c i.succ) (fun i => hc i.succ)).comp
        (continuous_pi fun i => continuous_apply i.succ))
end GlobalTheory
