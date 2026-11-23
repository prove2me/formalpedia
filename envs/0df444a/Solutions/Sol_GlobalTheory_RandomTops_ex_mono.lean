-- Prove2me | solution 1 for GlobalTheory.RandomTops.ex_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:07:17.472451+00:00
-- url     : https://prove2.me/submissions/9d4f5fe6-a307-431e-81b3-836c9cd9ecf5

import Mathlib
import Definitions.Def_Formalism_SubspaceCounting_GoodOrbitIntervalTileCondition
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ChoiceOfTops

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset Formalism.G0
open GlobalTheory GlobalTheory.RandomTops
variable {δ : ℝ}
namespace GlobalTheory.RandomTops
theorem _root_.solution (h0 : 0 ≤ δ) (h1 : δ ≤ 1) {S : Finset ℕ} {f g : Finset ℕ → ℝ}
    (h : ∀ T ⊆ S, f T ≤ g T) : ex δ S f ≤ ex δ S g := by
  unfold ex
  refine sum_le_sum fun T hT => mul_le_mul_of_nonneg_left (h T (mem_powerset.mp hT)) ?_
  exact mul_nonneg (pow_nonneg h0 _) (pow_nonneg (by linarith) _)
end GlobalTheory.RandomTops
