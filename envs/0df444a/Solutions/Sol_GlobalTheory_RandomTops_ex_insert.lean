-- Prove2me | solution 1 for GlobalTheory.RandomTops.ex_insert
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:07:47.119326+00:00
-- url     : https://prove2.me/submissions/c4789534-964a-44b3-8f8d-5c470b928ef6

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
theorem _root_.solution {a : ℕ} {S : Finset ℕ} (ha : a ∉ S) (f : Finset ℕ → ℝ) :
    ex δ (insert a S) f = (1 - δ) * ex δ S f + δ * ex δ S (fun T => f (insert a T)) := by
  unfold ex
  rw [sum_powerset_insert ha, card_insert_of_notMem ha, mul_sum, mul_sum]
  congr 1
  · refine sum_congr rfl fun T hT => ?_
    have := card_le_card (mem_powerset.mp hT)
    rw [show #S + 1 - #T = (#S - #T) + 1 by omega, pow_succ]
    ring
  · refine sum_congr rfl fun T hT => ?_
    have hT' : a ∉ T := fun h => ha (mem_powerset.mp hT h)
    rw [card_insert_of_notMem hT', show #S + 1 - (#T + 1) = #S - #T by omega, pow_succ]
    ring
end GlobalTheory.RandomTops
