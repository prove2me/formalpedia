-- Prove2me | solution 1 for GlobalTheory.RandomTops.ex_union
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:50:10.309457+00:00
-- url     : https://prove2.me/submissions/701281d8-2d60-4ebd-8de2-7fa36670a06d

import Mathlib
import Definitions.Def_Formalism_SubspaceCounting_GoodOrbitIntervalTileCondition
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ChoiceOfTops
import Theorems.Thm_GlobalTheory_RandomTops_ex_empty
import Theorems.Thm_GlobalTheory_RandomTops_ex_insert

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
theorem _root_.solution {A B : Finset ℕ} (hAB : Disjoint A B) (f : Finset ℕ → ℝ) :
    ex δ (A ∪ B) f = ex δ A (fun T => ex δ B (fun U => f (T ∪ U))) := by
  induction A using Finset.induction_on generalizing f with
  | empty => simp [ex_empty]
  | insert a A ha ih =>
    have haB : a ∉ B := fun h => disjoint_left.mp hAB (mem_insert_self a A) h
    have hAB' : Disjoint A B := disjoint_of_subset_left (subset_insert a A) hAB
    have haU : a ∉ A ∪ B := by simp [ha, haB]
    rw [insert_union, ex_insert haU, ex_insert ha, ih hAB', ih hAB']
    simp only [insert_union]
end GlobalTheory.RandomTops
