-- Prove2me | solution 1 for GlobalTheory.RandomTops.ex_one_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:50:08.606834+00:00
-- url     : https://prove2.me/submissions/b8858a66-f9e1-4cda-a831-97660475cac2

import Mathlib
import Definitions.Def_Formalism_SubspaceCounting_GoodOrbitIntervalTileCondition
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ChoiceOfTops
import Theorems.Thm_GlobalTheory_RandomTops_ex_const

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
theorem _root_.solution (S : Finset ℕ) (f : Finset ℕ → ℝ) :
    ex δ S (fun T => 1 - f T) = 1 - ex δ S f := by
  rw [show (1 : ℝ) - ex δ S f = ex δ S (fun _ => 1) - ex δ S f by rw [ex_const]]
  unfold ex
  rw [← sum_sub_distrib]
  exact sum_congr rfl fun _ _ => by ring
end GlobalTheory.RandomTops
