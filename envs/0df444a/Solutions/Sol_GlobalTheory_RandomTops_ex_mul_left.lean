-- Prove2me | solution 1 for GlobalTheory.RandomTops.ex_mul_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:50:07.842201+00:00
-- url     : https://prove2.me/submissions/1b01b896-77f1-44a4-a480-cfb2f88afdf3

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
theorem _root_.solution (S : Finset ℕ) (c : ℝ) (f : Finset ℕ → ℝ) :
    ex δ S (fun T => c * f T) = c * ex δ S f := by
  unfold ex
  rw [mul_sum]
  exact sum_congr rfl fun _ _ => by ring
end GlobalTheory.RandomTops
