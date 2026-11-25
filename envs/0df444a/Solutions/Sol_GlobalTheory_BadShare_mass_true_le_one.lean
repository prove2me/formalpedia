-- Prove2me | solution 1 for GlobalTheory.BadShare.mass_true_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:03:00.201247+00:00
-- url     : https://prove2.me/submissions/9a56cb87-949c-4b58-aaab-223a007a4529

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_MassDegTypeLeCycleTypeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SquarefreeLabelTorusMassDivisorBound
import Theorems.Thm_GlobalTheory_T_mass_degType_le_card_cycleType_div


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Classical GlobalTheory.BadShare
open GlobalTheory GlobalTheory.BadShare
namespace GlobalTheory.BadShare
theorem _root_.solution (g : ℕ) [Fact g.Prime] (N : ℕ) : (mass g N fun _ => True) ≤ 1 := by
  refine (GlobalTheory.T.mass_degType_le_card_cycleType_div g N (fun _ => True)).trans (le_of_eq ?_)
  rw [Finset.filter_true, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  have hN : (N.factorial : ℝ) ≠ 0 := by positivity
  exact div_self hN
end GlobalTheory.BadShare
