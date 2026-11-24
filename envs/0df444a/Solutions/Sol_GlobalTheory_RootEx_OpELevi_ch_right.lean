-- Prove2me | solution 1 for GlobalTheory.RootEx.OpELevi.ch_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:06:03.258778+00:00
-- url     : https://prove2.me/submissions/59ebd33a-59dc-48a7-8405-5f68900aa121

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralCompBlocks
import Theorems.Thm_GlobalTheory_RootEx_OpELevi_right_inr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.OpELevi
variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
omit [Fintype n] [DecidableEq n] [DecidableEq n']
namespace GlobalTheory.RootEx.OpELevi
theorem _root_.solution (A : Matrix n' n' k) (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) :
    ch (x * (fromBlocks A 0 0 1 : Matrix (n' ⊕ Fin (c + 1)) (n' ⊕ Fin (c + 1)) k)) = ch x := by
  simp only [ch, right_inr]
end GlobalTheory.RootEx.OpELevi
