-- Prove2me | solution 1 for GlobalTheory.RootEx.OpELevi.ch_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:06:02.379621+00:00
-- url     : https://prove2.me/submissions/749c21ee-3629-48a5-ba1d-94e35c06859f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralCompBlocks
import Theorems.Thm_GlobalTheory_RootEx_OpELevi_left_inr

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
omit [DecidableEq n] [Fintype n'] [DecidableEq n']
namespace GlobalTheory.RootEx.OpELevi
theorem _root_.solution (A : Matrix n n k) (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) :
    ch ((fromBlocks A 0 0 1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) * x) = ch x := by
  simp only [ch, left_inr]
end GlobalTheory.RootEx.OpELevi
