-- Prove2me | solution 1 for GlobalTheory.PartRed.chL_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:29:08.998721+00:00
-- url     : https://prove2.me/submissions/8f9f321e-23ef-4036-b49e-b50162aa6df5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ChLApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
noncomputable section
open GlobalTheory GlobalTheory.PartRed
open GlobalTheory.SplitWeil GlobalTheory.RootEx
variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
namespace GlobalTheory.PartRed
theorem _root_.solution (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) : chL x = ch x := rfl
end GlobalTheory.PartRed
