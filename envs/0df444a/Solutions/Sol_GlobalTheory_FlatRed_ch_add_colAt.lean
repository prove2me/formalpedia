-- Prove2me | solution 1 for GlobalTheory.FlatRed.ch_add_colAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:35:59.383036+00:00
-- url     : https://prove2.me/submissions/34bdf8eb-0602-4359-9e2c-8a6ea7b8817a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IsRead
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PartialReductionEqZeroOfFlatMapColumnZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
open GlobalTheory GlobalTheory.FlatRed
open GlobalTheory.FlatFactor GlobalTheory.LocFlat
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
variable {k : Type} [Field k]
namespace GlobalTheory.FlatRed
theorem _root_.solution (p : ℕ) (z : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) (y : n → k) :
    ch (z + colAt n' c p y) = ch z := by
  simp [ch, colAt]
end GlobalTheory.FlatRed
