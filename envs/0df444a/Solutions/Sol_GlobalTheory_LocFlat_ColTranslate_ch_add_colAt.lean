-- Prove2me | solution 1 for GlobalTheory.LocFlat.ColTranslate.ch_add_colAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:39:27.553812+00:00
-- url     : https://prove2.me/submissions/084df240-d407-44bf-9b4c-15af7fa42604

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ContinuousWittExtendByZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatColumnMapEqRootExchangeOperatorTranslate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
open GlobalTheory GlobalTheory.LocFlat GlobalTheory.LocFlat.ColTranslate
open GlobalTheory.RootEx.Exchange GlobalTheory.LocFlat
namespace GlobalTheory.LocFlat.ColTranslate
theorem _root_.solution {k : Type} [Field k] {n n' : Type} {c : ℕ} (p : ℕ) (y : n → k)
    (z : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) : ch (z + colAt n' c p y) = ch z := by
  simp [ch, colAt]
end GlobalTheory.LocFlat.ColTranslate
