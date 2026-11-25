-- Prove2me | solution 1 for GlobalTheory.LocFlat.ColTranslate.colE_neg_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:42:17.010803+00:00
-- url     : https://prove2.me/submissions/4f7fa756-ff8c-4787-a9c9-6cc16322d6ad

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
theorem _root_.solution {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] (c p : ℕ) (y : n → k) :
    ((colE c p (-y))⁻¹ : GL (n ⊕ Fin c) k).val = (colE c p y).val := by
  ext r s
  rcases r with r | r <;> rcases s with s | s <;>
    simp [colE, upU, -Matrix.coe_units_inv, Units.inv_mk, neg_ite]
end GlobalTheory.LocFlat.ColTranslate
