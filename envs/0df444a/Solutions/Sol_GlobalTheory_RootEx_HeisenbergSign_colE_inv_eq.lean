-- Prove2me | solution 1 for GlobalTheory.RootEx.HeisenbergSign.colE_inv_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:58:51.769127+00:00
-- url     : https://prove2.me/submissions/d679f7ce-dace-4182-8792-929467f847c6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FourierJacobiAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeSupportAndFourierRelation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ContinuousWittExtendByZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeHeisenbergVariableSign
import Theorems.Thm_GlobalTheory_RootEx_ExchangeSupport_colE_inv_val
import Theorems.Thm_GlobalTheory_RootEx_ExchangeSupport_colE_val


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.HeisenbergSign
namespace GlobalTheory.RootEx.HeisenbergSign
theorem _root_.solution {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] (c p : ℕ) (β : n → k) :
    ((colE c p β)⁻¹ : GL (n ⊕ Fin c) k).val = 1 - ((colE c p β).val - 1) := by
  rw [ExchangeSupport.colE_inv_val, ExchangeSupport.colE_val]
  ext (i | i) (j | j) <;> simp [Matrix.one_apply]
end GlobalTheory.RootEx.HeisenbergSign
