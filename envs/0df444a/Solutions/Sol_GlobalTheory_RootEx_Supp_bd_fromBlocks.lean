-- Prove2me | solution 1 for GlobalTheory.RootEx.Supp.bd_fromBlocks
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:03:13.030129+00:00
-- url     : https://prove2.me/submissions/9eab41ff-d9e5-4d35-9df8-7bc0e0dbc507

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CharEqOneOfOpENeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.Supp
variable {k : Type} [Field k] [ValuativeRel k]
namespace GlobalTheory.RootEx.Supp
theorem _root_.solution {ι κ ι' κ' : Type} {γ : ValueGroupWithZero k} {a : Matrix ι κ k} {b : Matrix ι κ' k}
    {c : Matrix ι' κ k} {d : Matrix ι' κ' k} (ha : Bd γ a) (hb : Bd γ b) (hc : Bd γ c) (hd : Bd γ d) :
    Bd γ (fromBlocks a b c d) := by
  rintro (r | r) (s | s)
  exacts [ha r s, hb r s, hc r s, hd r s]
end GlobalTheory.RootEx.Supp
