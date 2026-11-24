-- Prove2me | solution 1 for GlobalTheory.RootEx.Supp.Bd.mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:10:13.381328+00:00
-- url     : https://prove2.me/submissions/85dda46d-0d8d-42fe-82c6-ccc8974e8f10

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
namespace Bd
theorem _root_.solution {ι κ : Type} {γ δ : ValueGroupWithZero k} {x : Matrix ι κ k} (hx : Bd γ x) (h : γ ≤ δ) :
    Bd δ x := fun r s => (hx r s).trans h
end Bd
end GlobalTheory.RootEx.Supp
