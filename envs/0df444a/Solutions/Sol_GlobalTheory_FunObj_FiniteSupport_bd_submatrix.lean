-- Prove2me | solution 1 for GlobalTheory.FunObj.FiniteSupport.bd_submatrix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:46:54.472962+00:00
-- url     : https://prove2.me/submissions/a704689f-f4dd-42f4-82c7-e77cdbc140df

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CharEqOneOfOpENeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierJacobiUnipotentEqProdRootExchange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteUnfSupportOfNeOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.FunObj GlobalTheory.FunObj.FiniteSupport
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.RootEx.Supp GlobalTheory.RootEx.FJUnipotent
variable {k : Type} [Field k] {a c b : ℕ}
variable [ValuativeRel k]
namespace GlobalTheory.FunObj.FiniteSupport
theorem _root_.solution {ι κ ι' κ' : Type} {γ : ValueGroupWithZero k} {x : Matrix ι κ k} (hx : Bd γ x) (f : ι' → ι)
    (g : κ' → κ) : Bd γ (x.submatrix f g) := fun _ _ => hx _ _
end GlobalTheory.FunObj.FiniteSupport
