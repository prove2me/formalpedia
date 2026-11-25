-- Prove2me | solution 1 for GlobalTheory.FunObj.FiniteSupport.frameGL_symm_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:57:33.294065+00:00
-- url     : https://prove2.me/submissions/a76659fd-96c3-4e2f-a533-4f6020a6344c

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
namespace GlobalTheory.FunObj.FiniteSupport
theorem _root_.solution (h : a + c = b) (g : GL (Fin a ⊕ Fin c) k) :
    ((frameGL h).symm g).val = g.val.submatrix (frame h).symm (frame h).symm := rfl
end GlobalTheory.FunObj.FiniteSupport
