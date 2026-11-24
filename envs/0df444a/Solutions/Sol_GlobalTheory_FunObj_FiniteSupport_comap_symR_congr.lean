-- Prove2me | solution 1 for GlobalTheory.FunObj.FiniteSupport.comap_symR_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:47:03.865418+00:00
-- url     : https://prove2.me/submissions/90141156-1259-48ce-bca8-d4672d3ff00c

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
theorem _root_.solution {c' : ℕ} (hc : c = c') (h : a + c = b) (h' : a + c' = b) :
    (symR k (Fin a) c).comap (frameGL h).toMonoidHom = (symR k (Fin a) c').comap (frameGL h').toMonoidHom := by
  subst hc; rfl
end GlobalTheory.FunObj.FiniteSupport
