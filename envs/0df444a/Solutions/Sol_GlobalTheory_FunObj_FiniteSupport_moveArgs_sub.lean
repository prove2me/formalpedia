-- Prove2me | solution 1 for GlobalTheory.FunObj.FiniteSupport.moveArgs_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:47:12.997393+00:00
-- url     : https://prove2.me/submissions/4609bc2f-d939-4b68-aca4-cf9742905c73

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
variable {k : Type} [Field k] {G : Grid k} (hs : 1 ≤ G.s)
namespace GlobalTheory.FunObj.FiniteSupport
theorem _root_.solution (g : G.VertexGroup) (z z' : G.Args) :
    G.moveArgs .one g (z - z') = G.moveArgs .one g z - G.moveArgs .one g z' := by
  funext b
  simp only [Grid.moveArgs, Pi.sub_apply, Matrix.mul_sub, Matrix.sub_mul]
end GlobalTheory.FunObj.FiniteSupport
