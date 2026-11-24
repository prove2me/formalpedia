-- Prove2me | solution 1 for GlobalTheory.FunObj.FiniteSupport.stepPt_shift
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:40:21.103329+00:00
-- url     : https://prove2.me/submissions/9252bc0d-ce3e-4398-9426-30986b2aac10

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
theorem _root_.solution {d : Shifts G} (hd : IsAuxiliaryHeckeCharacter d) (x : ColArgs G) (e : Vars G) (j : Fin (G.m - 1)) :
    stepPt (x j) ((shiftVars d + e) j) = stepPt (x j) (e j) + d j := by
  ext r s
  simp only [stepPt, Matrix.add_apply, of_apply]
  split_ifs with h
  · simp only [shiftVars, Pi.add_apply]; ring
  · rw [(hd j).1 r s fun h' => h (Or.inl h'), add_zero, add_zero]
end GlobalTheory.FunObj.FiniteSupport
