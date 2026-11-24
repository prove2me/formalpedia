-- Prove2me | solution 1 for GlobalTheory.FunObj.FiniteSupport.midLev_lt_of_symLev_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:47:12.184216+00:00
-- url     : https://prove2.me/submissions/a31b03aa-4520-4b1a-9b6b-92818972d053

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
variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
omit [Fintype n] [DecidableEq n]
namespace GlobalTheory.FunObj.FiniteSupport
theorem _root_.solution {r s : n ⊕ Fin c} (h : symLev c r < symLev c s) :
    midLev (c / 2) r < midLev (c / 2) s := by
  unfold symLev at h
  split_ifs at h
  · exact h
  · rcases r with r | r <;> rcases s with s | s <;> simp [lev, midLev] at h ⊢ <;> omega
end GlobalTheory.FunObj.FiniteSupport
