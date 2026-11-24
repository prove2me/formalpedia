-- Prove2me | solution 1 for GlobalTheory.RootEx.TargetUnip.det_linPart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:19:10.725135+00:00
-- url     : https://prove2.me/submissions/12e159b7-84c6-49ad-a551-59338a8c8397

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_OpEOmTargetUnipotent
import Theorems.Thm_GlobalTheory_RootEx_TargetUnip_det_eq_one_of_level

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.TargetUnip
variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}
variable {n' : Type*} [Fintype n'] [DecidableEq n']
open Classical
namespace GlobalTheory.RootEx.TargetUnip
theorem _root_.solution {p : ℕ} {h : GL (n ⊕ Fin c) k} (hh : InN p h) :
    (linPart (n' := n') p h.val).det = 1 := by
  refine det_eq_one_of_level (fun a => lev p a.1.1) _ fun a b hab => ?_
  simp only [linPart, Matrix.of_apply]
  rw [hh _ _ hab]
  simp only [Matrix.one_apply, Subtype.ext_iff, Prod.ext_iff]
  by_cases h1 : a.1.1 = b.1.1 <;> by_cases h2 : a.1.2 = b.1.2 <;> simp [h1, h2]
end GlobalTheory.RootEx.TargetUnip
