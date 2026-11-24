-- Prove2me | solution 1 for GlobalTheory.RootEx.TargetUnip.affPt_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:03:18.165104+00:00
-- url     : https://prove2.me/submissions/b9805f0d-0062-4a50-8de4-5970da789eaa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_OpEOmTargetUnipotent
import Theorems.Thm_GlobalTheory_RootEx_TargetUnip_affPt_of_not_free

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
omit [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
namespace GlobalTheory.RootEx.TargetUnip
theorem _root_.solution (p : ℕ) (x₀ : Matrix n n' k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) {r r' : n ⊕ Fin c} {s : n' ⊕ Fin (c + 1)}
    (hrs : ¬ Free p (r, s))
    (hl : lev p r < lev p r') : affPt p x₀ e r' s = 0 := by
  rcases r with r | r <;> rcases r' with r' | r' <;> rcases s with s | s <;>
    simp only [lev, Free, Sum.elim_inl, Sum.elim_inr, lt_irrefl] at hrs hl <;>
    rw [affPt_of_not_free _ _ _ (by simp only [Free]; omega)] <;>
    simp [basePt] <;> omega
end GlobalTheory.RootEx.TargetUnip
