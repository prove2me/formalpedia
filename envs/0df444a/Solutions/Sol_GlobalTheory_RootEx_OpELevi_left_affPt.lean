-- Prove2me | solution 1 for GlobalTheory.RootEx.OpELevi.left_affPt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:06:04.863949+00:00
-- url     : https://prove2.me/submissions/ac964de3-899c-427f-b925-8054772867b7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralCompBlocks
import Theorems.Thm_GlobalTheory_RootEx_OpELevi_affPt_eq
import Theorems.Thm_GlobalTheory_RootEx_OpELevi_ext_free
import Theorems.Thm_GlobalTheory_RootEx_OpELevi_ext_not_free
import Theorems.Thm_GlobalTheory_RootEx_OpELevi_left_inl
import Theorems.Thm_GlobalTheory_RootEx_OpELevi_left_inr

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
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.OpELevi
variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
omit [DecidableEq n] [Fintype n'] [DecidableEq n']
namespace GlobalTheory.RootEx.OpELevi
theorem _root_.solution (p : ℕ) (A : Matrix n n k) (x₀ : Matrix n n' k) (e) :
    (fromBlocks A 0 0 1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) * affPt (c := c) p x₀ e
      = affPt p (A * x₀) (TL p A e) := by
  rw [affPt_eq, affPt_eq, Matrix.mul_add]
  congr 1
  · simp [basePt, fromBlocks_multiply]
  · ext r s
    by_cases h : Free p (r, s)
    · rw [ext_free _ _ _ _ h]; rfl
    · rw [ext_not_free _ _ _ _ h]
      rcases r with r | r
      · rw [left_inl]
        refine Finset.sum_eq_zero fun t _ => ?_
        rw [ext_not_free, mul_zero]
        rcases s with s | s <;> exact h
      · rw [left_inr, ext_not_free _ _ _ _ h]
end GlobalTheory.RootEx.OpELevi
