-- Prove2me | solution 1 for GlobalTheory.RootEx.TargetUnip.mul_affPt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:19:11.591856+00:00
-- url     : https://prove2.me/submissions/55a061c9-2632-43c9-9a5f-6919f3ad69c8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_OpEOmTargetUnipotent
import Theorems.Thm_GlobalTheory_RootEx_TargetUnip_mul_apply_of_inN
import Theorems.Thm_GlobalTheory_RootEx_TargetUnip_affPt_of_not_free
import Theorems.Thm_GlobalTheory_RootEx_TargetUnip_affPt_eq_zero
import Theorems.Thm_GlobalTheory_RootEx_TargetUnip_linPart_mulVec

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
theorem _root_.solution {p : ℕ} {h : GL (n ⊕ Fin c) k} (hh : InN p h) (x₀ : Matrix n n' k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) :
    h.val * affPt p x₀ e = affPt p x₀ ((linPart p h.val).mulVec e +
      fun a => (h.val * basePt c x₀ - basePt c x₀) a.1.1 a.1.2) := by
  ext r s
  by_cases hf : Free p (r, s)
  · have : affPt p x₀ ((linPart p h.val).mulVec e +
      fun a => (h.val * basePt c x₀ - basePt c x₀) a.1.1 a.1.2) r s =
        basePt c x₀ r s + ((linPart p h.val).mulVec e ⟨(r, s), hf⟩ +
          (h.val * basePt c x₀ - basePt c x₀) r s) := by
      simp [affPt, hf]
    rw [this, linPart_mulVec, affPt, Matrix.mul_add, Matrix.add_apply, Matrix.sub_apply]
    simp only [Matrix.mul_apply, Matrix.of_apply]
    ring
  · rw [affPt_of_not_free _ _ _ hf, mul_apply_of_inN hh, affPt_of_not_free _ _ _ hf,
      Finset.sum_eq_zero, add_zero]
    intro r' _
    split_ifs with hl
    · rw [affPt_eq_zero p x₀ e hf hl, mul_zero]
    · rfl
end GlobalTheory.RootEx.TargetUnip
