-- Prove2me | solution 1 for GlobalTheory.RootEx.Exchange.colE_inv_mul_affPt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:00:50.905948+00:00
-- url     : https://prove2.me/submissions/e2d051cd-5b10-4503-b386-f2bc45cfb4d7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ContinuousWittExtendByZero
import Theorems.Thm_GlobalTheory_RootEx_Exchange_colE_inv_mul
import Theorems.Thm_GlobalTheory_RootEx_Exchange_affPt_eq

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
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.Exchange
variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
omit [Fintype n']
namespace GlobalTheory.RootEx.Exchange
theorem _root_.solution (q : Fin c) (β : n → k) (x₀ : Matrix n n' k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free (q.val + 1) rs} → k) :
    ((colE c (q.val + 1) β)⁻¹ : GL (n ⊕ Fin c) k).val * affPt (q.val + 1) x₀ e =
      mat x₀ (ext0 (Free (q.val + 1)) (e + sCol q β e) + gCol q (-β)) := by
  ext r s
  rw [colE_inv_mul, affPt_eq]
  rcases r with r | r <;> rcases s with s | s
  · simp [mat, ext0, gCol, sCol, Free, basePt]
  · rcases lt_trichotomy s q.castSucc with h | h | h
    · have h' : s.val < q.val := h
      simp [mat, ext0, gCol, sCol, Free, basePt, h'.not_gt, h.ne, h'.ne']
    · subst h
      simp [mat, ext0, gCol, sCol, Free, basePt]
    · have h' : q.val < s.val := h
      have h1 : Free (q.val + 1) ((Sum.inl r : n ⊕ Fin c), (Sum.inr s : n' ⊕ Fin (c + 1))) := by
        simpa [Free] using h'
      have h2 : Free (q.val + 1) ((Sum.inr q : n ⊕ Fin c), (Sum.inr s : n' ⊕ Fin (c + 1))) := by
        simpa [Free] using h'
      simp [mat, ext0, gCol, sCol, basePt, h1, h2, h.ne', h'.ne]
  · by_cases h : Free (q.val + 1) ((Sum.inr r : n ⊕ Fin c), (Sum.inl s : n' ⊕ Fin (c + 1))) <;>
      simp [mat, ext0, gCol, sCol, h]
  · by_cases h : Free (q.val + 1) ((Sum.inr r : n ⊕ Fin c), (Sum.inr s : n' ⊕ Fin (c + 1))) <;>
      simp [mat, ext0, gCol, sCol, h]
end GlobalTheory.RootEx.Exchange
