-- Prove2me | solution 1 for GlobalTheory.RootEx.Exchange.affPt_mul_rowE
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:02:06.276892+00:00
-- url     : https://prove2.me/submissions/5bf20c48-06e4-4d74-9caf-d830aeab597c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ContinuousWittExtendByZero
import Theorems.Thm_GlobalTheory_RootEx_Exchange_mul_rowE
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
omit [Fintype n]
namespace GlobalTheory.RootEx.Exchange
theorem _root_.solution (q : Fin c) (u : n' → k) (x₀ : Matrix n n' k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free (q.val + 1) rs} → k) :
    affPt (q.val + 1) x₀ e * (rowE (c + 1) (q.val + 1) u).val =
      mat x₀ (ext0 (Free (q.val + 1)) (e + sRow q u e) + gRow q u) := by
  ext r s
  have := mul_rowE q.castSucc u (affPt (q.val + 1) x₀ e) r s
  rw [Fin.val_castSucc] at this
  rw [this, affPt_eq]
  rcases r with r | r <;> rcases s with s | s
  · simp [mat, ext0, gRow, sRow, Free, basePt]
  · by_cases h : Free (q.val + 1) ((Sum.inl r : n ⊕ Fin c), (Sum.inr s : n' ⊕ Fin (c + 1))) <;>
      simp [mat, ext0, gRow, sRow, h]
  · rcases lt_trichotomy r q with h | h | h
    · have h' : r.val < q.val := h
      have h1 : Free (q.val + 1) ((Sum.inr r : n ⊕ Fin c), (Sum.inl s : n' ⊕ Fin (c + 1))) := by
        simpa [Free] using h'
      have h2 : Free (q.val + 1) ((Sum.inr r : n ⊕ Fin c), (Sum.inr q.castSucc : n' ⊕ Fin (c + 1))) := by
        simpa [Free] using h'
      simp [mat, ext0, gRow, sRow, basePt, h1, h2, h.ne, h'.ne]
    · subst h
      simp [mat, ext0, gRow, sRow, Free, basePt]
    · have h' : q.val < r.val := h
      simp [mat, ext0, gRow, sRow, Free, basePt, h'.le, h'.not_gt, h.ne', h'.ne']
  · by_cases h : Free (q.val + 1) ((Sum.inr r : n ⊕ Fin c), (Sum.inr s : n' ⊕ Fin (c + 1))) <;>
      simp [mat, ext0, gRow, sRow, h]
end GlobalTheory.RootEx.Exchange
