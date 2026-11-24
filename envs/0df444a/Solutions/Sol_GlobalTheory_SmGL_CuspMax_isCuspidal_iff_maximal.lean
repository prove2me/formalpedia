-- Prove2me | solution 1 for GlobalTheory.SmGL.CuspMax.isCuspidal_iff_maximal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:17:12.552835+00:00
-- url     : https://prove2.me/submissions/071e3a24-6373-4742-b9a4-9437863d32f3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SubsingletonJacquetOfPerm
import Theorems.Thm_GlobalTheory_SmGL_CuspMax_unipRad_ne_bot_iff
import Theorems.Thm_GlobalTheory_SmGL_CuspMax_subsingleton_jacquet_of_perm
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.CuspMax
variable {R : Type} [CommRing R] {α β n : Type} {m : α → Type} {m' : β → Type}
  [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
  [Fintype β] [LinearOrder β] [∀ a, Fintype (m' a)] [∀ a, DecidableEq (m' a)]
  [Fintype n] [DecidableEq n]
namespace GlobalTheory.SmGL.CuspMax
theorem _root_.solution (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) :
    IsCuspidal π ↔ IsSmooth π ∧ ∀ (r t : ℕ) (h : r + t = N), 0 < r → 0 < t →
      Subsingleton (Jacquet π (unipRad k (two (stdSum h)))) := by
  refine and_congr_right fun _ => ⟨fun H r t h hr ht => ?_, fun H s d e he => ?_⟩
  · let f : Fin N → Fin 2 := fun i => if blk (two (stdSum h)) i then 1 else 0
    let e : (Σ a : Fin 2, Fin (Fintype.card {i // f i = a})) ≃ Fin N :=
      (Equiv.sigmaCongrRight fun a => (Fintype.equivFin {i // f i = a}).symm).trans
        (Equiv.sigmaFiberEquiv f)
    have hb : ∀ i, blk e i = f i := fun i => rfl
    have hlt : ∀ i j, blk e i < blk e j ↔ blk (two (stdSum h)) i < blk (two (stdSum h)) j := by
      intro i j
      rw [hb, hb]
      simp only [f]
      cases blk (two (stdSum h)) i <;> cases blk (two (stdSum h)) j <;> decide
    refine subsingleton_jacquet_of_perm π (e := e) 1 (fun i j hij => (hlt i j).1 hij)
      (H 2 _ e (unipRad_ne_bot_iff.2 ⟨two (stdSum h) ⟨false, ⟨0, hr⟩⟩, two (stdSum h) ⟨true, ⟨0, ht⟩⟩,
        (hlt _ _).2 ?_⟩))
    rw [blk_apply, blk_apply]
    decide
  · obtain ⟨i₀, j₀, hij⟩ := unipRad_ne_bot_iff.1 he
    let p : Fin N → Prop := fun i => blk e i ≤ blk e i₀
    have hsum : Fintype.card {i // p i} + Fintype.card {i // ¬ p i} = N := by
      rw [← Fintype.card_sum, Fintype.card_congr (Equiv.sumCompl p), Fintype.card_fin]
    let τ : Fin (Fintype.card {i // p i}) ⊕ Fin (Fintype.card {i // ¬ p i}) ≃ Fin N :=
      (Equiv.sumCongr (Fintype.equivFin _).symm (Fintype.equivFin _).symm).trans (Equiv.sumCompl p)
    refine subsingleton_jacquet_of_perm π (τ.symm.trans (stdSum hsum)) (fun i j hh => ?_)
      (H _ _ hsum (Fintype.card_pos_iff.2 ⟨⟨i₀, le_rfl⟩⟩) (Fintype.card_pos_iff.2 ⟨⟨j₀, hij.not_ge⟩⟩))
    obtain ⟨i, rfl⟩ := τ.surjective i
    obtain ⟨j, rfl⟩ := τ.surjective j
    simp only [Equiv.trans_apply, Equiv.symm_apply_apply] at hh
    rcases i with i | i <;> rcases j with j | j
    · rw [← two_false, ← two_false, blk_apply, blk_apply] at hh
      exact absurd hh (by decide)
    · have h1 : p (τ (.inl i)) := ((Fintype.equivFin {i // p i}).symm i).2
      have h2 : ¬ p (τ (.inr j)) := ((Fintype.equivFin {i // ¬ p i}).symm j).2
      exact lt_of_le_of_lt h1 (not_le.1 h2)
    · rw [← two_false, ← two_true, blk_apply, blk_apply] at hh
      exact absurd hh (by decide)
    · rw [← two_true, ← two_true, blk_apply, blk_apply] at hh
      exact absurd hh (by decide)
end GlobalTheory.SmGL.CuspMax
