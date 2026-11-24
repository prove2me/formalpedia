-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Multiset.exists_antitone_listing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:54:13.338244+00:00
-- url     : https://prove2.me/submissions/967efc7a-b835-4820-b99f-0db228fff10a

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MultisetAntitoneEnumeration

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Multiset
namespace GlobalTheory.CompanionTheory.Multiset
theorem _root_.solution {α : Type*} (m : Multiset α) (f : α → ℝ) (P : α → α → Prop)
    (hP : ∀ a b, P a b → f a < f b) :
    ∃ (h : ℕ) (Δ : Fin h → α), Finset.univ.val.map Δ = m ∧ Antitone (f ∘ Δ) ∧
      ∀ i j, i < j → ¬ P (Δ i) (Δ j) := by
  classical
  obtain ⟨l, rfl⟩ := Quot.exists_rep m
  let r : α → α → Prop := fun a b => f b ≤ f a
  haveI : DecidableRel r := fun _ _ => Classical.dec _
  haveI : IsTotal α r := ⟨fun a b => le_total (f b) (f a)⟩
  haveI : IsTrans α r := ⟨fun a b c h1 h2 => le_trans h2 h1⟩
  let l' := l.insertionSort r
  have hperm : l'.Perm l := List.perm_insertionSort r l
  have hsort : l'.Pairwise r := List.pairwise_insertionSort r l
  have hlt : ∀ i j : Fin l'.length, i < j → f (l'.get j) ≤ f (l'.get i) := by
    intro i j hij
    exact (List.pairwise_iff_get.mp hsort) i j hij
  refine ⟨l'.length, l'.get, ?_, ?_, ?_⟩
  · have h1 : (Finset.univ : Finset (Fin l'.length)).val.map l'.get = ((List.ofFn l'.get : List α) : Multiset α) := by
      rw [Fin.univ_val_map]
    rw [h1, List.ofFn_get]
    exact Quot.sound hperm
  · intro i j hij
    rcases hij.lt_or_eq with h | h
    · exact hlt i j h
    · subst h; exact le_rfl
  · intro i j hij hp
    exact absurd (hP _ _ hp) (not_lt.mpr (hlt i j hij))
end GlobalTheory.CompanionTheory.Multiset
