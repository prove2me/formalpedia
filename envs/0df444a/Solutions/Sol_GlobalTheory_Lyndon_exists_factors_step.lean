-- Prove2me | solution 1 for GlobalTheory.Lyndon.exists_factors_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:26:03.256977+00:00
-- url     : https://prove2.me/submissions/cb7cf259-23ff-4c59-a32a-f3696eca7d6e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RadfordShufflePolynomialHolds
import Theorems.Thm_GlobalTheory_Lyndon_lt_of_isLyndon
import Theorems.Thm_GlobalTheory_Lyndon_lt_cases
import Theorems.Thm_GlobalTheory_Lyndon_append_lt_of_lt_of_length
import Theorems.Thm_GlobalTheory_Lyndon_append_lt_append_left
import Theorems.Thm_GlobalTheory_Lyndon_le_append
import Theorems.Thm_GlobalTheory_Lyndon_IsFactors_tail
import Theorems.Thm_GlobalTheory_Lyndon_exists_suffix_le_of_mem
import Theorems.Thm_GlobalTheory_Lyndon_exists_cut
import Theorems.Thm_GlobalTheory_Lyndon_exists_sorted

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Shuffle
open GlobalTheory.Lyndon
variable {A : Type} [LinearOrder A]
namespace GlobalTheory.Lyndon
theorem _root_.solution {L F : List (List A)} {a : A} {u : List A} {T : Multiset (List A)}
    (hL : IsFactors L) (hF : IsFactors F) (hu : F.flatten = u)
    (e : (L : Multiset (List A)) = (a :: u) ::ₘ T) :
    ∃ L', IsFactors L' ∧ (L' : Multiset (List A)) = ↑F + T ∧ a :: L'.flatten ≤ L.flatten := by
  cases L with
  | nil => exact absurd e.symm (Multiset.cons_ne_zero)
  | cons m L =>
    have hm := hL.1 m (by simp)
    have hmax := (List.pairwise_cons.1 hL.2).1
    rw [← Multiset.cons_coe] at e
    rcases Multiset.cons_eq_cons.1 e with ⟨e1, e2⟩ | ⟨hne, R, e1, e2⟩
    · subst e1 e2
      refine ⟨F ++ L, ⟨?_, List.pairwise_append.2 ⟨hF.2, hL.tail.2, ?_⟩⟩, by simp, by simp [hu]⟩
      · intro x hx
        rcases List.mem_append.1 hx with hx | hx
        · exact hF.1 x hx
        · exact hL.tail.1 x hx
      · intro f hf x hx
        obtain ⟨s, g, h1, h2, h3⟩ := exists_suffix_le_of_mem hF hf
        have : a :: u < g := lt_of_isLyndon hm (u := a :: s) (by simp) h1 (by simp [← hu, h2])
        exact le_trans (hmax x hx) (this.le.trans h3)
    · subst e2
      have hmem : ∀ x, x ∈ (a :: u) ::ₘ R → x ∈ L := fun x hx => by
        rw [← e1] at hx; exact Multiset.mem_coe.1 hx
      have hlt : a :: u < m :=
        lt_of_le_of_ne (hmax _ (hmem _ (Multiset.mem_cons_self _ _))) (Ne.symm hne)
      obtain ⟨P, P', eF, h1, h2⟩ := exists_cut m F hF.2
      obtain ⟨Q, hQ, hQs⟩ := exists_sorted ((P' : Multiset (List A)) + R)
      have hQm : ∀ x ∈ Q, x ∈ P' ∨ x ∈ L := fun x hx => by
        have : x ∈ (↑P' + R : Multiset (List A)) := by rw [← hQ]; exact Multiset.mem_coe.2 hx
        rcases Multiset.mem_add.1 this with h | h
        · exact Or.inl (Multiset.mem_coe.1 h)
        · exact Or.inr (hmem x (Multiset.mem_cons_of_mem h))
      have hQle : ∀ x ∈ Q, x ≤ m := fun x hx => (hQm x hx).elim (h2 x) (hmax x)
      subst eF
      refine ⟨P ++ m :: Q, ⟨?_, List.pairwise_append.2 ⟨(List.pairwise_append.1 hF.2).1,
        List.pairwise_cons.2 ⟨hQle, hQs⟩, ?_⟩⟩, ?_, ?_⟩
      · intro x hx
        rcases List.mem_append.1 hx with hx | hx
        · exact hF.1 x (List.mem_append_left _ hx)
        · rcases List.mem_cons.1 hx with rfl | hx
          · exact hm
          · exact (hQm x hx).elim (fun h => hF.1 x (List.mem_append_right _ h)) (hL.tail.1 x)
      · intro f hf x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact h1 f hf
        · exact le_trans (hQle x hx) (h1 f hf)
      · rw [← Multiset.coe_add, ← Multiset.coe_add, ← Multiset.cons_coe, hQ, Multiset.add_cons,
          Multiset.add_cons, add_assoc]
      · have hp : a :: P.flatten < m := by
          refine lt_of_le_of_lt ?_ hlt
          have := le_append (a :: P.flatten) P'.flatten
          simpa [← hu] using this
        have goal : (a :: P.flatten) ++ (m ++ Q.flatten) < m ++ L.flatten := by
          rcases lt_cases hp with h | ⟨q, hq, em⟩
          · exact h _ _
          · have h3 := append_lt_of_lt_of_length (lt_of_isLyndon hm (by simp) hq em)
              (by rw [em]; simp; omega) Q.flatten L.flatten
            have h4 := append_lt_append_left (a :: P.flatten) h3
            rwa [← List.append_assoc _ q, ← em] at h4
        simpa using goal.le
end GlobalTheory.Lyndon
