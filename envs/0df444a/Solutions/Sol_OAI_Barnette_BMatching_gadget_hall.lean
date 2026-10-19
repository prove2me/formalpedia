-- Prove2me | solution 1 for OAI.Barnette.BMatching.gadget_hall
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T04:26:11.362457+00:00
-- url     : https://prove2.me/submissions/e1f38b94-182f-4582-b987-c39d921942ed

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/BMatching.lean:L45-L136
-- (upload_full_project.md Phase 4): solution for node OAI.Barnette.BMatching.gadget_hall. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_BarnetteHamiltonian
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Network
import Definitions.Def_OAI_Combinatorics_Hamiltonian_CutSpaces
import Definitions.Def_OAI_Combinatorics_Hamiltonian_FlowCircuits
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Bonds
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Quotients
import Definitions.Def_OAI_Combinatorics_Hamiltonian_DiskRegions
import Definitions.Def_OAI_Combinatorics_Hamiltonian_StateDisk
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Circulation
import Definitions.Def_OAI_Combinatorics_Hamiltonian_TriangleSystem
import Definitions.Def_OAI_Combinatorics_Hamiltonian_ColoredDual
import Definitions.Def_OAI_Combinatorics_Hamiltonian_CycleReversal
import Definitions.Def_OAI_Combinatorics_Hamiltonian_PairPhases
import Definitions.Def_OAI_Combinatorics_Hamiltonian_PairPolynomials
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Forest
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Contraction
import Definitions.Def_OAI_Combinatorics_Hamiltonian_MinorDuality
import Definitions.Def_OAI_Combinatorics_Hamiltonian_BMatching

-- ---- from OAI.Combinatorics.Hamiltonian.BMatching ----
namespace OAI

/-! Integral flows, capacitated matchings, and incidence-state pairs. -/

namespace Barnette.BMatching
noncomputable section
open scoped Classical
variable {A B : Type*} [Fintype A] [Fintype B]

lemma count_sum {C D : Type*} [Fintype C] [Fintype D] (p : C ⊕ D → Prop) [DecidablePred p] :
    (Finset.univ.filter p).card = (Finset.univ.filter fun c => p (.inl c)).card +
      (Finset.univ.filter fun d => p (.inr d)).card := by
  simp only [Finset.card_filter,Fintype.sum_sum_type]

lemma count_prod {C D : Type*} [Fintype C] [Fintype D] (p : C × D → Prop) [DecidablePred p] :
    (Finset.univ.filter p).card = ∑ c, (Finset.univ.filter fun d => p (c,d)).card := by
  simp only [Finset.card_filter,Fintype.sum_prod_type]

lemma incidence_fiber (R : A → B → Prop) (S : Finset A) (b : B) :
    ((Finset.univ.filter fun e : Inc R => e.val.1 ∈ S).filter
      fun e => e.val.2 = b).card = (S.filter fun a => R a b).card := by
  apply Finset.card_bij (fun e _ => e.val.1)
  · intro e he
    obtain ⟨he,hb⟩ := Finset.mem_filter.mp he
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp he).2,hb ▸ e.property⟩
  · intro e he f hf hh
    apply Subtype.ext
    exact Prod.ext hh ((Finset.mem_filter.mp he).2.trans (Finset.mem_filter.mp hf).2.symm)
  · intro a ha
    obtain ⟨ha,hab⟩ := Finset.mem_filter.mp ha
    exact ⟨⟨(a,b),hab⟩,by simp [ha],rfl⟩

lemma gadget_hall (R : A → B → Prop)
    (hcap : ∀ S : Finset A, 2*S.card ≤ ∑ b, min 2 ((S.filter fun a => R a b).card))
    (L : Finset (Left R)) :
    L.card ≤ (Finset.univ.filter fun r : Right R => ∃ l ∈ L, gadget R l r).card := by
  let S := Finset.univ.filter fun a : A => ∃ k : Fin 2, Sum.inl (a,k) ∈ L
  let T := Finset.univ.filter fun e : Inc R => Sum.inr e ∈ L
  let I := Finset.univ.filter fun e : Inc R => e.val.1 ∈ S
  let Y := Finset.univ.filter fun b : B => ∃ e ∈ T, e.val.2 = b
  have hLc : L.card ≤ 2*S.card + T.card := by
    have hL : L = Finset.univ.filter (fun l => l ∈ L) := by ext; simp
    conv_lhs => rw [hL,count_sum (fun l : Left R => l ∈ L),count_prod]
    change (∑ a, (Finset.univ.filter fun k : Fin 2 => Sum.inl (a,k) ∈ L).card) +
      T.card ≤ _
    apply Nat.add_le_add_right
    calc
      _ ≤ ∑ a, if a ∈ S then 2 else 0 := by
        apply Finset.sum_le_sum
        intro a _
        by_cases ha : a ∈ S
        · simp only [ha,ite_true]
          exact le_trans (Finset.card_le_card (Finset.filter_subset _ _)) (by simp)
        · have hn : ∀ k : Fin 2, Sum.inl (a,k) ∉ L := by simpa [S] using ha
          simp [ha,hn]
      _ = 2*S.card := by simp [mul_comm]
  have hY (b : B) (k : Fin 2) :
      (∃ l ∈ L, gadget R l (.inl (b,k))) ↔ b ∈ Y := by
    constructor
    · rintro ⟨l,hl,hg⟩
      cases l with
      | inl a => exact hg.elim
      | inr e => exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,e,by simp [T,hl],hg⟩
    · intro hb
      obtain ⟨e,he,hb⟩ := (Finset.mem_filter.mp hb).2
      exact ⟨.inr e,(Finset.mem_filter.mp he).2,hb⟩
  have hI (e : Inc R) : (∃ l ∈ L, gadget R l (.inr e)) ↔ e ∈ I ∪ T := by
    constructor
    · rintro ⟨l,hl,hg⟩
      cases l with
      | inl a =>
        apply Finset.mem_union_left
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _,Finset.mem_filter.mpr ⟨Finset.mem_univ _,a.2,?_⟩⟩
        change e.val.1 = a.1 at hg
        simpa only [hg] using hl
      | inr f =>
        change f = e at hg
        exact Finset.mem_union_right _ (by simpa [T,← hg] using hl)
    · intro he
      rcases Finset.mem_union.mp he with he | he
      · obtain ⟨k,hk⟩ := (Finset.mem_filter.mp ((Finset.mem_filter.mp he).2)).2
        exact ⟨.inl (e.val.1,k),hk,rfl⟩
      · exact ⟨.inr e,(Finset.mem_filter.mp he).2,rfl⟩
  have hNc : (Finset.univ.filter fun r : Right R => ∃ l ∈ L, gadget R l r).card =
      2*Y.card + (I ∪ T).card := by
    rw [count_sum (fun r : Right R => ∃ l ∈ L, gadget R l r),count_prod]
    simp only [hY,hI]
    have hconst (b : B) : (Finset.univ.filter fun _ : Fin 2 => b ∈ Y).card =
        if b ∈ Y then 2 else 0 := by by_cases hb : b ∈ Y <;> simp [hb]
    have hfilter : (Finset.univ.filter fun e : Inc R => e ∈ I ∪ T) = I ∪ T := by ext; simp
    rw [hfilter]
    simp only [hconst]
    simp [mul_comm]
  have hcap' : 2*S.card ≤ 2*Y.card + (I \ T).card := by
    have hsum : ∑ b, min 2 ((S.filter fun a => R a b).card) ≤
        (∑ b, if b ∈ Y then 2 else 0) + ∑ b, ((I \ T).filter fun e => e.val.2 = b).card := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro b _
      by_cases hb : b ∈ Y
      · simp only [hb,ite_true]
        exact le_trans (Nat.min_le_left _ _) (Nat.le_add_right _ _)
      · have hIT : (I \ T).filter (fun e => e.val.2 = b) = I.filter (fun e => e.val.2 = b) := by
          ext e
          simp only [Finset.mem_filter,Finset.mem_sdiff]
          constructor
          · exact fun ⟨⟨hi,_⟩,he⟩ => ⟨hi,he⟩
          · rintro ⟨hi,he⟩
            refine ⟨⟨hi,fun ht => hb (Finset.mem_filter.mpr ⟨Finset.mem_univ _,e,ht,he⟩)⟩,he⟩
        rw [hIT]
        dsimp only [I]
        rw [incidence_fiber]
        simp only [hb,ite_false,zero_add]
        exact Nat.min_le_right _ _
    have hcount : ∑ b, ((I \ T).filter fun e => e.val.2 = b).card = (I \ T).card := by
      simpa using Finset.sum_card_fiberwise_eq_card_filter (I \ T) Finset.univ (fun e => e.val.2)
    rw [hcount] at hsum
    have hycount : (∑ b, if b ∈ Y then 2 else 0 : ℕ) = 2*Y.card := by
      simp [mul_comm]
    rw [hycount] at hsum
    exact (hcap S).trans hsum
  rw [hNc,← Finset.card_sdiff_add_card]
  omega

end
end Barnette.BMatching
namespace Barnette.BMatching
noncomputable section
open scoped Classical
variable {A B : Type*} [Fintype A] [Fintype B]

end
end Barnette.BMatching
namespace Barnette.TriangleSystem.State
variable {A V : Type*} {T : TriangleSystem A V} {X : Set V}
end Barnette.TriangleSystem.State

namespace Barnette.Network.ColoredDual
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  {N : Network V E} {D : Network F E} (M : N.ColoredDual D)

end
end Barnette.Network.ColoredDual

end OAI

-- ---- platform node ----
open OAI OAI.Barnette OAI.Barnette.BMatching
open scoped Classical


theorem solution : type_of% @_root_.OAI.Barnette.BMatching.gadget_hall := @_root_.OAI.Barnette.BMatching.gadget_hall
