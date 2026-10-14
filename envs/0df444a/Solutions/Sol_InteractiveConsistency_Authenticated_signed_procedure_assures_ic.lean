-- Prove2me | solution 1 for InteractiveConsistency.Authenticated.signed_procedure_assures_ic
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T04:55:27.177435+00:00
-- url     : https://prove2.me/submissions/328a5c36-e739-4915-ad3f-5cdabeda85a0

import Mathlib
import Definitions.Def_InteractiveConsistency_Authenticated_Procedure
set_option autoImplicit false


namespace InteractiveConsistency.Authenticated

theorem nonfaulty_origin_set_core {α V : Type*} [DecidableEq α]
    (P N : Finset α) (m : ℕ) (σ : List α → Option V)
    (hmn : m ≤ P.card) (hN : N ⊆ P) (hcount : P.card ≤ N.card + m)
    (hscenario : IsAuthScenario P σ)
    (hconsistent : AuthConsistent P N m σ)
    (p q : α) (hp : p ∈ N) (hq : q ∈ N) :
    ∃ v : V, σ [q] = some v ∧ S m P (view σ p) p q = {v} := by
  obtain ⟨h1, h2⟩ := hconsistent
  have hqP : q ∈ P := hN hq
  have hpP : p ∈ P := hN hp
  have hne : σ [q] ≠ none := hscenario q hqP
  obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp hne
  refine ⟨v, hv, ?_⟩
  ext v'
  simp only [S, view, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨w, hnd, hlen, hw, hval⟩
    have e : p :: (w ++ [q]) = (p :: w) ++ q :: [] := by simp
    rw [e] at hval
    have := h2 q hq (p :: w) [] (by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hpP
      · exact (hw x hx).1) (by simp) (by simp; omega)
    rcases this with h | h
    · rw [h, hv] at hval
      exact (Option.some.inj hval).symm
    · rw [h] at hval
      simp at hval
  · rintro rfl
    refine ⟨[], by simp, by simp, by simp, ?_⟩
    have := h1 q hq p hpP [] (by simp) (by simp)
    have e : σ (p :: ([] ++ [q])) = σ (p :: q :: []) := by simp
    rw [e, this]
    exact hv

theorem faulty_origin_set_subset_core {α V : Type*} [DecidableEq α]
    (P N : Finset α) (m : ℕ) (σ : List α → Option V)
    (hmn : m ≤ P.card) (hN : N ⊆ P) (hcount : P.card ≤ N.card + m)
    (hscenario : IsAuthScenario P σ)
    (hconsistent : AuthConsistent P N m σ)
    (p p' q : α) (hp : p ∈ N) (hp' : p' ∈ N)
    (hqP : q ∈ P) (hqN : q ∉ N) :
    S m P (view σ p) p q ⊆ S m P (view σ p') p' q := by
  obtain ⟨h1, h2⟩ := hconsistent
  have hpP := hN hp
  have hp'P := hN hp'
  rcases eq_or_ne p p' with hpp | hpp
  · subst hpp; exact le_rfl
  intro v hv
  simp only [S, view, Set.mem_ofPred_eq] at hv ⊢
  obtain ⟨w, hnd, hlen, hw, hval⟩ := hv
  have key : ∀ (a b : List α) (x : α), x ∈ N → w = a ++ x :: b →
      σ (x :: (b ++ [q])) = some v := by
    intro a b x hx hxw
    subst hxw
    have e : p :: ((a ++ x :: b) ++ [q]) = (p :: a) ++ x :: (b ++ [q]) := by simp
    rw [e] at hval
    have := h2 x hx (p :: a) (b ++ [q]) (by
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hpP
      · exact (hw y (by simp [hy])).1) (by
      intro y hy
      rcases List.mem_append.mp hy with hy | hy
      · exact (hw y (by simp [hy])).1
      · simp at hy; subst hy; exact hqP) (by simp at hlen ⊢; omega)
    rcases this with h | h
    · rw [← h]; exact hval
    · rw [h] at hval; simp at hval
  by_cases hmem : p' ∈ w
  · obtain ⟨a, b, hab⟩ := List.append_of_mem hmem
    have hk := key a b p' hp' hab
    have hsub : b.Sublist w := by
      rw [hab]; exact (List.sublist_cons_self p' b).trans (List.sublist_append_right a _)
    have hnd' := hnd
    rw [hab] at hnd'
    have hnb := (List.nodup_cons.mp (List.nodup_middle.mp hnd')).1
    refine ⟨b, hnd.sublist hsub, (hsub.length_le).trans hlen, ?_, hk⟩
    intro x hx
    refine ⟨(hw x (hsub.subset hx)).1, ?_, (hw x (hsub.subset hx)).2.2⟩
    rintro rfl
    exact hnb (List.mem_append_right _ hx)
  · by_cases hlt : w.length < m
    · refine ⟨p :: w, ?_, ?_, ?_, ?_⟩
      · exact List.nodup_cons.mpr ⟨fun h => (hw p h).2.1 rfl, hnd⟩
      · simp; omega
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ⟨hpP, hpp, fun h => hqN (h ▸ hp)⟩
        · exact ⟨(hw x hx).1, fun h => hmem (h ▸ hx), (hw x hx).2.2⟩
      · have := h1 p hp p' hp'P (w ++ [q]) (by
          intro y hy
          rcases List.mem_append.mp hy with hy | hy
          · exact (hw y hy).1
          · simp at hy; subst hy; exact hqP) (by simp; omega)
        have e : p' :: (p :: w ++ [q]) = p' :: p :: (w ++ [q]) := by simp
        rw [e, this]
        simpa using hval
    · have hlen' : w.length = m := le_antisymm hlen (not_lt.mp hlt)
      have hex : ∃ x ∈ w, x ∈ N := by
        by_contra hno
        push_neg at hno
        have hqw : q ∉ w := fun h => (hw q h).2.2 rfl
        have hsubset : insert q w.toFinset ⊆ P \ N := by
          intro y hy
          rcases Finset.mem_insert.mp hy with rfl | hy
          · exact Finset.mem_sdiff.mpr ⟨hqP, hqN⟩
          · have hy' := List.mem_toFinset.mp hy
            exact Finset.mem_sdiff.mpr ⟨(hw y hy').1, hno y hy'⟩
        have hc := Finset.card_le_card hsubset
        rw [Finset.card_insert_of_notMem (by simpa using hqw), List.toFinset_card_of_nodup hnd,
          Finset.card_sdiff_of_subset hN] at hc
        omega
      obtain ⟨x, hxw, hxN⟩ := hex
      obtain ⟨a, b, hab⟩ := List.append_of_mem hxw
      have hk := key a b x hxN hab
      have hsub : b.Sublist w := by
        rw [hab]; exact (List.sublist_cons_self x b).trans (List.sublist_append_right a _)
      have hnd' := hnd
      rw [hab] at hnd'
      have hnb := (List.nodup_cons.mp (List.nodup_middle.mp hnd')).1
      have hl : a.length + b.length + 1 = m := by rw [← hlen', hab]; simp; omega
      refine ⟨x :: b, List.nodup_cons.mpr ⟨fun h => hnb (List.mem_append_right _ h), hnd.sublist hsub⟩,
        by simp; omega, ?_, ?_⟩
      · intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact ⟨(hw y hxw).1, fun h => hmem (h ▸ hxw), (hw y hxw).2.2⟩
        · exact ⟨(hw y (hsub.subset hy)).1, fun h => hmem (h ▸ hsub.subset hy),
            (hw y (hsub.subset hy)).2.2⟩
      · have := h1 x hxN p' hp'P (b ++ [q]) (by
          intro y hy
          rcases List.mem_append.mp hy with hy | hy
          · exact (hw y (hsub.subset hy)).1
          · simp at hy; subst hy; exact hqP) (by simp; omega)
        have e : p' :: (x :: b ++ [q]) = p' :: x :: (b ++ [q]) := by simp
        rw [e, this]
        exact hk

theorem record_congr_core {α V : Type*} [DecidableEq α] (m : ℕ) (P : Finset α)
    (τ τ' : List α → Option V) (p p' q q' : α)
    (h : S m P τ p q = S m P τ' p' q') :
    record m P τ p q = record m P τ' p' q' := by
  classical
  have key : ∀ A B : Set V, A = B →
      (if h : ∃ v : V, A = {v} then some h.choose else none) =
      (if h : ∃ v : V, B = {v} then some h.choose else none) := by
    intro A B hAB
    subst hAB
    rfl
  unfold record
  exact key _ _ h

theorem signed_procedure_assures_ic_core {α V : Type*} [DecidableEq α]
    (P : Finset α) (m : ℕ) (hmn : m ≤ P.card) :
    ∀ N : Finset α, N ⊆ P → P.card ≤ N.card + m →
    ∀ σ : List α → Option V,
      IsAuthScenario P σ → AuthConsistent P N m σ →
      (∀ p ∈ N, ∀ q ∈ N, record m P (view σ p) p q = σ [q]) ∧
      (∀ p ∈ N, ∀ p' ∈ N, ∀ r ∈ P,
        record m P (view σ p) p r = record m P (view σ p') p' r) := by
  intro N hN hcount σ hsc hcons
  have hrec : ∀ p ∈ N, ∀ q ∈ N, record m P (view σ p) p q = σ [q] := by
    intro p hp q hq
    obtain ⟨v, hv, hS⟩ := nonfaulty_origin_set_core P N m σ hmn hN hcount hsc hcons p q hp hq
    unfold record
    have hex : ∃ v : V, S m P (view σ p) p q = {v} := ⟨v, hS⟩
    rw [dif_pos hex, hv]
    have := hS.symm.trans hex.choose_spec
    exact congrArg some (Set.singleton_eq_singleton_iff.mp this).symm
  refine ⟨hrec, ?_⟩
  intro p hp p' hp' r hr
  by_cases hrN : r ∈ N
  · rw [hrec p hp r hrN, hrec p' hp' r hrN]
  · apply record_congr_core
    exact Set.Subset.antisymm
      (faulty_origin_set_subset_core P N m σ hmn hN hcount hsc hcons p p' r hp hp' hr hrN)
      (faulty_origin_set_subset_core P N m σ hmn hN hcount hsc hcons p' p r hp' hp hr hrN)

end InteractiveConsistency.Authenticated

open InteractiveConsistency.Authenticated


theorem solution {α V : Type*} [DecidableEq α]
    (P : Finset α) (m : ℕ) (hmn : m ≤ P.card) :
    ∀ N : Finset α, N ⊆ P → P.card ≤ N.card + m →
    ∀ σ : List α → Option V,
      IsAuthScenario P σ → AuthConsistent P N m σ →
      (∀ p ∈ N, ∀ q ∈ N, record m P (view σ p) p q = σ [q]) ∧
      (∀ p ∈ N, ∀ p' ∈ N, ∀ r ∈ P,
        record m P (view σ p) p r = record m P (view σ p') p' r) := by
  exact signed_procedure_assures_ic_core P m hmn
