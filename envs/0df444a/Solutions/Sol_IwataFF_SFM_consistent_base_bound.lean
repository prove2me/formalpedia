-- Prove2me | solution 1 for IwataFF.SFM.consistent_base_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T12:13:10.123321+00:00
-- url     : https://prove2.me/submissions/2244e354-c896-43ec-af25-f622fd8ce41a

import Mathlib
import Definitions.Def_IwataFF_SFM_Basic
import Definitions.Def_IwataFF_SFM_Phase
import Definitions.Def_IwataFF_SFM_Main
open IwataFF.SFM

theorem g69g_reach_idx {α : Type} [DecidableEq α] (V : Finset α)
    (F : Finset (α × α)) (hF : ∀ e ∈ F, e.1 ∈ V ∧ e.2 ∈ V)
    (L : List α) (hL : IsOrdering V L) (hcons : IsConsistent F L) (v : α) (hv : v ∈ V) :
    ∀ b, Relation.ReflTransGen (fun a c => (a, c) ∈ F) v b → b ∈ L ∧ L.idxOf b ≤ L.idxOf v := by
  intro b hb
  induction hb with
  | refl => exact ⟨(hL.2 v).mpr hv, le_refl _⟩
  | @tail b c _ hbc ih =>
    have hc : c ∈ L := (hL.2 c).mpr (hF _ hbc).2
    refine ⟨hc, ?_⟩
    by_contra hlt
    push Not at hlt
    have hlt' : L.idxOf b < L.idxOf c := by omega
    exact hcons _ _ hlt' b c (List.getElem?_idxOf ih.1) (List.getElem?_idxOf hc) hbc

theorem g69g_consistent_bound {α : Type} [DecidableEq α] (V : Finset α)
    (f : Finset α → ℝ) (hsub : SubmodularOn V f)
    (F : Finset (α × α)) (hF : ∀ e ∈ F, e.1 ∈ V ∧ e.2 ∈ V)
    (L : List α) (hL : IsOrdering V L) (hcons : IsConsistent F L) :
    ∀ v ∈ V, greedy f L v ≤ f (reach V F v) - f ((reach V F v).erase v) := by
  classical
  intro v hv
  have hvL : v ∈ L := (hL.2 v).mpr hv
  set P := (L.take (L.idxOf v + 1)).toFinset with hP
  set Q := (L.take (L.idxOf v)).toFinset with hQ
  set R := reach V F v with hR
  have hg : greedy f L v = f P - f Q := by unfold greedy; rw [if_pos hvL]
  have memP : ∀ b, b ∈ P ↔ b ∈ L ∧ L.idxOf b ≤ L.idxOf v := by
    intro b; rw [hP, List.mem_toFinset]
    constructor
    · intro h; have hb := List.mem_of_mem_take h
      exact ⟨hb, by have := (List.mem_take_iff_idxOf_lt hb).mp h; omega⟩
    · rintro ⟨hb, hi⟩; exact (List.mem_take_iff_idxOf_lt hb).mpr (by omega)
  have memQ : ∀ b, b ∈ Q ↔ b ∈ L ∧ L.idxOf b < L.idxOf v := by
    intro b; rw [hQ, List.mem_toFinset]
    constructor
    · intro h; have hb := List.mem_of_mem_take h
      exact ⟨hb, (List.mem_take_iff_idxOf_lt hb).mp h⟩
    · rintro ⟨hb, hi⟩; exact (List.mem_take_iff_idxOf_lt hb).mpr hi
  have memR : ∀ b, b ∈ R → b ∈ L ∧ L.idxOf b ≤ L.idxOf v := by
    intro b hb
    rw [hR, reach, Finset.mem_filter] at hb
    exact g69g_reach_idx V F hF L hL hcons v hv b hb.2
  have hvR : v ∈ R := by
    rw [hR, reach, Finset.mem_filter]; exact ⟨hv, Relation.ReflTransGen.refl⟩
  have hRV : R ⊆ V := by rw [hR, reach]; exact Finset.filter_subset _ _
  have hQV : Q ⊆ V := by
    intro b hb; exact (hL.2 b).mp ((memQ b).mp hb).1
  have hU : R ∪ Q = P := by
    ext b; rw [Finset.mem_union, memP]
    constructor
    · rintro (h | h)
      · exact memR b h
      · have := (memQ b).mp h; exact ⟨this.1, this.2.le⟩
    · rintro ⟨hb, hi⟩
      rcases lt_or_eq_of_le hi with h | h
      · exact Or.inr ((memQ b).mpr ⟨hb, h⟩)
      · left; rw [(List.idxOf_inj hb).mp h]; exact hvR
  have hI : R ∩ Q = R.erase v := by
    ext b; rw [Finset.mem_inter, Finset.mem_erase, memQ]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨by rintro rfl; omega, h1⟩
    · rintro ⟨hne, h1⟩
      have := memR b h1
      refine ⟨h1, this.1, ?_⟩
      rcases lt_or_eq_of_le this.2 with h | h
      · exact h
      · exact absurd ((List.idxOf_inj this.1).mp h) hne
  have := hsub R hRV Q hQV
  rw [hU, hI] at this
  rw [hg]; linarith

theorem solution {α : Type} [DecidableEq α] (V : Finset α) (hV : V.Nonempty)
    (f : Finset α → ℝ) (hsub : SubmodularOn V f) (hf0 : f ∅ = 0)
    (F : Finset (α × α)) (hF : ∀ e ∈ F, e.1 ∈ V ∧ e.2 ∈ V)
    (L : List α) (hL : IsOrdering V L) (hcons : IsConsistent F L) :
    ∀ v ∈ V, greedy f L v ≤ f (reach V F v) - f ((reach V F v).erase v) :=
  g69g_consistent_bound V f hsub F hF L hL hcons
