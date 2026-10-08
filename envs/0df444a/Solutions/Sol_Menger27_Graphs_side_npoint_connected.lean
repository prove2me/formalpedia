-- Prove2me | solution 1 for Menger27.Graphs.side_npoint_connected
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T05:56:23.109073+00:00
-- url     : https://prove2.me/submissions/8640e8fc-fdbc-4e4c-9a29-b592087115c8

import Mathlib
import Definitions.Def_Menger27_Graphs_Separation
import Definitions.Def_Menger27_Graphs_Parts



namespace Menger27.Graphs

theorem sideVerts_not_mem {V : Type*} (G : SimpleGraph V) (P S : Finset V) {u : V}
    (hu : u ∈ sideVerts G P S) : u ∉ S := by
  obtain ⟨x, hx, w, hw⟩ := hu
  exact hw u w.end_mem_support

theorem sideVerts_of_P {V : Type*} (G : SimpleGraph V) (P S : Finset V) {x : V}
    (hx : x ∈ P) (hxS : x ∉ S) : x ∈ sideVerts G P S :=
  ⟨x, hx, SimpleGraph.Walk.nil, by simpa using hxS⟩

theorem first_hit {V : Type*} (G : SimpleGraph V) (P S : Finset V) {u y : V} (w : G.Walk u y) :
    u ∈ sideVerts G P S → (∃ v ∈ w.support, v ∈ S) →
    (∃ v ∈ w.support, v ∈ S ∧ v ∈ P) ∨
      ∃ v ∈ S, v ∉ P ∧ ∃ w' : (sidePart G P S).Walk u v, ∀ z ∈ w'.support, z ∈ w.support := by
  induction w with
  | nil =>
    intro hu ⟨v, hv, hvS⟩
    simp at hv
    subst hv
    exact absurd hvS (sideVerts_not_mem G P S hu)
  | @cons u z y h p ih =>
    intro hu ⟨v, hv, hvS⟩
    by_cases hz : z ∈ S
    · by_cases hzP : z ∈ P
      · exact Or.inl ⟨z, by simp, hz, hzP⟩
      · refine Or.inr ⟨z, hz, hzP, (show (sidePart G P S).Adj u z from
          ⟨h, Or.inl hu, Or.inl hu, Or.inr ⟨hz, hzP⟩⟩).toWalk, ?_⟩
        intro q hq
        simp at hq
        rcases hq with rfl | rfl <;> simp
    · have hzsv : z ∈ sideVerts G P S := by
        obtain ⟨x, hx, wx, hwx⟩ := hu
        refine ⟨x, hx, wx.concat h, ?_⟩
        intro q hq
        rw [SimpleGraph.Walk.support_concat] at hq
        simp at hq
        rcases hq with hq | rfl
        · exact hwx q hq
        · exact hz
      have hv' : ∃ v ∈ p.support, v ∈ S := by
        simp at hv
        rcases hv with rfl | hv
        · exact absurd hvS (sideVerts_not_mem G P S hu)
        · exact ⟨v, hv, hvS⟩
      rcases ih hzsv hv' with ⟨q, hq, hqS, hqP⟩ | ⟨q, hqS, hqP, w', hw'⟩
      · exact Or.inl ⟨q, by simp [hq], hqS, hqP⟩
      · refine Or.inr ⟨q, hqS, hqP, SimpleGraph.Walk.cons
          (show (sidePart G P S).Adj u z from ⟨h, Or.inl hu, Or.inl hu, Or.inl hzsv⟩) w', ?_⟩
        intro r hr
        simp at hr
        rcases hr with rfl | hr
        · simp
        · simp [hw' r hr]

theorem side_npoint_connected_core {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (P Q : Finset V) (hPQ : Disjoint P Q) (n : ℕ) (hG : NPointConnected G P Q n)
    (S : Finset V) (hS : Separates G P Q S) (hcard : S.card = n) :
    NPointConnected (sidePart G P S) (P \ S) (S \ P) (n - (S ∩ P).card) := by
  intro T hT
  have hsep : Separates G P Q (T ∪ (S ∩ P)) := by
    intro x hx y hy w
    by_cases hxS : x ∈ S
    · exact ⟨x, w.start_mem_support, Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hxS, hx⟩)⟩
    · obtain ⟨v, hv, hvS⟩ := hS x hx y hy w
      rcases first_hit G P S w (sideVerts_of_P G P S hx hxS) ⟨v, hv, hvS⟩ with
        ⟨q, hq, hqS, hqP⟩ | ⟨q, hqS, hqP, w', hw'⟩
      · exact ⟨q, hq, Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hqS, hqP⟩)⟩
      · obtain ⟨z, hz, hzT⟩ := hT x (Finset.mem_sdiff.mpr ⟨hx, hxS⟩) q
          (Finset.mem_sdiff.mpr ⟨hqS, hqP⟩) w'
        exact ⟨z, hw' z hz, Finset.mem_union_left _ hzT⟩
  have h1 := hG _ hsep
  have h2 := Finset.card_union_le T (S ∩ P)
  omega

end Menger27.Graphs

open Menger27.Graphs


theorem solution {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (P Q : Finset V) (hPQ : Disjoint P Q) (n : ℕ) (hG : NPointConnected G P Q n)
    (S : Finset V) (hS : Separates G P Q S) (hcard : S.card = n) :
    NPointConnected (sidePart G P S) (P \ S) (S \ P) (n - (S ∩ P).card) := by
  exact side_npoint_connected_core G P Q hPQ n hG S hS hcard
