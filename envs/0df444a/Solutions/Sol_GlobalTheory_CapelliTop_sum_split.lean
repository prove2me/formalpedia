-- Prove2me | solution 1 for GlobalTheory.CapelliTop.sum_split
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:10:25.099642+00:00
-- url     : https://prove2.me/submissions/e235af53-d84e-484c-a65d-5eb97bdd5872

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_QdetTopThreeOrders

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open GlobalTheory GlobalTheory.CapelliTop
variable {A : Type} [Ring A] {n : ℕ}
namespace GlobalTheory.CapelliTop
theorem _root_.solution {M : Type} [AddCommMonoid M] (F : Finset (Fin n) → M) :
    ∑ S, F S = F ∅ + ∑ i, F {i} + ∑ i, ∑ j ∈ univ.filter (fun j => i < j), F {i, j} +
      ∑ S ∈ univ.filter (fun S : Finset (Fin n) => 3 ≤ S.card), F S := by
  have h0 : univ.filter (fun S : Finset (Fin n) => S.card = 0) = {∅} := by
    ext S; simp
  have h1 : ∑ S ∈ univ.filter (fun S : Finset (Fin n) => S.card = 1), F S = ∑ i, F {i} := by
    symm
    refine Finset.sum_bij (fun i _ => {i}) (by simp) (by simp) ?_ (by simp)
    intro S hS
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 (mem_filter.1 hS).2
    exact ⟨a, mem_univ _, rfl⟩
  have h2 : ∑ S ∈ univ.filter (fun S : Finset (Fin n) => S.card = 2), F S =
      ∑ i, ∑ j ∈ univ.filter (fun j => i < j), F {i, j} := by
    rw [Finset.sum_sigma']
    symm
    refine Finset.sum_bij (fun p _ => {p.1, p.2}) ?_ ?_ ?_ (by simp)
    · rintro ⟨i, j⟩ hp
      have : i < j := by simpa using hp
      simp [Finset.card_pair this.ne]
    · rintro ⟨i, j⟩ hp ⟨i', j'⟩ hp' h
      have a1 : i < j := by simpa using hp
      have a2 : i' < j' := by simpa using hp'
      have h' : ({i, j} : Finset (Fin n)) = {i', j'} := h
      have b1 : i ∈ ({i', j'} : Finset (Fin n)) := h' ▸ by simp
      have b2 : j ∈ ({i', j'} : Finset (Fin n)) := h' ▸ by simp
      have b3 : i' ∈ ({i, j} : Finset (Fin n)) := h' ▸ by simp
      simp only [mem_insert, mem_singleton] at b1 b2 b3
      have : i = i' ∧ j = j' := by omega
      obtain ⟨rfl, rfl⟩ := this
      rfl
    · intro S hS
      obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 (mem_filter.1 hS).2
      rcases lt_or_gt_of_ne hab with h | h
      · exact ⟨⟨a, b⟩, by simpa using h, rfl⟩
      · exact ⟨⟨b, a⟩, by simpa using h, Finset.pair_comm _ _⟩
  have h0' : F ∅ = ∑ S ∈ univ.filter (fun S : Finset (Fin n) => S.card = 0), F S := by
    rw [h0, Finset.sum_singleton]
  rw [← h1, ← h2, h0']
  simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun S _ => ?_
  rcases hc : S.card with _ | _ | _ | m <;> simp
end GlobalTheory.CapelliTop
