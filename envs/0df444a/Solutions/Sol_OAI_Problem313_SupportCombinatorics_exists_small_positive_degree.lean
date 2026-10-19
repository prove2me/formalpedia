-- Prove2me | solution 1 for OAI.Problem313.SupportCombinatorics.exists_small_positive_degree
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T02:04:47.268224+00:00
-- url     : https://prove2.me/submissions/8e2b611b-7532-4f05-b841-38aae19c48f2

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SharpThreshold/SupportDegree.lean:L88-L108
-- (upload_full_project.md Phase 4): solution for node OAI.Problem313.SupportCombinatorics.exists_small_positive_degree. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SharpThreshold
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Model
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockOrbit
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierBasis
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOrthogonality
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOption
import Definitions.Def_OAI_Combinatorics_SharpThreshold_SupportDegree

-- ---- from OAI.Combinatorics.SharpThreshold.SupportDegree ----
namespace OAI

universe u

/-! Elementary support-graph combinatorics, independent of probability. -/

namespace Problem313.SupportCombinatorics

open Finset

variable {α : Type u} [DecidableEq α]

lemma edge_subset_vertices {S : Finset (Finset α)} {e : Finset α}
    (he : e ∈ S) : e ⊆ vertices S := by
  intro u hu
  exact mem_biUnion.mpr ⟨e, he, hu⟩

lemma degree_pos_iff {S : Finset (Finset α)} {u : α} :
    0 < degree S u ↔ u ∈ vertices S := by
  simp [degree, vertices, card_pos, Finset.Nonempty]

lemma degree_le_card_vertices_sub_one {S : Finset (Finset α)}
    (hS : ∀ e ∈ S, e.card = 2) (u : α) :
    degree S u ≤ (vertices S).card - 1 := by
  have hinj : Set.InjOn (fun e : Finset α => e.erase u) (S.filter (fun e => u ∈ e)) := by
    intro e he f hf hef
    have he' := (mem_filter.mp he).2
    have hf' := (mem_filter.mp hf).2
    calc
      e = insert u (e.erase u) := (insert_erase he').symm
      _ = insert u (f.erase u) := congrArg (insert u) hef
      _ = f := insert_erase hf'
  have hsub : (S.filter (fun e => u ∈ e)).image (fun e => e.erase u) ⊆
      ((vertices S).erase u).powersetCard 1 := by
    intro e he
    obtain ⟨f, hf, rfl⟩ := mem_image.mp he
    obtain ⟨hfS, huf⟩ := mem_filter.mp hf
    apply mem_powersetCard.mpr
    constructor
    · exact erase_subset_erase u (edge_subset_vertices hfS)
    · rw [card_erase_of_mem huf, hS f hfS]
  have hcard := card_le_card hsub
  rw [card_image_of_injOn hinj, card_powersetCard, Nat.choose_one_right] at hcard
  by_cases hu : u ∈ vertices S
  · simpa [degree, card_erase_of_mem hu] using hcard
  · have hd : degree S u = 0 := by
      have := degree_pos_iff.not.mpr hu
      omega
    simp [hd]

lemma sum_degrees {S : Finset (Finset α)}
    (hS : ∀ e ∈ S, e.card = 2) :
    ∑ u ∈ vertices S, degree S u = 2 * S.card := by
  classical
  conv_lhs => simp only [degree, card_eq_sum_ones, sum_filter]
  rw [sum_comm]
  calc
    ∑ e ∈ S, ∑ u ∈ vertices S, (if u ∈ e then (1 : ℕ) else 0) = ∑ e ∈ S, e.card := by
      apply sum_congr rfl
      intro e he
      rw [← sum_filter]
      have hh : (vertices S).filter (fun u => u ∈ e) = e := by
        ext u
        simp only [mem_filter]
        exact and_iff_right_of_imp (fun hu => edge_subset_vertices he hu)
      simp [hh]
    _ = 2 * S.card := by
      rw [sum_congr rfl hS]
      simp [Nat.mul_comm]

lemma exists_small_positive_degree {S : Finset (Finset α)}
    (hS : ∀ e ∈ S, e.card = 2) (hne : S.Nonempty) :
    ∃ u ∈ vertices S, 1 ≤ degree S u ∧ (degree S u)^2 ≤ 2 * S.card := by
  have hv : (vertices S).Nonempty := by
    obtain ⟨e, he⟩ := hne
    have hepos : 0 < e.card := by rw [hS e he]; omega
    obtain ⟨u, hu⟩ := card_pos.mp hepos
    exact ⟨u, edge_subset_vertices he hu⟩
  obtain ⟨u, hu, hmin⟩ := exists_min_image (vertices S) (degree S) hv
  refine ⟨u, hu, degree_pos_iff.mpr hu, ?_⟩
  have hsum : (vertices S).card * degree S u ≤ 2 * S.card := by
    calc
      (vertices S).card * degree S u = ∑ v ∈ vertices S, degree S u := by simp
      _ ≤ ∑ v ∈ vertices S, degree S v := sum_le_sum (fun v hv => hmin v hv)
      _ = 2 * S.card := sum_degrees hS
  have hdeg := degree_le_card_vertices_sub_one hS u
  have hle : degree S u ≤ (vertices S).card := hdeg.trans (Nat.sub_le _ _)
  calc
    (degree S u)^2 = degree S u * degree S u := pow_two _
    _ ≤ (vertices S).card * degree S u := Nat.mul_le_mul_right _ hle
    _ ≤ 2 * S.card := hsum

end Problem313.SupportCombinatorics

end OAI

-- ---- platform node ----
open OAI OAI.Problem313 OAI.Problem313.SupportCombinatorics
open Finset


theorem solution.{u} : type_of% @_root_.OAI.Problem313.SupportCombinatorics.exists_small_positive_degree.{u} := @_root_.OAI.Problem313.SupportCombinatorics.exists_small_positive_degree.{u}
