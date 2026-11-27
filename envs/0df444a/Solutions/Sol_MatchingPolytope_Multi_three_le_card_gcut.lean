-- Prove2me | solution 1 for MatchingPolytope.Multi.three_le_card_gcut
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:30:11.053601+00:00
-- url     : https://prove2.me/submissions/416545d9-9073-443a-a6bf-05593334d733

module
public import Definitions.Def_MatchingPolytope_Glue
public import Definitions.Def_MatchingPolytope_Induction
public import Theorems.Thm_MatchingPolytope_Multi_InHull_push
public import Theorems.Thm_MatchingPolytope_Multi_Valid_pair_of_mem
public import Theorems.Thm_MatchingPolytope_Multi_mem_gcut_singleton
public import Theorems.Thm_MatchingPolytope_Multi_sum_degree


set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope MatchingPolytope.Multi
open Finset
variable {V E : Type*} {ends : E → Sym2 V} {W : Finset V} {F : Finset E}
namespace MatchingPolytope.Multi
theorem _root_.solution [DecidableEq V] (hV : Valid ends W F) {x : E → ℝ} (hx : x ∈ Poly ends W F)
    (hirr : ¬ Reducible ends W F x) (hW5 : 5 ≤ W.card) {v : V} (hv : v ∈ W) :
    3 ≤ (gcut ends F {v}).card := by
  classical
  by_contra hlt
  push Not at hlt
  set N : Finset V := insert v ((gcut ends F {v}).biUnion
    fun e => W.filter fun u => u ∈ ends e ∧ u ≠ v) with hN
  have hinner : ∀ e ∈ gcut ends F {v}, (W.filter fun u => u ∈ ends e ∧ u ≠ v).card ≤ 1 := by
    intro e he
    rw [mem_gcut_singleton hV subset_rfl] at he
    obtain ⟨b, -, -, hb⟩ := hV.pair_of_mem he.1 he.2
    apply Finset.card_le_one.2
    intro u hu u' hu'
    simp only [Finset.mem_filter, hb, Sym2.mem_iff] at hu hu'
    rcases hu.2.1 with h | h
    · exact absurd h hu.2.2
    rcases hu'.2.1 with h' | h'
    · exact absurd h' hu'.2.2
    rw [h, h']
  have hNcard : N.card ≤ 3 := by
    have h1 := Finset.card_insert_le v ((gcut ends F {v}).biUnion
      fun e => W.filter fun u => u ∈ ends e ∧ u ≠ v)
    have h2 := Finset.card_biUnion_le (s := gcut ends F {v})
      (t := fun e => W.filter fun u => u ∈ ends e ∧ u ≠ v)
    have h3 : ∑ e ∈ gcut ends F {v}, (W.filter fun u => u ∈ ends e ∧ u ≠ v).card ≤
        ∑ e ∈ gcut ends F {v}, 1 := Finset.sum_le_sum hinner
    simp only [Finset.sum_const, smul_eq_mul, mul_one] at h3
    rw [← hN] at h1
    omega
  have hNW : N ⊆ W := by
    intro u hu
    rw [hN, Finset.mem_insert, Finset.mem_biUnion] at hu
    rcases hu with rfl | ⟨e, -, hu⟩
    · exact hv
    · exact (Finset.mem_filter.1 hu).1
  obtain ⟨S, hNS, hSW, hS3⟩ := Finset.exists_subsuperset_card_eq hNW hNcard (by omega)
  have hsub : gcut ends F {v} ⊆ inside ends F S := by
    intro e he
    have he' := (mem_gcut_singleton hV subset_rfl).1 he
    simp only [inside, Finset.mem_filter]
    refine ⟨he'.1, fun u hu => hNS ?_⟩
    by_cases huv : u = v
    · rw [huv, hN]; exact Finset.mem_insert_self _ _
    · rw [hN, Finset.mem_insert, Finset.mem_biUnion]
      exact Or.inr ⟨e, he, Finset.mem_filter.2 ⟨hV.sub e he'.1 u hu, hu, huv⟩⟩
  have hdeg := sum_degree hV subset_rfl S x
  rw [Finset.sum_congr rfl (fun u hu => hx.2.2.1 u (hSW hu))] at hdeg
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, hS3] at hdeg
  have hin : 1 ≤ ∑ e ∈ inside ends F S, x e := by
    rw [← hx.2.2.1 v hv]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun e _ _ => hx.2.1 e)
  have hodd : Odd S.card := by rw [hS3]; decide
  have hge := hx.2.2.2 S hSW hodd
  apply hirr
  refine Or.inr ⟨S, hSW, hodd, by omega, ?_, ?_⟩
  · have := Finset.card_sdiff_add_card_eq_card hSW
    omega
  · push_cast at hdeg
    linarith
end MatchingPolytope.Multi
