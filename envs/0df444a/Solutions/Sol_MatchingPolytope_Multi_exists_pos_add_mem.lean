-- Prove2me | solution 1 for MatchingPolytope.Multi.exists_pos_add_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:30:07.324239+00:00
-- url     : https://prove2.me/submissions/9af19410-1700-4c6a-966b-6a3c2010b3c2

module
public import Definitions.Def_MatchingPolytope_Glue
public import Definitions.Def_MatchingPolytope_Induction
public import Theorems.Thm_MatchingPolytope_Multi_odd_card_sdiff
public import Theorems.Thm_MatchingPolytope_Multi_sum_add_smul
public import Theorems.Thm_MatchingPolytope_Multi_even_card_of_mem_poly
public import Theorems.Thm_MatchingPolytope_Multi_gcut_compl


set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope MatchingPolytope.Multi
open Finset
variable {V E : Type*} {ends : E → Sym2 V} {W : Finset V} {F : Finset E}
namespace MatchingPolytope.Multi
theorem _root_.solution [DecidableEq V] (hV : Valid ends W F) {y d : E → ℝ}
    (hy : y ∈ Poly ends W F)
    (hirr : ¬ Reducible ends W F y) (hd : Ker ends W F d) :
    ∃ ε : ℝ, 0 < ε ∧ y + ε • d ∈ Poly ends W F := by
  have hW := even_card_of_mem_poly hV hy
  have hpos : ∀ e ∈ F, 0 < y e := by
    intro e he
    refine lt_of_le_of_ne (hy.2.1 e) ?_
    intro h
    exact hirr (Or.inl ⟨e, he, h.symm⟩)
  have hnt : ∀ S ∈ W.powerset.filter (fun S => Odd S.card ∧ 1 < S.card ∧ 1 < (W \ S).card),
      1 < ∑ e ∈ gcut ends F S, y e := by
    intro S hS
    rw [Finset.mem_filter, Finset.mem_powerset] at hS
    refine lt_of_le_of_ne (hy.2.2.2 S hS.1 hS.2.1) ?_
    intro h
    exact hirr (Or.inr ⟨S, hS.1, hS.2.1, hS.2.2.1, hS.2.2.2, h.symm⟩)
  have hev : ∀ᶠ ε in nhds (0 : ℝ), (∀ e ∈ F, 0 < y e + ε * d e) ∧
      (∀ S ∈ W.powerset.filter (fun S => Odd S.card ∧ 1 < S.card ∧ 1 < (W \ S).card),
        1 < ∑ e ∈ gcut ends F S, y e + ε * ∑ e ∈ gcut ends F S, d e) := by
    refine Filter.Eventually.and ?_ ?_
    · rw [Filter.eventually_all_finset]
      intro e he
      have hc : Continuous fun ε : ℝ => y e + ε * d e := by fun_prop
      exact continuousAt_const.eventually_lt hc.continuousAt (by simpa using hpos e he)
    · rw [Filter.eventually_all_finset]
      intro S hS
      have hc : Continuous fun ε : ℝ =>
          ∑ e ∈ gcut ends F S, y e + ε * ∑ e ∈ gcut ends F S, d e := by fun_prop
      exact continuousAt_const.eventually_lt hc.continuousAt (by simpa using hnt S hS)
  obtain ⟨ε, hε, hε1, hε2⟩ := hev.exists_gt
  refine ⟨ε, hε, fun e he => ?_, fun e => ?_, fun v hv => ?_, fun S hS hodd => ?_⟩
  · simp [hy.1 e he, hd.1 e he]
  · by_cases he : e ∈ F
    · exact (hε1 e he).le
    · simp [hy.1 e he, hd.1 e he]
  · rw [sum_add_smul, hy.2.2.1 v hv, hd.2 v hv]; ring
  · rw [sum_add_smul]
    by_cases h1 : S.card = 1
    · obtain ⟨v, rfl⟩ := Finset.card_eq_one.1 h1
      have hv : v ∈ W := hS (Finset.mem_singleton_self v)
      rw [hy.2.2.1 v hv, hd.2 v hv]; norm_num
    by_cases h2 : (W \ S).card = 1
    · obtain ⟨v, hv'⟩ := Finset.card_eq_one.1 h2
      have hv : v ∈ W := Finset.sdiff_subset (hv' ▸ Finset.mem_singleton_self v)
      rw [← gcut_compl hV subset_rfl, hv', hy.2.2.1 v hv, hd.2 v hv]; norm_num
    have hodd' := odd_card_sdiff hS hW hodd
    have hS1 : 1 < S.card := by
      obtain ⟨k, hk⟩ := hodd; omega
    have hS2 : 1 < (W \ S).card := by
      obtain ⟨k, hk⟩ := hodd'; omega
    have := hε2 S (by rw [Finset.mem_filter, Finset.mem_powerset]; exact ⟨hS, hodd, hS1, hS2⟩)
    exact this.le
end MatchingPolytope.Multi
