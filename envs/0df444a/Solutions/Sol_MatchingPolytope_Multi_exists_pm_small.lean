-- Prove2me | solution 1 for MatchingPolytope.Multi.exists_pm_small
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:30:04.565806+00:00
-- url     : https://prove2.me/submissions/7955892d-f457-4ad6-b26e-537883468939

module
public import Definitions.Def_MatchingPolytope_Glue
public import Definitions.Def_MatchingPolytope_Induction
public import Theorems.Thm_MatchingPolytope_Multi_Valid_pair
public import Theorems.Thm_MatchingPolytope_Multi_Valid_pair_of_mem
public import Theorems.Thm_MatchingPolytope_Multi_even_card_of_mem_poly
public import Theorems.Thm_MatchingPolytope_Multi_gcut_compl
public import Theorems.Thm_MatchingPolytope_Multi_mem_gcut_singleton
public import Theorems.Thm_MatchingPolytope_Multi_mem_inside_of_pair
public import Theorems.Thm_MatchingPolytope_Multi_sum_degree


set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope MatchingPolytope.Multi
open Finset
variable {V E : Type*} {ends : E → Sym2 V} {W : Finset V} {F : Finset E}
namespace MatchingPolytope.Multi
theorem _root_.solution (hV : Valid ends W F) {x : E → ℝ} (hx : x ∈ Poly ends W F)
    (hW4 : W.card ≤ 4) : ∃ M, IsPM ends W F M := by
  classical
  have hW := even_card_of_mem_poly hV hx
  rcases Nat.eq_zero_or_pos W.card with h0 | hpos
  · refine ⟨∅, Finset.empty_subset _, fun v hv => ?_⟩
    rw [Finset.card_eq_zero.1 h0] at hv
    simp at hv
  obtain ⟨a, ha⟩ := Finset.card_pos.1 hpos
  have hsa := hx.2.2.1 a ha
  obtain ⟨e, he, hxe⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by rw [hsa]; norm_num :
    ∑ e ∈ gcut ends F {a}, x e ≠ 0)
  rw [mem_gcut_singleton hV subset_rfl] at he
  obtain ⟨heF, hae⟩ := he
  obtain ⟨b, hba, hbW, hab⟩ := hV.pair_of_mem heF hae
  have hxe' : 0 < x e := lt_of_le_of_ne (hx.2.1 e) (Ne.symm hxe)
  set A : Finset V := {a, b} with hA
  have hAW : A ⊆ W := by
    intro u hu; simp only [hA, Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl <;> assumption
  have hAcard : A.card = 2 := Finset.card_pair (Ne.symm hba)
  have hmemA : ∀ v, v ∈ ends e ↔ v ∈ A := by
    intro v; rw [hab]; simp [hA]
  obtain ⟨k, hk⟩ := hW
  have hcases : W.card = 2 ∨ W.card = 4 := by omega
  rcases hcases with h2 | h4
  · -- `W = {a, b}` and `{e}` is a perfect matching
    have hWA : W = A := (Finset.eq_of_subset_of_card_le hAW (by omega)).symm
    refine ⟨{e}, Finset.singleton_subset_iff.2 heF, fun v hv => ?_⟩
    rw [Finset.card_eq_one]
    refine ⟨e, ?_⟩
    ext e'
    rw [mem_gcut_singleton hV (Finset.singleton_subset_iff.2 heF), Finset.mem_singleton]
    constructor
    · exact fun h => h.1
    · rintro rfl; exact ⟨rfl, (hmemA v).2 (hWA ▸ hv)⟩
  · set B := W \ A with hB
    have hBcard : B.card = 2 := by
      have := Finset.card_sdiff_add_card_eq_card hAW
      rw [← hB] at this
      omega
    have hBW : B ⊆ W := Finset.sdiff_subset
    -- the inner weights of `A` and `B` agree
    have hA2 := sum_degree hV subset_rfl A x
    have hB2 := sum_degree hV subset_rfl B x
    rw [Finset.sum_congr rfl (fun v hv => hx.2.2.1 v (hAW hv))] at hA2
    rw [Finset.sum_congr rfl (fun v hv => hx.2.2.1 v (hBW hv))] at hB2
    rw [hB, gcut_compl hV subset_rfl] at hB2
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hA2 hB2
    rw [hAcard] at hA2
    rw [← hB, hBcard] at hB2
    have heA : e ∈ inside ends F A := by
      rw [mem_inside_of_pair hab]
      exact ⟨heF, by simp [hA], by simp [hA]⟩
    have hinA : x e ≤ ∑ e ∈ inside ends F A, x e :=
      Finset.single_le_sum (fun e _ => hx.2.1 e) heA
    have hinB : ∑ e ∈ inside ends F B, x e ≠ 0 := by
      push_cast at hA2 hB2
      linarith
    obtain ⟨g, hg, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hinB
    simp only [inside, Finset.mem_filter] at hg
    obtain ⟨hgF, hgB⟩ := hg
    obtain ⟨c, c', hcc', -, -, hgc⟩ := hV.pair hgF
    have hcB : c ∈ B := hgB c (by simp [hgc])
    have hc'B : c' ∈ B := hgB c' (by simp [hgc])
    have hmemB : ∀ v, v ∈ ends g ↔ v ∈ B := by
      intro v
      constructor
      · exact hgB v
      · intro hv
        by_contra hvg
        rw [hgc, Sym2.mem_iff, not_or] at hvg
        have hsub : ({v, c, c'} : Finset V) ⊆ B := by
          intro u hu
          simp only [Finset.mem_insert, Finset.mem_singleton] at hu
          rcases hu with rfl | rfl | rfl <;> assumption
        have := Finset.card_le_card hsub
        rw [Finset.card_insert_of_notMem (by simp [hvg.1, hvg.2]),
          Finset.card_pair hcc'] at this
        omega
    have hdisj : ∀ v, v ∈ A → v ∉ B := fun v hv hvB => (Finset.mem_sdiff.1 hvB).2 hv
    have heg : e ≠ g := by
      rintro rfl
      exact hdisj a (by simp [hA]) ((hmemB a).1 hae)
    have hMF : ({e, g} : Finset E) ⊆ F := by
      intro u hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl <;> assumption
    refine ⟨{e, g}, hMF, fun v hv => ?_⟩
    rw [Finset.card_eq_one]
    by_cases hvA : v ∈ A
    · refine ⟨e, ?_⟩
      ext e'
      rw [mem_gcut_singleton hV hMF, Finset.mem_singleton]
      simp only [Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨rfl | rfl, h⟩
        · rfl
        · exact absurd ((hmemB v).1 h) (hdisj v hvA)
      · rintro rfl; exact ⟨Or.inl rfl, (hmemA v).2 hvA⟩
    · have hvB : v ∈ B := Finset.mem_sdiff.2 ⟨hv, hvA⟩
      refine ⟨g, ?_⟩
      ext e'
      rw [mem_gcut_singleton hV hMF, Finset.mem_singleton]
      simp only [Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨rfl | rfl, h⟩
        · exact absurd ((hmemA v).1 h) hvA
        · rfl
      · rintro rfl; exact ⟨Or.inr rfl, (hmemB v).2 hvB⟩
end MatchingPolytope.Multi
