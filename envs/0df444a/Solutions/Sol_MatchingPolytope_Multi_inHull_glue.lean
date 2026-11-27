-- Prove2me | solution 1 for MatchingPolytope.Multi.inHull_glue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:32:09.210818+00:00
-- url     : https://prove2.me/submissions/4260899a-031a-4261-85a6-ecf20fc649a7

module
public import Definitions.Def_MatchingPolytope_Shrink
public import Definitions.Def_MatchingPolytope_Glue
public import Theorems.Thm_MatchingPolytope_Multi_gw_nonneg
public import Theorems.Thm_MatchingPolytope_Multi_gw_ne_zero
public import Theorems.Thm_MatchingPolytope_Multi_gw_left
public import Theorems.Thm_MatchingPolytope_Multi_gw_right
public import Theorems.Thm_MatchingPolytope_Multi_gcut_subset_shrinkF
public import Theorems.Thm_MatchingPolytope_Multi_isPM_union
public import Theorems.Thm_MatchingPolytope_Multi_mem_gcut_of_mem_both
public import Theorems.Thm_P2M_MatchingPolytope_Multi_gcut_subset_shrinkF__d7b6c02936a8
public import Theorems.Thm_MatchingPolytope_Multi_mem_shrinkF_or
public import Theorems.Thm_MatchingPolytope_Multi_eval_sum_smul_chi
public import Theorems.Thm_MatchingPolytope_Multi_InHull_push
public import Theorems.Thm_MatchingPolytope_Multi_IsPM_of_shrink
public import Theorems.Thm_MatchingPolytope_Multi_gcut_compl
public import Theorems.Thm_MatchingPolytope_Multi_gcut_subset
public import Theorems.Thm_MatchingPolytope_Multi_shrinkF_subset
public import Theorems.Thm_MatchingPolytope_Multi_sum_chi_gcut


set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope MatchingPolytope.Multi
open Finset
variable {V E : Type*}
variable {ends : E → Sym2 V} {W : Finset V} {F : Finset E}
variable [DecidableEq V]
namespace MatchingPolytope.Multi
theorem _root_.solution [Fintype E] (hV : Valid ends W F) {x : E → ℝ} (hx : x ∈ Poly ends W F)
    (hpos : ∀ e ∈ F, 0 < x e) {S : Finset V} (hSW : S ⊆ W) {s t : V} (hs : s ∈ S)
    (ht : t ∈ W \ S)
    (h1 : InHull (IsPM (shrinkEnds ends S s) (shrinkW W S s) (shrinkF ends F S))
      (restr (shrinkF ends F S) x))
    (h2 : InHull (IsPM (shrinkEnds ends (W \ S) t) (shrinkW W (W \ S) t)
      (shrinkF ends F (W \ S))) (restr (shrinkF ends F (W \ S)) x)) :
    InHull (IsPM ends W F) x := by
  classical
  set F1 := shrinkF ends F S with hF1
  set F2 := shrinkF ends F (W \ S) with hF2
  set C := gcut ends F S with hC
  obtain ⟨w1, h10, h11, h12, h13⟩ := h1
  obtain ⟨w2, h20, h21, h22, h23⟩ := h2
  have hS' : W \ S ⊆ W := Finset.sdiff_subset
  have hWS : W \ (W \ S) = S := Finset.sdiff_sdiff_eq_self hSW
  -- properties of the matchings on each side
  have pm1 : ∀ M, w1 M ≠ 0 → M ⊆ F1 ∧ (gcut ends M S).card = 1 ∧
      ∀ v ∈ W, v ∉ S → (gcut ends M {v}).card = 1 :=
    fun M hM => (h11 M hM).of_shrink hV hSW hs
  have pm2 : ∀ N, w2 N ≠ 0 → N ⊆ F2 ∧ (gcut ends N S).card = 1 ∧
      ∀ v ∈ W, v ∈ S → (gcut ends N {v}).card = 1 := by
    intro N hN
    obtain ⟨a, b, c⟩ := (h21 N hN).of_shrink hV hS' ht
    refine ⟨a, ?_, fun v hv hvS => c v hv (fun h => (Finset.mem_sdiff.1 h).2 hvS)⟩
    rwa [gcut_compl hV (a.trans (shrinkF_subset _))] at b
  have hCF1 : C ⊆ F1 := gcut_subset_shrinkF (fun u hu => hu)
  have hCF2 : C ⊆ F2 := gcut_subset_shrinkF' S
  have hxC : ∀ g ∈ C, x g ≠ 0 := fun g hg => (hpos g (gcut_subset _ _ hg)).ne'
  have ev1 : ∀ e, ∑ M, w1 M * chi M e = restr F1 x e := fun e => by
    rw [← h13, eval_sum_smul_chi]
  have ev2 : ∀ e, ∑ N, w2 N * chi N e = restr F2 x e := fun e => by
    rw [← h23, eval_sum_smul_chi]
  have hc1 : ∀ g ∈ C, ∑ M, w1 M * chi M g = x g := fun g hg => by
    rw [ev1]; simp [restr, hCF1 hg]
  have hc2 : ∀ g ∈ C, ∑ N, w2 N * chi N g = x g := fun g hg => by
    rw [ev2]; simp [restr, hCF2 hg]
  have hd1 : ∀ M, w1 M ≠ 0 → ∑ g ∈ C, chi M g = 1 := fun M hM => by
    obtain ⟨a, b, -⟩ := pm1 M hM
    rw [hC, sum_chi_gcut (a.trans (shrinkF_subset _)), b]; simp
  have hd2 : ∀ N, w2 N ≠ 0 → ∑ g ∈ C, chi N g = 1 := fun N hN => by
    obtain ⟨a, b, -⟩ := pm2 N hN
    rw [hC, sum_chi_gcut (a.trans (shrinkF_subset _)), b]; simp
  -- a nonzero glued weight gives two matchings with the same cut edge
  have hpair : ∀ p : Finset E × Finset E, gw C x w1 w2 p ≠ 0 →
      gcut ends p.1 S = gcut ends p.2 S ∧ w1 p.1 ≠ 0 ∧ w2 p.2 ≠ 0 := by
    intro p hp
    obtain ⟨g, hgC, hg1, hg2, hw1, hw2⟩ := gw_ne_zero hp
    obtain ⟨a1, b1, -⟩ := pm1 _ hw1
    obtain ⟨a2, b2, -⟩ := pm2 _ hw2
    have hgC' := hgC
    simp only [hC, gcut, Finset.mem_filter] at hgC'
    have m1 : g ∈ gcut ends p.1 S := by
      simp only [gcut, Finset.mem_filter]; exact ⟨hg1, hgC'.2⟩
    have m2 : g ∈ gcut ends p.2 S := by
      simp only [gcut, Finset.mem_filter]; exact ⟨hg2, hgC'.2⟩
    obtain ⟨g1, hg1'⟩ := Finset.card_eq_one.1 b1
    obtain ⟨g2, hg2'⟩ := Finset.card_eq_one.1 b2
    rw [hg1'] at m1 ⊢
    rw [hg2'] at m2 ⊢
    rw [Finset.mem_singleton] at m1 m2
    exact ⟨by rw [← m1, ← m2], hw1, hw2⟩
  have hsum : ∑ p, gw C x w1 w2 p = 1 := by
    have := gw_left hxC hc2 hd1 (fun _ => 1)
    simp only [mul_one] at this
    rw [this, h12]
  have key := InHull.push (Q := IsPM ends W F) (gw C x w1 w2) (gw_nonneg
    (fun g hg => hpos g (gcut_subset _ _ hg)) h10 h20) hsum (fun p => p.1 ∪ p.2) (by
      intro p hp
      obtain ⟨hcut, hw1, hw2⟩ := hpair p hp
      obtain ⟨a1, -, c1⟩ := pm1 _ hw1
      obtain ⟨a2, -, c2⟩ := pm2 _ hw2
      exact isPM_union hV a1 a2 hcut c1 c2)
  convert key using 1
  funext e
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  by_cases he : e ∈ F1 ∨ e ∉ F2
  · have hterm : ∀ p : Finset E × Finset E,
        gw C x w1 w2 p * chi (p.1 ∪ p.2) e = gw C x w1 w2 p * chi p.1 e := by
      intro p
      by_cases hp : gw C x w1 w2 p = 0
      · simp [hp]
      obtain ⟨hcut, hw1, hw2⟩ := hpair p hp
      obtain ⟨a2, -, -⟩ := pm2 _ hw2
      congr 1
      have : e ∈ p.2 → e ∈ p.1 := by
        intro he2
        have heF2 : e ∈ F2 := a2 he2
        have heF1 : e ∈ F1 := he.resolve_right (not_not.2 heF2)
        have heC : e ∈ gcut ends p.2 S := by
          have := mem_gcut_of_mem_both hV heF1 heF2
          simp only [gcut, Finset.mem_filter] at this ⊢
          exact ⟨he2, this.2⟩
        rw [← hcut] at heC
        exact gcut_subset _ _ heC
      simp only [chi, Finset.mem_union]
      by_cases h1 : e ∈ p.1
      · simp [h1]
      · simp [h1, show e ∉ p.2 from fun h => h1 (this h)]
    rw [Finset.sum_congr rfl (fun p _ => hterm p), gw_left hxC hc2 hd1 (fun M => chi M e), ev1]
    simp only [restr]
    split_ifs with h
    · rfl
    · have heF : e ∉ F := by
        intro heF
        rcases mem_shrinkF_or hV (S := S) heF with h' | h'
        · exact h h'
        · exact (he.resolve_left h) h'
      exact hx.1 e heF
  · push Not at he
    obtain ⟨he1, he2⟩ := he
    have hterm : ∀ p : Finset E × Finset E,
        gw C x w1 w2 p * chi (p.1 ∪ p.2) e = gw C x w1 w2 p * chi p.2 e := by
      intro p
      by_cases hp : gw C x w1 w2 p = 0
      · simp [hp]
      obtain ⟨-, hw1, -⟩ := hpair p hp
      obtain ⟨a1, -, -⟩ := pm1 _ hw1
      congr 1
      have : e ∉ p.1 := fun h => he1 (a1 h)
      simp [chi, this]
    rw [Finset.sum_congr rfl (fun p _ => hterm p), gw_right hxC hc1 hd2 (fun N => chi N e), ev2]
    simp [restr, he2]
end MatchingPolytope.Multi
