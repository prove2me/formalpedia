-- Prove2me | solution 1 for HDXHitting.link_heredity
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T07:07:53.092865+00:00
-- url     : https://prove2.me/submissions/1a5c8158-6b61-419a-a808-92a4bf94116c

import Mathlib
import Definitions.Def_HDXHitting_IsTopDist
import Definitions.Def_HDXHitting_linkWeight
import Definitions.Def_HDXConc_SecondEigLE
import Definitions.Def_HDXHitting_IsOneSidedHDX
import Definitions.Def_HDXHitting_linkDist
import Definitions.Def_HDXHitting_IsRainbow
import Definitions.Def_HDXHitting_BipSingLE
import Definitions.Def_HDXHitting_IsPartiteHDX

section
set_option autoImplicit false
namespace HDXHitting.Dev.LH
open HDXHitting

noncomputable def Pm {V : Type*} [Fintype V] [DecidableEq V] (p : Finset V → ℝ) (τ : Finset V) : ℝ :=
  ∑ σ' ∈ Finset.univ.filter (fun σ' : Finset V => τ ⊆ σ'), p σ'

theorem ld_eq {V : Type*} [Fintype V] [DecidableEq V] (p : Finset V → ℝ) (τ σ : Finset V) :
    linkDist p τ σ = if Disjoint τ σ then p (τ ∪ σ) / Pm p τ else 0 := rfl

theorem sum_link {V : Type*} [Fintype V] [DecidableEq V] (τ : Finset V) (g : Finset V → ℝ) :
    ∑ σ : Finset V, (if Disjoint τ σ then g (τ ∪ σ) else 0) =
      ∑ σ' ∈ Finset.univ.filter (fun σ' : Finset V => τ ⊆ σ'), g σ' := by
  rw [← Finset.sum_filter]
  apply Finset.sum_nbij' (fun σ => τ ∪ σ) (fun σ => σ \ τ)
  · intro σ _; simp
  · intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
    exact Finset.disjoint_sdiff
  · intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    exact Finset.union_sdiff_cancel_left hσ
  · intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    exact Finset.union_sdiff_of_subset hσ
  · intro σ _; rfl

theorem lw_link_meet {V : Type*} [Fintype V] [DecidableEq V] (p : Finset V → ℝ)
    (τ τ' : Finset V) (hd : ¬ Disjoint τ τ') (u w : V) :
    linkWeight (linkDist p τ) τ' u w = 0 := by
  unfold linkWeight
  split_ifs with hc
  · apply Finset.sum_eq_zero
    intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    obtain ⟨x, hx1, hx2⟩ := Finset.not_disjoint_iff.mp hd
    have hxσ : x ∈ σ := hσ (by simp [hx2])
    have hn : ¬ Disjoint τ σ := Finset.not_disjoint_iff.mpr ⟨x, hx1, hxσ⟩
    rw [ld_eq, if_neg hn]
  · rfl

theorem lw_link_disjoint {V : Type*} [Fintype V] [DecidableEq V] (p : Finset V → ℝ)
    (τ τ' : Finset V) (hd : Disjoint τ τ') (u w : V) :
    linkWeight (linkDist p τ) τ' u w = (1 / Pm p τ) * linkWeight p (τ ∪ τ') u w := by
  by_cases hc : u ≠ w ∧ u ∉ τ ∪ τ' ∧ w ∉ τ ∪ τ'
  · obtain ⟨h1, h2, h3⟩ := hc
    rw [Finset.mem_union, not_or] at h2 h3
    have hcl : u ≠ w ∧ u ∉ τ' ∧ w ∉ τ' := ⟨h1, h2.2, h3.2⟩
    have hcr : u ≠ w ∧ u ∉ τ ∪ τ' ∧ w ∉ τ ∪ τ' := by
      refine ⟨h1, ?_, ?_⟩ <;> simp [h2, h3]
    unfold linkWeight
    rw [if_pos hcl, if_pos hcr]
    set g : Finset V → ℝ := fun σ' =>
      if insert u (insert w (τ ∪ τ')) ⊆ σ' then p σ' else 0 with hg
    have e1 : ∑ σ ∈ Finset.univ.filter (fun σ : Finset V => insert u (insert w τ') ⊆ σ),
        linkDist p τ σ = (1 / Pm p τ) * ∑ σ : Finset V, (if Disjoint τ σ then g (τ ∪ σ) else 0) := by
      rw [Finset.sum_filter, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro σ _
      rw [ld_eq]
      by_cases hs : Disjoint τ σ
      · rw [if_pos hs, if_pos hs, hg]
        simp only
        have hiff : insert u (insert w τ') ⊆ σ ↔ insert u (insert w (τ ∪ τ')) ⊆ τ ∪ σ := by
          constructor
          · intro H x hx
            simp only [Finset.mem_insert, Finset.mem_union] at hx H ⊢
            rcases hx with hx | hx | hx | hx
            · right; exact H (show x ∈ insert u (insert w τ') by simp [hx])
            · right; exact H (show x ∈ insert u (insert w τ') by simp [hx])
            · left; exact hx
            · right; exact H (show x ∈ insert u (insert w τ') by simp [hx])
          · intro H x hx
            simp only [Finset.mem_insert] at hx
            rcases hx with hx | hx | hx
            · have := H (show u ∈ insert u (insert w (τ ∪ τ')) by simp)
              rw [Finset.mem_union] at this
              rw [hx]
              rcases this with h | h
              · exact absurd h h2.1
              · exact h
            · have := H (show w ∈ insert u (insert w (τ ∪ τ')) by simp)
              rw [Finset.mem_union] at this
              rw [hx]
              rcases this with h | h
              · exact absurd h h3.1
              · exact h
            · have := H (show x ∈ insert u (insert w (τ ∪ τ')) by simp [hx])
              rw [Finset.mem_union] at this
              rcases this with h | h
              · exact absurd hx (Finset.disjoint_left.mp hd h)
              · exact h
        by_cases hA : insert u (insert w τ') ⊆ σ
        · rw [if_pos hA, if_pos (hiff.mp hA)]; ring
        · rw [if_neg hA, if_neg (fun H => hA (hiff.mpr H))]; simp
      · rw [if_neg hs, if_neg hs]; simp
    rw [e1, sum_link]
    congr 1
    rw [Finset.sum_filter, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro σ _
    rw [hg]
    simp only
    by_cases hB : insert u (insert w (τ ∪ τ')) ⊆ σ
    · have hτσ : τ ⊆ σ := fun x hx => hB (by simp [hx])
      rw [if_pos hB, if_pos hτσ]
    · simp [hB]
  · unfold linkWeight
    rw [if_neg hc, mul_zero]
    split_ifs with hcl
    · apply Finset.sum_eq_zero
      intro σ hσ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
      have : u ∈ τ ∨ w ∈ τ := by
        by_contra hn
        push Not at hn
        exact hc ⟨hcl.1, by simp [hn.1, hcl.2.1], by simp [hn.2, hcl.2.2]⟩
      have hn : ¬ Disjoint τ σ := by
        rcases this with h | h
        · exact Finset.not_disjoint_iff.mpr ⟨u, h, hσ (by simp)⟩
        · exact Finset.not_disjoint_iff.mpr ⟨w, h, hσ (by simp)⟩
      rw [ld_eq, if_neg hn]
    · rfl

theorem secondEig_scale {V : Type*} [Fintype V] (W : V → V → ℝ) (a lam : ℝ) (ha : 0 < a)
    (h : HDXConc.SecondEigLE Finset.univ W lam) :
    HDXConc.SecondEigLE Finset.univ (fun u w => a * W u w) lam := by
  intro g hg
  have hdeg : ∀ v, HDXConc.weightedDeg Finset.univ (fun u w => a * W u w) v =
      a * HDXConc.weightedDeg Finset.univ W v := by
    intro v; unfold HDXConc.weightedDeg; rw [Finset.mul_sum]
  simp only [hdeg] at hg ⊢
  have hg' : ∑ v, HDXConc.weightedDeg Finset.univ W v * g v = 0 := by
    have : a * ∑ v, HDXConc.weightedDeg Finset.univ W v * g v = 0 := by
      rw [Finset.mul_sum]; rw [← hg]; apply Finset.sum_congr rfl; intros; ring
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd h0 ha.ne'
    · exact h0
  have := h g hg'
  have e1 : ∑ u, ∑ v, a * W u v * g u * g v = a * ∑ u, ∑ v, W u v * g u * g v := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro u _
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring
  have e2 : ∑ v, a * HDXConc.weightedDeg Finset.univ W v * g v ^ 2 =
      a * ∑ v, HDXConc.weightedDeg Finset.univ W v * g v ^ 2 := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring
  rw [e1, e2]
  nlinarith

theorem secondEig_zero {V : Type*} [Fintype V] (W : V → V → ℝ) (lam : ℝ)
    (h0 : ∀ u w, W u w = 0) : HDXConc.SecondEigLE Finset.univ W lam := by
  intro g _
  simp [h0, HDXConc.weightedDeg]

theorem bip_scale {U W : Type*} [Fintype U] [Fintype W] (B : U → W → ℝ) (a lam : ℝ) (ha : 0 < a)
    (h : BipSingLE B lam) : BipSingLE (fun u w => a * B u w) lam := by
  intro g k hg hk
  have er : ∀ u, ∑ w, a * B u w = a * ∑ w, B u w := fun u => (Finset.mul_sum _ _ _).symm
  have ec : ∀ w, ∑ u, a * B u w = a * ∑ u, B u w := fun w => (Finset.mul_sum _ _ _).symm
  simp only [er] at hg
  simp only [ec] at hk
  have hg' : ∑ u, (∑ w, B u w) * g u = 0 := by
    have : a * ∑ u, (∑ w, B u w) * g u = 0 := by
      rw [Finset.mul_sum, ← hg]; apply Finset.sum_congr rfl; intros; ring
    exact (mul_eq_zero.mp this).resolve_left ha.ne'
  have hk' : ∑ w, (∑ u, B u w) * k w = 0 := by
    have : a * ∑ w, (∑ u, B u w) * k w = 0 := by
      rw [Finset.mul_sum, ← hk]; apply Finset.sum_congr rfl; intros; ring
    exact (mul_eq_zero.mp this).resolve_left ha.ne'
  have H := h g k hg' hk'
  simp only [er, ec]
  have e1 : ∑ u, ∑ w, a * B u w * g u * k w = a * ∑ u, ∑ w, B u w * g u * k w := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro u _
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring
  have e2 : ∑ u, a * (∑ w, B u w) * g u ^ 2 = a * ∑ u, (∑ w, B u w) * g u ^ 2 := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring
  have e3 : ∑ w, a * (∑ u, B u w) * k w ^ 2 = a * ∑ w, (∑ u, B u w) * k w ^ 2 := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring
  rw [e1, e2, e3]
  have := mul_le_mul_of_nonneg_left H (sq_nonneg a)
  nlinarith

end HDXHitting.Dev.LH
namespace HDXHitting
open HDXHitting.Dev.LH in
theorem chk_link_heredity {V ι : Type*} [Fintype V] [DecidableEq V] [DecidableEq ι] (d : ℕ)
    (p : Finset V → ℝ) (hp : IsTopDist d p) (τ : Finset V)
    (hτ : 0 < ∑ σ ∈ Finset.univ.filter (fun σ : Finset V => τ ⊆ σ), p σ) (lam : ℝ)
    (c : V → ι) (S : Finset ι) :
    IsTopDist (d - τ.card) (linkDist p τ) ∧
      (IsOneSidedHDX d p lam → IsOneSidedHDX (d - τ.card) (linkDist p τ) lam) ∧
      (IsRainbow p c S → IsRainbow (linkDist p τ) c (S \ τ.image c)) ∧
      (IsRainbow p c S → IsPartiteHDX p c S lam →
        IsPartiteHDX (linkDist p τ) c (S \ τ.image c) lam) := by
  have hP : 0 < Pm p τ := hτ
  have hcard : τ.card ≤ d := by
    obtain ⟨σ', hσ', hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hP.ne'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ'
    have := hp.2.1 σ' hne
    rw [← this]; exact Finset.card_le_card hσ'
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro σ
      rw [ld_eq]
      split_ifs
      · exact div_nonneg (hp.1 _) hP.le
      · exact le_rfl
    · intro σ hne
      rw [ld_eq] at hne
      by_cases hdj : Disjoint τ σ
      · rw [if_pos hdj] at hne
        have h1 : p (τ ∪ σ) ≠ 0 := fun h => hne (by rw [h]; simp)
        have := hp.2.1 _ h1
        rw [Finset.card_union_of_disjoint hdj] at this
        omega
      · rw [if_neg hdj] at hne; exact absurd rfl hne
    · have e : ∀ σ : Finset V, linkDist p τ σ =
          (1 / Pm p τ) * (if Disjoint τ σ then p (τ ∪ σ) else 0) := by
        intro σ; rw [ld_eq]; split_ifs <;> simp [div_eq_inv_mul]
      simp_rw [e]
      rw [← Finset.mul_sum, sum_link]
      show 1 / Pm p τ * Pm p τ = 1
      field_simp
  · intro hH τ' hτ'
    by_cases hd : Disjoint τ τ'
    · have hh := hH (τ ∪ τ') (by rw [Finset.card_union_of_disjoint hd]; omega)
      have : linkWeight (linkDist p τ) τ' = fun u w => (1 / Pm p τ) * linkWeight p (τ ∪ τ') u w := by
        funext u w; exact lw_link_disjoint p τ τ' hd u w
      rw [this]
      exact secondEig_scale _ _ _ (by positivity) hh
    · exact secondEig_zero _ _ (lw_link_meet p τ τ' hd)
  · intro hR σ hne
    rw [ld_eq] at hne
    by_cases hdj : Disjoint τ σ
    · rw [if_pos hdj] at hne
      have h1 : p (τ ∪ σ) ≠ 0 := fun h => hne (by rw [h]; simp)
      obtain ⟨hS, hU⟩ := hR _ h1
      have hnot : ∀ v ∈ σ, c v ∉ τ.image c := by
        intro v hv hmem
        obtain ⟨t, ht, hct⟩ := Finset.mem_image.mp hmem
        obtain ⟨x, _, hx⟩ := hU (c v) (hS v (Finset.mem_union_right _ hv))
        have a1 := hx t ⟨Finset.mem_union_left _ ht, hct⟩
        have a2 := hx v ⟨Finset.mem_union_right _ hv, rfl⟩
        exact Finset.disjoint_left.mp hdj ht (by rw [a1, ← a2]; exact hv)
      refine ⟨fun v hv => Finset.mem_sdiff.mpr ⟨hS v (Finset.mem_union_right _ hv), hnot v hv⟩, ?_⟩
      intro i hi
      obtain ⟨hiS, hiN⟩ := Finset.mem_sdiff.mp hi
      obtain ⟨x, ⟨hxm, hxc⟩, hxu⟩ := hU i hiS
      have hxσ : x ∈ σ := by
        rcases Finset.mem_union.mp hxm with h | h
        · exact absurd (Finset.mem_image.mpr ⟨x, h, hxc⟩) hiN
        · exact h
      exact ⟨x, ⟨hxσ, hxc⟩, fun y hy => hxu y ⟨Finset.mem_union_right _ hy.1, hy.2⟩⟩
    · rw [if_neg hdj] at hne; exact absurd rfl hne
  · intro _ hPH i hi j hj hij τ' hτ'
    obtain ⟨hiS, hiN⟩ := Finset.mem_sdiff.mp hi
    obtain ⟨hjS, hjN⟩ := Finset.mem_sdiff.mp hj
    by_cases hd : Disjoint τ τ'
    · have key := hPH i hiS j hjS hij (τ ∪ τ') (by
        intro v hv
        rcases Finset.mem_union.mp hv with h | h
        · exact ⟨fun e => hiN (Finset.mem_image.mpr ⟨v, h, e⟩),
            fun e => hjN (Finset.mem_image.mpr ⟨v, h, e⟩)⟩
        · exact hτ' v h)
      have : (fun u w => if c u = i ∧ c w = j then linkWeight (linkDist p τ) τ' u w else 0) =
          fun u w => (1 / Pm p τ) *
            (if c u = i ∧ c w = j then linkWeight p (τ ∪ τ') u w else 0) := by
        funext u w
        split_ifs
        · exact lw_link_disjoint p τ τ' hd u w
        · simp
      rw [this]
      exact bip_scale _ _ _ (by positivity) key
    · have : (fun u w => if c u = i ∧ c w = j then linkWeight (linkDist p τ) τ' u w else 0) =
          fun _ _ => 0 := by
        funext u w
        split_ifs
        · exact lw_link_meet p τ τ' hd u w
        · rfl
      rw [this]
      intro g h _ _
      simp
end HDXHitting
end

theorem solution : type_of% @HDXHitting.chk_link_heredity := @HDXHitting.chk_link_heredity
