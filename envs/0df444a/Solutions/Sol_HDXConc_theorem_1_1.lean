-- Prove2me | solution 1 for HDXConc.theorem_1_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:38:09.234762+00:00
-- url     : https://prove2.me/submissions/d30ef515-d05c-478d-b8a4-8f97cc78c045

import Mathlib
import Definitions.Def_SteurerHDX_IsPure
import Definitions.Def_HDXConc_IsTopDensity
import Definitions.Def_HDXConc_IsTopLinkExpander
import Definitions.Def_HDXConc_walkOp
import Theorems.Thm_HDXConc_upper_tail

section
set_option autoImplicit false
namespace HDXConc.Dev.T11
open HDXConc

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma topMean_eq {X : Finset (Finset V)} {d : ℕ} (hd : 2 ≤ d) (hX : SteurerHDX.IsSimplicialComplex X)
    (ρ : Finset V → ℝ) (f : V → ℝ) :
    topMean X d ρ (topSum f) = (d : ℝ) * vertexMean X d ρ f := by
  have hd0 : (d : ℝ) ≠ 0 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  unfold topMean topSum vertexMean faceMeasure
  simp only [Nat.choose_one_right, Finset.sum_filter, Finset.singleton_subset_iff]
  -- RHS
  have : ∀ v, (1 / (d : ℝ)) * (∑ t ∈ SteurerHDX.faces X d, if v ∈ t then ρ t else 0) * f v
      = (1 / (d : ℝ)) * ∑ t ∈ SteurerHDX.faces X d, (if v ∈ t then ρ t * f v else 0) := by
    intro v
    rw [mul_assoc, Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl; intro t _
    split_ifs <;> simp
  have e : ∑ v ∈ vertices X, (1 / (d : ℝ)) * (∑ t ∈ SteurerHDX.faces X d, if v ∈ t then ρ t else 0) * f v
      = (1 / (d : ℝ)) * ∑ t ∈ SteurerHDX.faces X d, ρ t * ∑ v ∈ t, f v := by
    simp_rw [this]
    rw [← Finset.mul_sum, Finset.sum_comm]
    congr 1
    apply Finset.sum_congr rfl; intro t ht
    rw [Finset.mul_sum]
    have hsub : t ⊆ vertices X := by
      intro v hv
      simp only [vertices, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hX t (Finset.mem_filter.1 ht).1 {v} (Finset.singleton_subset_iff.2 hv)
    rw [← Finset.sum_filter]
    have h1 : (vertices X).filter (fun v => v ∈ t) = t := by
      ext v; simp only [Finset.mem_filter]; exact ⟨fun h => h.2, fun h => ⟨hsub h, h⟩⟩
    rw [h1]
  rw [e]; field_simp

end HDXConc.Dev.T11
namespace HDXConc
open HDXConc.Dev.T11 in
theorem chk_theorem_1_1 {V : Type*} [Fintype V] [DecidableEq V] {d : ℕ} (hd : 2 ≤ d) {η : ℝ} (hη0 : 0 < η)
    (hη1 : η ≤ 1) {X : Finset (Finset V)} {π : Finset V → ℝ} (hX : SteurerHDX.IsPure X d)
    (hπ : IsTopDensity X d π) (hexp : IsTopLinkExpander X d π ((1 - η) / ((d : ℝ) - 1)))
    (f : V → ℝ) (hf : ∀ v, ({v} : Finset V) ∈ X → 0 ≤ f v ∧ f v ≤ 1) {α : ℝ} (hα : 0 < α) :
    ∑ s ∈ (SteurerHDX.faces X d).filter
        (fun s => α < |(1 / (d : ℝ)) * ∑ v ∈ s, f v - vertexMean X d π f|), π s ≤
      2 * Real.exp (-(η / 4) * α ^ 2 * (d : ℝ)) := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  have hsc : SteurerHDX.IsSimplicialComplex X := hX.1
  set μ := vertexMean X d π f with hμ
  have hm : topMean X d π (topSum f) = d * μ := topMean_eq hd hsc π f
  have hE : 0 ≤ Real.exp (-(η / 4) * α ^ 2 * (d : ℝ)) := (Real.exp_pos _).le
  have hπnn : ∀ s, s ∈ SteurerHDX.faces X d → 0 ≤ π s := fun s hs => (hπ.pos s hs).le
  -- F bounds on facets
  have hFb : ∀ σ ∈ SteurerHDX.faces X d, 0 ≤ topSum f σ ∧ topSum f σ ≤ d := by
    intro σ hσ
    have hc : σ.card = d := (Finset.mem_filter.1 hσ).2
    have hv : ∀ v ∈ σ, 0 ≤ f v ∧ f v ≤ 1 := fun v hv =>
      hf v (hsc σ (Finset.mem_filter.1 hσ).1 {v} (Finset.singleton_subset_iff.2 hv))
    refine ⟨Finset.sum_nonneg (fun v h => (hv v h).1), ?_⟩
    calc topSum f σ ≤ ∑ v ∈ σ, (1 : ℝ) := Finset.sum_le_sum (fun v h => (hv v h).2)
      _ = d := by simp [hc]
  by_cases hα1 : α ≤ 1
  · -- two tails
    set g : V → ℝ := fun v => 1 - f v with hg
    have hgb : ∀ v, ({v} : Finset V) ∈ X → 0 ≤ g v ∧ g v ≤ 1 := by
      intro v hv; have := hf v hv; simp only [hg]; constructor <;> linarith
    have hgs : ∀ σ ∈ SteurerHDX.faces X d, topSum g σ = d - topSum f σ := by
      intro σ hσ
      have hc : σ.card = d := (Finset.mem_filter.1 hσ).2
      simp [topSum, hg, Finset.sum_sub_distrib, hc]
    have hgm : topMean X d π (topSum g) = d - d * μ := by
      rw [← hm]; unfold topMean
      have : ∀ σ ∈ SteurerHDX.faces X d, π σ * topSum g σ = π σ * d - π σ * topSum f σ := by
        intro σ hσ; rw [hgs σ hσ]; ring
      rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib, ← Finset.sum_mul, hπ.sum_eq_one]; ring
    have U1 := upper_tail hd hη0 hη1 hX hπ hexp f hf hα hα1
    have U2 := upper_tail hd hη0 hη1 hX hπ hexp g hgb hα hα1
    set A := (SteurerHDX.faces X d).filter (fun σ => α * (d : ℝ) ≤ topSum f σ - topMean X d π (topSum f))
    set B := (SteurerHDX.faces X d).filter (fun σ => α * (d : ℝ) ≤ topSum g σ - topMean X d π (topSum g))
    have hsub : (SteurerHDX.faces X d).filter
        (fun s => α < |(1 / (d : ℝ)) * ∑ v ∈ s, f v - vertexMean X d π f|) ⊆ A ∪ B := by
      intro σ hσ
      rw [Finset.mem_filter] at hσ
      obtain ⟨hσf, hlt⟩ := hσ
      have hF := hgs σ hσf
      have key : (1 / (d : ℝ)) * ∑ v ∈ σ, f v - μ = (topSum f σ - d * μ) / d := by
        unfold topSum; field_simp
      rw [← hμ, key] at hlt
      rw [Finset.mem_union]
      rcases lt_abs.1 hlt with h | h
      · left
        rw [Finset.mem_filter]; refine ⟨hσf, ?_⟩
        rw [hm]; rw [lt_div_iff₀ hdpos] at h; linarith
      · right
        rw [Finset.mem_filter]; refine ⟨hσf, ?_⟩
        rw [hF, hgm]; rw [← neg_div, lt_div_iff₀ hdpos] at h; linarith
    calc _ ≤ ∑ σ ∈ A ∪ B, π σ :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun σ hσ _ => by
            rcases Finset.mem_union.1 hσ with h | h <;> exact hπnn σ (Finset.mem_filter.1 h).1)
      _ ≤ ∑ σ ∈ A, π σ + ∑ σ ∈ B, π σ := by
          have := Finset.sum_union_inter (s₁ := A) (s₂ := B) (f := π)
          have h2 : 0 ≤ ∑ x ∈ A ∩ B, π x := Finset.sum_nonneg (fun x hx =>
            hπnn x (Finset.mem_filter.1 (Finset.mem_inter.1 hx).1).1)
          linarith
      _ ≤ _ := by linarith
  · -- empty event
    rw [not_le] at hα1
    have hmb : 0 ≤ d * μ ∧ d * μ ≤ d := by
      rw [← hm]; unfold topMean
      constructor
      · exact Finset.sum_nonneg (fun σ hσ => mul_nonneg (hπnn σ hσ) (hFb σ hσ).1)
      · calc _ ≤ ∑ σ ∈ SteurerHDX.faces X d, π σ * d :=
              Finset.sum_le_sum (fun σ hσ => mul_le_mul_of_nonneg_left (hFb σ hσ).2 (hπnn σ hσ))
          _ = d := by rw [← Finset.sum_mul, hπ.sum_eq_one]; ring
    have : (SteurerHDX.faces X d).filter
        (fun s => α < |(1 / (d : ℝ)) * ∑ v ∈ s, f v - vertexMean X d π f|) = ∅ := by
      apply Finset.filter_eq_empty_iff.2
      intro σ hσ hlt
      have hF := hFb σ hσ
      have key : (1 / (d : ℝ)) * ∑ v ∈ σ, f v - vertexMean X d π f = (topSum f σ - d * μ) / d := by
        unfold topSum; rw [← hμ]; field_simp
      rw [key] at hlt
      have hab : |(topSum f σ - d * μ) / d| ≤ 1 := by
        rw [abs_div, abs_of_pos hdpos, div_le_one hdpos, abs_le]
        constructor <;> linarith [hF.1, hF.2, hmb.1, hmb.2]
      linarith
    rw [this]; simp; positivity
end HDXConc
end

theorem solution : type_of% @HDXConc.chk_theorem_1_1 := @HDXConc.chk_theorem_1_1
