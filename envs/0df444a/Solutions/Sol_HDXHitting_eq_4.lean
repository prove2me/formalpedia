-- Prove2me | solution 1 for HDXHitting.eq_4
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T07:07:54.082675+00:00
-- url     : https://prove2.me/submissions/297c7873-04ba-44b2-924d-f925274f89e7

import Mathlib
import Definitions.Def_HDXHitting_IsTopDist
import Definitions.Def_HDXHitting_vertexMeasure
import Definitions.Def_HDXHitting_mean
import Definitions.Def_HDXHitting_hit
import Definitions.Def_HDXHitting_linkWeight
import Definitions.Def_HDXHitting_IsOneSidedHDX
import Definitions.Def_HDXHitting_cMax
import Definitions.Def_HDXHitting_linkDist
import Theorems.Thm_HDXHitting_good_vertex
import Theorems.Thm_HDXHitting_vertex_decomposition
import Theorems.Thm_HDXHitting_link_heredity
import Theorems.Thm_HDXHitting_cmax_lipschitz

section
set_option autoImplicit false
namespace HDXHitting.Dev.E4
open HDXHitting

theorem mean_update {V : Type*} [Fintype V] [DecidableEq V] (e : ℕ) (q : Finset V → ℝ) (f : V → ℝ)
    (v : V) (a : ℝ) :
    mean e q (Function.update f v a) = mean e q f - vertexMeasure e q v * (f v - a) := by
  unfold mean
  have : ∀ w, vertexMeasure e q w * Function.update f v a w =
      vertexMeasure e q w * f w - (if w = v then vertexMeasure e q v * (f v - a) else 0) := by
    intro w
    by_cases h : w = v
    · subst h; simp; ring
    · simp [h]
  simp_rw [this]
  rw [Finset.sum_sub_distrib, Finset.sum_ite_eq']
  simp

theorem vm_link_self {V : Type*} [Fintype V] [DecidableEq V] (e : ℕ) (p : Finset V → ℝ) (v : V) :
    vertexMeasure e (linkDist p {v}) v = 0 := by
  unfold vertexMeasure
  rw [Finset.sum_eq_zero, mul_zero]
  intro σ hσ
  unfold linkDist
  rw [if_neg]
  rw [Finset.disjoint_singleton_left]
  simpa using hσ

theorem mean_nonneg {V : Type*} [Fintype V] [DecidableEq V] (e : ℕ) (q : Finset V → ℝ)
    (hq : ∀ σ, 0 ≤ q σ) (f : V → ℝ) (hf : ∀ v, 0 ≤ f v) : 0 ≤ mean e q f := by
  unfold mean vertexMeasure
  apply Finset.sum_nonneg
  intro w _
  apply mul_nonneg _ (hf w)
  apply mul_nonneg (by positivity)
  exact Finset.sum_nonneg (fun σ _ => hq σ)

theorem hit_le_one {V : Type*} [Fintype V] (d : ℕ) (p : Finset V → ℝ) (hp : IsTopDist d p)
    (g : V → ℝ) (hg : ∀ v, 0 ≤ g v ∧ g v ≤ 1) : hit p g ≤ 1 := by
  unfold hit
  calc ∑ σ, p σ * ∏ v ∈ σ, g v ≤ ∑ σ, p σ * 1 := by
        apply Finset.sum_le_sum
        intro σ _
        apply mul_le_mul_of_nonneg_left _ (hp.1 σ)
        exact Finset.prod_le_one (fun v _ => (hg v).1) (fun v _ => (hg v).2)
    _ = 1 := by simp [hp.2.2]

end HDXHitting.Dev.E4
namespace HDXHitting
open HDXHitting.Dev.E4 in
theorem chk_eq_4 {V : Type*} [Fintype V] [DecidableEq V] (d : ℕ) (hd : 2 ≤ d)
    (p : Finset V → ℝ) (hp : IsTopDist d p) (lam : ℝ) (hlam : 0 ≤ lam)
    (hX : IsOneSidedHDX d p lam)
    (ih : ∀ p' : Finset V → ℝ, IsTopDist (d - 1) p' → IsOneSidedHDX (d - 1) p' lam →
      ∀ f : V → ℝ, (∀ v, 0 ≤ f v ∧ f v ≤ 1) →
        hit p' f ≤ mean (d - 1) p' f * (mean (d - 1) p' f + ((d - 1 : ℕ) : ℝ) * lam) ^ (d - 2)) :
    ∀ μ : ℝ, 0 < μ → μ < 1 → ∃ s₀ : ℝ, 0 < s₀ ∧ ∀ s : ℝ, 0 < s → s < s₀ →
      cMax d p μ ≤ cMax d p (μ - s) + s * ((d : ℝ) * (μ + lam) * (μ + d * lam) ^ (d - 2)) := by
  intro μ hμ0 hμ1
  obtain ⟨f, hf, hmean, hhit⟩ := (HDXHitting.cmax_lipschitz d (by omega) p hp).1 μ hμ0.le hμ1.le
  obtain ⟨v, hfv, hv, hlink⟩ := HDXHitting.good_vertex d hd p hp lam hlam hX f hf (by rw [hmean]; exact hμ0)
  rw [hmean] at hlink
  refine ⟨f v * vertexMeasure d p v, mul_pos hfv hv, ?_⟩
  intro s hs hs1
  set π := vertexMeasure d p v with hπ
  set ε := s / π with hε
  have hε0 : 0 < ε := div_pos hs hv
  have hεs : ε * π = s := by rw [hε]; field_simp
  have hεf : ε < f v := by
    rw [hε, div_lt_iff₀ hv]; exact hs1
  set g := Function.update f v (f v - ε) with hg
  have hg01 : ∀ w, 0 ≤ g w ∧ g w ≤ 1 := by
    intro w
    by_cases h : w = v
    · subst h; simp only [hg, Function.update_self]; exact ⟨by linarith, by linarith [(hf w).2]⟩
    · simp only [hg, Function.update_of_ne h]; exact hf w
  have hgmean : mean d p g = μ - s := by
    rw [hg, mean_update, hmean]
    simp only [sub_sub_cancel]
    rw [← hπ, mul_comm, hεs]
  -- decomposition
  have hdec := HDXHitting.vertex_decomposition d p hp v hv f ε
  rw [← hg] at hdec
  -- link
  have hPv : 0 < ∑ σ ∈ Finset.univ.filter (fun σ : Finset V => ({v} : Finset V) ⊆ σ), p σ := by
    have hd0 : (d : ℝ) ≠ 0 := by
      have : (2 : ℝ) ≤ d := by exact_mod_cast hd
      intro h; linarith
    have : (∑ σ ∈ Finset.univ.filter (fun σ : Finset V => ({v} : Finset V) ⊆ σ), p σ) =
        (d : ℝ) * vertexMeasure d p v := by
      unfold vertexMeasure
      field_simp
      apply Finset.sum_congr _ (fun _ _ => rfl); ext; simp
    rw [this]; exact mul_pos (by positivity) hv
  obtain ⟨hT, hH, -, -⟩ := HDXHitting.link_heredity (ι := ℕ) d p hp {v} hPv lam (fun _ => 0) ∅
  rw [Finset.card_singleton] at hT hH
  have hlinkle := ih (linkDist p {v}) hT (hH hX) g hg01
  have hmg : mean (d - 1) (linkDist p {v}) g = mean (d - 1) (linkDist p {v}) f := by
    rw [hg, mean_update, vm_link_self]; ring
  rw [hmg] at hlinkle
  have hμv0 : 0 ≤ mean (d - 1) (linkDist p {v}) f :=
    mean_nonneg _ _ hT.1 f (fun w => (hf w).1)
  have hcast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  set x := mean (d - 1) (linkDist p {v}) f with hx
  have hmono : x * (x + ((d - 1 : ℕ) : ℝ) * lam) ^ (d - 2) ≤ (μ + lam) * (μ + d * lam) ^ (d - 2) := by
    have hd1 : (0 : ℝ) ≤ (d : ℝ) - 1 := by
      have : (2 : ℝ) ≤ d := by exact_mod_cast hd
      linarith
    rw [hcast]
    have h1 : x + ((d : ℝ) - 1) * lam ≤ μ + d * lam := by nlinarith
    have h2 : 0 ≤ x + ((d : ℝ) - 1) * lam := by positivity
    calc x * (x + ((d : ℝ) - 1) * lam) ^ (d - 2)
        ≤ (μ + lam) * (x + ((d : ℝ) - 1) * lam) ^ (d - 2) :=
          mul_le_mul_of_nonneg_right hlink (by positivity)
      _ ≤ (μ + lam) * (μ + d * lam) ^ (d - 2) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h2 h1 _) (by linarith)
  have hcm : hit p g ≤ cMax d p (μ - s) := by
    unfold cMax
    apply le_csSup
    · refine ⟨1, ?_⟩
      rintro _ ⟨h, ⟨hh, _⟩, rfl⟩
      exact hit_le_one d p hp h hh
    · exact ⟨g, ⟨hg01, hgmean⟩, rfl⟩
  have hdε : (d : ℝ) * ε * π = (d : ℝ) * s := by rw [mul_assoc, hεs]
  rw [hdε] at hdec
  have hds : 0 ≤ (d : ℝ) * s := by positivity
  have := mul_le_mul_of_nonneg_left (hlinkle.trans hmono) hds
  rw [← hhit, hdec]
  nlinarith

end HDXHitting
end

theorem solution : type_of% @HDXHitting.chk_eq_4 := @HDXHitting.chk_eq_4
