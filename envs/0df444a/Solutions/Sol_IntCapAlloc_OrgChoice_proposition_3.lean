-- Prove2me | solution 1 for IntCapAlloc.OrgChoice.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T16:03:23.623077+00:00
-- url     : https://prove2.me/submissions/ba3048ff-4e45-44d2-ad39-f35765d8e102

import Mathlib
import Definitions.Def_IntCapAlloc_OrgChoice_Model
import Theorems.Thm_IntCapAlloc_OrgChoice_proposition_1
import Theorems.Thm_IntCapAlloc_OrgChoice_proposition_2_i
import Theorems.Thm_IntCapAlloc_OrgChoice_proposition_2_ii
import Theorems.Thm_IntCapAlloc_OrgChoice_proposition_2_iii
import Theorems.Thm_IntCapAlloc_OrgChoice_proposition_2_iv

open IntCapAlloc.OrgChoice

theorem solution (p X c q bet : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (hX : 1 < X) (hc : 0 < c)
    (hq0 : 0 < q) (hq1 : q < 1) (hbet : q * X < bet) (hfocus : 1 + c ≤ X) :
    ∃ vm vs : ℝ, IsGreatest (effSetM p X c q bet) vm ∧ IsGreatest (effSetS p X c q bet) vs ∧
      ((1 - p) / (2 * p) ≤ c → c < (1 - p ^ 2) / (2 * p ^ 2) → X < min (2 + c) ((1 + p) / p) →
        vs ≤ vm) ∧
      ((1 - p) / (2 * p) < c → c < (1 - p ^ 2) / (2 * p ^ 2) → X < min (2 + c) ((1 + p) / p) →
        vs < vm) ∧
      (c < (1 - p) / p → 2 + c ≤ X → vm < vs) ∧
      (¬ ((1 - p) / (2 * p) < c ∧ c < (1 - p ^ 2) / (2 * p ^ 2) ∧ X < min (2 + c) ((1 + p) / p)) →
        ¬ (c < (1 - p) / p ∧ 2 + c ≤ X) → vm = vs) := by
  have h2p : (0:ℝ) < 2 * p := by positivity
  have h2p2 : (0:ℝ) < 2 * p ^ 2 := by positivity
  -- the stand-alone structure doubles a single firm's greatest efficiency
  have hS : ∀ v, IsGreatest (effSet1 p X c q bet) v → IsGreatest (effSetS p X c q bet) (2 * v) := by
    intro v hv
    obtain ⟨⟨σ, μ, hE, rfl⟩, hub⟩ := hv
    refine ⟨⟨σ, μ, σ, μ, hE, hE, by ring⟩, ?_⟩
    rintro w ⟨σ₁, μ₁, σ₂, μ₂, h₁, h₂, rfl⟩
    have a := hub ⟨σ₁, μ₁, h₁, rfl⟩
    have b := hub ⟨σ₂, μ₂, h₂, rfl⟩
    linarith
  have P1 := proposition_1 p X c q bet hp0 hp1 hX hc hq0 hq1 hbet hfocus
  -- normal forms of the region boundaries
  have eA : c < (1 - p) / p ↔ c * p < 1 - p := lt_div_iff₀ hp0
  have eB : (1 - p) / (2 * p) ≤ c ↔ 1 - p ≤ c * (2 * p) := div_le_iff₀ h2p
  have eB' : (1 - p) / (2 * p) < c ↔ 1 - p < c * (2 * p) := div_lt_iff₀ h2p
  have eC : c < (1 - p ^ 2) / (2 * p ^ 2) ↔ c * (2 * p ^ 2) < 1 - p ^ 2 := lt_div_iff₀ h2p2
  have eC' : (1 - p ^ 2) / (2 * p ^ 2) ≤ c ↔ 1 - p ^ 2 ≤ c * (2 * p ^ 2) := div_le_iff₀ h2p2
  have eB2 : c < (1 - p) / (2 * p) ↔ c * (2 * p) < 1 - p := lt_div_iff₀ h2p
  have eA' : (1 - p) / p ≤ c ↔ 1 - p ≤ c * p := div_le_iff₀ hp0
  have eD : X < (1 + p) / p ↔ X * p < 1 + p := lt_div_iff₀ hp0
  have eD' : (1 + p) / p ≤ X ↔ 1 + p ≤ X * p := div_le_iff₀ hp0
  -- the stand-alone value
  obtain ⟨vs, hvs, hvsv⟩ : ∃ vs, IsGreatest (effSetS p X c q bet) vs ∧
      vs = if c * p < 1 - p then 2 * (p * (X - 1 - c)) else 2 * (p * X - 1) := by
    by_cases h : c * p < 1 - p
    · exact ⟨_, hS _ (P1.1 (eA.mpr h)).1, by simp [h]⟩
    · exact ⟨_, hS _ (P1.2 (eA'.mpr (le_of_not_gt h))).1, by simp [h]⟩
  -- the multi-divisional value, by the region of Proposition 2
  obtain ⟨vm, hvm, hvmv⟩ : ∃ vm, IsGreatest (effSetM p X c q bet) vm ∧
      ((c * p < 1 - p ∧ 2 + c ≤ X ∧ vm = 2 * p * (X + p - 2 - c)) ∨
       (c * (2 * p) < 1 - p ∧ X < 2 + c ∧ vm = 2 * p * (X - 1 - c)) ∨
       (1 - p ≤ c * (2 * p) ∧ c * (2 * p ^ 2) < 1 - p ^ 2 ∧ X < 2 + c ∧ X * p < 1 + p ∧
          vm = p * (2 * X - p * (1 + 2 * c)) - 1) ∨
       (((1 - p ≤ c * p ∧ 1 + p ≤ X * p) ∨ 1 - p ^ 2 ≤ c * (2 * p ^ 2)) ∧ vm = 2 * (p * X - 1))) := by
    by_cases h3 : c * p < 1 - p ∧ 2 + c ≤ X
    · exact ⟨_, (proposition_2_iii p X c q bet hp0 hp1 hX hc hq0 hq1 hbet hfocus
        (eA.mpr h3.1) h3.2).1, Or.inl ⟨h3.1, h3.2, rfl⟩⟩
    by_cases h2 : c * (2 * p) < 1 - p ∧ X < 2 + c
    · exact ⟨_, (proposition_2_ii p X c q bet hp0 hp1 hX hc hq0 hq1 hbet hfocus
        (eB2.mpr h2.1) h2.2).1, Or.inr (Or.inl ⟨h2.1, h2.2, rfl⟩)⟩
    by_cases h1 : 1 - p ≤ c * (2 * p) ∧ c * (2 * p ^ 2) < 1 - p ^ 2 ∧ X < 2 + c ∧ X * p < 1 + p
    · exact ⟨_, (proposition_2_i p X c q bet hp0 hp1 hX hc hq0 hq1 hbet hfocus
        (eB.mpr h1.1) (eC.mpr h1.2.1) (lt_min h1.2.2.1 (eD.mpr h1.2.2.2))).1,
        Or.inr (Or.inr (Or.inl ⟨h1.1, h1.2.1, h1.2.2.1, h1.2.2.2, rfl⟩))⟩
    have hreg : (1 - p ≤ c * p ∧ 1 + p ≤ X * p) ∨ 1 - p ^ 2 ≤ c * (2 * p ^ 2) := by
      by_cases hC : 1 - p ^ 2 ≤ c * (2 * p ^ 2)
      · exact Or.inr hC
      left
      push Not at h3 h2 h1 hC
      by_cases hB : c * (2 * p) < 1 - p
      · have hX2 := h2 hB
        have : c * p < 1 - p := by nlinarith
        exact absurd (h3 this) (by linarith)
      · push Not at hB
        by_cases hX2 : X < 2 + c
        · have hXp := h1 hB hC hX2
          by_cases hA : c * p < 1 - p
          · nlinarith
          · push Not at hA; exact ⟨hA, hXp⟩
        · push Not at hX2
          by_cases hA : c * p < 1 - p
          · have := h3 hA; linarith
          · push Not at hA; exact ⟨hA, by nlinarith⟩
    refine ⟨_, (proposition_2_iv p X c q bet hp0 hp1 hX hc hq0 hq1 hbet hfocus ?_).1,
      Or.inr (Or.inr (Or.inr ⟨hreg, rfl⟩))⟩
    rcases hreg with h | h
    · exact Or.inl ⟨eA'.mpr h.1, eD'.mpr h.2⟩
    · exact Or.inr (eC'.mpr h)
  refine ⟨vm, vs, hvm, hvs, ?_, ?_, ?_, ?_⟩
  · intro hB hC hX2
    rw [eB] at hB; rw [eC] at hC; rw [lt_min_iff, eD] at hX2
    obtain ⟨hX2, hXp⟩ := hX2
    rcases hvmv with ⟨h, h', -⟩ | ⟨h, -, -⟩ | ⟨-, -, -, -, rfl⟩ | ⟨h | h, -⟩
    · linarith
    · linarith
    · subst hvsv; split_ifs with hA
      · nlinarith [mul_nonneg (sub_nonneg.mpr hp1.le) (sub_nonneg.mpr hB)]
      · push Not at hA; nlinarith
    · nlinarith [h.2]
    · linarith
  · intro hB hC hX2
    rw [eB'] at hB; rw [eC] at hC; rw [lt_min_iff, eD] at hX2
    obtain ⟨hX2, hXp⟩ := hX2
    rcases hvmv with ⟨h, h', -⟩ | ⟨h, -, -⟩ | ⟨-, -, -, -, rfl⟩ | ⟨h | h, -⟩
    · linarith
    · linarith
    · subst hvsv; split_ifs with hA
      · nlinarith [mul_pos (sub_pos.mpr hp1) (sub_pos.mpr hB)]
      · push Not at hA; nlinarith
    · nlinarith [h.2]
    · linarith
  · intro hA hX2
    rw [eA] at hA
    rcases hvmv with ⟨-, -, rfl⟩ | ⟨-, h, -⟩ | ⟨-, -, h, -⟩ | ⟨h | h, -⟩
    · rw [hvsv, if_pos hA]; nlinarith
    · linarith
    · linarith
    · linarith [h.1]
    · nlinarith
  · intro hn1 hn2
    rw [eB', eC, lt_min_iff, eD] at hn1
    rw [eA] at hn2
    rcases hvmv with ⟨h, h', -⟩ | ⟨h, -, rfl⟩ | ⟨hB, hC, hX2, hXp, rfl⟩ | ⟨h | h, rfl⟩
    · exact absurd ⟨h, h'⟩ hn2
    · rw [hvsv, if_pos (by nlinarith [mul_pos hc hp0])]; ring
    · have hBe : 1 - p = c * (2 * p) := by
        by_contra hne
        exact hn1 ⟨lt_of_le_of_ne hB hne, hC, hX2, hXp⟩
      rw [hvsv, if_pos (by nlinarith)]; nlinarith
    · rw [hvsv, if_neg (by linarith [h.1])]
    · rw [hvsv, if_neg (by nlinarith)]
