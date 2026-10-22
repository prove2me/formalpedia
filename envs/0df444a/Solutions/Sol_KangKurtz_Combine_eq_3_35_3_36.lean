-- Prove2me | solution 1 for KangKurtz.Combine.eq_3_35_3_36
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:46:25.552674+00:00
-- url     : https://prove2.me/submissions/2346e927-079c-4cd2-84ae-cf02d2102ce2

import Mathlib
import Definitions.Def_KangKurtz_Combine_Setting

set_option autoImplicit false

open KangKurtz.SCC in
theorem dot_comb {s r : ℕ} (ν ν' : Fin r → Fin s → ℕ) (θ₁ θ₂ : Fin s → ℝ) (c₁ c₂ : ℝ)
    (k : Fin r) :
    dot ν ν' (c₁ • θ₁ + c₂ • θ₂) k = c₁ * dot ν ν' θ₁ k + c₂ * dot ν ν' θ₂ k := by
  unfold dot
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib,
    Finset.mul_sum, mul_assoc]

open KangKurtz.SCC in
theorem mem_gam {s r : ℕ} (ν ν' : Fin r → Fin s → ℕ) (θ : Fin s → ℝ) (k : Fin r) :
    k ∈ GammaPlus ν ν' θ ∪ GammaMinus ν ν' θ ↔ dot ν ν' θ k ≠ 0 := by
  simp only [GammaPlus, GammaMinus, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
    true_and]
  constructor
  · rintro (h | h)
    · exact ne_of_gt h
    · exact ne_of_lt h
  · intro h
    rcases lt_or_gt_of_ne h with h | h
    · right; exact h
    · left; exact h

open KangKurtz.SCC in
theorem gp_sub {s r : ℕ} (ν ν' : Fin r → Fin s → ℕ) (θ₁ θ₂ : Fin s → ℝ) (c₁ c₂ : ℝ)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) :
    GammaPlus ν ν' (c₁ • θ₁ + c₂ • θ₂) ⊆ GammaPlus ν ν' θ₁ ∪ GammaPlus ν ν' θ₂ := by
  intro k hk
  simp only [GammaPlus, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
  rw [dot_comb] at hk
  by_contra h
  push_neg at h
  have h1 := mul_nonpos_of_nonneg_of_nonpos hc₁.le h.1
  have h2 := mul_nonpos_of_nonneg_of_nonpos hc₂.le h.2
  linarith

open KangKurtz.SCC in
theorem gm_sub {s r : ℕ} (ν ν' : Fin r → Fin s → ℕ) (θ₁ θ₂ : Fin s → ℝ) (c₁ c₂ : ℝ)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) :
    GammaMinus ν ν' (c₁ • θ₁ + c₂ • θ₂) ⊆ GammaMinus ν ν' θ₁ ∪ GammaMinus ν ν' θ₂ := by
  intro k hk
  simp only [GammaMinus, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
  rw [dot_comb] at hk
  by_contra h
  push_neg at h
  have h1 := mul_nonneg hc₁.le h.1 |>.trans_eq' rfl
  have h1 : 0 ≤ c₁ * dot ν ν' θ₁ k := mul_nonneg hc₁.le h.1
  have h2 : 0 ≤ c₂ * dot ν ν' θ₂ k := mul_nonneg hc₂.le h.2
  linarith

open KangKurtz.SCC in
theorem maxRho_mono {s r : ℕ} (ν : Fin r → Fin s → ℕ) (α : Fin s → ℝ) (β : Fin r → ℝ)
    {S T : Finset (Fin r)} (h : S ⊆ T) : maxRho ν α β S ≤ maxRho ν α β T := by
  unfold maxRho
  exact Finset.sup_mono h

open KangKurtz.SCC in
theorem maxRho_union {s r : ℕ} (ν : Fin r → Fin s → ℕ) (α : Fin s → ℝ) (β : Fin r → ℝ)
    (S T : Finset (Fin r)) : maxRho ν α β (S ∪ T) = maxRho ν α β S ⊔ maxRho ν α β T := by
  unfold maxRho
  exact Finset.sup_union

open KangKurtz.SCC in
theorem le_maxRho {s r : ℕ} (ν : Fin r → Fin s → ℕ) (α : Fin s → ℝ) (β : Fin r → ℝ)
    {S : Finset (Fin r)} {k : Fin r} (h : k ∈ S) : ((rho ν α β k : ℝ) : WithBot ℝ) ≤ maxRho ν α β S := by
  unfold maxRho
  exact Finset.le_sup (f := fun k => ((rho ν α β k : ℝ) : WithBot ℝ)) h

theorem solution {s r : ℕ} (ν ν' : Fin r → Fin s → ℕ) (α : Fin s → ℝ) (hα : ∀ i, 0 ≤ α i)
    (β : Fin r → ℝ)
    (θ₁ θ₂ : Fin s → ℝ) (hθ₁ : ∀ i, 0 ≤ θ₁ i) (hθ₂ : ∀ i, 0 ≤ θ₂ i)
    (hdisj : Disjoint (KangKurtz.SCC.GammaMinus ν ν' θ₁) (KangKurtz.SCC.GammaPlus ν ν' θ₂))
    (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) :
    (KangKurtz.SCC.maxRho ν α β (KangKurtz.SCC.GammaMinus ν ν' θ₁) ≤ KangKurtz.SCC.maxRho ν α β (KangKurtz.SCC.GammaMinus ν ν' (c₁ • θ₁ + c₂ • θ₂)) ∧
      KangKurtz.SCC.maxRho ν α β (KangKurtz.SCC.GammaMinus ν ν' (c₁ • θ₁ + c₂ • θ₂)) ≤
        KangKurtz.SCC.maxRho ν α β (KangKurtz.SCC.GammaMinus ν ν' θ₁) ⊔ KangKurtz.SCC.maxRho ν α β (KangKurtz.SCC.GammaMinus ν ν' θ₂)) ∧
    (KangKurtz.SCC.maxRho ν α β (KangKurtz.SCC.GammaPlus ν ν' θ₂) ≤ KangKurtz.SCC.maxRho ν α β (KangKurtz.SCC.GammaPlus ν ν' (c₁ • θ₁ + c₂ • θ₂)) ∧
      KangKurtz.SCC.maxRho ν α β (KangKurtz.SCC.GammaPlus ν ν' (c₁ • θ₁ + c₂ • θ₂)) ≤
        KangKurtz.SCC.maxRho ν α β (KangKurtz.SCC.GammaPlus ν ν' θ₁) ⊔ KangKurtz.SCC.maxRho ν α β (KangKurtz.SCC.GammaPlus ν ν' θ₂)) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · apply maxRho_mono
    intro k hk
    have hk2 : k ∉ KangKurtz.SCC.GammaPlus ν ν' θ₂ := fun h => Finset.disjoint_left.1 hdisj hk h
    simp only [KangKurtz.SCC.GammaMinus, KangKurtz.SCC.GammaPlus, Finset.mem_filter,
      Finset.mem_univ, true_and, not_lt] at hk hk2 ⊢
    rw [dot_comb]
    have h1 := mul_neg_of_pos_of_neg hc₁ hk
    have h2 := mul_nonpos_of_nonneg_of_nonpos hc₂.le hk2
    linarith
  · calc _ ≤ KangKurtz.SCC.maxRho ν α β (KangKurtz.SCC.GammaMinus ν ν' θ₁ ∪ KangKurtz.SCC.GammaMinus ν ν' θ₂) :=
          maxRho_mono ν α β (gm_sub ν ν' θ₁ θ₂ c₁ c₂ hc₁ hc₂)
      _ = _ := maxRho_union ν α β _ _
  · apply maxRho_mono
    intro k hk
    have hk1 : k ∉ KangKurtz.SCC.GammaMinus ν ν' θ₁ := fun h => Finset.disjoint_left.1 hdisj h hk
    simp only [KangKurtz.SCC.GammaMinus, KangKurtz.SCC.GammaPlus, Finset.mem_filter,
      Finset.mem_univ, true_and, not_lt] at hk hk1 ⊢
    rw [dot_comb]
    have h1 := mul_nonneg hc₁.le hk1
    have h2 := mul_pos hc₂ hk
    linarith
  · calc _ ≤ KangKurtz.SCC.maxRho ν α β (KangKurtz.SCC.GammaPlus ν ν' θ₁ ∪ KangKurtz.SCC.GammaPlus ν ν' θ₂) :=
          maxRho_mono ν α β (gp_sub ν ν' θ₁ θ₂ c₁ c₂ hc₁ hc₂)
      _ = _ := maxRho_union ν α β _ _
