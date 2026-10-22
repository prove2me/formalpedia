-- Prove2me | solution 1 for KangKurtz.Combine.lemma_3_6
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:43:45.752062+00:00
-- url     : https://prove2.me/submissions/4db754e9-170e-4161-b413-e7f569e7b349

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

open KangKurtz.SCC in
theorem balLemma {s r : ℕ} (ν ν' : Fin r → Fin s → ℕ) (α : Fin s → ℝ) (β : Fin r → ℝ)
    (θ₁ θ₂ : Fin s → ℝ) (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (h_eq : maxRho ν α β (GammaMinus ν ν' θ₁) = maxRho ν α β (GammaPlus ν ν' θ₁))
    (h_lt : maxRho ν α β (GammaPlus ν ν' θ₂ ∪ GammaMinus ν ν' θ₂) < maxRho ν α β (GammaPlus ν ν' θ₁)) :
    Balance ν ν' α β (c₁ • θ₁ + c₂ • θ₂) := by
  have hP : maxRho ν α β (GammaPlus ν ν' (c₁ • θ₁ + c₂ • θ₂)) = maxRho ν α β (GammaPlus ν ν' θ₁) := by
    apply le_antisymm
    · calc _ ≤ maxRho ν α β (GammaPlus ν ν' θ₁ ∪ GammaPlus ν ν' θ₂) :=
            maxRho_mono ν α β (gp_sub ν ν' θ₁ θ₂ c₁ c₂ hc₁ hc₂)
        _ = maxRho ν α β (GammaPlus ν ν' θ₁) ⊔ maxRho ν α β (GammaPlus ν ν' θ₂) :=
            maxRho_union ν α β _ _
        _ ≤ maxRho ν α β (GammaPlus ν ν' θ₁) := by
            refine sup_le le_rfl ?_
            exact le_trans (maxRho_mono ν α β Finset.subset_union_left) h_lt.le
    · have hne : (GammaPlus ν ν' θ₁).Nonempty := by
        by_contra hcon
        rw [Finset.not_nonempty_iff_eq_empty] at hcon
        have : maxRho ν α β (GammaPlus ν ν' θ₁) = ⊥ := by
          rw [hcon]; unfold maxRho; simp
        rw [this] at h_lt
        exact not_lt_bot h_lt
      obtain ⟨k, hk, hkeq⟩ := Finset.exists_mem_eq_sup (GammaPlus ν ν' θ₁) hne
        (fun k => ((rho ν α β k : ℝ) : WithBot ℝ))
      have hkn : k ∉ GammaPlus ν ν' θ₂ ∪ GammaMinus ν ν' θ₂ := by
        intro hk2
        have := le_maxRho ν α β hk2
        have h3 : maxRho ν α β (GammaPlus ν ν' θ₁) = ((rho ν α β k : ℝ) : WithBot ℝ) := hkeq
        rw [← h3] at this
        exact absurd (lt_of_le_of_lt this h_lt) (lt_irrefl _)
      rw [mem_gam] at hkn
      push_neg at hkn
      have hk1 : 0 < dot ν ν' θ₁ k := by
        simpa [GammaPlus] using hk
      have hk' : k ∈ GammaPlus ν ν' (c₁ • θ₁ + c₂ • θ₂) := by
        simp only [GammaPlus, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [dot_comb, hkn]
        have := mul_pos hc₁ hk1
        linarith
      have h3 : maxRho ν α β (GammaPlus ν ν' θ₁) = ((rho ν α β k : ℝ) : WithBot ℝ) := hkeq
      rw [h3]
      exact le_maxRho ν α β hk'
  have hM : maxRho ν α β (GammaMinus ν ν' (c₁ • θ₁ + c₂ • θ₂)) = maxRho ν α β (GammaPlus ν ν' θ₁) := by
    apply le_antisymm
    · calc _ ≤ maxRho ν α β (GammaMinus ν ν' θ₁ ∪ GammaMinus ν ν' θ₂) :=
            maxRho_mono ν α β (gm_sub ν ν' θ₁ θ₂ c₁ c₂ hc₁ hc₂)
        _ = maxRho ν α β (GammaMinus ν ν' θ₁) ⊔ maxRho ν α β (GammaMinus ν ν' θ₂) :=
            maxRho_union ν α β _ _
        _ ≤ maxRho ν α β (GammaPlus ν ν' θ₁) := by
            refine sup_le h_eq.le ?_
            exact le_trans (maxRho_mono ν α β Finset.subset_union_right) h_lt.le
    · have hne : (GammaMinus ν ν' θ₁).Nonempty := by
        by_contra hcon
        rw [Finset.not_nonempty_iff_eq_empty] at hcon
        have : maxRho ν α β (GammaMinus ν ν' θ₁) = ⊥ := by
          rw [hcon]; unfold maxRho; simp
        rw [this] at h_eq
        rw [← h_eq] at h_lt
        exact not_lt_bot h_lt
      obtain ⟨k, hk, hkeq⟩ := Finset.exists_mem_eq_sup (GammaMinus ν ν' θ₁) hne
        (fun k => ((rho ν α β k : ℝ) : WithBot ℝ))
      have h3 : maxRho ν α β (GammaMinus ν ν' θ₁) = ((rho ν α β k : ℝ) : WithBot ℝ) := hkeq
      have hkn : k ∉ GammaPlus ν ν' θ₂ ∪ GammaMinus ν ν' θ₂ := by
        intro hk2
        have := le_maxRho ν α β hk2
        rw [← h_eq, h3] at h_lt
        exact absurd (lt_of_le_of_lt this h_lt) (lt_irrefl _)
      rw [mem_gam] at hkn
      push_neg at hkn
      have hk1 : dot ν ν' θ₁ k < 0 := by
        simpa [GammaMinus] using hk
      have hk' : k ∈ GammaMinus ν ν' (c₁ • θ₁ + c₂ • θ₂) := by
        simp only [GammaMinus, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [dot_comb, hkn]
        have := mul_neg_of_pos_of_neg hc₁ hk1
        linarith
      rw [← h_eq, h3]
      exact le_maxRho ν α β hk'
  unfold Balance
  rw [hP, hM]

theorem solution {s r : ℕ} (ν ν' : Fin r → Fin s → ℕ) (α : Fin s → ℝ) (hα : ∀ i, 0 ≤ α i)
    (β : Fin r → ℝ)
    (θ₁ θ₂ : Fin s → ℝ) (hθ₁ : ∀ i, 0 ≤ θ₁ i) (hθ₂ : ∀ i, 0 ≤ θ₂ i)
    (h331_eq : KangKurtz.SCC.maxRho ν α β (KangKurtz.SCC.GammaMinus ν ν' θ₁) = KangKurtz.SCC.maxRho ν α β (KangKurtz.SCC.GammaPlus ν ν' θ₁))
    (h331_lt : KangKurtz.SCC.maxRho ν α β (KangKurtz.SCC.GammaPlus ν ν' θ₂ ∪ KangKurtz.SCC.GammaMinus ν ν' θ₂) <
      KangKurtz.SCC.maxRho ν α β (KangKurtz.SCC.GammaPlus ν ν' θ₁))
    (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) :
    KangKurtz.SCC.Balance ν ν' α β (c₁ • θ₁ + c₂ • θ₂) :=
  balLemma ν ν' α β θ₁ θ₂ c₁ c₂ hc₁ hc₂ h331_eq h331_lt
