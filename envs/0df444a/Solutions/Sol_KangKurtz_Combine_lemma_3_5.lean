-- Prove2me | solution 1 for KangKurtz.Combine.lemma_3_5
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:43:55.212269+00:00
-- url     : https://prove2.me/submissions/a3b5e124-f67d-427d-a9d3-83c2808f567f

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

theorem ts_iff {s r : ℕ} (ν ν' : Fin r → Fin s → ℕ) (α : Fin s → ℝ) (β : Fin r → ℝ) (γ : ℝ)
    (θ : Fin s → ℝ) (hθ : ∀ i, 0 ≤ θ i) :
    KangKurtz.Combine.TimeScale ν ν' α β γ θ ↔
      ∀ k ∈ KangKurtz.SCC.GammaPlus ν ν' θ ∪ KangKurtz.SCC.GammaMinus ν ν' θ,
        ∃ i, 0 < θ i ∧ KangKurtz.SCC.rho ν α β k + γ ≤ α i := by
  unfold KangKurtz.Combine.TimeScale KangKurtz.Combine.gammaTheta
  by_cases h : (KangKurtz.SCC.GammaPlus ν ν' θ ∪ KangKurtz.SCC.GammaMinus ν ν' θ).Nonempty
  · have hsupp : (KangKurtz.Combine.supp θ).Nonempty := by
      obtain ⟨k, hk⟩ := h
      rw [mem_gam] at hk
      unfold KangKurtz.SCC.dot at hk
      obtain ⟨i, _, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hk
      have hne : θ i ≠ 0 := left_ne_zero_of_mul hi
      have hpos : 0 < θ i := lt_of_le_of_ne (hθ i) (Ne.symm hne)
      exact ⟨i, by simp [KangKurtz.Combine.supp, hpos]⟩
    rw [dif_pos h, dif_pos hsupp, EReal.coe_le_coe_iff]
    constructor
    · intro hγ k hk
      have h1 : KangKurtz.SCC.rho ν α β k ≤
          (KangKurtz.SCC.GammaPlus ν ν' θ ∪ KangKurtz.SCC.GammaMinus ν ν' θ).sup' h
            (KangKurtz.SCC.rho ν α β) := Finset.le_sup' _ hk
      have h2 : KangKurtz.SCC.rho ν α β k + γ ≤ (KangKurtz.Combine.supp θ).sup' hsupp α := by
        linarith
      obtain ⟨i, hi, hle⟩ := (Finset.le_sup'_iff hsupp).1 h2
      exact ⟨i, by simpa [KangKurtz.Combine.supp] using hi, hle⟩
    · intro hk
      have : (KangKurtz.SCC.GammaPlus ν ν' θ ∪ KangKurtz.SCC.GammaMinus ν ν' θ).sup' h
            (KangKurtz.SCC.rho ν α β) ≤ (KangKurtz.Combine.supp θ).sup' hsupp α - γ := by
        apply Finset.sup'_le
        intro k hk'
        obtain ⟨i, hi, hle⟩ := hk k hk'
        have hi' : i ∈ KangKurtz.Combine.supp θ := by simp [KangKurtz.Combine.supp, hi]
        have := Finset.le_sup' α hi'
        linarith
      linarith
  · rw [dif_neg h]
    simp only [le_top, true_iff]
    intro k hk
    exact absurd ⟨k, hk⟩ h

theorem solution {s r : ℕ} (ν ν' : Fin r → Fin s → ℕ) (α : Fin s → ℝ) (hα : ∀ i, 0 ≤ α i)
    (β : Fin r → ℝ)
    (γ : ℝ) {m : ℕ} (θs : Fin m → Fin s → ℝ) (hθs : ∀ j i, 0 ≤ θs j i)
    (hts : ∀ j, KangKurtz.Combine.TimeScale ν ν' α β γ (θs j))
    (c : Fin m → ℝ) (hc : ∀ j, 0 < c j) :
    KangKurtz.Combine.TimeScale ν ν' α β γ (∑ j, c j • θs j) := by
  have hθ : ∀ i, 0 ≤ (∑ j, c j • θs j) i := by
    intro i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_nonneg (fun j _ => mul_nonneg (hc j).le (hθs j i))
  rw [ts_iff ν ν' α β γ _ hθ]
  intro k hk
  rw [mem_gam] at hk
  have hdot : KangKurtz.SCC.dot ν ν' (∑ j, c j • θs j) k =
      ∑ j, c j * KangKurtz.SCC.dot ν ν' (θs j) k := by
    unfold KangKurtz.SCC.dot
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hdot] at hk
  have : ∃ j, KangKurtz.SCC.dot ν ν' (θs j) k ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hk
    apply Finset.sum_eq_zero
    intro j _
    rw [hcon j, mul_zero]
  obtain ⟨j, hj⟩ := this
  have hkj : k ∈ KangKurtz.SCC.GammaPlus ν ν' (θs j) ∪ KangKurtz.SCC.GammaMinus ν ν' (θs j) :=
    (mem_gam ν ν' (θs j) k).2 hj
  obtain ⟨i, hi, hle⟩ := (ts_iff ν ν' α β γ (θs j) (hθs j)).1 (hts j) k hkj
  refine ⟨i, ?_, hle⟩
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have h1 : c j * θs j i ≤ ∑ j', c j' * θs j' i :=
    Finset.single_le_sum (f := fun j' => c j' * θs j' i)
      (fun j' _ => mul_nonneg (hc j').le (hθs j' i)) (Finset.mem_univ j)
  have h2 : 0 < c j * θs j i := mul_pos (hc j) hi
  linarith
