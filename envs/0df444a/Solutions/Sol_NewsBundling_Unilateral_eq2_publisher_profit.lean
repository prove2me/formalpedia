-- Prove2me | solution 1 for NewsBundling.Unilateral.eq2_publisher_profit
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:15:27.683777+00:00
-- url     : https://prove2.me/submissions/15259958-d57e-42c0-96bf-d846a3657aca

import Mathlib
import Definitions.Def_NewsBundling_Unilateral_Setting
set_option autoImplicit false
open NewsBundling.Unilateral

lemma vv_cons (q lam T1 : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hl0 : 0 ≤ lam) (hl1 : lam < 1)
    (h : IsConsumerBR q lam T1) : 1 - T1 = (1 - max q lam) / (1 - lam) := by
  obtain ⟨hT1, hbr⟩ := h
  have hk : 0 < 1 - lam := by linarith
  set k := 1 - lam with hkdef
  set Ts := (max q lam - lam) / k with hTs
  have hkT : k * Ts = max q lam - lam := by rw [hTs]; field_simp
  have hmax : lam ≤ max q lam := le_max_right _ _
  have hmax1 : max q lam ≤ 1 := max_le hq1 hl1.le
  have hTs0 : 0 ≤ Ts := by
    rw [hTs]; exact div_nonneg (by linarith) hk.le
  have hTs1 : Ts ≤ 1 := by
    rw [hTs, div_le_one hk]; linarith
  have key : ∀ T ∈ Set.Icc (0:ℝ) 1,
      consumerPayoff q lam T + k ^ 2 * (T - Ts) ^ 2 / 2 ≤ consumerPayoff q lam Ts := by
    intro T hT
    unfold consumerPayoff utility
    rcases le_total q lam with hql | hql
    · have hm : max q lam = lam := max_eq_right hql
      rw [hm] at hkT
      have hTs' : Ts = 0 := by
        have : k * Ts = 0 := by linarith
        rcases mul_eq_zero.1 this with h0 | h0
        · exact absurd h0 hk.ne'
        · exact h0
      rw [hTs']
      have hT0 := hT.1
      have : lam = 1 - k := by rw [hkdef]; ring
      rw [this]
      nlinarith [mul_nonneg (mul_nonneg hk.le hT0) (by linarith : (0:ℝ) ≤ (1 - k) - q), mul_nonneg hk.le hT0, sq_nonneg (k * T)]
    · have hm : max q lam = q := max_eq_left hql
      rw [hm] at hkT
      have hq' : q = k * Ts + lam := by linarith
      have : lam = 1 - k := by rw [hkdef]; ring
      rw [hq', this]
      nlinarith [sq_nonneg (k * (T - Ts))]
  have h1 := key T1 hT1
  have h2 := hbr Ts ⟨hTs0, hTs1⟩
  have h3 : k ^ 2 * (T1 - Ts) ^ 2 ≤ 0 := by linarith
  have h4 : T1 = Ts := by
    have : (k * (T1 - Ts)) ^ 2 ≤ 0 := by nlinarith
    have h5 : k * (T1 - Ts) = 0 := by nlinarith [sq_nonneg (k * (T1 - Ts))]
    rcases mul_eq_zero.1 h5 with h0 | h0
    · exact absurd h0 hk.ne'
    · linarith
  rw [h4, hTs]
  field_simp
  ring

lemma vv_plat (φ0 Λ q l0 : ℝ) (hφ0 : 0 < φ0) (hφ1 : φ0 < 1) (hΛ0 : 0 < Λ) (hΛ1 : Λ < 1 / 2)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hl0 : l0 ∈ Set.Icc 0 Λ)
    (hopt : ∀ lam ∈ Set.Icc 0 Λ, (1 - lam + lam * φ0) * ((1 - max q lam) / (1 - lam)) ≤
      (1 - l0 + l0 * φ0) * ((1 - max q l0) / (1 - l0))) : l0 = min q Λ := by
  have hm : min q Λ ∈ Set.Icc 0 Λ := ⟨le_min hq0 hΛ0.le, min_le_right _ _⟩
  have h1 := hopt _ hm
  have claim : ∀ lam ∈ Set.Icc 0 Λ, lam ≠ min q Λ →
      (1 - lam + lam * φ0) * ((1 - max q lam) / (1 - lam)) <
        (1 - min q Λ + min q Λ * φ0) * ((1 - max q (min q Λ)) / (1 - min q Λ)) := by
    intro lam hlam hne
    have hk : 0 < 1 - lam := by linarith [hlam.2]
    rcases le_or_gt q Λ with hqΛ | hqΛ
    · rw [min_eq_left hqΛ] at hne ⊢
      have hqk : 0 < 1 - q := by linarith
      rw [max_self, div_self hqk.ne', mul_one]
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · rw [max_eq_left hlt.le]
        have : (1 - lam + lam * φ0) * ((1 - q) / (1 - lam)) = ((1 - lam + lam * φ0) * (1 - q)) / (1 - lam) := by ring
        rw [this, div_lt_iff₀ hk]
        nlinarith [mul_pos hφ0 (sub_pos.2 hlt)]
      · rw [max_eq_right hgt.le, div_self hk.ne', mul_one]
        nlinarith [mul_pos (sub_pos.2 hφ1) (sub_pos.2 hgt)]
    · rw [min_eq_right hqΛ.le] at hne ⊢
      have hqk : 0 < 1 - q := by linarith
      have hkΛ : 0 < 1 - Λ := by linarith
      have hlt : lam < Λ := lt_of_le_of_ne hlam.2 hne
      rw [max_eq_left (by linarith : lam ≤ q), max_eq_left hqΛ.le]
      have e1 : (1 - lam + lam * φ0) * ((1 - q) / (1 - lam)) = ((1 - lam + lam * φ0) * (1 - q)) / (1 - lam) := by ring
      have e2 : (1 - Λ + Λ * φ0) * ((1 - q) / (1 - Λ)) = ((1 - Λ + Λ * φ0) * (1 - q)) / (1 - Λ) := by ring
      rw [e1, e2, div_lt_div_iff₀ hk hkΛ]
      have : 0 < (1 - q) * (φ0 * (Λ - lam)) := mul_pos hqk (mul_pos hφ0 (sub_pos.2 hlt))
      nlinarith
  by_contra hne
  exact absurd h1 (not_le.2 (claim l0 hl0 hne))

theorem solution (β φ0 φ1 c Λ : ℝ)
    (h : StandingAssumptions β φ0 φ1 c Λ) :
    ∀ σ, IsSPE β φ0 φ1 c Λ σ →
      ∀ q ∈ Set.Icc (0 : ℝ) 1,
        publisherProfit β φ1 c σ q =
          if q ≤ Λ then φ1 * q - c * q ^ 2 / 2
          else φ1 * Λ * (1 - q) / (1 - Λ) +
            β * (q - Λ) / (1 - Λ) - c * q ^ 2 / 2 := by
  obtain ⟨⟨hφ0, hφ0'⟩, ⟨hφ1, hφ1'⟩, hφβ, hβc, hΛ0, hΛ1⟩ := h
  intro σ hσ q hq
  obtain ⟨hcons, hplat, hqual, hpub⟩ := hσ
  have hΛ : Λ < 1 := by linarith
  have hl0 := (hplat q hq).1
  have hT0 := vv_cons q (σ.platform q) (σ.consumer q (σ.platform q)) hq.1 hq.2 hl0.1
    (by linarith [hl0.2]) (hcons q hq _ hl0)
  unfold publisherProfit publisherRevenue
  rcases lt_or_eq_of_le hq.2 with hq1 | hq1
  · have hl : σ.platform q = min q Λ := by
      apply vv_plat φ0 Λ q _ hφ0 hφ0' hΛ0 hΛ1 hq.1 hq1 hl0
      intro lam hlam
      have := (hplat q hq).2 lam hlam
      unfold platformRevenue at this
      have hc' := vv_cons q lam (σ.consumer q lam) hq.1 hq.2 hlam.1 (by linarith [hlam.2]) (hcons q hq lam hlam)
      have hc0 := vv_cons q (σ.platform q) (σ.consumer q (σ.platform q)) hq.1 hq.2 hl0.1 (by linarith [hl0.2]) (hcons q hq _ hl0)
      rw [hc', ] at this
      rw [hc0] at this
      exact this
    set T := σ.consumer q (σ.platform q) with hT
    rw [hl] at hT0 ⊢
    have hT' : T = 1 - (1 - max q (min q Λ)) / (1 - min q Λ) := by linarith
    rw [hT']
    split_ifs with hqΛ
    · rw [min_eq_left hqΛ, max_self]
      have : 1 - q ≠ 0 := by linarith
      rw [div_self this]; ring
    · push_neg at hqΛ
      rw [min_eq_right hqΛ.le, max_eq_left hqΛ.le]
      have : 1 - Λ ≠ 0 := by linarith
      field_simp
      ring
  · subst hq1
    have hqΛ : ¬ (1 ≤ Λ) := by linarith
    rw [if_neg hqΛ]
    have : 1 - max 1 (σ.platform 1) = 0 := by
      rw [max_eq_left (by linarith [hl0.2])]; ring
    rw [this, zero_div] at hT0
    have hT1 : σ.consumer 1 (σ.platform 1) = 1 := by linarith
    rw [hT1]
    have : 1 - Λ ≠ 0 := by linarith
    field_simp
    ring
