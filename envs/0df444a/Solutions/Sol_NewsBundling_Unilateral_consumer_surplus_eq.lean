-- Prove2me | solution 1 for NewsBundling.Unilateral.consumer_surplus_eq
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T22:02:16.023346+00:00
-- url     : https://prove2.me/submissions/4590359a-e791-48b9-9031-c86a205d47bf

import Mathlib
import Definitions.Def_NewsBundling_Unilateral_Setting

set_option autoImplicit false
open NewsBundling.Unilateral

namespace NBHelp

/-- The consumer's payoff gap to the interior optimum `Ts = (max q λ - λ)/(1-λ)`. -/
lemma key (q lam T : ℝ) (hl0 : 0 ≤ lam) (hl1 : lam < 1) (hT : T ∈ Set.Icc (0:ℝ) 1) :
    consumerPayoff q lam T + (1 - lam) ^ 2 * (T - (max q lam - lam) / (1 - lam)) ^ 2 / 2 ≤
      consumerPayoff q lam ((max q lam - lam) / (1 - lam)) := by
  have hk : 0 < 1 - lam := by linarith
  set k := 1 - lam with hkdef
  set Ts := (max q lam - lam) / k with hTs
  have hkT : k * Ts = max q lam - lam := by rw [hTs]; field_simp
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
    nlinarith [mul_nonneg (mul_nonneg hk.le hT0) (by linarith : (0:ℝ) ≤ (1 - k) - q),
      mul_nonneg hk.le hT0, sq_nonneg (k * T)]
  · have hm : max q lam = q := max_eq_left hql
    rw [hm] at hkT
    have hq' : q = k * Ts + lam := by linarith
    have : lam = 1 - k := by rw [hkdef]; ring
    rw [hq', this]
    nlinarith [sq_nonneg (k * (T - Ts))]

lemma Ts_mem (q lam : ℝ) (hq1 : q ≤ 1) (hl0 : 0 ≤ lam) (hl1 : lam < 1) :
    (max q lam - lam) / (1 - lam) ∈ Set.Icc (0:ℝ) 1 := by
  have hk : 0 < 1 - lam := by linarith
  have hmax : lam ≤ max q lam := le_max_right _ _
  have hmax1 : max q lam ≤ 1 := max_le hq1 hl1.le
  refine ⟨div_nonneg (by linarith) hk.le, ?_⟩
  rw [div_le_one hk]; linarith

lemma BR_exists (q lam : ℝ) (hq1 : q ≤ 1) (hl0 : 0 ≤ lam) (hl1 : lam < 1) :
    IsConsumerBR q lam ((max q lam - lam) / (1 - lam)) := by
  refine ⟨Ts_mem q lam hq1 hl0 hl1, fun T hT => ?_⟩
  have := key q lam T hl0 hl1 hT
  have : 0 ≤ (1 - lam) ^ 2 * (T - (max q lam - lam) / (1 - lam)) ^ 2 / 2 := by positivity
  linarith

lemma cons (q lam T1 : ℝ) (hq1 : q ≤ 1) (hl0 : 0 ≤ lam) (hl1 : lam < 1)
    (h : IsConsumerBR q lam T1) : 1 - T1 = (1 - max q lam) / (1 - lam) := by
  obtain ⟨hT1, hbr⟩ := h
  have hk : 0 < 1 - lam := by linarith
  have h1 := key q lam T1 hl0 hl1 hT1
  have h2 := hbr _ (Ts_mem q lam hq1 hl0 hl1)
  have h3 : (1 - lam) ^ 2 * (T1 - (max q lam - lam) / (1 - lam)) ^ 2 ≤ 0 := by linarith
  have h5 : (1 - lam) * (T1 - (max q lam - lam) / (1 - lam)) = 0 := by
    nlinarith [sq_nonneg ((1 - lam) * (T1 - (max q lam - lam) / (1 - lam)))]
  rcases mul_eq_zero.1 h5 with h0 | h0
  · exact absurd h0 hk.ne'
  · have : T1 = (max q lam - lam) / (1 - lam) := by linarith
    rw [this]
    field_simp
    ring

lemma strict (φ0 Λ q lam : ℝ) (hφ0 : 0 < φ0) (hφ1 : φ0 < 1) (hΛ0 : 0 ≤ Λ) (hΛ1 : Λ < 1)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hlam : lam ∈ Set.Icc 0 Λ) (hne : lam ≠ min q Λ) :
    (1 - lam + lam * φ0) * ((1 - max q lam) / (1 - lam)) <
      (1 - min q Λ + min q Λ * φ0) * ((1 - max q (min q Λ)) / (1 - min q Λ)) := by
  have hk : 0 < 1 - lam := by linarith [hlam.2]
  rcases le_or_gt q Λ with hqΛ | hqΛ
  · rw [min_eq_left hqΛ] at hne ⊢
    have hqk : 0 < 1 - q := by linarith
    rw [max_self, div_self hqk.ne', mul_one]
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · rw [max_eq_left hlt.le]
      have : (1 - lam + lam * φ0) * ((1 - q) / (1 - lam)) =
          ((1 - lam + lam * φ0) * (1 - q)) / (1 - lam) := by ring
      rw [this, div_lt_iff₀ hk]
      nlinarith [mul_pos hφ0 (sub_pos.2 hlt)]
    · rw [max_eq_right hgt.le, div_self hk.ne', mul_one]
      nlinarith [mul_pos (sub_pos.2 hφ1) (sub_pos.2 hgt)]
  · rw [min_eq_right hqΛ.le] at hne ⊢
    have hqk : 0 < 1 - q := by linarith
    have hkΛ : 0 < 1 - Λ := by linarith
    have hlt : lam < Λ := lt_of_le_of_ne hlam.2 hne
    rw [max_eq_left (by linarith [hlam.2] : lam ≤ q), max_eq_left hqΛ.le]
    have e1 : (1 - lam + lam * φ0) * ((1 - q) / (1 - lam)) =
        ((1 - lam + lam * φ0) * (1 - q)) / (1 - lam) := by ring
    have e2 : (1 - Λ + Λ * φ0) * ((1 - q) / (1 - Λ)) =
        ((1 - Λ + Λ * φ0) * (1 - q)) / (1 - Λ) := by ring
    rw [e1, e2, div_lt_div_iff₀ hk hkΛ]
    have : 0 < (1 - q) * (φ0 * (Λ - lam)) := mul_pos hqk (mul_pos hφ0 (sub_pos.2 hlt))
    nlinarith

/-- Stage-2/3 optimality (consumer and platform) of a profile. -/
def Sub (φ0 Λ : ℝ) (σ : Profile) : Prop :=
  (∀ q ∈ Set.Icc (0 : ℝ) 1, ∀ lam ∈ Set.Icc (0 : ℝ) Λ,
      IsConsumerBR q lam (σ.consumer q lam)) ∧
  (∀ q ∈ Set.Icc (0 : ℝ) 1,
      σ.platform q ∈ Set.Icc (0 : ℝ) Λ ∧
        ∀ lam ∈ Set.Icc (0 : ℝ) Λ,
          platformRevenue φ0 lam (σ.consumer q lam) ≤
            platformRevenue φ0 (σ.platform q) (σ.consumer q (σ.platform q)))

lemma Sub_of_SPE (β φ0 φ1 c Λ : ℝ) (σ : Profile) (h : IsSPE β φ0 φ1 c Λ σ) : Sub φ0 Λ σ :=
  ⟨h.1, h.2.1⟩

/-- The platform's choice at q < 1 is min q Λ. -/
lemma plat_eq (φ0 Λ : ℝ) (hφ0 : 0 < φ0) (hφ1 : φ0 < 1) (hΛ0 : 0 ≤ Λ) (hΛ1 : Λ < 1)
    (σ : Profile) (hs : Sub φ0 Λ σ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    σ.platform q = min q Λ := by
  have hq : q ∈ Set.Icc (0:ℝ) 1 := ⟨hq0, hq1.le⟩
  obtain ⟨hcons, hplat⟩ := hs
  have hl0 := (hplat q hq).1
  have hm : min q Λ ∈ Set.Icc 0 Λ := ⟨le_min hq0 hΛ0, min_le_right _ _⟩
  have h1 := (hplat q hq).2 _ hm
  unfold platformRevenue at h1
  rw [cons q _ _ hq.2 hm.1 (by linarith [hm.2]) (hcons q hq _ hm),
    cons q _ _ hq.2 hl0.1 (by linarith [hl0.2]) (hcons q hq _ hl0)] at h1
  by_contra hne
  exact absurd h1 (not_le.2 (strict φ0 Λ q _ hφ0 hφ1 hΛ0 hΛ1 hq0 hq1 hl0 hne))

lemma plat_le (φ0 Λ : ℝ) (hφ0 : 0 < φ0) (hφ1 : φ0 < 1) (hΛ0 : 0 ≤ Λ) (hΛ1 : Λ < 1)
    (σ : Profile) (hs : Sub φ0 Λ σ) (q : ℝ) (hq : q ∈ Set.Icc (0:ℝ) 1) :
    σ.platform q ≤ q := by
  rcases lt_or_eq_of_le hq.2 with hq1 | hq1
  · rw [plat_eq φ0 Λ hφ0 hφ1 hΛ0 hΛ1 σ hs q hq.1 hq1]; exact min_le_left _ _
  · subst hq1; linarith [(hs.2 1 hq).1.2]

/-- The reduced-form publisher profit, equation (2). -/
noncomputable def F (β φ1 c Λ q : ℝ) : ℝ :=
  φ1 * q - c * q ^ 2 / 2 + (β - φ1) * max (q - Λ) 0 / (1 - Λ)

lemma profit (β φ0 φ1 c Λ : ℝ) (hφ0 : 0 < φ0) (hφ1 : φ0 < 1) (hΛ0 : 0 ≤ Λ) (hΛ1 : Λ < 1)
    (σ : Profile) (hs : Sub φ0 Λ σ) (q : ℝ) (hq : q ∈ Set.Icc (0:ℝ) 1) :
    publisherProfit β φ1 c σ q = F β φ1 c Λ q := by
  have hl0 := (hs.2 q hq).1
  have hT := cons q _ _ hq.2 hl0.1 (by linarith [hl0.2]) (hs.1 q hq _ hl0)
  have hkΛ : (1 - Λ) ≠ 0 := by linarith
  unfold publisherProfit publisherRevenue F
  rcases lt_or_eq_of_le hq.2 with hq1 | hq1
  · have hl := plat_eq φ0 Λ hφ0 hφ1 hΛ0 hΛ1 σ hs q hq.1 hq1
    set T := σ.consumer q (σ.platform q) with hTdef
    rw [hl] at hT ⊢
    have hT' : T = 1 - (1 - max q (min q Λ)) / (1 - min q Λ) := by linarith
    rw [hT']
    rcases le_or_gt q Λ with hqΛ | hqΛ
    · rw [min_eq_left hqΛ, max_self, max_eq_right (by linarith : q - Λ ≤ 0)]
      have : 1 - q ≠ 0 := by linarith
      rw [div_self this]; ring
    · rw [min_eq_right hqΛ.le, max_eq_left hqΛ.le, max_eq_left (by linarith : (0:ℝ) ≤ q - Λ)]
      field_simp
      ring
  · subst hq1
    have : 1 - max 1 (σ.platform 1) = 0 := by
      rw [max_eq_left (by linarith [hl0.2])]; ring
    rw [this, zero_div] at hT
    have hT1 : σ.consumer 1 (σ.platform 1) = 1 := by linarith
    rw [hT1, max_eq_left (by linarith : (0:ℝ) ≤ 1 - Λ)]
    field_simp
    ring

lemma surplus (φ0 Λ : ℝ) (hφ0 : 0 < φ0) (hφ1 : φ0 < 1) (hΛ0 : 0 ≤ Λ) (hΛ1 : Λ < 1)
    (σ : Profile) (hs : Sub φ0 Λ σ) (q : ℝ) (hq : q ∈ Set.Icc (0:ℝ) 1) :
    consumerPayoff q (σ.platform q) (σ.consumer q (σ.platform q)) = 1 + q ^ 2 / 2 := by
  have hl0 := (hs.2 q hq).1
  have hk : 1 - σ.platform q ≠ 0 := by linarith [hl0.2]
  have hT := cons q _ _ hq.2 hl0.1 (by linarith [hl0.2]) (hs.1 q hq _ hl0)
  rw [max_eq_left (plat_le φ0 Λ hφ0 hφ1 hΛ0 hΛ1 σ hs q hq)] at hT
  have hT' : σ.consumer q (σ.platform q) = 1 - (1 - q) / (1 - σ.platform q) := by linarith
  rw [hT']
  unfold consumerPayoff utility
  field_simp
  ring

/-- The canonical subgame strategies. -/
noncomputable def prof (Λ q0 : ℝ) : Profile where
  consumer := fun q lam => (max q lam - lam) / (1 - lam)
  platform := fun q => min q Λ
  quality := q0

lemma prof_sub (φ0 Λ q0 : ℝ) (hφ0 : 0 < φ0) (hφ1 : φ0 < 1) (hΛ0 : 0 ≤ Λ) (hΛ1 : Λ < 1) :
    Sub φ0 Λ (prof Λ q0) := by
  refine ⟨fun q hq lam hlam => BR_exists q lam hq.2 hlam.1 (by linarith [hlam.2]), ?_⟩
  intro q hq
  have hm : min q Λ ∈ Set.Icc 0 Λ := ⟨le_min hq.1 hΛ0, min_le_right _ _⟩
  refine ⟨hm, fun lam hlam => ?_⟩
  simp only [prof, platformRevenue]
  have hk : 0 < 1 - lam := by linarith [hlam.2]
  have hk' : 0 < 1 - min q Λ := by linarith [hm.2]
  have e1 : 1 - (max q lam - lam) / (1 - lam) = (1 - max q lam) / (1 - lam) := by
    field_simp; ring
  have e2 : 1 - (max q (min q Λ) - min q Λ) / (1 - min q Λ) =
      (1 - max q (min q Λ)) / (1 - min q Λ) := by
    field_simp; ring
  rw [e1, e2]
  rcases lt_or_eq_of_le hq.2 with hq1 | hq1
  · by_cases hne : lam = min q Λ
    · rw [hne]
    · exact (strict φ0 Λ q lam hφ0 hφ1 hΛ0 hΛ1 hq.1 hq1 hlam hne).le
  · subst hq1
    rw [max_eq_left (by linarith [hlam.2]), max_eq_left (by linarith [hm.2])]
    simp

/-! ### The publisher's optimization -/

section opt
variable (β φ1 c Λ : ℝ)

lemma F_low (q : ℝ) (hq : q ≤ Λ) : F β φ1 c Λ q = pi1L φ1 q c := by
  unfold F pi1L
  rw [max_eq_right (by linarith : q - Λ ≤ 0)]; ring

lemma F_high (hΛ1 : Λ < 1) (q : ℝ) (hq : Λ ≤ q) : F β φ1 c Λ q = pi1H β φ1 Λ q c := by
  have : (1 - Λ) ≠ 0 := by linarith
  unfold F pi1H
  rw [max_eq_left (by linarith : (0:ℝ) ≤ q - Λ)]
  field_simp; ring

lemma L_le_F (hβ : φ1 < β) (hΛ1 : Λ < 1) (q : ℝ) : pi1L φ1 q c ≤ F β φ1 c Λ q := by
  unfold F pi1L
  have : 0 ≤ (β - φ1) * max (q - Λ) 0 / (1 - Λ) := by
    apply div_nonneg _ (by linarith)
    exact mul_nonneg (by linarith) (le_max_right _ _)
  linarith

lemma H_le_F (hβ : φ1 < β) (hΛ1 : Λ < 1) (q : ℝ) : pi1H β φ1 Λ q c ≤ F β φ1 c Λ q := by
  have hk : (0:ℝ) < 1 - Λ := by linarith
  have e : pi1H β φ1 Λ q c = φ1 * q - c * q ^ 2 / 2 + (β - φ1) * (q - Λ) / (1 - Λ) := by
    unfold pi1H; field_simp; ring
  rw [e]; unfold F
  have : (β - φ1) * (q - Λ) / (1 - Λ) ≤ (β - φ1) * max (q - Λ) 0 / (1 - Λ) := by
    apply div_le_div_of_nonneg_right _ hk.le
    exact mul_le_mul_of_nonneg_left (le_max_left _ _) (by linarith)
  linarith

lemma L_vertex (hc : 0 < c) (q : ℝ) :
    pi1L φ1 q c = pi1L φ1 (qL φ1 c) c - c / 2 * (q - qL φ1 c) ^ 2 := by
  unfold pi1L qL; field_simp; ring

lemma H_vertex (hc : 0 < c) (hΛ1 : Λ < 1) (q : ℝ) :
    pi1H β φ1 Λ q c = pi1H β φ1 Λ (qH β φ1 c Λ) c - c / 2 * (q - qH β φ1 c Λ) ^ 2 := by
  have : (1 - Λ) ≠ 0 := by linarith
  unfold pi1H qH; field_simp; ring

lemma gap (hc : 0 < c) (hΛ1 : Λ < 1) :
    pi1H β φ1 Λ (qH β φ1 c Λ) c - pi1L φ1 (qL φ1 c) c =
      (β - φ1) * ((β + φ1 * (1 - 2 * Λ)) - 2 * c * Λ * (1 - Λ)) / (2 * c * (1 - Λ) ^ 2) := by
  have : (1 - Λ) ≠ 0 := by linarith
  unfold pi1H pi1L qH qL; field_simp; ring

lemma cdagger_lt_iff (hΛ0 : 0 < Λ) (hΛ1 : Λ < 1) :
    cdagger β φ1 Λ < c ↔ (β + φ1 * (1 - 2 * Λ)) < 2 * c * Λ * (1 - Λ) := by
  have hp : 0 < 2 * Λ * (1 - Λ) := mul_pos (mul_pos two_pos hΛ0) (by linarith)
  unfold cdagger
  rw [div_lt_iff₀ hp]; constructor <;> intro h <;> linarith

lemma lt_cdagger_iff (hΛ0 : 0 < Λ) (hΛ1 : Λ < 1) :
    c < cdagger β φ1 Λ ↔ 2 * c * Λ * (1 - Λ) < (β + φ1 * (1 - 2 * Λ)) := by
  have hp : 0 < 2 * Λ * (1 - Λ) := mul_pos (mul_pos two_pos hΛ0) (by linarith)
  unfold cdagger
  rw [lt_div_iff₀ hp]; constructor <;> intro h <;> linarith

lemma gap_neg_iff (hc : 0 < c) (hβ : φ1 < β) (hΛ0 : 0 < Λ) (hΛ1 : Λ < 1) :
    pi1H β φ1 Λ (qH β φ1 c Λ) c < pi1L φ1 (qL φ1 c) c ↔ cdagger β φ1 Λ < c := by
  rw [cdagger_lt_iff β φ1 c Λ hΛ0 hΛ1, ← sub_neg, gap β φ1 c Λ hc hΛ1]
  have hd : 0 < 2 * c * (1 - Λ) ^ 2 := mul_pos (mul_pos two_pos hc) (pow_pos (by linarith) 2)
  rw [div_lt_iff₀ hd, zero_mul]
  constructor
  · intro h
    by_contra h'
    push_neg at h'
    have := mul_nonneg (by linarith : (0:ℝ) ≤ β - φ1) (by linarith : (0:ℝ) ≤ β + φ1 * (1 - 2 * Λ) - 2 * c * Λ * (1 - Λ))
    linarith
  · intro h
    exact mul_neg_of_pos_of_neg (by linarith) (by linarith)

lemma gap_pos_iff (hc : 0 < c) (hβ : φ1 < β) (hΛ0 : 0 < Λ) (hΛ1 : Λ < 1) :
    pi1L φ1 (qL φ1 c) c < pi1H β φ1 Λ (qH β φ1 c Λ) c ↔ c < cdagger β φ1 Λ := by
  rw [lt_cdagger_iff β φ1 c Λ hΛ0 hΛ1, ← sub_pos, gap β φ1 c Λ hc hΛ1]
  have hd : 0 < 2 * c * (1 - Λ) ^ 2 := mul_pos (mul_pos two_pos hc) (pow_pos (by linarith) 2)
  rw [lt_div_iff₀ hd, zero_mul]
  constructor
  · intro h
    by_contra h'
    push_neg at h'
    have := mul_nonpos_of_nonneg_of_nonpos (by linarith : (0:ℝ) ≤ β - φ1) (by linarith : β + φ1 * (1 - 2 * Λ) - 2 * c * Λ * (1 - Λ) ≤ 0)
    linarith
  · intro h; exact mul_pos (by linarith) (by linarith)

lemma gap_zero (hc : 0 < c) (hΛ1 : Λ < 1) (hΛ0 : 0 < Λ) (hcd : c = cdagger β φ1 Λ) :
    pi1L φ1 (qL φ1 c) c = pi1H β φ1 Λ (qH β φ1 c Λ) c := by
  have h := gap β φ1 c Λ hc hΛ1
  have hp : 2 * Λ * (1 - Λ) ≠ 0 := (mul_pos (mul_pos two_pos hΛ0) (by linarith)).ne'
  have : (β + φ1 * (1 - 2 * Λ)) - 2 * c * Λ * (1 - Λ) = 0 := by
    rw [hcd]; unfold cdagger
    rw [show 2 * ((β + φ1 * (1 - 2 * Λ)) / (2 * Λ * (1 - Λ))) * Λ * (1 - Λ) =
      (β + φ1 * (1 - 2 * Λ)) / (2 * Λ * (1 - Λ)) * (2 * Λ * (1 - Λ)) by ring,
      div_mul_cancel₀ _ hp]
    ring
  rw [this, mul_zero, zero_div] at h
  linarith

lemma qL_mem (hφ : 0 < φ1) (hβ : φ1 < β) (hc : 2 * β < c) : qL φ1 c ∈ Set.Icc (0:ℝ) 1 := by
  have hc0 : 0 < c := by linarith
  unfold qL
  exact ⟨by positivity, by rw [div_le_one hc0]; linarith⟩

lemma qH_mem (hφ : 0 < φ1) (hβ : φ1 < β) (hc : 2 * β < c) (hΛ0 : 0 < Λ) (hΛ1 : Λ < 1 / 2) :
    qH β φ1 c Λ ∈ Set.Icc (0:ℝ) 1 := by
  have hc0 : 0 < c := by linarith
  have hk : 0 < 1 - Λ := by linarith
  unfold qH
  refine ⟨div_nonneg (by nlinarith) (by positivity), ?_⟩
  rw [div_le_one (by positivity)]
  nlinarith

/-- The maximizers of F over [0,1]. -/
lemma argmax (hφ : 0 < φ1) (hβ : φ1 < β) (hc : 2 * β < c) (hΛ0 : 0 < Λ) (hΛ1 : Λ < 1 / 2)
    (qs : ℝ) (hqs : qs ∈ Set.Icc (0:ℝ) 1)
    (hmax : ∀ q ∈ Set.Icc (0:ℝ) 1, F β φ1 c Λ q ≤ F β φ1 c Λ qs) :
    (qs = qL φ1 c ∧ pi1H β φ1 Λ (qH β φ1 c Λ) c ≤ pi1L φ1 (qL φ1 c) c) ∨
    (qs = qH β φ1 c Λ ∧ pi1L φ1 (qL φ1 c) c ≤ pi1H β φ1 Λ (qH β φ1 c Λ) c) := by
  have hc0 : 0 < c := by linarith
  have hΛ1' : Λ < 1 := by linarith
  have hA := (L_le_F β φ1 c Λ hβ hΛ1' (qL φ1 c)).trans (hmax _ (qL_mem β φ1 c hφ hβ hc))
  have hB := (H_le_F β φ1 c Λ hβ hΛ1' (qH β φ1 c Λ)).trans
    (hmax _ (qH_mem β φ1 c Λ hφ hβ hc hΛ0 hΛ1))
  rcases le_total qs Λ with h | h
  · left
    rw [F_low β φ1 c Λ qs h, L_vertex φ1 c hc0 qs] at hA hB
    have hsq : c / 2 * (qs - qL φ1 c) ^ 2 ≤ 0 := by linarith
    have hsq0 : 0 ≤ c / 2 * (qs - qL φ1 c) ^ 2 := by positivity
    have : (qs - qL φ1 c) ^ 2 = 0 := by
      have := le_antisymm hsq hsq0
      rcases mul_eq_zero.1 this with h1 | h1
      · linarith
      · exact h1
    refine ⟨by nlinarith [pow_eq_zero_iff (n := 2) (a := qs - qL φ1 c) two_ne_zero |>.1 this], ?_⟩
    linarith
  · right
    rw [F_high β φ1 c Λ hΛ1' qs h, H_vertex β φ1 c Λ hc0 hΛ1' qs] at hA hB
    have hsq : c / 2 * (qs - qH β φ1 c Λ) ^ 2 ≤ 0 := by linarith
    have hsq0 : 0 ≤ c / 2 * (qs - qH β φ1 c Λ) ^ 2 := by positivity
    have : (qs - qH β φ1 c Λ) ^ 2 = 0 := by
      have := le_antisymm hsq hsq0
      rcases mul_eq_zero.1 this with h1 | h1
      · linarith
      · exact h1
    refine ⟨by nlinarith [pow_eq_zero_iff (n := 2) (a := qs - qH β φ1 c Λ) two_ne_zero |>.1 this], ?_⟩
    linarith

lemma F_le_max (hc0 : 0 < c) (hΛ1 : Λ < 1) (q : ℝ) :
    F β φ1 c Λ q ≤ max (pi1L φ1 (qL φ1 c) c) (pi1H β φ1 Λ (qH β φ1 c Λ) c) := by
  rcases le_total q Λ with h | h
  · rw [F_low β φ1 c Λ q h, L_vertex φ1 c hc0 q]
    have : 0 ≤ c / 2 * (q - qL φ1 c) ^ 2 := by positivity
    have := le_max_left (pi1L φ1 (qL φ1 c) c) (pi1H β φ1 Λ (qH β φ1 c Λ) c)
    linarith
  · rw [F_high β φ1 c Λ hΛ1 q h, H_vertex β φ1 c Λ hc0 hΛ1 q]
    have : 0 ≤ c / 2 * (q - qH β φ1 c Λ) ^ 2 := by positivity
    have := le_max_right (pi1L φ1 (qL φ1 c) c) (pi1H β φ1 Λ (qH β φ1 c Λ) c)
    linarith

lemma qL_opt (hc0 : 0 < c) (hβ : φ1 < β) (hΛ1 : Λ < 1)
    (hle : pi1H β φ1 Λ (qH β φ1 c Λ) c ≤ pi1L φ1 (qL φ1 c) c) (q : ℝ) :
    F β φ1 c Λ q ≤ F β φ1 c Λ (qL φ1 c) := by
  have h1 := F_le_max β φ1 c Λ hc0 hΛ1 q
  rw [max_eq_left hle] at h1
  exact h1.trans (L_le_F β φ1 c Λ hβ hΛ1 _)

lemma qH_opt (hc0 : 0 < c) (hβ : φ1 < β) (hΛ1 : Λ < 1)
    (hle : pi1L φ1 (qL φ1 c) c ≤ pi1H β φ1 Λ (qH β φ1 c Λ) c) (q : ℝ) :
    F β φ1 c Λ q ≤ F β φ1 c Λ (qH β φ1 c Λ) := by
  have h1 := F_le_max β φ1 c Λ hc0 hΛ1 q
  rw [max_eq_right hle] at h1
  exact h1.trans (H_le_F β φ1 c Λ hβ hΛ1 _)

end opt

/-- An SPE of the bundling game with a prescribed optimal quality. -/
lemma spe_of (β φ0 φ1 c Λ q0 : ℝ) (hφ0 : 0 < φ0) (hφ1 : φ0 < 1) (hΛ0 : 0 ≤ Λ) (hΛ1 : Λ < 1)
    (hq0 : q0 ∈ Set.Icc (0:ℝ) 1) (hopt : ∀ q ∈ Set.Icc (0:ℝ) 1, F β φ1 c Λ q ≤ F β φ1 c Λ q0) :
    IsSPE β φ0 φ1 c Λ (prof Λ q0) := by
  have hs := prof_sub φ0 Λ q0 hφ0 hφ1 hΛ0 hΛ1
  refine ⟨hs.1, hs.2, hq0, fun q hq => ?_⟩
  show publisherProfit β φ1 c (prof Λ q0) q ≤ publisherProfit β φ1 c (prof Λ q0) q0
  rw [profit β φ0 φ1 c Λ hφ0 hφ1 hΛ0 hΛ1 _ hs q hq,
    profit β φ0 φ1 c Λ hφ0 hφ1 hΛ0 hΛ1 _ hs _ hq0]
  exact hopt q hq

lemma spe_quality (β φ0 φ1 c Λ : ℝ) (h : StandingAssumptions β φ0 φ1 c Λ) (σ : Profile)
    (hσ : IsSPE β φ0 φ1 c Λ σ) :
    (σ.quality = qL φ1 c ∧ pi1H β φ1 Λ (qH β φ1 c Λ) c ≤ pi1L φ1 (qL φ1 c) c) ∨
    (σ.quality = qH β φ1 c Λ ∧ pi1L φ1 (qL φ1 c) c ≤ pi1H β φ1 Λ (qH β φ1 c Λ) c) := by
  obtain ⟨⟨hφ0, hφ0'⟩, ⟨hφ1, hφ1'⟩, hφβ, hβc, hΛ0, hΛ1⟩ := h
  have hs := Sub_of_SPE β φ0 φ1 c Λ σ hσ
  have hq := hσ.2.2.1
  apply argmax β φ1 c Λ hφ1 hφβ hβc hΛ0 hΛ1 _ hq
  intro q hq'
  rw [← profit β φ0 φ1 c Λ hφ0 hφ0' hΛ0.le (by linarith) σ hs q hq',
    ← profit β φ0 φ1 c Λ hφ0 hφ0' hΛ0.le (by linarith) σ hs _ hq]
  exact hσ.2.2.2 q hq'

/-! ### Benchmark (Λ = 0) -/

lemma bench_profit (β φ0 φ1 c : ℝ) (σ : Profile)
    (hcons : ∀ q ∈ Set.Icc (0 : ℝ) 1, ∀ lam ∈ Set.Icc (0 : ℝ) 0,
      IsConsumerBR q lam (σ.consumer q lam))
    (hplat : ∀ q ∈ Set.Icc (0 : ℝ) 1, σ.platform q ∈ Set.Icc (0 : ℝ) 0)
    (q : ℝ) (hq : q ∈ Set.Icc (0:ℝ) 1) :
    publisherProfit β φ1 c σ q = β * q - c * q ^ 2 / 2 := by
  have hl0 := hplat q hq
  have hp : σ.platform q = 0 := le_antisymm hl0.2 hl0.1
  have hT := cons q _ _ hq.2 hl0.1 (by linarith [hl0.2]) (hcons q hq _ hl0)
  unfold publisherProfit publisherRevenue
  rw [hp] at hT ⊢
  rw [max_eq_left hq.1] at hT
  have : σ.consumer q 0 = q := by linarith
  rw [this]; ring

lemma bench_spe (β φ0 φ1 c : ℝ) (hβ : 0 < β) (hc : 2 * β < c) :
    IsSPE β φ0 φ1 c 0 (prof 0 (β / c)) := by
  have hc0 : 0 < c := by linarith
  have hcons : ∀ q ∈ Set.Icc (0 : ℝ) 1, ∀ lam ∈ Set.Icc (0 : ℝ) 0,
      IsConsumerBR q lam ((prof 0 (β / c)).consumer q lam) :=
    fun q hq lam hlam => BR_exists q lam hq.2 hlam.1 (by linarith [hlam.2])
  have hplat : ∀ q ∈ Set.Icc (0 : ℝ) 1, (prof 0 (β / c)).platform q ∈ Set.Icc (0 : ℝ) 0 := by
    intro q hq; simp only [prof, min_eq_right hq.1]; exact ⟨le_refl _, le_refl _⟩
  have hqm : β / c ∈ Set.Icc (0:ℝ) 1 :=
    ⟨by positivity, by rw [div_le_one hc0]; linarith⟩
  refine ⟨hcons, fun q hq => ⟨hplat q hq, fun lam hlam => ?_⟩, hqm, fun q hq => ?_⟩
  · have h1 : lam = 0 := le_antisymm hlam.2 hlam.1
    have h2 : (prof 0 (β / c)).platform q = 0 := le_antisymm (hplat q hq).2 (hplat q hq).1
    rw [h1, h2]
  · show publisherProfit β φ1 c (prof 0 (β / c)) q ≤ publisherProfit β φ1 c (prof 0 (β / c)) (β / c)
    rw [bench_profit β φ0 φ1 c _ hcons hplat q hq, bench_profit β φ0 φ1 c _ hcons hplat _ hqm]
    show β * q - c * q ^ 2 / 2 ≤ β * (β / c) - c * (β / c) ^ 2 / 2
    have : β * (β / c) - c * (β / c) ^ 2 / 2 - (β * q - c * q ^ 2 / 2) = (c * q - β) ^ 2 / (2 * c) := by
      field_simp; ring
    have : 0 ≤ (c * q - β) ^ 2 / (2 * c) := by positivity
    linarith

lemma bench_unique (β φ0 φ1 c : ℝ) (hβ : 0 < β) (hc : 2 * β < c) (σ : Profile)
    (hσ : IsSPE β φ0 φ1 c 0 σ) :
    σ.quality = β / c ∧ eqProfit β φ1 c σ = β ^ 2 / (2 * c) := by
  have hc0 : 0 < c := by linarith
  have hplat : ∀ q ∈ Set.Icc (0 : ℝ) 1, σ.platform q ∈ Set.Icc (0 : ℝ) 0 :=
    fun q hq => (hσ.2.1 q hq).1
  have hqm : β / c ∈ Set.Icc (0:ℝ) 1 :=
    ⟨by positivity, by rw [div_le_one hc0]; linarith⟩
  have hq := hσ.2.2.1
  have h1 := hσ.2.2.2 _ hqm
  rw [bench_profit β φ0 φ1 c σ hσ.1 hplat _ hqm, bench_profit β φ0 φ1 c σ hσ.1 hplat _ hq] at h1
  have e : β * (β / c) - c * (β / c) ^ 2 / 2 - (β * σ.quality - c * σ.quality ^ 2 / 2) =
      (c * σ.quality - β) ^ 2 / (2 * c) := by field_simp; ring
  have h2 : (c * σ.quality - β) ^ 2 / (2 * c) ≤ 0 := by linarith
  have h3 : (c * σ.quality - β) ^ 2 = 0 := by
    have : 0 ≤ (c * σ.quality - β) ^ 2 / (2 * c) := by positivity
    have h4 : (c * σ.quality - β) ^ 2 / (2 * c) = 0 := le_antisymm h2 this
    rcases div_eq_zero_iff.1 h4 with h5 | h5
    · exact h5
    · linarith
  have hq' : σ.quality = β / c := by
    have := pow_eq_zero_iff (n := 2) two_ne_zero |>.1 h3
    field_simp; linarith
  refine ⟨hq', ?_⟩
  unfold eqProfit
  rw [bench_profit β φ0 φ1 c σ hσ.1 hplat _ hq, hq']
  field_simp; ring

end NBHelp

open NBHelp

theorem solution (β φ0 φ1 c : ℝ)
    (hφ0 : 0 < φ0 ∧ φ0 < 1) :
    ∀ Λ' : ℝ, 0 ≤ Λ' → Λ' < 1 →
      ∀ σ, IsSPE β φ0 φ1 c Λ' σ →
        consumerSurplus σ = 1 + σ.quality ^ 2 / 2 := by
  intro Λ' h0 h1 σ hσ
  exact surplus φ0 Λ' hφ0.1 hφ0.2 h0 h1 σ (Sub_of_SPE β φ0 φ1 c Λ' σ hσ) _ hσ.2.2.1
