-- Prove2me | solution 1 for NewsBundling.Negotiated.eq4_fee_low
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T19:38:05.427994+00:00
-- url     : https://prove2.me/submissions/53f260b3-ed1d-436e-ad94-fccde6bed5a1

import Mathlib
import Definitions.Def_NewsBundling_Negotiated_Setting
import Theorems.Thm_NewsBundling_Unilateral_lemma2_attention

open NewsBundling.Negotiated NewsBundling.Unilateral

/-- Stages 2–4 (consumer, platform, bargaining) of the negotiated SPE. -/
def nbnStages (β Λ : ℝ) (σ : NegProfile) : Prop :=
  (∀ q ∈ Set.Icc (0 : ℝ) 1, ∀ lam ∈ Set.Icc (0 : ℝ) Λ,
      NewsBundling.Unilateral.IsConsumerBR q lam (σ.consumer q lam)) ∧
  (∀ q ∈ Set.Icc (0 : ℝ) 1,
      σ.platform q ∈ Set.Icc (0 : ℝ) Λ ∧
        (∀ lam ∈ Set.Icc (0 : ℝ) Λ,
          NewsBundling.Unilateral.platformRevenue 1 lam (σ.consumer q lam) ≤
            NewsBundling.Unilateral.platformRevenue 1 (σ.platform q) (σ.consumer q (σ.platform q))) ∧
        (∀ lam ∈ Set.Icc (0 : ℝ) Λ,
          NewsBundling.Unilateral.platformRevenue 1 lam (σ.consumer q lam) =
              NewsBundling.Unilateral.platformRevenue 1 (σ.platform q) (σ.consumer q (σ.platform q)) →
            σ.platform q ≤ lam)) ∧
  (∀ q ∈ Set.Icc (0 : ℝ) 1, ∀ F : ℝ,
      nashProduct β q (σ.consumer q (σ.platform q)) F ≤
        nashProduct β q (σ.consumer q (σ.platform q)) (σ.fee q))

lemma nbn_stages {β c Λ : ℝ} {σ : NegProfile} (h : IsNegotiatedSPE β c Λ σ) :
    nbnStages β Λ σ := ⟨h.1, h.2.1, h.2.2.1⟩

lemma nbn_T (q l : ℝ) (hl : l < 1) :
    1 - max ((q - l) / (1 - l)) 0 = if q ≤ l then 1 else (1 - q) / (1 - l) := by
  have hk : 0 < 1 - l := by linarith
  split_ifs with hql
  · rw [max_eq_right (div_nonpos_of_nonpos_of_nonneg (by linarith) hk.le)]; ring
  · push Not at hql
    rw [max_eq_left (div_nonneg (by linarith) hk.le)]
    field_simp; ring

lemma nbn_rev (lam T : ℝ) : platformRevenue 1 lam T = 1 - T := by
  unfold platformRevenue; ring

lemma nbn_cons {β Λ : ℝ} (hΛ : Λ < 1) {σ : NegProfile} (h : nbnStages β Λ σ) :
    ∀ q ∈ Set.Icc (0 : ℝ) 1, ∀ lam ∈ Set.Icc (0 : ℝ) Λ,
      σ.consumer q lam = max ((q - lam) / (1 - lam)) 0 := by
  intro q hq lam hlam
  exact (lemma2_attention q hq lam hlam.1 (by linarith [hlam.2]) _).1 (h.1 q hq lam hlam)

/-- Revenue of the platform (φ₀ = 1) at news share `lam`. -/
lemma nbn_R {β Λ : ℝ} (hΛ : Λ < 1) {σ : NegProfile} (h : nbnStages β Λ σ) :
    ∀ q ∈ Set.Icc (0 : ℝ) 1, ∀ lam ∈ Set.Icc (0 : ℝ) Λ,
      platformRevenue 1 lam (σ.consumer q lam) =
        if q ≤ lam then 1 else (1 - q) / (1 - lam) := by
  intro q hq lam hlam
  rw [nbn_rev, nbn_cons hΛ h q hq lam hlam, nbn_T q lam (by linarith [hlam.2])]

theorem nbn_platform {β Λ : ℝ} (hΛ0 : 0 < Λ) (hΛ : Λ < 1) {σ : NegProfile}
    (h : nbnStages β Λ σ) : ∀ q ∈ Set.Ico (0 : ℝ) 1, σ.platform q = min q Λ := by
  intro q hq
  have hq' : q ∈ Set.Icc (0 : ℝ) 1 := ⟨hq.1, hq.2.le⟩
  obtain ⟨hp, hopt, htie⟩ := h.2.1 q hq'
  have R := nbn_R hΛ h q hq'
  set p := σ.platform q with hpdef
  have hq1 : 0 < 1 - q := by linarith [hq.2]
  rcases le_or_gt q Λ with hqΛ | hqΛ
  · rw [min_eq_left hqΛ]
    have hqm : q ∈ Set.Icc (0 : ℝ) Λ := ⟨hq.1, hqΛ⟩
    have h1 := hopt q hqm
    rw [R q hqm, R p hp, if_pos le_rfl] at h1
    have hqp : q ≤ p := by
      by_contra hlt; push Not at hlt
      rw [if_neg (not_le.2 hlt)] at h1
      have hk : 0 < 1 - p := by linarith
      rw [le_div_iff₀ hk] at h1
      linarith
    have h2 := htie q hqm
    rw [R q hqm, R p hp, if_pos le_rfl, if_pos hqp] at h2
    exact le_antisymm (h2 rfl) hqp
  · rw [min_eq_right hqΛ.le]
    have hΛm : Λ ∈ Set.Icc (0 : ℝ) Λ := ⟨hΛ0.le, le_rfl⟩
    have h1 := hopt Λ hΛm
    rw [R Λ hΛm, R p hp, if_neg (not_le.2 hqΛ), if_neg (by linarith [hp.2])] at h1
    have hk : 0 < 1 - p := by linarith [hp.2]
    have hkΛ : 0 < 1 - Λ := by linarith
    rw [div_le_div_iff₀ hkΛ hk] at h1
    have : Λ ≤ p := by nlinarith
    exact le_antisymm hp.2 this

/-- Direct traffic at the platform's choice. -/
theorem nbn_T1 {β Λ : ℝ} (hΛ0 : 0 < Λ) (hΛ : Λ < 1) {σ : NegProfile}
    (h : nbnStages β Λ σ) : ∀ q ∈ Set.Icc (0 : ℝ) 1,
      σ.consumer q (σ.platform q) = if q ≤ Λ then 0 else (q - Λ) / (1 - Λ) := by
  intro q hq
  have hp := (h.2.1 q hq).1
  rw [nbn_cons hΛ h q hq _ hp]
  have hkΛ : 0 < 1 - Λ := by linarith
  rcases lt_or_eq_of_le hq.2 with hq1 | hq1
  · rw [nbn_platform hΛ0 hΛ h q ⟨hq.1, hq1⟩]
    split_ifs with hqΛ
    · rw [min_eq_left hqΛ, sub_self, zero_div, max_self]
    · push Not at hqΛ
      rw [min_eq_right hqΛ.le, max_eq_left (div_nonneg (by linarith) hkΛ.le)]
  · subst hq1
    have hk : 0 < 1 - σ.platform 1 := by linarith [hp.2]
    rw [if_neg (by linarith), div_self hk.ne', div_self hkΛ.ne', max_eq_left zero_le_one]

lemma nbn_nash (β q T F : ℝ) :
    nashProduct β q T F = nashProduct β q T ((1 + β) * (q - T) / 2) -
      (F - (1 + β) * (q - T) / 2) ^ 2 := by
  unfold nashProduct; ring

theorem nbn_fee {β Λ : ℝ} {σ : NegProfile} (h : nbnStages β Λ σ) :
    ∀ q ∈ Set.Icc (0 : ℝ) 1,
      σ.fee q = (1 + β) * (q - σ.consumer q (σ.platform q)) / 2 := by
  intro q hq
  have h1 := h.2.2 q hq ((1 + β) * (q - σ.consumer q (σ.platform q)) / 2)
  rw [nbn_nash β q _ (σ.fee q)] at h1
  have h2 : (σ.fee q - (1 + β) * (q - σ.consumer q (σ.platform q)) / 2) ^ 2 = 0 :=
    le_antisymm (by linarith) (sq_nonneg _)
  have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h2
  linarith

theorem nbn_fee_low {β Λ : ℝ} (hΛ0 : 0 < Λ) (hΛ : Λ < 1) {σ : NegProfile}
    (h : nbnStages β Λ σ) : ∀ q ∈ Set.Icc (0 : ℝ) Λ, σ.fee q = q * (1 + β) / 2 := by
  intro q hq
  have hq' : q ∈ Set.Icc (0 : ℝ) 1 := ⟨hq.1, by linarith [hq.2]⟩
  rw [nbn_fee h q hq', nbn_T1 hΛ0 hΛ h q hq', if_pos hq.2]; ring

theorem nbn_fee_high {β Λ : ℝ} (hΛ0 : 0 < Λ) (hΛ : Λ < 1) {σ : NegProfile}
    (h : nbnStages β Λ σ) : ∀ q ∈ Set.Ioc Λ 1,
      σ.fee q = (1 - q) * (1 + β) * Λ / (2 * (1 - Λ)) := by
  intro q hq
  have hq' : q ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hq.1], hq.2⟩
  rw [nbn_fee h q hq', nbn_T1 hΛ0 hΛ h q hq', if_neg (not_le.2 hq.1)]
  have hkΛ : (1 - Λ) ≠ 0 := by linarith
  field_simp; ring

/-- The stage-1 profit (7). -/
noncomputable def nbnP (β c Λ q : ℝ) : ℝ :=
  if q ≤ Λ then q * (1 + β) / 2 - c * q ^ 2 / 2
  else (1 - q) * (1 + β) * Λ / (2 * (1 - Λ)) + β * (q - Λ) / (1 - Λ) - c * q ^ 2 / 2

theorem nbn_profit {β c Λ : ℝ} (hΛ0 : 0 < Λ) (hΛ : Λ < 1) {σ : NegProfile}
    (h : nbnStages β Λ σ) : ∀ q ∈ Set.Icc (0 : ℝ) 1,
      negPublisherProfit β c σ q = nbnP β c Λ q := by
  intro q hq
  unfold negPublisherProfit nbnP
  rw [nbn_T1 hΛ0 hΛ h q hq]
  split_ifs with hqΛ
  · rw [nbn_fee_low hΛ0 hΛ h q ⟨hq.1, hqΛ⟩]; ring
  · rw [nbn_fee_high hΛ0 hΛ h q ⟨not_le.1 hqΛ, hq.2⟩]; ring

/-! ### Maximising (7) -/

lemma nbn_low_diff (β c r q : ℝ) (hc : 0 < c) :
    (r * (1 + β) / 2 - c * r ^ 2 / 2) - (q * (1 + β) / 2 - c * q ^ 2 / 2) =
      c / 2 * (r - q) * (2 * q1 β c - r - q) := by
  unfold q1; field_simp; ring

lemma nbn_high_diff (β c Λ r q : ℝ) (hc : 0 < c) (hΛ : Λ < 1) :
    ((1 - r) * (1 + β) * Λ / (2 * (1 - Λ)) + β * (r - Λ) / (1 - Λ) - c * r ^ 2 / 2) -
      ((1 - q) * (1 + β) * Λ / (2 * (1 - Λ)) + β * (q - Λ) / (1 - Λ) - c * q ^ 2 / 2) =
      c / 2 * (r - q) * (2 * q2 β c Λ - r - q) := by
  have : (1 - Λ) ≠ 0 := by linarith
  unfold q2; field_simp; ring

/-- The equilibrium quality of Lemma 5. -/
noncomputable def nbnQ (β c Λ : ℝ) : ℝ :=
  if c < (β * (2 - Λ) - Λ) / (2 * (1 - Λ) * Λ) then q2 β c Λ
  else if c ≤ (1 + β) / (2 * Λ) then Λ
  else q1 β c

theorem nbn_argmax (β c Λ : ℝ) (hN : NegAssumptions β c Λ) :
    nbnQ β c Λ ∈ Set.Icc (0 : ℝ) 1 ∧
      ∀ q ∈ Set.Icc (0 : ℝ) 1, q ≠ nbnQ β c Λ → nbnP β c Λ q < nbnP β c Λ (nbnQ β c Λ) := by
  obtain ⟨⟨hβ1, hβ2⟩, hc, hΛ0, hΛ1⟩ := hN
  have hc0 : 0 < c := by linarith
  have hΛ' : 0 < 1 - Λ := by linarith
  have hq1lt : q1 β c < 1 := by
    unfold q1; rw [div_lt_one (by positivity)]; linarith
  have hq10 : 0 < q1 β c := by unfold q1; positivity
  have hq21 : q2 β c Λ ≤ q1 β c := by
    unfold q1 q2
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos hc0 hΛ0, mul_nonneg (mul_nonneg hc0.le hΛ0.le) (by linarith : (0:ℝ) ≤ 1 - β)]
  have ha : c < (β * (2 - Λ) - Λ) / (2 * (1 - Λ) * Λ) ↔ Λ < q2 β c Λ := by
    unfold q2
    rw [lt_div_iff₀ (by positivity), lt_div_iff₀ (by positivity)]
    constructor <;> intro h <;> nlinarith
  have hb : c ≤ (1 + β) / (2 * Λ) ↔ Λ ≤ q1 β c := by
    unfold q1
    rw [le_div_iff₀ (by positivity), le_div_iff₀ (by positivity)]
    constructor <;> intro h <;> nlinarith
  -- branch values
  have PL : ∀ q, q ≤ Λ → nbnP β c Λ q = q * (1 + β) / 2 - c * q ^ 2 / 2 := by
    intro q hq; unfold nbnP; rw [if_pos hq]
  have PH : ∀ q, Λ < q → nbnP β c Λ q =
      (1 - q) * (1 + β) * Λ / (2 * (1 - Λ)) + β * (q - Λ) / (1 - Λ) - c * q ^ 2 / 2 := by
    intro q hq; unfold nbnP; rw [if_neg (not_le.2 hq)]
  have cont : (1 - Λ) * (1 + β) * Λ / (2 * (1 - Λ)) + β * (Λ - Λ) / (1 - Λ) - c * Λ ^ 2 / 2 =
      nbnP β c Λ Λ := by
    rw [PL Λ le_rfl]; field_simp; ring
  have hc2 : 0 < c / 2 := by linarith
  unfold nbnQ
  split_ifs with h1 h2
  · -- regime q2 > Λ
    rw [ha] at h1
    have hq2le : q2 β c Λ ≤ 1 := by linarith
    refine ⟨⟨by linarith, hq2le⟩, fun q hq hne => ?_⟩
    rw [PH _ h1]
    rcases le_or_gt q Λ with hqΛ | hqΛ
    · rw [PL q hqΛ]
      have e1 := nbn_low_diff β c Λ q hc0
      have e2 := nbn_high_diff β c Λ (q2 β c Λ) Λ hc0 (by linarith)
      have i1 : 0 ≤ c / 2 * (Λ - q) * (2 * q1 β c - Λ - q) :=
        mul_nonneg (mul_nonneg hc2.le (by linarith)) (by linarith)
      have i2 : 0 < c / 2 * (q2 β c Λ - Λ) * (2 * q2 β c Λ - q2 β c Λ - Λ) :=
        mul_pos (mul_pos hc2 (by linarith)) (by linarith)
      have := cont
      rw [PL Λ le_rfl] at this
      linarith
    · rw [PH q hqΛ]
      have e := nbn_high_diff β c Λ (q2 β c Λ) q hc0 (by linarith)
      have : 0 < c / 2 * (q2 β c Λ - q) * (2 * q2 β c Λ - q2 β c Λ - q) := by
        have : 0 < (q2 β c Λ - q) ^ 2 := by
          have : q2 β c Λ - q ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
          positivity
        nlinarith
      linarith
  · -- regime Λ
    push Not at h1
    rw [hb] at h2
    have h1' : q2 β c Λ ≤ Λ := by
      by_contra h; push Not at h; exact absurd (ha.2 h) (not_lt.2 h1)
    refine ⟨⟨hΛ0.le, by linarith⟩, fun q hq hne => ?_⟩
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · rw [PL q hlt.le]
      have e1 := nbn_low_diff β c Λ q hc0
      have i1 : 0 < c / 2 * (Λ - q) * (2 * q1 β c - Λ - q) :=
        mul_pos (mul_pos hc2 (by linarith)) (by linarith)
      rw [PL Λ le_rfl]; linarith
    · rw [PH q hgt]
      have e2 := nbn_high_diff β c Λ Λ q hc0 (by linarith)
      have i2 : 0 < c / 2 * (Λ - q) * (2 * q2 β c Λ - Λ - q) :=
        mul_pos_of_neg_of_neg (mul_neg_of_pos_of_neg hc2 (by linarith)) (by linarith)
      linarith
  · -- regime q1 < Λ
    push Not at h1 h2
    have h2' : q1 β c < Λ := by
      by_contra h; push Not at h; exact absurd (hb.2 h) (not_le.2 h2)
    refine ⟨⟨hq10.le, hq1lt.le⟩, fun q hq hne => ?_⟩
    rw [PL _ h2'.le]
    rcases le_or_gt q Λ with hqΛ | hqΛ
    · rw [PL q hqΛ]
      have e := nbn_low_diff β c (q1 β c) q hc0
      have : 0 < c / 2 * (q1 β c - q) * (2 * q1 β c - q1 β c - q) := by
        have : 0 < (q1 β c - q) ^ 2 := by
          have : q1 β c - q ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
          positivity
        nlinarith
      linarith
    · rw [PH q hqΛ]
      have e1 := nbn_low_diff β c (q1 β c) Λ hc0
      have e2 := nbn_high_diff β c Λ Λ q hc0 (by linarith)
      have i1 : 0 < c / 2 * (q1 β c - Λ) * (2 * q1 β c - q1 β c - Λ) :=
        mul_pos_of_neg_of_neg (mul_neg_of_pos_of_neg hc2 (by linarith)) (by linarith)
      have i2 : 0 ≤ c / 2 * (Λ - q) * (2 * q2 β c Λ - Λ - q) :=
        mul_nonneg_of_nonpos_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hc2.le (by linarith))
          (by linarith)
      have := cont
      rw [PL Λ le_rfl] at this
      linarith

/-! ### Existence -/

noncomputable def nbnProf (β Λ Q : ℝ) : NegProfile :=
  ⟨fun q lam => max ((q - lam) / (1 - lam)) 0,
   fun q => if q < 1 then min q Λ else 0,
   fun q => (1 + β) * (q - max ((q - (if q < 1 then min q Λ else 0)) /
      (1 - (if q < 1 then min q Λ else 0))) 0) / 2,
   Q⟩

theorem nbn_prof_stages (β Λ Q : ℝ) (hΛ0 : 0 < Λ) (hΛ : Λ < 1) :
    nbnStages β Λ (nbnProf β Λ Q) := by
  have hcons : ∀ q ∈ Set.Icc (0 : ℝ) 1, ∀ lam ∈ Set.Icc (0 : ℝ) Λ,
      NewsBundling.Unilateral.IsConsumerBR q lam ((nbnProf β Λ Q).consumer q lam) := by
    intro q hq lam hlam
    exact (lemma2_attention q hq lam hlam.1 (by linarith [hlam.2]) _).2 rfl
  refine ⟨hcons, ?_, ?_⟩
  · intro q hq
    have R : ∀ lam ∈ Set.Icc (0 : ℝ) Λ, platformRevenue 1 lam ((nbnProf β Λ Q).consumer q lam) =
        if q ≤ lam then 1 else (1 - q) / (1 - lam) := by
      intro lam hlam
      rw [nbn_rev]; exact nbn_T q lam (by linarith [hlam.2])
    have hpl : (nbnProf β Λ Q).platform q = if q < 1 then min q Λ else 0 := rfl
    rcases lt_or_eq_of_le hq.2 with hq1 | hq1
    · rw [hpl, if_pos hq1]
      have hk : 0 < 1 - q := by linarith
      rcases le_or_gt q Λ with hqΛ | hqΛ
      · rw [min_eq_left hqΛ]
        have hqm : q ∈ Set.Icc (0 : ℝ) Λ := ⟨hq.1, hqΛ⟩
        refine ⟨hqm, fun lam hlam => ?_, fun lam hlam heq => ?_⟩
        · rw [R lam hlam, R q hqm, if_pos le_rfl]
          split_ifs with hql
          · exact le_rfl
          · push Not at hql
            rw [div_le_one (by linarith)]; linarith
        · rw [R lam hlam, R q hqm, if_pos le_rfl] at heq
          by_contra hlt; push Not at hlt
          rw [if_neg (not_le.2 hlt), div_eq_one_iff_eq (by linarith)] at heq
          linarith
      · rw [min_eq_right hqΛ.le]
        have hΛm : Λ ∈ Set.Icc (0 : ℝ) Λ := ⟨hΛ0.le, le_rfl⟩
        refine ⟨hΛm, fun lam hlam => ?_, fun lam hlam heq => ?_⟩
        · rw [R lam hlam, R Λ hΛm, if_neg (not_le.2 hqΛ), if_neg (by linarith [hlam.2])]
          have hk1 : 0 < 1 - lam := by linarith [hlam.2]
          have hk2 : 0 < 1 - Λ := by linarith
          rw [div_le_div_iff₀ hk1 hk2]
          nlinarith [hlam.2]
        · rw [R lam hlam, R Λ hΛm, if_neg (not_le.2 hqΛ), if_neg (by linarith [hlam.2])] at heq
          have hk1 : 0 < 1 - lam := by linarith [hlam.2]
          have hk2 : 0 < 1 - Λ := by linarith
          rw [div_eq_div_iff hk1.ne' hk2.ne'] at heq
          have : (1 - q) * (lam - Λ) = 0 := by linarith
          rcases mul_eq_zero.1 this with h0 | h0
          · linarith
          · show Λ ≤ lam; linarith
    · subst hq1
      rw [hpl, if_neg (lt_irrefl 1)]
      have h0m : (0 : ℝ) ∈ Set.Icc (0 : ℝ) Λ := ⟨le_rfl, hΛ0.le⟩
      refine ⟨h0m, fun lam hlam => ?_, fun lam hlam _ => hlam.1⟩
      rw [R lam hlam, R 0 h0m, if_neg (show ¬ (1:ℝ) ≤ lam by linarith [hlam.2]),
        if_neg (show ¬ (1:ℝ) ≤ 0 by norm_num)]
      simp
  · intro q hq F
    rw [nbn_nash β q _ F]
    have : (nbnProf β Λ Q).fee q =
        (1 + β) * (q - (nbnProf β Λ Q).consumer q ((nbnProf β Λ Q).platform q)) / 2 := rfl
    rw [this]
    linarith [sq_nonneg (F - (1 + β) * (q - (nbnProf β Λ Q).consumer q ((nbnProf β Λ Q).platform q)) / 2)]

theorem nbn_lemma5 (β c Λ : ℝ) (hN : NegAssumptions β c Λ) :
    (∃ σ, IsNegotiatedSPE β c Λ σ) ∧
      ∀ σ, IsNegotiatedSPE β c Λ σ →
        σ.quality =
          if c < (β * (2 - Λ) - Λ) / (2 * (1 - Λ) * Λ) then q2 β c Λ
          else if c ≤ (1 + β) / (2 * Λ) then Λ
          else q1 β c := by
  have hΛ0 : 0 < Λ := hN.2.2.1
  have hΛ : Λ < 1 := by linarith [hN.2.2.2]
  obtain ⟨hQm, hQmax⟩ := nbn_argmax β c Λ hN
  refine ⟨⟨nbnProf β Λ (nbnQ β c Λ), ?_⟩, ?_⟩
  · have hS := nbn_prof_stages β Λ (nbnQ β c Λ) hΛ0 hΛ
    refine ⟨hS.1, hS.2.1, hS.2.2, hQm, fun q hq => ?_⟩
    show _ ≤ negPublisherProfit β c (nbnProf β Λ (nbnQ β c Λ)) (nbnQ β c Λ)
    rw [nbn_profit hΛ0 hΛ hS q hq, nbn_profit hΛ0 hΛ hS _ hQm]
    by_cases hne : q = nbnQ β c Λ
    · rw [hne]
    · exact (hQmax q hq hne).le
  · intro σ hσ
    have hS := nbn_stages hσ
    by_contra hne
    have h1 := hσ.2.2.2.2 (nbnQ β c Λ) hQm
    rw [nbn_profit hΛ0 hΛ hS _ hQm, nbn_profit hΛ0 hΛ hS _ hσ.2.2.2.1] at h1
    exact absurd h1 (not_le.2 (hQmax _ hσ.2.2.2.1 hne))

theorem solution (β c Λ : ℝ) (hN : NegAssumptions β c Λ) :
    ∀ σ, IsNegotiatedSPE β c Λ σ → ∀ q ∈ Set.Icc (0 : ℝ) Λ, σ.fee q = q * (1 + β) / 2 := by
  intro σ hσ
  exact nbn_fee_low hN.2.2.1 (by linarith [hN.2.2.2]) (nbn_stages hσ)
