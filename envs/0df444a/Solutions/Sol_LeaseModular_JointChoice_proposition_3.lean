-- Prove2me | solution 1 for LeaseModular.JointChoice.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T20:57:22.348986+00:00
-- url     : https://prove2.me/submissions/8337ea55-4e06-4926-9ea8-ede4bde69899

import Mathlib
import Definitions.Def_LeaseModular_JointChoice_Setting

open LeaseModular.JointChoice

namespace LMP3

/-- separable form of all four objectives -/
noncomputable def FL (P : Params) (x t s : ℝ) : ℝ :=
  ((1 - P.γ*P.δ₁)/2 - P.c)*x - (1 - P.γ*P.δ₁)/2*x^2 + ((1 - P.γ*P.δ₂)/2 - P.c)*t
    - (1 - P.γ*P.δ₂)/2*t^2 + P.γ*(P.δ₁+P.δ₂)/2*(s - s^2)

def P1 (P : Params) : Params := ⟨P.δ₁, P.δ₂, 1, P.c⟩

lemma profitLM_eq (P : Params) (y : LMQty) :
    profitLM P y = FL P y.nn (y.nn+y.un) (y.nn+y.un+y.uu) := by
  unfold profitLM rLMnn rLMun rLMuu FL δ₁l δ₂l; ring

lemma profitLI_eq (P : Params) (y : LIQty) :
    profitLI P y = FL P y.n y.n (y.n+y.u) := by
  unfold profitLI rLIn rLIu FL δ₁l δ₂l; ring

lemma profitSM_eq (P : Params) (y : SMQty) :
    profitSM P y = FL (P1 P) y.n1 y.n2 (2*y.n1) := by
  unfold profitSM pSM1 pSM2 FL P1; simp; ring

lemma profitSI_eq (P : Params) (S : ℝ) :
    profitSI P S = FL (P1 P) S S (2*S) := by
  unfold profitSI pSI FL P1; simp; ring

lemma FL_gamma (P : Params) (x t s : ℝ) :
    FL P x t s - FL (P1 P) x t s =
      (P.γ - 1)/2 * ((P.δ₁+P.δ₂)*(s - s^2) - P.δ₁*(x - x^2) - P.δ₂*(t - t^2)) := by
  unfold FL P1; simp; ring

lemma Phi_nonneg (a b x t s : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hx : 0 ≤ x) (hxt : x ≤ t)
    (hts : t ≤ s) (hs : s ≤ 1/2) :
    0 ≤ (a+b)*(s - s^2) - a*(x - x^2) - b*(t - t^2) := by
  have h1 : 0 ≤ (s - x)*(1 - s - x) := mul_nonneg (by linarith) (by linarith)
  have h2 : 0 ≤ (s - t)*(1 - s - t) := mul_nonneg (by linarith) (by linarith)
  nlinarith [mul_nonneg ha h1, mul_nonneg hb h2]

lemma Phi_pos (a b x t s : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hx : 0 ≤ x) (hxt : x ≤ t)
    (hts : t ≤ s) (hs : s ≤ 1/2) (hxs : x < s) :
    0 < (a+b)*(s - s^2) - a*(x - x^2) - b*(t - t^2) := by
  have h1 : 0 < (s - x)*(1 - s - x) := mul_pos (by linarith) (by linarith)
  have h2 : 0 ≤ (s - t)*(1 - s - t) := mul_nonneg (by linarith) (by linarith)
  nlinarith [mul_pos ha h1, mul_nonneg hb h2]

/-- generic expansion of FL around a point -/
lemma FL_diff (P : Params) (x t s y1 y2 y3 : ℝ) :
    FL P x t s - FL P y1 y2 y3 =
      (1 - P.γ*P.δ₁)/2 * (y1 - x)^2 + (1 - P.γ*P.δ₂)/2 * (y2 - t)^2
      + P.γ*(P.δ₁+P.δ₂)/2 * (y3 - s)^2
      - (((1 - P.γ*P.δ₁)/2 - P.c) - (1 - P.γ*P.δ₁)*x) * (y1 - x)
      - (((1 - P.γ*P.δ₂)/2 - P.c) - (1 - P.γ*P.δ₂)*t) * (y2 - t)
      - (P.γ*(P.δ₁+P.δ₂)/2 * (1 - 2*s)) * (y3 - s) := by
  unfold FL; ring

lemma P1_standing (P : Params) (hP : Standing P) : Standing (P1 P) := by
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩ := hP
  refine ⟨h1,h2,h3, by norm_num [P1], by simp [P1]; linarith, h6, h7, by simp [P1]; linarith⟩


def LMgood (P : Params) (x t s : ℝ) : Prop :=
  (0 ≤ x ∧ x ≤ t ∧ t ≤ s ∧ s ≤ 2*x) ∧ 0 < x ∧ x < s ∧ s ≤ 1/2 ∧
    ∀ y1 y2 y3 : ℝ, 0 ≤ y1 → y1 ≤ y2 → y2 ≤ y3 → y3 ≤ 2*y1 → FL P y1 y2 y3 ≤ FL P x t s

lemma LM_case2 (d1 d2 g c : ℝ) (hP : Standing ⟨d1,d2,g,c⟩) (h1 : (1-g*d1)/4 ≤ c)
    (h2 : c ≤ CLM2 d1 d2 g) :
    ∃ x t s, LMgood ⟨d1,d2,g,c⟩ x t s ∧ 2*x ≤ 1/2 ∧
      (c < CLM2 d1 d2 g → ∀ y1 y3 : ℝ, 0 ≤ y1 → y1 ≤ y3 → y3 ≤ 2*y1 →
        FL ⟨d1,d2,g,c⟩ y1 y1 y3 < FL ⟨d1,d2,g,c⟩ x t s) := by
  obtain ⟨hd2, hd21, hd1, hg, hgd1, hc, hcs, hcl⟩ := hP
  simp only at *
  have hgd2 : g*d2 < g*d1 := mul_lt_mul_of_pos_left hd21 hg
  have hB : 0 < g*(d1+d2) := mul_pos hg (by linarith)
  have hp : 0 < 1 - g*d1 := by linarith
  have hsplit : g*(d1+d2) = g*d1 + g*d2 := by ring
  have hgd2p : 0 < g*d2 := mul_pos hg hd2
  have hK : 0 < 3*d1+5*d2 := by linarith
  have hD : 0 < 2*((1-g*d1) + 4*g*(d1+d2)) := by linarith
  have hDne := hD.ne'
  obtain ⟨x, hx⟩ : ∃ x, 2*((1-g*d1) + 4*g*(d1+d2))*x = (1-g*d1) - 2*c + 2*g*(d1+d2) :=
    ⟨((1-g*d1) - 2*c + 2*g*(d1+d2)) / (2*((1-g*d1) + 4*g*(d1+d2))), mul_div_cancel₀ _ hDne⟩
  have hq : 0 < 1 - g*d2 := by linarith
  have hqne := hq.ne'
  obtain ⟨t, ht⟩ : ∃ t, (1-g*d2)*t = (1-g*d2)/2 - c :=
    ⟨((1-g*d2)/2 - c)/(1-g*d2), mul_div_cancel₀ _ hqne⟩
  have hx0 : 0 < x := by
    by_contra hh; push Not at hh
    have : 2*((1-g*d1) + 4*g*(d1+d2))*x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hD.le hh
    linarith
  have hx4 : x ≤ 1/4 := by
    by_contra hh; push Not at hh
    have : 2*((1-g*d1) + 4*g*(d1+d2))*(1/4) < 2*((1-g*d1) + 4*g*(d1+d2))*x :=
      mul_lt_mul_of_pos_left hh hD
    linarith
  have hpos : 0 < (1-g*d2)*(2*((1-g*d1) + 4*g*(d1+d2))) := mul_pos hq hD
  have hxt : (1-g*d2)*(2*((1-g*d1) + 4*g*(d1+d2))) * (t - x) =
      g*(c*(-2)*(3*d1+5*d2) + 2*(1-g*d2)*(d1+d2)) := by
    linear_combination (2*((1-g*d1) + 4*g*(d1+d2)))*ht - (1-g*d2)*hx
  have h2' : c*(3*d1+5*d2) ≤ (1-g*d2)*(d1+d2) := by
    unfold CLM2 at h2; rwa [le_div_iff₀ hK] at h2
  have hxt' : x ≤ t := by
    by_contra hh; push Not at hh
    have : (1-g*d2)*(2*((1-g*d1) + 4*g*(d1+d2))) * (t - x) < 0 :=
      mul_neg_of_pos_of_neg hpos (by linarith)
    rw [hxt] at this
    have : 0 ≤ g*(c*(-2)*(3*d1+5*d2) + 2*(1-g*d2)*(d1+d2)) := mul_nonneg hg.le (by linarith)
    linarith
  have ht2 : t ≤ 2*x := by
    have E : (1-g*d2)*(2*((1-g*d1) + 4*g*(d1+d2))) * (2*x - t) =
        (1-g*d2)*(1-g*d1) + 2*c*(-1 + 3*g*d1 + 6*g*d2) := by
      linear_combination (1-g*d2)*2*hx - (2*((1-g*d1) + 4*g*(d1+d2)))*ht
    have e1 : 0 < (1-g*d2)*(1-g*d1) + 2*c*(-1 + 3*g*d1 + 6*g*d2) := by
      rcases le_or_gt 0 (-1 + 3*g*d1 + 6*g*d2) with hk | hk
      · have := mul_nonneg (by linarith : (0:ℝ) ≤ 2*c) hk
        nlinarith [mul_pos hq hp]
      · have := mul_nonneg (by linarith : (0:ℝ) ≤ (1-g*d2) - 2*c) (by linarith : (0:ℝ) ≤ -(-1 + 3*g*d1 + 6*g*d2))
        have h3 : 0 < (1-g*d2)*(2*g*d1 + 6*g*d2) := mul_pos hq (by nlinarith)
        nlinarith
    by_contra hh; push Not at hh
    have : (1-g*d2)*(2*((1-g*d1) + 4*g*(d1+d2))) * (2*x - t) < 0 :=
      mul_neg_of_pos_of_neg hpos (by linarith)
    linarith
  refine ⟨x, t, 2*x, ⟨⟨hx0.le, hxt', ht2, le_refl _⟩, hx0, by linarith, by linarith, ?_⟩, by linarith, ?_⟩
  · intro y1 y2 y3 hy1 hy12 hy23 hy31
    have key := FL_diff ⟨d1,d2,g,c⟩ x t (2*x) y1 y2 y3
    simp only at key
    have e : FL ⟨d1,d2,g,c⟩ x t (2*x) - FL ⟨d1,d2,g,c⟩ y1 y2 y3 =
        (1 - g*d1)/2 * (y1 - x)^2 + (1 - g*d2)/2 * (y2 - t)^2 + g*(d1+d2)/2 * (y3 - 2*x)^2
        + g*(d1+d2)/2*(1 - 4*x)*(2*y1 - y3) := by
      linear_combination key + (y1 - x)/2*hx + (y2 - t)*ht
    have : 0 ≤ (1 - g*d1)/2 * (y1 - x)^2 + (1 - g*d2)/2 * (y2 - t)^2 + g*(d1+d2)/2 * (y3 - 2*x)^2
        + g*(d1+d2)/2*(1 - 4*x)*(2*y1 - y3) := by
      have a1 := mul_nonneg (by linarith : (0:ℝ) ≤ (1 - g*d1)/2) (sq_nonneg (y1 - x))
      have a2 := mul_nonneg (by linarith : (0:ℝ) ≤ (1 - g*d2)/2) (sq_nonneg (y2 - t))
      have a3 := mul_nonneg (by linarith : (0:ℝ) ≤ g*(d1+d2)/2) (sq_nonneg (y3 - 2*x))
      have a4 := mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ g*(d1+d2)/2) (by linarith : (0:ℝ) ≤ 1 - 4*x)) (by linarith : (0:ℝ) ≤ 2*y1 - y3)
      linarith only [a1, a2, a3, a4]
    linarith only [e, this]
  · intro hlt y1 y3 hy1 hy13 hy31
    have hxt2 : x < t := by
      have h2'' : c*(3*d1+5*d2) < (1-g*d2)*(d1+d2) := by
        unfold CLM2 at hlt; rwa [lt_div_iff₀ hK] at hlt
      by_contra hh; push Not at hh
      have : (1-g*d2)*(2*((1-g*d1) + 4*g*(d1+d2))) * (t - x) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hpos.le (by linarith)
      rw [hxt] at this
      have : 0 < g*(c*(-2)*(3*d1+5*d2) + 2*(1-g*d2)*(d1+d2)) := mul_pos hg (by linarith)
      linarith
    have key := FL_diff ⟨d1,d2,g,c⟩ x t (2*x) y1 y1 y3
    simp only at key
    have e : FL ⟨d1,d2,g,c⟩ x t (2*x) - FL ⟨d1,d2,g,c⟩ y1 y1 y3 =
        (1 - g*d1)/2 * (y1 - x)^2 + (1 - g*d2)/2 * (y1 - t)^2 + g*(d1+d2)/2 * (y3 - 2*x)^2
        + g*(d1+d2)/2*(1 - 4*x)*(2*y1 - y3) := by
      linear_combination key + (y1 - x)/2*hx + (y1 - t)*ht
    have hp2 : (0:ℝ) < (1 - g*d1)/2 := by linarith
    have hq2 : (0:ℝ) < (1 - g*d2)/2 := by linarith
    have hsq : 0 < (1 - g*d1)/2 * (y1 - x)^2 + (1 - g*d2)/2 * (y1 - t)^2 := by
      have b1 := mul_nonneg hp2.le (sq_nonneg (y1 - x))
      have b2 := mul_nonneg hq2.le (sq_nonneg (y1 - t))
      by_cases h : y1 = x
      · have hne : y1 - t ≠ 0 := by rw [h]; exact sub_ne_zero.mpr hxt2.ne
        have := mul_pos hq2 (by positivity : (0:ℝ) < (y1 - t)^2)
        linarith only [this, b1]
      · have hne : y1 - x ≠ 0 := sub_ne_zero.mpr h
        have := mul_pos hp2 (by positivity : (0:ℝ) < (y1 - x)^2)
        linarith only [this, b2]
    have a3 := mul_nonneg (by linarith : (0:ℝ) ≤ g*(d1+d2)/2) (sq_nonneg (y3 - 2*x))
    have a4 := mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ g*(d1+d2)/2) (by linarith : (0:ℝ) ≤ 1 - 4*x)) (by linarith : (0:ℝ) ≤ 2*y1 - y3)
    linarith only [e, hsq, a3, a4]


lemma std_facts (d1 d2 g c : ℝ) (hP : Standing ⟨d1,d2,g,c⟩) :
    0 < d2 ∧ d2 < d1 ∧ d1 < 1 ∧ 0 < g ∧ g*d1 < 1 ∧ 0 < c ∧ c < (1-d2)/2 ∧ c < (1-g*d2)/2 ∧
    g*d2 < g*d1 ∧ 0 < g*d2 ∧ 0 < g*(d1+d2) ∧ 0 < 1 - g*d1 ∧ 0 < 1 - g*d2 ∧ 0 < 3*d1+5*d2 := by
  obtain ⟨hd2, hd21, hd1, hg, hgd1, hc, hcs, hcl⟩ := hP
  simp only at *
  have hgd2 : g*d2 < g*d1 := mul_lt_mul_of_pos_left hd21 hg
  have hgd2p : 0 < g*d2 := mul_pos hg hd2
  refine ⟨hd2, hd21, hd1, hg, hgd1, hc, hcs, hcl, hgd2, hgd2p, mul_pos hg (by linarith),
    by linarith, by linarith, by linarith⟩

lemma LM_case1 (d1 d2 g c : ℝ) (hP : Standing ⟨d1,d2,g,c⟩) (h1 : c ≤ (1-g*d1)/4) :
    ∃ x t s, LMgood ⟨d1,d2,g,c⟩ x t s ∧ ((1-g*d1)/4 ≤ c → 2*x ≤ 1/2) ∧
      (∀ y1 y3 : ℝ, 0 ≤ y1 → y1 ≤ y3 → y3 ≤ 2*y1 →
        FL ⟨d1,d2,g,c⟩ y1 y1 y3 < FL ⟨d1,d2,g,c⟩ x t s) := by
  obtain ⟨hd2, hd21, hd1, hg, hgd1, hc, hcs, hcl, hgd2, hgd2p, hB, hp, hq, hK⟩ :=
    std_facts d1 d2 g c hP
  obtain ⟨x, hx⟩ : ∃ x, (1-g*d1)*x = (1-g*d1)/2 - c :=
    ⟨((1-g*d1)/2 - c)/(1-g*d1), mul_div_cancel₀ _ hp.ne'⟩
  obtain ⟨t, ht⟩ : ∃ t, (1-g*d2)*t = (1-g*d2)/2 - c :=
    ⟨((1-g*d2)/2 - c)/(1-g*d2), mul_div_cancel₀ _ hq.ne'⟩
  have hx4 : 1/4 ≤ x := by
    by_contra hh; push Not at hh
    have := mul_lt_mul_of_pos_left hh hp; linarith
  have hxt : x < t := by
    by_contra hh; push Not at hh
    have e : (1-g*d1)*(1-g*d2)*(t - x) = c*(g*d1 - g*d2) := by
      linear_combination (1-g*d1)*ht - (1-g*d2)*hx
    have : (1-g*d1)*(1-g*d2)*(t - x) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (mul_pos hp hq).le (by linarith)
    have : 0 < c*(g*d1 - g*d2) := mul_pos hc (by linarith)
    linarith
  have ht2 : t < 1/2 := by
    by_contra hh; push Not at hh
    have := mul_le_mul_of_nonneg_left hh hq.le; linarith
  have hp2 : (0:ℝ) < (1 - g*d1)/2 := by linarith
  have hq2 : (0:ℝ) < (1 - g*d2)/2 := by linarith
  have hB2 : (0:ℝ) ≤ g*(d1+d2)/2 := by linarith
  refine ⟨x, t, 1/2, ⟨⟨by linarith, hxt.le, ht2.le, by linarith⟩, by linarith, by linarith,
    le_refl _, ?_⟩, ?_, ?_⟩
  · intro y1 y2 y3 _ _ _ _
    have key := FL_diff ⟨d1,d2,g,c⟩ x t (1/2) y1 y2 y3
    simp only at key
    have e : FL ⟨d1,d2,g,c⟩ x t (1/2) - FL ⟨d1,d2,g,c⟩ y1 y2 y3 =
        (1 - g*d1)/2 * (y1 - x)^2 + (1 - g*d2)/2 * (y2 - t)^2 + g*(d1+d2)/2 * (y3 - 1/2)^2 := by
      linear_combination key + (y1 - x)*hx + (y2 - t)*ht
    have a1 := mul_nonneg hp2.le (sq_nonneg (y1 - x))
    have a2 := mul_nonneg hq2.le (sq_nonneg (y2 - t))
    have a3 := mul_nonneg hB2 (sq_nonneg (y3 - 1/2))
    linarith only [e, a1, a2, a3]
  · intro hc4
    have : (1-g*d1)*x = (1-g*d1)*(1/4) := by linarith
    have := mul_left_cancel₀ hp.ne' this
    linarith
  · intro y1 y3 _ _ _
    have key := FL_diff ⟨d1,d2,g,c⟩ x t (1/2) y1 y1 y3
    simp only at key
    have e : FL ⟨d1,d2,g,c⟩ x t (1/2) - FL ⟨d1,d2,g,c⟩ y1 y1 y3 =
        (1 - g*d1)/2 * (y1 - x)^2 + (1 - g*d2)/2 * (y1 - t)^2 + g*(d1+d2)/2 * (y3 - 1/2)^2 := by
      linear_combination key + (y1 - x)*hx + (y1 - t)*ht
    have hsq : 0 < (1 - g*d1)/2 * (y1 - x)^2 + (1 - g*d2)/2 * (y1 - t)^2 := by
      have b1 := mul_nonneg hp2.le (sq_nonneg (y1 - x))
      have b2 := mul_nonneg hq2.le (sq_nonneg (y1 - t))
      by_cases h : y1 = x
      · have hne : y1 - t ≠ 0 := by rw [h]; exact sub_ne_zero.mpr hxt.ne
        have := mul_pos hq2 (by positivity : (0:ℝ) < (y1 - t)^2)
        linarith only [this, b1]
      · have hne : y1 - x ≠ 0 := sub_ne_zero.mpr h
        have := mul_pos hp2 (by positivity : (0:ℝ) < (y1 - x)^2)
        linarith only [this, b2]
    have a3 := mul_nonneg hB2 (sq_nonneg (y3 - 1/2))
    linarith only [e, hsq, a3]

lemma CLI_lt_CLM2 (d1 d2 g : ℝ) (hd2 : 0 < d2) (hd21 : d2 < d1) (hg : 0 < g) :
    CLI d1 d2 g < CLM2 d1 d2 g := by
  unfold CLI CLM2
  have hK : 0 < 3*d1+5*d2 := by linarith
  rw [div_lt_div_iff₀ (by norm_num) hK]
  have : 0 < g*(d1+d2)*(d1-d2) := mul_pos (mul_pos hg (by linarith)) (by linarith)
  nlinarith

lemma LM_case3 (d1 d2 g c : ℝ) (hP : Standing ⟨d1,d2,g,c⟩) (h1 : CLM2 d1 d2 g ≤ c) :
    ∃ x, LMgood ⟨d1,d2,g,c⟩ x x (2*x) ∧ 2*x ≤ 1/2 := by
  have hCLI := CLI_lt_CLM2 d1 d2 g hP.δ₂_pos hP.δ₂_lt_δ₁ hP.γ_pos
  obtain ⟨hd2, hd21, hd1, hg, hgd1, hc, hcs, hcl, hgd2, hgd2p, hB, hp, hq, hK⟩ :=
    std_facts d1 d2 g c hP
  have hD : 0 < 2 + 3*(g*(d1+d2)) := by linarith
  obtain ⟨x, hx⟩ : ∃ x, (2 + 3*(g*(d1+d2)))*x = 1 + g*(d1+d2)/2 - 2*c :=
    ⟨(1 + g*(d1+d2)/2 - 2*c)/(2 + 3*(g*(d1+d2))), mul_div_cancel₀ _ hD.ne'⟩
  have h1' : (1-g*d2)*(d1+d2) ≤ c*(3*d1+5*d2) := by
    unfold CLM2 at h1; rwa [div_le_iff₀ hK] at h1
  have hcli : (2 - g*(d1+d2))/8 ≤ c := by unfold CLI at hCLI; linarith
  have hx0 : 0 < x := by
    by_contra hh; push Not at hh
    have := mul_nonpos_of_nonneg_of_nonpos hD.le hh; linarith
  have hx4 : x ≤ 1/4 := by
    by_contra hh; push Not at hh
    have := mul_lt_mul_of_pos_left hh hD; linarith
  have hgt : 0 ≤ (1-g*d2)*x - ((1-g*d2)/2 - c) := by
    have e : (2 + 3*(g*(d1+d2)))*((1-g*d2)*x - ((1-g*d2)/2 - c)) =
        g*(c*(3*d1+5*d2) - (1-g*d2)*(d1+d2)) := by
      linear_combination (1-g*d2)*hx
    have : 0 ≤ g*(c*(3*d1+5*d2) - (1-g*d2)*(d1+d2)) := mul_nonneg hg.le (by linarith)
    by_contra hh; push Not at hh
    have := mul_neg_of_pos_of_neg hD hh; linarith
  have hp2 : (0:ℝ) < (1 - g*d1)/2 := by linarith
  have hq2 : (0:ℝ) < (1 - g*d2)/2 := by linarith
  have hB2 : (0:ℝ) ≤ g*(d1+d2)/2 := by linarith
  refine ⟨x, ⟨⟨hx0.le, le_refl _, by linarith, le_refl _⟩, hx0, by linarith, by linarith, ?_⟩,
    by linarith⟩
  intro y1 y2 y3 _ hy12 _ hy31
  have key := FL_diff ⟨d1,d2,g,c⟩ x x (2*x) y1 y2 y3
  simp only at key
  have e : FL ⟨d1,d2,g,c⟩ x x (2*x) - FL ⟨d1,d2,g,c⟩ y1 y2 y3 =
      (1 - g*d1)/2 * (y1 - x)^2 + (1 - g*d2)/2 * (y2 - x)^2 + g*(d1+d2)/2 * (y3 - 2*x)^2
      + ((1-g*d2)*x - ((1-g*d2)/2 - c))*(y2 - y1) + g*(d1+d2)/2*(1 - 4*x)*(2*y1 - y3) := by
    linear_combination key + (y1 - x)*hx
  have a1 := mul_nonneg hp2.le (sq_nonneg (y1 - x))
  have a2 := mul_nonneg hq2.le (sq_nonneg (y2 - x))
  have a3 := mul_nonneg hB2 (sq_nonneg (y3 - 2*x))
  have a4 := mul_nonneg hgt (by linarith : (0:ℝ) ≤ y2 - y1)
  have a5 := mul_nonneg (mul_nonneg hB2 (by linarith : (0:ℝ) ≤ 1 - 4*x)) (by linarith : (0:ℝ) ≤ 2*y1 - y3)
  linarith only [e, a1, a2, a3, a4, a5]


lemma LM_opt (P : Params) (hP : Standing P) :
    ∃ x t s, LMgood P x t s ∧ (CLM1 P.δ₁ P.γ ≤ P.c → 2*x ≤ 1/2) ∧
      (P.c < CLM2 P.δ₁ P.δ₂ P.γ → ∀ y1 y3 : ℝ, 0 ≤ y1 → y1 ≤ y3 → y3 ≤ 2*y1 →
        FL P y1 y1 y3 < FL P x t s) ∧
      (CLM2 P.δ₁ P.δ₂ P.γ ≤ P.c → x = t) := by
  obtain ⟨d1, d2, g, c⟩ := P
  have hCLI := CLI_lt_CLM2 d1 d2 g hP.δ₂_pos hP.δ₂_lt_δ₁ hP.γ_pos
  obtain ⟨hd2, hd21, hd1, hg, hgd1, hc, hcs, hcl, hgd2, hgd2p, hB, hp, hq, hK⟩ :=
    std_facts d1 d2 g c hP
  have h14 : (1 - g*d1)/4 < CLI d1 d2 g := by unfold CLI; linarith
  simp only [CLM1]
  rcases le_or_gt c ((1-g*d1)/4) with h | h
  · obtain ⟨x, t, s, hg1, hg2, hg3⟩ := LM_case1 d1 d2 g c hP h
    exact ⟨x, t, s, hg1, hg2, fun _ => hg3, fun h' => absurd h' (by linarith)⟩
  · rcases lt_or_ge c (CLM2 d1 d2 g) with h' | h'
    · obtain ⟨x, t, s, hg1, hg2, hg3⟩ := LM_case2 d1 d2 g c hP h.le h'.le
      exact ⟨x, t, s, hg1, fun _ => hg2, hg3, fun h'' => absurd h'' (by linarith)⟩
    · obtain ⟨x, hg1, hg2⟩ := LM_case3 d1 d2 g c hP h'
      refine ⟨x, x, 2*x, hg1, fun _ => hg2, fun h'' => absurd h'' (by linarith), fun _ => rfl⟩

def LIgood (P : Params) (n s : ℝ) : Prop :=
  (0 ≤ n ∧ n ≤ s ∧ s ≤ 2*n) ∧ 0 < n ∧ n < s ∧ s ≤ 1/2 ∧
    ∀ y1 y3 : ℝ, 0 ≤ y1 → y1 ≤ y3 → y3 ≤ 2*y1 → FL P y1 y1 y3 ≤ FL P n n s

lemma LI_opt (P : Params) (hP : Standing P) :
    ∃ n s, LIgood P n s ∧ (CLI P.δ₁ P.δ₂ P.γ ≤ P.c → 2*n ≤ 1/2) := by
  obtain ⟨d1, d2, g, c⟩ := P
  obtain ⟨hd2, hd21, hd1, hg, hgd1, hc, hcs, hcl, hgd2, hgd2p, hB, hp, hq, hK⟩ :=
    std_facts d1 d2 g c hP
  have hp2 : (0:ℝ) < (1 - g*d1)/2 := by linarith
  have hq2 : (0:ℝ) < (1 - g*d2)/2 := by linarith
  have hB2 : (0:ℝ) ≤ g*(d1+d2)/2 := by linarith
  simp only [CLI]
  rcases le_or_gt c ((2 - g*(d1+d2))/8) with h | h
  · have hD : 0 < 2 - g*(d1+d2) := by linarith
    obtain ⟨n, hn⟩ : ∃ n, (2 - g*(d1+d2))*n = (2 - g*(d1+d2))/2 - 2*c :=
      ⟨((2 - g*(d1+d2))/2 - 2*c)/(2 - g*(d1+d2)), mul_div_cancel₀ _ hD.ne'⟩
    have hn4 : 1/4 ≤ n := by
      by_contra hh; push Not at hh
      have := mul_lt_mul_of_pos_left hh hD; linarith
    have hn2 : n < 1/2 := by
      by_contra hh; push Not at hh
      have := mul_le_mul_of_nonneg_left hh hD.le; linarith
    refine ⟨n, 1/2, ⟨⟨by linarith, by linarith, by linarith⟩, by linarith, hn2, le_refl _, ?_⟩, ?_⟩
    · intro y1 y3 _ _ _
      have key := FL_diff ⟨d1,d2,g,c⟩ n n (1/2) y1 y1 y3
      simp only at key
      have e : FL ⟨d1,d2,g,c⟩ n n (1/2) - FL ⟨d1,d2,g,c⟩ y1 y1 y3 =
          (1 - g*d1)/2 * (y1 - n)^2 + (1 - g*d2)/2 * (y1 - n)^2 + g*(d1+d2)/2 * (y3 - 1/2)^2 := by
        linear_combination key + (y1 - n)*hn
      have a1 := mul_nonneg hp2.le (sq_nonneg (y1 - n))
      have a2 := mul_nonneg hq2.le (sq_nonneg (y1 - n))
      have a3 := mul_nonneg hB2 (sq_nonneg (y3 - 1/2))
      linarith only [e, a1, a2, a3]
    · intro hc4
      have : (2 - g*(d1+d2))*n = (2 - g*(d1+d2))*(1/4) := by linarith
      have := mul_left_cancel₀ hD.ne' this
      linarith
  · have hD : 0 < 2 + 3*(g*(d1+d2)) := by linarith
    obtain ⟨n, hn⟩ : ∃ n, (2 + 3*(g*(d1+d2)))*n = 1 + g*(d1+d2)/2 - 2*c :=
      ⟨(1 + g*(d1+d2)/2 - 2*c)/(2 + 3*(g*(d1+d2))), mul_div_cancel₀ _ hD.ne'⟩
    have hn0 : 0 < n := by
      by_contra hh; push Not at hh
      have := mul_nonpos_of_nonneg_of_nonpos hD.le hh; linarith
    have hn4 : n ≤ 1/4 := by
      by_contra hh; push Not at hh
      have := mul_lt_mul_of_pos_left hh hD; linarith
    refine ⟨n, 2*n, ⟨⟨hn0.le, by linarith, le_refl _⟩, hn0, by linarith, by linarith, ?_⟩,
      fun _ => by linarith⟩
    intro y1 y3 _ _ hy31
    have key := FL_diff ⟨d1,d2,g,c⟩ n n (2*n) y1 y1 y3
    simp only at key
    have e : FL ⟨d1,d2,g,c⟩ n n (2*n) - FL ⟨d1,d2,g,c⟩ y1 y1 y3 =
        (1 - g*d1)/2 * (y1 - n)^2 + (1 - g*d2)/2 * (y1 - n)^2 + g*(d1+d2)/2 * (y3 - 2*n)^2
        + g*(d1+d2)/2*(1 - 4*n)*(2*y1 - y3) := by
      linear_combination key + (y1 - n)*hn
    have a1 := mul_nonneg hp2.le (sq_nonneg (y1 - n))
    have a2 := mul_nonneg hq2.le (sq_nonneg (y1 - n))
    have a3 := mul_nonneg hB2 (sq_nonneg (y3 - 2*n))
    have a5 := mul_nonneg (mul_nonneg hB2 (by linarith : (0:ℝ) ≤ 1 - 4*n)) (by linarith : (0:ℝ) ≤ 2*y1 - y3)
    linarith only [e, a1, a2, a3, a5]

lemma SM_opt (P : Params) (hP : Standing P) :
    ∃ x t, (0 ≤ x ∧ x ≤ t ∧ t ≤ 2*x) ∧
      (∀ y1 y2 : ℝ, 0 ≤ y1 → y1 ≤ y2 → FL (P1 P) y1 y2 (2*y1) ≤ FL (P1 P) x t (2*x)) ∧
      (CSM P.δ₁ P.δ₂ ≤ P.c → x = t) := by
  obtain ⟨d1, d2, g, c⟩ := P
  obtain ⟨hd2, hd21, hd1, hg, hgd1, hc, hcs, hcl, hgd2, hgd2p, hB, hp, hq, hK⟩ :=
    std_facts d1 d2 g c hP
  simp only [P1]
  have hr : 0 < 1 - d2 := by linarith
  have hs1 : 0 < 1 - d1 := by linarith
  rcases lt_or_ge c (CSM d1 d2) with h | h
  · have h' : c*(3*d1+5*d2) < (1-d2)*(d1+d2) := by
      unfold CSM at h; rwa [lt_div_iff₀ hK] at h
    have hA : 0 < 1 - d1 + 4*(d1+d2) := by linarith
    obtain ⟨x, hx⟩ : ∃ x, (1 - d1 + 4*(d1+d2))*x = (1-d1)/2 + (d1+d2) - c :=
      ⟨((1-d1)/2 + (d1+d2) - c)/(1 - d1 + 4*(d1+d2)), mul_div_cancel₀ _ hA.ne'⟩
    obtain ⟨t, ht⟩ : ∃ t, (1 - d2)*t = (1-d2)/2 - c :=
      ⟨((1-d2)/2 - c)/(1 - d2), mul_div_cancel₀ _ hr.ne'⟩
    have hx0 : 0 < x := by
      by_contra hh; push Not at hh
      have := mul_nonpos_of_nonneg_of_nonpos hA.le hh; linarith
    have hpos := mul_pos hA hr
    have hxt : x ≤ t := by
      have e : (1 - d1 + 4*(d1+d2))*(1-d2)*(t - x) = (1-d2)*(d1+d2) - c*(3*d1+5*d2) := by
        linear_combination (1 - d1 + 4*(d1+d2))*ht - (1-d2)*hx
      by_contra hh; push Not at hh
      have := mul_neg_of_pos_of_neg hpos (by linarith : t - x < 0); linarith
    have ht2 : t ≤ 2*x := by
      have e : (1 - d1 + 4*(d1+d2))*(1-d2)*(2*x - t) =
          (1-d2)*(1-d1)/2 + c*(1 - d1 + 4*(d1+d2) - 2*(1-d2)) := by
        linear_combination 2*(1-d2)*hx - (1 - d1 + 4*(d1+d2))*ht
      have e2 : 0 < (1-d2)*(1-d1)/2 + c*(1 - d1 + 4*(d1+d2) - 2*(1-d2)) := by
        rcases le_or_gt 0 (1 - d1 + 4*(d1+d2) - 2*(1-d2)) with hk | hk
        · have := mul_nonneg hc.le hk
          have := mul_pos hr hs1; linarith
        · have := mul_nonneg (by linarith : (0:ℝ) ≤ (1-d2) - 2*c) (by linarith : (0:ℝ) ≤ -(1 - d1 + 4*(d1+d2) - 2*(1-d2)))
          have := mul_pos hr (by linarith : (0:ℝ) < 2*d1 + 6*d2)
          nlinarith
      by_contra hh; push Not at hh
      have := mul_neg_of_pos_of_neg hpos (by linarith : 2*x - t < 0); linarith
    refine ⟨x, t, ⟨hx0.le, hxt, ht2⟩, ?_, fun h'' => absurd h'' (by linarith)⟩
    intro y1 y2 _ _
    have key := FL_diff ⟨d1,d2,1,c⟩ x t (2*x) y1 y2 (2*y1)
    simp only at key
    have e : FL ⟨d1,d2,1,c⟩ x t (2*x) - FL ⟨d1,d2,1,c⟩ y1 y2 (2*y1) =
        (1 - d1)/2 * (y1 - x)^2 + (1 - d2)/2 * (y2 - t)^2 + (d1+d2)/2 * (2*y1 - 2*x)^2 := by
      linear_combination key + (y1 - x)*hx + (y2 - t)*ht
    have a1 := mul_nonneg (by linarith : (0:ℝ) ≤ (1 - d1)/2) (sq_nonneg (y1 - x))
    have a2 := mul_nonneg (by linarith : (0:ℝ) ≤ (1 - d2)/2) (sq_nonneg (y2 - t))
    have a3 := mul_nonneg (by linarith : (0:ℝ) ≤ (d1+d2)/2) (sq_nonneg (2*y1 - 2*x))
    linarith only [e, a1, a2, a3]
  · have h' : (1-d2)*(d1+d2) ≤ c*(3*d1+5*d2) := by
      unfold CSM at h; rwa [div_le_iff₀ hK] at h
    have hD : 0 < 2 + 3*(d1+d2) := by linarith
    obtain ⟨S, hS⟩ : ∃ S, (2 + 3*(d1+d2))*S = 1 + (d1+d2)/2 - 2*c :=
      ⟨(1 + (d1+d2)/2 - 2*c)/(2 + 3*(d1+d2)), mul_div_cancel₀ _ hD.ne'⟩
    have hS0 : 0 < S := by
      by_contra hh; push Not at hh
      have := mul_nonpos_of_nonneg_of_nonpos hD.le hh; linarith
    have hgt : 0 ≤ (1-d2)*S - ((1-d2)/2 - c) := by
      have e : (2 + 3*(d1+d2))*((1-d2)*S - ((1-d2)/2 - c)) =
          c*(3*d1+5*d2) - (1-d2)*(d1+d2) := by
        linear_combination (1-d2)*hS
      by_contra hh; push Not at hh
      have := mul_neg_of_pos_of_neg hD hh; linarith
    refine ⟨S, S, ⟨hS0.le, le_refl _, by linarith⟩, ?_, fun _ => rfl⟩
    intro y1 y2 _ hy12
    have key := FL_diff ⟨d1,d2,1,c⟩ S S (2*S) y1 y2 (2*y1)
    simp only at key
    have e : FL ⟨d1,d2,1,c⟩ S S (2*S) - FL ⟨d1,d2,1,c⟩ y1 y2 (2*y1) =
        (1 - d1)/2 * (y1 - S)^2 + (1 - d2)/2 * (y2 - S)^2 + (d1+d2)/2 * (2*y1 - 2*S)^2
        + ((1-d2)*S - ((1-d2)/2 - c))*(y2 - y1) := by
      linear_combination key + (y1 - S)*hS
    have a1 := mul_nonneg (by linarith : (0:ℝ) ≤ (1 - d1)/2) (sq_nonneg (y1 - S))
    have a2 := mul_nonneg (by linarith : (0:ℝ) ≤ (1 - d2)/2) (sq_nonneg (y2 - S))
    have a3 := mul_nonneg (by linarith : (0:ℝ) ≤ (d1+d2)/2) (sq_nonneg (2*y1 - 2*S))
    have a4 := mul_nonneg hgt (by linarith : (0:ℝ) ≤ y2 - y1)
    linarith only [e, a1, a2, a3, a4]

lemma SI_opt (P : Params) (hP : Standing P) :
    ∃ S, 0 ≤ S ∧ ∀ y : ℝ, 0 ≤ y → FL (P1 P) y y (2*y) ≤ FL (P1 P) S S (2*S) := by
  obtain ⟨d1, d2, g, c⟩ := P
  obtain ⟨hd2, hd21, hd1, hg, hgd1, hc, hcs, hcl, hgd2, hgd2p, hB, hp, hq, hK⟩ :=
    std_facts d1 d2 g c hP
  simp only [P1]
  have hD : 0 < 2 + 3*(d1+d2) := by linarith
  obtain ⟨S, hS⟩ : ∃ S, (2 + 3*(d1+d2))*S = 1 + (d1+d2)/2 - 2*c :=
    ⟨(1 + (d1+d2)/2 - 2*c)/(2 + 3*(d1+d2)), mul_div_cancel₀ _ hD.ne'⟩
  have hS0 : 0 < S := by
    by_contra hh; push Not at hh
    have := mul_nonpos_of_nonneg_of_nonpos hD.le hh; linarith
  refine ⟨S, hS0.le, ?_⟩
  intro y _
  have key := FL_diff ⟨d1,d2,1,c⟩ S S (2*S) y y (2*y)
  simp only at key
  have e : FL ⟨d1,d2,1,c⟩ S S (2*S) - FL ⟨d1,d2,1,c⟩ y y (2*y) =
      (1 - d1)/2 * (y - S)^2 + (1 - d2)/2 * (y - S)^2 + (d1+d2)/2 * (2*y - 2*S)^2 := by
    linear_combination key + (y - S)*hS
  have a1 := mul_nonneg (by linarith : (0:ℝ) ≤ (1 - d1)/2) (sq_nonneg (y - S))
  have a2 := mul_nonneg (by linarith : (0:ℝ) ≤ (1 - d2)/2) (sq_nonneg (y - S))
  have a3 := mul_nonneg (by linarith : (0:ℝ) ≤ (d1+d2)/2) (sq_nonneg (2*y - 2*S))
  linarith only [e, a1, a2, a3]


noncomputable def Uf (P : Params) : ℝ :=
  P.γ*(P.δ₁+P.δ₂)/8 + (1 - P.γ*P.δ₂ - 2*P.c)^2/(8*(1 - P.γ*P.δ₂))
    + (1 - P.γ*P.δ₁ - 2*P.c)^2/(8*(1 - P.γ*P.δ₁))

noncomputable def Wf (P : Params) : ℝ :=
  (1 - P.δ₂ - 2*P.c)^2/(8*(1 - P.δ₂)) + (1 + P.δ₁ + 2*P.δ₂ - 2*P.c)^2/(8*(1 + 3*P.δ₁ + 4*P.δ₂))

lemma U_facts (P : Params) (hP : Standing P) :
    (∀ y1 y2 y3 : ℝ, FL P y1 y2 y3 ≤ Uf P) ∧
    (P.c ≤ (1 - P.γ*P.δ₁)/4 → ∃ x t s : ℝ, (0 ≤ x ∧ x ≤ t ∧ t ≤ s ∧ s ≤ 2*x) ∧ FL P x t s = Uf P) := by
  obtain ⟨d1, d2, g, c⟩ := P
  obtain ⟨hd2, hd21, hd1, hg, hgd1, hc, hcs, hcl, hgd2, hgd2p, hB, hp, hq, hK⟩ :=
    std_facts d1 d2 g c hP
  simp only [Uf]
  set x := ((1-g*d1)/2 - c)/(1-g*d1) with hxdef
  set t := ((1-g*d2)/2 - c)/(1-g*d2) with htdef
  have hx : (1-g*d1)*x = (1-g*d1)/2 - c := mul_div_cancel₀ _ hp.ne'
  have ht : (1-g*d2)*t = (1-g*d2)/2 - c := mul_div_cancel₀ _ hq.ne'
  have hval : FL ⟨d1,d2,g,c⟩ x t (1/2) = g*(d1+d2)/8 + (1 - g*d2 - 2*c)^2/(8*(1 - g*d2))
      + (1 - g*d1 - 2*c)^2/(8*(1 - g*d1)) := by
    unfold FL; simp only; rw [hxdef, htdef]; field_simp; ring
  refine ⟨?_, ?_⟩
  · intro y1 y2 y3
    have key := FL_diff ⟨d1,d2,g,c⟩ x t (1/2) y1 y2 y3
    simp only at key
    have e : FL ⟨d1,d2,g,c⟩ x t (1/2) - FL ⟨d1,d2,g,c⟩ y1 y2 y3 =
        (1 - g*d1)/2 * (y1 - x)^2 + (1 - g*d2)/2 * (y2 - t)^2 + g*(d1+d2)/2 * (y3 - 1/2)^2 := by
      linear_combination key + (y1 - x)*hx + (y2 - t)*ht
    have a1 := mul_nonneg (by linarith : (0:ℝ) ≤ (1 - g*d1)/2) (sq_nonneg (y1 - x))
    have a2 := mul_nonneg (by linarith : (0:ℝ) ≤ (1 - g*d2)/2) (sq_nonneg (y2 - t))
    have a3 := mul_nonneg (by linarith : (0:ℝ) ≤ g*(d1+d2)/2) (sq_nonneg (y3 - 1/2))
    linarith only [e, a1, a2, a3, hval]
  · intro h1
    refine ⟨x, t, 1/2, ⟨?_, ?_, ?_, ?_⟩, hval⟩
    · by_contra hh; push Not at hh
      have := mul_neg_of_pos_of_neg hp hh; linarith
    · have e : (1-g*d1)*(1-g*d2)*(t - x) = c*(g*d1 - g*d2) := by
        linear_combination (1-g*d1)*ht - (1-g*d2)*hx
      by_contra hh; push Not at hh
      have := mul_neg_of_pos_of_neg (mul_pos hp hq) (by linarith : t - x < 0)
      have : 0 < c*(g*d1 - g*d2) := mul_pos hc (by linarith)
      linarith
    · by_contra hh; push Not at hh
      have := mul_lt_mul_of_pos_left hh hq; linarith
    · by_contra hh; push Not at hh
      have := mul_lt_mul_of_pos_left (by linarith : x < 1/4) hp; linarith

lemma W_facts (P : Params) (hP : Standing P) :
    (∀ y1 y2 : ℝ, FL (P1 P) y1 y2 (2*y1) ≤ Wf P) ∧
    (P.c ≤ CSM P.δ₁ P.δ₂ → ∃ x t : ℝ, (0 ≤ x ∧ x ≤ t) ∧ FL (P1 P) x t (2*x) = Wf P) ∧
    (P.c < CSM P.δ₁ P.δ₂ → ∀ y : ℝ, FL (P1 P) y y (2*y) < Wf P) := by
  obtain ⟨d1, d2, g, c⟩ := P
  obtain ⟨hd2, hd21, hd1, hg, hgd1, hc, hcs, hcl, hgd2, hgd2p, hB, hp, hq, hK⟩ :=
    std_facts d1 d2 g c hP
  simp only [Wf, P1]
  have hr : 0 < 1 - d2 := by linarith
  have hA : 0 < 1 - d1 + 4*(d1+d2) := by linarith
  set x := ((1-d1)/2 + (d1+d2) - c)/(1 - d1 + 4*(d1+d2)) with hxdef
  set t := ((1-d2)/2 - c)/(1-d2) with htdef
  have hx : (1 - d1 + 4*(d1+d2))*x = (1-d1)/2 + (d1+d2) - c := mul_div_cancel₀ _ hA.ne'
  have ht : (1-d2)*t = (1-d2)/2 - c := mul_div_cancel₀ _ hr.ne'
  have hA' : (1 + 3*d1 + 4*d2) ≠ 0 := by linarith
  have hval : FL ⟨d1,d2,1,c⟩ x t (2*x) = (1 - d2 - 2*c)^2/(8*(1 - d2))
      + (1 + d1 + 2*d2 - 2*c)^2/(8*(1 + 3*d1 + 4*d2)) := by
    unfold FL; simp only; rw [hxdef, htdef]
    have : (1 - d1 + 4*(d1+d2)) = (1 + 3*d1 + 4*d2) := by ring
    rw [this]
    generalize hA2 : 1 + 3*d1 + 4*d2 = A at *
    generalize hr2 : 1 - d2 = r at *
    field_simp
    subst hA2 hr2
    ring
  have e : ∀ y1 y2, FL ⟨d1,d2,1,c⟩ x t (2*x) - FL ⟨d1,d2,1,c⟩ y1 y2 (2*y1) =
      (1 - d1)/2 * (y1 - x)^2 + (1 - d2)/2 * (y2 - t)^2 + (d1+d2)/2 * (2*y1 - 2*x)^2 := by
    intro y1 y2
    have key := FL_diff ⟨d1,d2,1,c⟩ x t (2*x) y1 y2 (2*y1)
    simp only at key
    linear_combination key + (y1 - x)*hx + (y2 - t)*ht
  have hpos : 0 < (1 - d1 + 4*(d1+d2))*(1-d2) := mul_pos hA hr
  have ext : (1 - d1 + 4*(d1+d2))*(1-d2)*(t - x) = (1-d2)*(d1+d2) - c*(3*d1+5*d2) := by
    linear_combination (1 - d1 + 4*(d1+d2))*ht - (1-d2)*hx
  refine ⟨?_, ?_, ?_⟩
  · intro y1 y2
    have a1 := mul_nonneg (by linarith : (0:ℝ) ≤ (1 - d1)/2) (sq_nonneg (y1 - x))
    have a2 := mul_nonneg (by linarith : (0:ℝ) ≤ (1 - d2)/2) (sq_nonneg (y2 - t))
    have a3 := mul_nonneg (by linarith : (0:ℝ) ≤ (d1+d2)/2) (sq_nonneg (2*y1 - 2*x))
    linarith only [e y1 y2, a1, a2, a3, hval]
  · intro h
    have h' : c*(3*d1+5*d2) ≤ (1-d2)*(d1+d2) := by
      unfold CSM at h; rwa [le_div_iff₀ hK] at h
    refine ⟨x, t, ⟨?_, ?_⟩, hval⟩
    · by_contra hh; push Not at hh
      have := mul_neg_of_pos_of_neg hA hh; linarith
    · by_contra hh; push Not at hh
      have := mul_neg_of_pos_of_neg hpos (by linarith : t - x < 0); linarith
  · intro h y
    have h' : c*(3*d1+5*d2) < (1-d2)*(d1+d2) := by
      unfold CSM at h; rwa [lt_div_iff₀ hK] at h
    have hxt : x < t := by
      by_contra hh; push Not at hh
      have := mul_nonpos_of_nonneg_of_nonpos hpos.le (by linarith : t - x ≤ 0); linarith
    have a3 := mul_nonneg (by linarith : (0:ℝ) ≤ (d1+d2)/2) (sq_nonneg (2*y - 2*x))
    have hp2 : (0:ℝ) < (1 - d1)/2 := by linarith
    have hq2 : (0:ℝ) < (1 - d2)/2 := by linarith
    have hsq : 0 < (1 - d1)/2 * (y - x)^2 + (1 - d2)/2 * (y - t)^2 := by
      have b1 := mul_nonneg hp2.le (sq_nonneg (y - x))
      have b2 := mul_nonneg hq2.le (sq_nonneg (y - t))
      by_cases hh : y = x
      · have hne : y - t ≠ 0 := by rw [hh]; exact sub_ne_zero.mpr hxt.ne
        have := mul_pos hq2 (by positivity : (0:ℝ) < (y - t)^2)
        linarith only [this, b1]
      · have hne : y - x ≠ 0 := sub_ne_zero.mpr hh
        have := mul_pos hp2 (by positivity : (0:ℝ) < (y - x)^2)
        linarith only [this, b2]
    linarith only [e y y, hsq, a3, hval]

noncomputable def kap (d1 d2 g : ℝ) : ℝ :=
  4*(1 + 3*d1 + 4*d2)/(1-g*d1) + 4*(1 + 3*d1 + 4*d2)/(1-g*d2) - 4*(1 + 3*d1 + 4*d2)/(1-d2) - 4

/-- 8A(U - W) is the quadratic f. -/
lemma UW_identity (P : Params) (hP : Standing P) :
    8*(1 + 3*P.δ₁ + 4*P.δ₂)*(Uf P - Wf P) =
      (P.δ₁+P.δ₂)*(1-P.δ₁) - 8*(P.δ₁+P.δ₂)*P.c + kap P.δ₁ P.δ₂ P.γ * P.c^2 := by
  obtain ⟨d1, d2, g, c⟩ := P
  obtain ⟨hd2, hd21, hd1, hg, hgd1, hc, hcs, hcl, hgd2, hgd2p, hB, hp, hq, hK⟩ :=
    std_facts d1 d2 g c hP
  simp only [Uf, Wf, kap]
  have hr : (1 - d2) ≠ 0 := by linarith
  have hA : (1 + 3*d1 + 4*d2) ≠ 0 := by linarith
  have hp' := hp.ne'
  have hq' := hq.ne'
  rw [show g*(d1+d2) = 2 - (1-g*d1) - (1-g*d2) by ring]
  generalize 1 - g*d1 = p at *
  generalize 1 - g*d2 = q at *
  generalize hA2 : 1 + 3*d1 + 4*d2 = A at *
  generalize hr2 : 1 - d2 = r at *
  field_simp
  subst hA2 hr2
  ring



lemma CM_facts (d1 d2 g : ℝ) (hd2 : 0 < d2) (hd21 : d2 < d1) (hd1 : d1 < 1) (hg : 0 < g)
    (hg1 : g ≤ 1) :
    0 ≤ CM d1 d2 g ∧ kap d1 d2 g * CM d1 d2 g ≤ 4*(d1+d2) ∧
      ∀ c : ℝ, (d1+d2)*(1-d1) - 8*(d1+d2)*c + kap d1 d2 g * c^2 =
        (c - CM d1 d2 g)*(kap d1 d2 g*(c + CM d1 d2 g) - 8*(d1+d2)) := by
  have hgd1 : g*d1 < 1 := by nlinarith
  have hgd2 : g*d2 < 1 := by nlinarith
  have hp : 0 < 1 - g*d1 := by linarith
  have hq : 0 < 1 - g*d2 := by linarith
  have hr : 0 < 1 - d2 := by linarith
  have hA : 0 < 1 + 3*d1 + 4*d2 := by linarith
  have hd : 0 < d1 + d2 := by linarith
  have hs1 : 0 < 1 - d1 := by linarith
  set R := (1 - g) * (d1 + d2) * (d1 + d2 - d1 * d2 * (2 + g * (2 - d1)) + g * d1 * d2 ^ 2) /
        ((1 - g * d1) * (1 - d2) * (1 - g * d2) * (1 + 3 * d1 + 4 * d2)) with hRdef
  have hN : 0 ≤ d1 + d2 - d1 * d2 * (2 + g * (2 - d1)) + g * d1 * d2 ^ 2 := by
    have h1 : 0 ≤ d1*d2*(2 - d1 - d2) := mul_nonneg (mul_nonneg (by linarith) hd2.le) (by linarith)
    have h2 : 0 ≤ (1 - g) * (d1*d2*(2 - d1 - d2)) := mul_nonneg (by linarith) h1
    have h3 : 0 ≤ d1*(1-d2)^2 + d2*(1-d1)^2 :=
      add_nonneg (mul_nonneg (by linarith) (sq_nonneg _)) (mul_nonneg hd2.le (sq_nonneg _))
    nlinarith
  have hR : 0 ≤ R := by
    apply div_nonneg
    · exact mul_nonneg (mul_nonneg (by linarith) hd.le) hN
    · positivity
  set S := (8 * (d1 + d2) + 2 * (1 - d1)) * Real.sqrt R with hSdef
  have hS0 : 0 ≤ S := mul_nonneg (by linarith) (Real.sqrt_nonneg _)
  have hS2 : S^2 = 16*(d1+d2)^2 - kap d1 d2 g * (d1+d2) * (1-d1) := by
    rw [hSdef, mul_pow, Real.sq_sqrt hR, hRdef]
    unfold kap
    have hp' := hp.ne'
    have hq' := hq.ne'
    have hr' := hr.ne'
    have hA' := hA.ne'
    generalize hp2 : 1 - g*d1 = p at *
    generalize hq2 : 1 - g*d2 = q at *
    generalize hA2 : 1 + 3*d1 + 4*d2 = A at *
    generalize hr2 : 1 - d2 = r at *
    field_simp
    subst hA2 hr2 hp2 hq2
    ring
  have hCM : CM d1 d2 g = (1 - d1)*(d1+d2) / (4*(d1+d2) + S) := by
    unfold CM; rw [hSdef, hRdef]
  have hden : 0 < 4*(d1+d2) + S := by linarith
  have hc0 : CM d1 d2 g * (4*(d1+d2) + S) = (1 - d1)*(d1+d2) := by
    rw [hCM]; exact div_mul_cancel₀ _ hden.ne'
  have hk : kap d1 d2 g * CM d1 d2 g = 4*(d1+d2) - S := by
    have : (kap d1 d2 g * CM d1 d2 g) * (4*(d1+d2) + S) = (4*(d1+d2) - S) * (4*(d1+d2) + S) := by
      linear_combination (kap d1 d2 g) * hc0 + hS2
    exact mul_right_cancel₀ hden.ne' this
  refine ⟨?_, by linarith, ?_⟩
  · rw [hCM]; exact div_nonneg (mul_nonneg hs1.le hd.le) hden.le
  · intro c
    linear_combination (CM d1 d2 g) * hk - hc0 + (0:ℝ) * hS2


lemma quad_pos (κ c0 d c : ℝ) (hd : 0 < d) (hc0 : 0 ≤ c0) (hk : κ*c0 ≤ 4*d) (hc : 0 < c)
    (hlt : c < c0) : 0 < (c - c0)*(κ*(c+c0) - 8*d) := by
  have hm : κ*(c+c0) - 8*d < 0 := by
    rcases le_or_gt κ 0 with h | h
    · have : κ*(c+c0) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h (by linarith)
      linarith
    · have : κ*c < κ*c0 := mul_lt_mul_of_pos_left hlt h
      nlinarith
  exact mul_pos_of_neg_of_neg (by linarith) hm

lemma quad_nonpos (κ c0 d σ c : ℝ) (hk : κ*c0 ≤ 4*d)
    (hσ : (σ - c0)*(κ*(σ+c0) - 8*d) ≤ 0) (h1 : c0 ≤ c) (h2 : c ≤ σ) :
    (c - c0)*(κ*(c+c0) - 8*d) ≤ 0 := by
  rcases eq_or_lt_of_le h1 with h | h
  · rw [← h]; simp
  · have hσ0 : 0 < σ - c0 := by linarith
    have hmσ : κ*(σ+c0) - 8*d ≤ 0 := by
      by_contra hh; push Not at hh
      have := mul_pos hσ0 hh; linarith
    have e : (σ - c0)*(κ*(c+c0) - 8*d) = (σ - c)*(2*κ*c0 - 8*d) + (c - c0)*(κ*(σ+c0) - 8*d) := by
      ring
    have a1 : (σ - c)*(2*κ*c0 - 8*d) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    have a2 : (c - c0)*(κ*(σ+c0) - 8*d) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) hmσ
    have hm : κ*(c+c0) - 8*d ≤ 0 := by
      by_contra hh; push Not at hh
      have := mul_pos hσ0 hh; linarith
    exact mul_nonpos_of_nonneg_of_nonpos (by linarith) hm

lemma quad_neg (κ c0 d σ c : ℝ) (hk : κ*c0 ≤ 4*d)
    (hσ : (σ - c0)*(κ*(σ+c0) - 8*d) < 0) (h1 : c0 < c) (h2 : c ≤ σ) :
    (c - c0)*(κ*(c+c0) - 8*d) < 0 := by
  have hσ0 : 0 < σ - c0 := by linarith
  have hmσ : κ*(σ+c0) - 8*d < 0 := by
    by_contra hh; push Not at hh
    have := mul_nonneg hσ0.le hh; linarith
  have e : (σ - c0)*(κ*(c+c0) - 8*d) = (σ - c)*(2*κ*c0 - 8*d) + (c - c0)*(κ*(σ+c0) - 8*d) := by
    ring
  have a1 : (σ - c)*(2*κ*c0 - 8*d) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
  have a2 : (c - c0)*(κ*(σ+c0) - 8*d) < 0 := mul_neg_of_pos_of_neg (by linarith) hmσ
  have hm : κ*(c+c0) - 8*d < 0 := by
    by_contra hh; push Not at hh
    have := mul_nonneg hσ0.le hh; linarith
  exact mul_neg_of_pos_of_neg (by linarith) hm

lemma hs_mono (P : Params) (hB : 0 ≤ P.γ*(P.δ₁+P.δ₂)) (x t s s' : ℝ) (h : s ≤ s')
    (h' : s' ≤ 1/2) : FL P x t s ≤ FL P x t s' := by
  have e : FL P x t s' - FL P x t s = P.γ*(P.δ₁+P.δ₂)/2 * ((s' - s)*(1 - s - s')) := by
    unfold FL; ring
  have := mul_nonneg (by linarith : (0:ℝ) ≤ P.γ*(P.δ₁+P.δ₂)/2)
    (mul_nonneg (by linarith : (0:ℝ) ≤ s' - s) (by linarith : (0:ℝ) ≤ 1 - s - s'))
  linarith

lemma gamma_le (P : Params) (hP : Standing P) (hγ : P.γ ≤ 1) (x t s : ℝ) (h0 : 0 ≤ x)
    (h1 : x ≤ t) (h2 : t ≤ s) (h3 : s ≤ 1/2) :
    FL P x t s ≤ FL (P1 P) x t s ∧ (P.γ < 1 → x < s → FL P x t s < FL (P1 P) x t s) := by
  have e := FL_gamma P x t s
  have hd1 : 0 < P.δ₁ := by linarith [hP.δ₂_pos, hP.δ₂_lt_δ₁]
  have hΦ := Phi_nonneg P.δ₁ P.δ₂ x t s hd1.le hP.δ₂_pos.le h0 h1 h2 h3
  refine ⟨?_, ?_⟩
  · have := mul_nonpos_of_nonpos_of_nonneg (by linarith : (P.γ - 1)/2 ≤ 0) hΦ
    linarith
  · intro hlt hxs
    have hΦ' := Phi_pos P.δ₁ P.δ₂ x t s hd1 hP.δ₂_pos.le h0 h1 h2 h3 hxs
    have := mul_neg_of_neg_of_pos (by linarith : (P.γ - 1)/2 < 0) hΦ'
    linarith

lemma gamma_gt (P : Params) (hP : Standing P) (hγ : 1 < P.γ) (x t s : ℝ) (h0 : 0 ≤ x)
    (h1 : x ≤ t) (h2 : t ≤ s) (h3 : s ≤ 1/2) (hxs : x < s) :
    FL (P1 P) x t s < FL P x t s := by
  have e := FL_gamma P x t s
  have hd1 : 0 < P.δ₁ := by linarith [hP.δ₂_pos, hP.δ₂_lt_δ₁]
  have hΦ' := Phi_pos P.δ₁ P.δ₂ x t s hd1 hP.δ₂_pos.le h0 h1 h2 h3 hxs
  have := mul_pos (by linarith : 0 < (P.γ - 1)/2) hΦ'
  linarith

lemma B1_nonneg (P : Params) (hP : Standing P) : 0 ≤ (P1 P).γ * ((P1 P).δ₁ + (P1 P).δ₂) := by
  simp only [P1]; linarith [hP.δ₂_pos, hP.δ₂_lt_δ₁]

lemma chain_LM (P : Params) (hP : Standing P) (hγ : P.γ ≤ 1) (hc : (1 - P.δ₁)/4 ≤ P.c)
    (x t s : ℝ) (hz : LMgood P x t s) :
    ∃ x' t' : ℝ, 0 ≤ x' ∧ x' ≤ t' ∧ FL P x t s ≤ FL (P1 P) x' t' (2*x') ∧
      (P.γ < 1 → FL P x t s < FL (P1 P) x' t' (2*x')) := by
  obtain ⟨⟨h0, h1, h2, h3⟩, hx0, hxs, hs, hmax⟩ := hz
  obtain ⟨g1, g2⟩ := gamma_le P hP hγ x t s h0 h1 h2 hs
  obtain ⟨x1, t1, s1, ⟨⟨k0, k1, k2, k3⟩, _, _, ks, kmax⟩, kc, _, _⟩ := LM_opt (P1 P) (P1_standing P hP)
  have hc' : CLM1 (P1 P).δ₁ (P1 P).γ ≤ (P1 P).c := by simp only [CLM1, P1]; linarith
  have h2x := kc hc'
  have m1 := kmax x t s h0 h1 h2 h3
  have m2 := hs_mono (P1 P) (B1_nonneg P hP) x1 t1 s1 (2*x1) k3 h2x
  refine ⟨x1, t1, k0, k1, by linarith, fun hlt => ?_⟩
  have := g2 hlt hxs
  linarith

lemma chain_LI (P : Params) (hP : Standing P) (hγ : P.γ ≤ 1) (hc : (2 - (P.δ₁+P.δ₂))/8 ≤ P.c)
    (n s : ℝ) (hz : LIgood P n s) :
    ∃ S : ℝ, 0 ≤ S ∧ FL P n n s ≤ FL (P1 P) S S (2*S) ∧
      (P.γ < 1 → FL P n n s < FL (P1 P) S S (2*S)) := by
  obtain ⟨⟨h0, h1, h2⟩, hx0, hxs, hs, hmax⟩ := hz
  obtain ⟨g1, g2⟩ := gamma_le P hP hγ n n s h0 le_rfl h1 hs
  obtain ⟨n1, s1, ⟨⟨k0, k1, k2⟩, _, _, ks, kmax⟩, kc⟩ := LI_opt (P1 P) (P1_standing P hP)
  have hc' : CLI (P1 P).δ₁ (P1 P).δ₂ (P1 P).γ ≤ (P1 P).c := by simp only [CLI, P1]; linarith
  have h2x := kc hc'
  have m1 := kmax n s h0 h1 h2
  have m2 := hs_mono (P1 P) (B1_nonneg P hP) n1 n1 s1 (2*n1) k2 h2x
  refine ⟨n1, k0, by linarith, fun hlt => ?_⟩
  have := g2 hlt hxs
  linarith

lemma lease_M (P : Params) (hP : Standing P) (hγ : 1 < P.γ) (x t s : ℝ) (hz : LMgood P x t s)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 2*a) :
    FL (P1 P) a b (2*a) < FL P x t s := by
  obtain ⟨x1, t1, s1, ⟨⟨k0, k1, k2, k3⟩, kx0, kxs, ks, kmax⟩, _, _, _⟩ := LM_opt (P1 P) (P1_standing P hP)
  have m1 := kmax a b (2*a) ha hab hb le_rfl
  have m2 := gamma_gt P hP hγ x1 t1 s1 k0 k1 k2 ks kxs
  have m3 := hz.2.2.2.2 x1 t1 s1 k0 k1 k2 k3
  linarith

lemma lease_I (P : Params) (hP : Standing P) (hγ : 1 < P.γ) (n s : ℝ) (hz : LIgood P n s)
    (a : ℝ) (ha : 0 ≤ a) : FL (P1 P) a a (2*a) < FL P n n s := by
  obtain ⟨n1, s1, ⟨⟨k0, k1, k2⟩, kx0, kxs, ks, kmax⟩, _⟩ := LI_opt (P1 P) (P1_standing P hP)
  have m1 := kmax a (2*a) ha (by linarith) le_rfl
  have m2 := gamma_gt P hP hγ n1 n1 s1 k0 le_rfl k1 ks kxs
  have m3 := hz.2.2.2.2 n1 s1 k0 k1 k2
  linarith


lemma thr_facts (P : Params) (hP : Standing P) :
    (1 - P.δ₁)/4 < CSM P.δ₁ P.δ₂ ∧ (2 - (P.δ₁+P.δ₂))/8 < CSM P.δ₁ P.δ₂ ∧
    CLM1 P.δ₁ P.γ < CLM2 P.δ₁ P.δ₂ P.γ ∧
    (P.γ ≤ 1 → CSM P.δ₁ P.δ₂ ≤ CLM2 P.δ₁ P.δ₂ P.γ ∧ (1 - P.δ₁)/4 ≤ CLM1 P.δ₁ P.γ) := by
  obtain ⟨d1, d2, g, c⟩ := P
  obtain ⟨hd2, hd21, hd1, hg, hgd1, hc, hcs, hcl, hgd2, hgd2p, hB, hp, hq, hK⟩ :=
    std_facts d1 d2 g c hP
  have hCLI := CLI_lt_CLM2 d1 d2 g hd2 hd21 hg
  simp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold CSM; rw [lt_div_iff₀ hK]
    nlinarith [mul_pos (by linarith : (0:ℝ) < d1 - d2) (by linarith : (0:ℝ) < 1 + 3*d1 + 4*d2)]
  · unfold CSM; rw [lt_div_iff₀ hK]
    nlinarith [mul_pos (by linarith : (0:ℝ) < d1 - d2) (by linarith : (0:ℝ) < 2 + 3*(d1 + d2))]
  · have : CLM1 d1 g < CLI d1 d2 g := by unfold CLM1 CLI; linarith
    linarith
  · intro hg1
    refine ⟨?_, ?_⟩
    · unfold CSM CLM2
      apply div_le_div_of_nonneg_right _ hK.le
      have : g*d2 ≤ d2 := by nlinarith
      nlinarith
    · unfold CLM1; have : g*d1 ≤ d1 := by nlinarith
      linarith

end LMP3

open LMP3 in
theorem solution (P : Params) (hP : Standing P) :
    ∃ vLM vSM vLI vSI : ℝ,
      IsOptLM P vLM ∧ IsOptSM P vSM ∧ IsOptLI P vLI ∧ IsOptSI P vSI ∧
      (P.γ ≤ 1 →
        (P.c < CM P.δ₁ P.δ₂ P.γ → vSM < vLM ∧ vLI < vLM ∧ vSI < vLM) ∧
        (CM P.δ₁ P.δ₂ P.γ ≤ P.c → P.c < CSM P.δ₁ P.δ₂ →
          vLM ≤ vSM ∧ vLI < vSM ∧ vSI < vSM) ∧
        (CSM P.δ₁ P.δ₂ ≤ P.c → vSM = vSI ∧ vLM ≤ vSI ∧ vLI ≤ vSI)) ∧
      (P.γ < 1 →
        (CM P.δ₁ P.δ₂ P.γ < P.c → P.c < CSM P.δ₁ P.δ₂ → vLM < vSM) ∧
        (CSM P.δ₁ P.δ₂ ≤ P.c → vLM < vSI ∧ vLI < vSI)) ∧
      (1 < P.γ →
        (P.c < CLM2 P.δ₁ P.δ₂ P.γ → vSM < vLM ∧ vLI < vLM ∧ vSI < vLM) ∧
        (CLM2 P.δ₁ P.δ₂ P.γ ≤ P.c → vLM = vLI ∧ vSM < vLI ∧ vSI < vLI)) := by
  obtain ⟨xL, tL, sL, hL, hLc1, hLstrict, hLeq⟩ := LM_opt P hP
  obtain ⟨nI, sI, hI, hIc⟩ := LI_opt P hP
  obtain ⟨xS, tS, ⟨hS0, hS1, hS2⟩, hSmax, hSeq⟩ := SM_opt P hP
  obtain ⟨S, hS, hSImax⟩ := SI_opt P hP
  obtain ⟨Wb, Wa, Ws⟩ := W_facts P hP
  obtain ⟨Ub, Ua⟩ := U_facts P hP
  obtain ⟨T1, T3, T5, T24⟩ := thr_facts P hP
  have hLb := hL.2.2.2.2
  have hIb := hI.2.2.2.2
  obtain ⟨⟨l0, l1, l2, l3⟩, _, _, _, _⟩ := hL
  obtain ⟨⟨i0, i1, i2⟩, _, _, _, _⟩ := hI
  have hd2 := hP.δ₂_pos
  have hd21 := hP.δ₂_lt_δ₁
  have hd1 := hP.δ₁_lt_one
  have hcpos := hP.c_pos
  have hA : 0 < 1 + 3*P.δ₁ + 4*P.δ₂ := by linarith
  refine ⟨FL P xL tL sL, FL (P1 P) xS tS (2*xS), FL P nI nI sI, FL (P1 P) S S (2*S),
    ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨⟨⟨xL, tL - xL, sL - tL⟩, ?_, ?_⟩, ?_⟩
    · simp only [feasLM, Set.mem_setOf_eq]; refine ⟨l0, by linarith, by linarith, by linarith⟩
    · rw [profitLM_eq]; dsimp only; congr 1 <;> ring
    · rintro v ⟨y, hy, rfl⟩
      simp only [feasLM, Set.mem_setOf_eq] at hy
      obtain ⟨a, b, c, d⟩ := hy
      rw [profitLM_eq]
      exact hLb _ _ _ a (by linarith) (by linarith) (by linarith)
  · refine ⟨⟨⟨xS, tS⟩, ⟨hS0, hS1⟩, ?_⟩, ?_⟩
    · rw [profitSM_eq]
    · rintro v ⟨y, hy, rfl⟩
      obtain ⟨a, b⟩ := hy
      rw [profitSM_eq]
      exact hSmax _ _ a b
  · refine ⟨⟨⟨nI, sI - nI⟩, ?_, ?_⟩, ?_⟩
    · simp only [feasLI, Set.mem_setOf_eq]; refine ⟨by linarith, by linarith⟩
    · rw [profitLI_eq]; dsimp only; congr 1; ring
    · rintro v ⟨y, hy, rfl⟩
      simp only [feasLI, Set.mem_setOf_eq] at hy
      obtain ⟨a, b⟩ := hy
      rw [profitLI_eq]
      exact hIb _ _ (by linarith) (by linarith) (by linarith)
  · refine ⟨⟨S, hS, ?_⟩, ?_⟩
    · rw [profitSI_eq]
    · rintro v ⟨y, hy, rfl⟩
      rw [profitSI_eq]
      exact hSImax _ hy
  -- general facts
  have G1 : FL P nI nI sI ≤ FL P xL tL sL := hLb _ _ _ i0 le_rfl i1 i2
  have G2 : P.c < CLM2 P.δ₁ P.δ₂ P.γ → FL P nI nI sI < FL P xL tL sL :=
    fun h => hLstrict h _ _ i0 i1 i2
  have G3 : CLM2 P.δ₁ P.δ₂ P.γ ≤ P.c → FL P xL tL sL ≤ FL P nI nI sI := by
    intro h; have e := hLeq h; rw [← e]
    exact hIb _ _ l0 (by linarith) l3
  have G4 : FL (P1 P) S S (2*S) ≤ FL (P1 P) xS tS (2*xS) := hSmax S S hS le_rfl
  have G5 : P.c < CSM P.δ₁ P.δ₂ → FL (P1 P) S S (2*S) < FL (P1 P) xS tS (2*xS) := by
    intro h
    obtain ⟨x, t, ⟨hx0, hxt⟩, hv⟩ := Wa h.le
    have := hSmax x t hx0 hxt
    have := Ws h S
    linarith
  have G6 : CSM P.δ₁ P.δ₂ ≤ P.c → FL (P1 P) xS tS (2*xS) ≤ FL (P1 P) S S (2*S) := by
    intro h; have e := hSeq h; rw [← e]; exact hSImax _ hS0
  have G7 : FL (P1 P) xS tS (2*xS) ≤ Wf P := Wb xS tS
  have hLgood : LMgood P xL tL sL := ⟨⟨l0, l1, l2, l3⟩, by assumption, by assumption,
    by assumption, hLb⟩
  have hIgood : LIgood P nI sI := ⟨⟨i0, i1, i2⟩, by assumption, by assumption, by assumption, hIb⟩
  -- leasing-vs-selling chain for c ≥ (1-δ₁)/4
  have H1 : P.γ ≤ 1 → (1 - P.δ₁)/4 ≤ P.c →
      FL P xL tL sL ≤ FL (P1 P) xS tS (2*xS) ∧
      (P.γ < 1 → FL P xL tL sL < FL (P1 P) xS tS (2*xS)) := by
    intro hg1 hc
    obtain ⟨x', t', hx', hxt', h1, h2⟩ := chain_LM P hP hg1 hc xL tL sL hLgood
    have := hSmax x' t' hx' hxt'
    exact ⟨by linarith, fun h => by have := h2 h; linarith⟩
  -- the quadratic at σ = (1-δ₁)/4
  have H2 : P.γ ≤ 1 →
      ((1 - P.δ₁)/4 - CM P.δ₁ P.δ₂ P.γ) *
          (kap P.δ₁ P.δ₂ P.γ * ((1 - P.δ₁)/4 + CM P.δ₁ P.δ₂ P.γ) - 8*(P.δ₁+P.δ₂)) ≤ 0 ∧
      (P.γ < 1 → ((1 - P.δ₁)/4 - CM P.δ₁ P.δ₂ P.γ) *
          (kap P.δ₁ P.δ₂ P.γ * ((1 - P.δ₁)/4 + CM P.δ₁ P.δ₂ P.γ) - 8*(P.δ₁+P.δ₂)) < 0) := by
    intro hg1
    obtain ⟨_, _, hf⟩ := CM_facts P.δ₁ P.δ₂ P.γ hd2 hd21 hd1 hP.γ_pos hg1
    set P' : Params := ⟨P.δ₁, P.δ₂, P.γ, (1 - P.δ₁)/4⟩ with hP'def
    have hgd2 : P.γ*P.δ₂ ≤ P.δ₂ := by nlinarith [hP.γ_pos]
    have hP' : Standing P' := ⟨hd2, hd21, hd1, hP.γ_pos, hP.γδ₁_lt_one, by simp [P']; linarith,
      by simp [P']; linarith, by simp [P']; linarith⟩
    obtain ⟨_, Ua'⟩ := U_facts P' hP'
    obtain ⟨Wb', _, _⟩ := W_facts P' hP'
    have hσ : P'.c ≤ (1 - P'.γ*P'.δ₁)/4 := by
      simp only [P']; have := (T24 hg1).2; unfold CLM1 at this; linarith
    obtain ⟨u1, u2, u3, ⟨v0, v1, v2, v3⟩, hUv⟩ := Ua' hσ
    obtain ⟨x2, t2, s2, hz2, _, _, _⟩ := LM_opt P' hP'
    have m1 := hz2.2.2.2.2 u1 u2 u3 v0 v1 v2 v3
    have hc' : (1 - P'.δ₁)/4 ≤ P'.c := by simp [P']
    obtain ⟨x', t', _, _, k1, k2⟩ := chain_LM P' hP' hg1 hc' x2 t2 s2 hz2
    have m2 := Wb' x' t'
    have e := UW_identity P' hP'
    rw [hf] at e
    simp only [P'] at e
    have hA8 : 0 < 8*(1 + 3*P.δ₁ + 4*P.δ₂) := by linarith
    refine ⟨?_, fun hlt => ?_⟩
    · rw [← e]; exact mul_nonpos_of_nonneg_of_nonpos hA8.le (by linarith)
    · have := k2 hlt
      rw [← e]; exact mul_neg_of_pos_of_neg hA8 (by linarith)
  -- CM ≤ σ
  have H3 : P.γ ≤ 1 → CM P.δ₁ P.δ₂ P.γ ≤ (1 - P.δ₁)/4 := by
    intro hg1
    obtain ⟨hc0, hk, _⟩ := CM_facts P.δ₁ P.δ₂ P.γ hd2 hd21 hd1 hP.γ_pos hg1
    by_contra hh; push Not at hh
    have := quad_pos _ _ _ ((1 - P.δ₁)/4) (by linarith) hc0 hk (by linarith) hh
    linarith [(H2 hg1).1]
  -- U - W sign at the actual c
  have UWc := UW_identity P hP
  refine ⟨fun hg1 => ?_, fun hg1 => ?_, fun hg1 => ?_⟩
  · obtain ⟨hc0, hk, hf⟩ := CM_facts P.δ₁ P.δ₂ P.γ hd2 hd21 hd1 hP.γ_pos hg1
    have h3 := H3 hg1
    obtain ⟨T2, T4⟩ := T24 hg1
    refine ⟨fun hc => ?_, fun hc1 hc2 => ?_, fun hc => ?_⟩
    · have hpos := quad_pos _ _ _ P.c (by linarith) hc0 hk hcpos hc
      rw [← hf, ← UWc] at hpos
      have hUW : Wf P < Uf P := by
        by_contra hh; push Not at hh
        have := mul_nonpos_of_nonneg_of_nonpos (by linarith : (0:ℝ) ≤ 8*(1 + 3*P.δ₁ + 4*P.δ₂))
          (by linarith : Uf P - Wf P ≤ 0)
        linarith
      have hc4 : P.c ≤ (1 - P.γ*P.δ₁)/4 := by unfold CLM1 at T4; linarith
      obtain ⟨u1, u2, u3, ⟨v0, v1, v2, v3⟩, hUv⟩ := Ua hc4
      have m1 := hLb u1 u2 u3 v0 v1 v2 v3
      have hlt2 : P.c < CLM2 P.δ₁ P.δ₂ P.γ := by linarith
      have := G2 hlt2
      refine ⟨by linarith, this, by linarith⟩
    · have hLS : FL P xL tL sL ≤ FL (P1 P) xS tS (2*xS) := by
        rcases le_or_gt ((1 - P.δ₁)/4) P.c with h | h
        · exact (H1 hg1 h).1
        · have hq := quad_nonpos _ _ _ _ P.c hk (H2 hg1).1 hc1 h.le
          rw [← hf, ← UWc] at hq
          have hUW : Uf P ≤ Wf P := by
            by_contra hh; push Not at hh
            have := mul_pos (by linarith : (0:ℝ) < 8*(1 + 3*P.δ₁ + 4*P.δ₂))
              (by linarith : 0 < Uf P - Wf P)
            linarith
          obtain ⟨x, t, ⟨hx0, hxt⟩, hv⟩ := Wa hc2.le
          have := hSmax x t hx0 hxt
          have := Ub xL tL sL
          linarith
      have := G2 (by linarith)
      have := G5 hc2
      exact ⟨hLS, by linarith, this⟩
    · have e1 := G6 hc
      have hLS := (H1 hg1 (by linarith)).1
      obtain ⟨S', hS', k1, _⟩ := chain_LI P hP hg1 (by linarith) nI sI hIgood
      have := hSImax S' hS'
      exact ⟨le_antisymm e1 G4, by linarith, by linarith⟩
  · have hg1' : P.γ ≤ 1 := hg1.le
    obtain ⟨hc0, hk, hf⟩ := CM_facts P.δ₁ P.δ₂ P.γ hd2 hd21 hd1 hP.γ_pos hg1'
    refine ⟨fun hc1 hc2 => ?_, fun hc => ?_⟩
    · rcases le_or_gt ((1 - P.δ₁)/4) P.c with h | h
      · exact (H1 hg1' h).2 hg1
      · have hq := quad_neg _ _ _ _ P.c hk ((H2 hg1').2 hg1) hc1 h.le
        rw [← hf, ← UWc] at hq
        have hUW : Uf P < Wf P := by
          by_contra hh; push Not at hh
          have := mul_nonneg (by linarith : (0:ℝ) ≤ 8*(1 + 3*P.δ₁ + 4*P.δ₂))
            (by linarith : 0 ≤ Uf P - Wf P)
          linarith
        obtain ⟨x, t, ⟨hx0, hxt⟩, hv⟩ := Wa hc2.le
        have := hSmax x t hx0 hxt
        have := Ub xL tL sL
        linarith
    · have e1 := G6 hc
      have hLS := (H1 hg1' (by linarith)).2 hg1
      obtain ⟨S', hS', _, k2⟩ := chain_LI P hP hg1' (by linarith) nI sI hIgood
      have := hSImax S' hS'
      have := k2 hg1
      exact ⟨by linarith, by linarith⟩
  · have K1 := lease_M P hP hg1 xL tL sL hLgood xS tS hS0 hS1 hS2
    have K2 := lease_I P hP hg1 nI sI hIgood S hS
    refine ⟨fun hc => ?_, fun hc => ?_⟩
    · have := G2 hc
      exact ⟨K1, this, by linarith⟩
    · have := G3 hc
      exact ⟨le_antisymm this G1, by linarith, K2⟩

