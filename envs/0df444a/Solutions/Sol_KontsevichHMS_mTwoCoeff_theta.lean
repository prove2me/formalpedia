-- Prove2me | solution 1 for KontsevichHMS.mTwoCoeff_theta
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:21:55.151484+00:00
-- url     : https://prove2.me/submissions/fd0331f1-0e6c-4de5-a6ba-33059ae4117e

import Mathlib
import Definitions.Def_KontsevichHMS_TorusBrane

namespace KontsevichHMS

open Brane

/-- Gaussian series over `ℤ` are summable. -/
lemma aux_mtt_summable (c d : ℝ) (hc : c ≠ 0) :
    Summable (fun n : ℤ => Real.exp (-(c * n + d) ^ 2)) := by
  have hT : 0 < c ^ 2 / Real.pi := by positivity
  have h := summable_pow_mul_jacobiTheta₂_term_bound (|c * d| / Real.pi) hT 0
  simp only [pow_zero, one_mul] at h
  refine Summable.of_nonneg_of_le (fun n => (Real.exp_pos _).le) (fun n => ?_) h
  rw [Real.exp_le_exp, Int.cast_abs]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have e1 : -Real.pi * (c ^ 2 / Real.pi * (n : ℝ) ^ 2 - 2 * (|c * d| / Real.pi) * |(n : ℝ)|)
      = -(c ^ 2 * (n : ℝ) ^ 2 - 2 * |c * d| * |(n : ℝ)|) := by
    field_simp
  rw [e1]
  have h2 : -(|c * d| * |(n : ℝ)|) ≤ c * d * n := by
    rw [← abs_mul]; exact neg_abs_le _
  nlinarith [sq_nonneg d]

/-- The auxiliary theta function `g c = ∑ exp (-(c n + c/2)^2)`. -/
noncomputable def aux_mtt_g (c : ℝ) : ℝ := ∑' n : ℤ, Real.exp (-(c * n + c / 2) ^ 2)

lemma aux_mtt_g_nonneg (c : ℝ) : 0 ≤ aux_mtt_g c :=
  tsum_nonneg (fun _ => (Real.exp_pos _).le)

lemma aux_mtt_cont (c₀ c₁ : ℝ) (hc₀ : 0 < c₀) :
    ContinuousOn aux_mtt_g (Set.Icc c₀ c₁) := by
  unfold aux_mtt_g
  refine continuousOn_tsum (u := fun n : ℤ => Real.exp (-(c₀ * n + c₀ / 2) ^ 2))
    (fun n => by fun_prop) (aux_mtt_summable c₀ (c₀ / 2) hc₀.ne') ?_
  intro n c hc
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_exp, neg_le_neg_iff]
  have e1 : (c * n + c / 2) ^ 2 = c ^ 2 * ((n : ℝ) + 1 / 2) ^ 2 := by ring
  have e2 : (c₀ * n + c₀ / 2) ^ 2 = c₀ ^ 2 * ((n : ℝ) + 1 / 2) ^ 2 := by ring
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hc₀.le hc.1 2) (sq_nonneg _)

lemma aux_mtt_lower (N : ℕ) :
    (N : ℝ) * Real.exp (-1) ≤ aux_mtt_g (1 / ((N : ℝ) + 1)) := by
  unfold aux_mtt_g
  have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hs := aux_mtt_summable (1 / ((N : ℝ) + 1)) (1 / ((N : ℝ) + 1) / 2) (by positivity)
  refine le_trans ?_ (hs.sum_le_tsum (Finset.Ico (0 : ℤ) N)
    (fun _ _ => (Real.exp_pos _).le))
  have hcard : ((Finset.Ico (0 : ℤ) N).card : ℝ) = N := by simp
  refine le_trans (le_of_eq ?_) (Finset.card_nsmul_le_sum (Finset.Ico (0 : ℤ) N) _ (Real.exp (-1)) ?_)
  · rw [nsmul_eq_mul, hcard]
  intro n hn
  rw [Finset.mem_Ico] at hn
  rw [Real.exp_le_exp, neg_le_neg_iff]
  have h0 : (0 : ℝ) ≤ n := by exact_mod_cast hn.1
  have h1 : (n : ℝ) + 1 ≤ N := by exact_mod_cast hn.2
  have e : 1 / ((N : ℝ) + 1) * n + 1 / ((N : ℝ) + 1) / 2 = ((n : ℝ) + 1 / 2) / ((N : ℝ) + 1) := by
    field_simp
  rw [e, div_pow, div_le_one (by positivity)]
  nlinarith

lemma aux_mtt_upper (c : ℝ) (hc : 1 ≤ c) :
    aux_mtt_g c ≤ Real.exp (-((c ^ 2 - 1) / 4)) * aux_mtt_g 1 := by
  unfold aux_mtt_g
  rw [← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun n => ?_) (aux_mtt_summable c (c / 2) (by linarith))
    ((aux_mtt_summable 1 (1 / 2) one_ne_zero).mul_left _)
  rw [← Real.exp_add, Real.exp_le_exp]
  have hn : (0 : ℝ) ≤ (n : ℝ) * ((n : ℝ) + 1) := by
    have : (0 : ℤ) ≤ n * (n + 1) := by
      rcases le_or_gt 0 n with h | h
      · positivity
      · have : n + 1 ≤ 0 := by omega
        nlinarith
    exact_mod_cast this
  have hc2 : 0 ≤ c ^ 2 - 1 := by nlinarith
  nlinarith [mul_nonneg hc2 hn]

lemma aux_mtt_surj (V : ℝ) (hV : 0 < V) :
    ∃ a b : ℝ, a ≠ 0 ∧ ∑' n : ℤ, Real.exp (-(a * n + b) ^ 2) = V := by
  -- small parameter: large value
  set N : ℕ := ⌈V * Real.exp 1⌉₊ + 1 with hNdef
  have hNV : V * Real.exp 1 < N := by
    rw [hNdef]; push_cast
    exact lt_of_le_of_lt (Nat.le_ceil _) (lt_add_one _)
  have hlow : V < aux_mtt_g (1 / ((N : ℝ) + 1)) := by
    refine lt_of_lt_of_le ?_ (aux_mtt_lower N)
    rw [Real.exp_neg, ← div_eq_mul_inv, lt_div_iff₀ (Real.exp_pos _)]
    exact hNV
  -- large parameter: small value
  set G1 := aux_mtt_g 1 with hG1
  have hG1n : 0 ≤ G1 := aux_mtt_g_nonneg 1
  set c₂ : ℝ := 1 + 2 * G1 / V with hc₂
  have hc₂1 : 1 ≤ c₂ := by
    rw [hc₂]; have : 0 ≤ 2 * G1 / V := by positivity
    linarith
  set x : ℝ := (c₂ ^ 2 - 1) / 4 with hx
  have hVx : V * x = G1 + G1 ^ 2 / V := by
    rw [hx, hc₂]; field_simp; ring
  have hG1x : G1 ≤ V * x := by
    rw [hVx]; have : 0 ≤ G1 ^ 2 / V := by positivity
    linarith
  have hup : aux_mtt_g c₂ < V := by
    refine lt_of_le_of_lt (aux_mtt_upper c₂ hc₂1) ?_
    rw [← hx, Real.exp_neg, inv_mul_lt_iff₀ (Real.exp_pos _)]
    have := Real.add_one_le_exp x
    nlinarith
  -- intermediate value theorem
  have hc₁pos : (0 : ℝ) < 1 / ((N : ℝ) + 1) := by positivity
  have hc₁le : 1 / ((N : ℝ) + 1) ≤ c₂ := by
    refine le_trans ?_ hc₂1
    rw [div_le_one (by positivity)]
    have : (0 : ℝ) ≤ N := by positivity
    linarith
  have hivt := intermediate_value_Icc' hc₁le (aux_mtt_cont _ c₂ hc₁pos)
  obtain ⟨c, hc, hcV⟩ := hivt ⟨hup.le, hlow.le⟩
  refine ⟨c, c / 2, (lt_of_lt_of_le hc₁pos hc.1).ne', ?_⟩
  exact hcV

end KontsevichHMS

open KontsevichHMS
open Brane

theorem solution (area : ℝ) (harea : 0 < area) (b₁ b₂ b₃ : Brane)
    (h₁₂ : Transverse b₁ b₂) (h₂₃ : Transverse b₂ b₃) (h₁₃ : Transverse b₁ b₃)
    (hc₁ : b₁.conn = 0) (hc₂ : b₂.conn = 0) (hc₃ : b₃.conn = 0)
    (p q r : Torus) (hp : p ∈ isect b₁ b₂) (hq : q ∈ isect b₂ b₃) (hr : r ∈ isect b₁ b₃) :
    mTwoCoeff area b₁ b₂ b₃ p q r = 0 ∨
      ∃ a b : ℝ, a ≠ 0 ∧
        mTwoCoeff area b₁ b₂ b₃ p q r
          = ∑' n : ℤ, Complex.exp (-((a * (n : ℝ) + b) ^ 2 : ℝ)) := by
  have hw : ∀ T : (ℝ × ℝ) × (ℝ × ℝ) × (ℝ × ℝ), triangleWeight area b₁ b₂ b₃ T
      = ((Real.exp (-(area * det2 (T.2.1 - T.1) (T.2.2 - T.1) / 2)) : ℝ) : ℂ) := by
    intro T
    unfold triangleWeight
    rw [hc₁, hc₂, hc₃]
    simp only [zero_mul, add_zero, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one]
    rw [Complex.ofReal_exp, Complex.ofReal_neg]
  have hm : mTwoCoeff area b₁ b₂ b₃ p q r
      = ((∑' T : ↥(triangles b₁ b₂ b₃ p q r),
          Real.exp (-(area * det2 (T.1.2.1 - T.1.1) (T.1.2.2 - T.1.1) / 2)) : ℝ) : ℂ) := by
    unfold mTwoCoeff
    rw [Complex.ofReal_tsum]
    exact tsum_congr (fun T => hw T.1)
  set x := ∑' T : ↥(triangles b₁ b₂ b₃ p q r),
    Real.exp (-(area * det2 (T.1.2.1 - T.1.1) (T.1.2.2 - T.1.1) / 2)) with hxdef
  have hx0 : 0 ≤ x := tsum_nonneg (fun _ => (Real.exp_pos _).le)
  rcases hx0.eq_or_lt with h | h
  · left
    rw [hm, ← h, Complex.ofReal_zero]
  · right
    obtain ⟨a, b, ha, hab⟩ := aux_mtt_surj x h
    refine ⟨a, b, ha, ?_⟩
    rw [hm, ← hab, Complex.ofReal_tsum]
    refine tsum_congr (fun n => ?_)
    rw [Complex.ofReal_exp, Complex.ofReal_neg]
