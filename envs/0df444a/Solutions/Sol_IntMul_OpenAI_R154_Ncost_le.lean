-- Prove2me | solution 1 for IntMul.OpenAI.R154.Ncost_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T21:03:18.503197+00:00
-- url     : https://prove2.me/submissions/4fcd8981-e2de-404c-aaeb-505d4aa5b24e

import Mathlib
import Definitions.Def_IntMul_OpenAI_R154

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

open Real

namespace IntMul.OpenAI.R154.Pf

open IntMul.OpenAI.R154

/-! ## Margins -/

theorem margins' :
    2 * κ ≤ 1 - ε * (1 + c) ∧ 2 * κ ≤ ε * c * (1 - τ) ∧ 2 * κ ≤ ε * (1 - lam') ∧
      2 * κ ≤ 1 - τ - ε * (2 - τ) ∧ 2 * κ ≤ 1 / 4 - δ - 3 * ε / 2 ∧ 2 * κ ≤ 1 - δ - ε ∧
      2 * κ ≤ ε ∧ τ * (1 + c / (1 / 2)) < lam' ∧ lam' < 1 ∧ 0 < lam' - τ - c := by
  unfold κ ε c τ lam' δ
  norm_num

/-! ## The cost table -/

lemma pw {p e : ℝ} (hp : 1 ≤ p) (he : e ≤ es) : p ^ e ≤ p ^ es :=
  Real.rpow_le_rpow_of_exponent_le hp he

lemma es_pos : 0 < es := by unfold es κ; norm_num

/-- `x ≥ a p^e`, `-1 ≤ z ≤ 0`, `0 < a ≤ 1` ⇒ `x^z ≤ a⁻¹ p^{ez}`. -/
lemma rpow_neg_bound {x a p e z : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hp : 0 < p)
    (hx : a * p ^ e ≤ x) (hz : z ≤ 0) (hz1 : -1 ≤ z) : x ^ z ≤ a⁻¹ * p ^ (e * z) := by
  have hpe : 0 < p ^ e := Real.rpow_pos_of_pos hp e
  calc x ^ z ≤ (a * p ^ e) ^ z := Real.rpow_le_rpow_of_nonpos (by positivity) hx hz
    _ = a ^ z * p ^ (e * z) := by rw [Real.mul_rpow ha.le hpe.le, ← Real.rpow_mul hp.le]
    _ ≤ a⁻¹ * p ^ (e * z) := by
        gcongr
        rw [← Real.rpow_neg_one]
        exact Real.rpow_le_rpow_of_exponent_ge ha ha1 hz1

theorem Ncost_le' (p d K ℓ α : ℝ) (hp : 1 ≤ p)
    (hd1 : p ^ ε / 12 ≤ d) (hd2 : d ≤ p ^ ε)
    (hK1 : p ^ (ε * c) / 24 ≤ K) (hK2 : K ≤ p ^ (ε * c))
    (hℓ0 : 0 ≤ ℓ) (hℓ : ℓ ≤ p / (3 * d))
    (hα0 : 0 ≤ α) (hα : α ≤ 4 * p ^ (1 / 4 + ε / 2)) :
    Ncost p d K ℓ α ≤ 50 * p ^ es := by
  have hp0 : 0 < p := by linarith
  have hpe : ∀ e : ℝ, 0 < p ^ e := fun e => Real.rpow_pos_of_pos hp0 e
  have hd0 : 0 < d := lt_of_lt_of_le (by have := hpe ε; positivity) hd1
  have hK0 : 0 < K := lt_of_lt_of_le (by have := hpe (ε * c); positivity) hK1
  have hes1 : 1 ≤ p ^ es := Real.one_le_rpow hp es_pos.le
  -- 1. d K
  have t1 : d * K ≤ p ^ es := by
    calc d * K ≤ p ^ ε * p ^ (ε * c) := mul_le_mul hd2 hK2 hK0.le (hpe _).le
      _ = p ^ (ε + ε * c) := (Real.rpow_add hp0 _ _).symm
      _ ≤ p ^ es := (by apply pw hp; unfold ε c es κ; norm_num)
  -- 2. p K^{τ-1}
  have t2 : p * K ^ (τ - 1) ≤ 24 * p ^ es := by
    have h := rpow_neg_bound (x := K) (a := 1 / 24) (p := p) (e := ε * c) (z := τ - 1)
      (by norm_num) (by norm_num) hp0 (by linarith) (by unfold τ; norm_num)
      (by unfold τ; norm_num)
    calc p * K ^ (τ - 1) ≤ p * ((1 / 24)⁻¹ * p ^ (ε * c * (τ - 1))) :=
          mul_le_mul_of_nonneg_left h hp0.le
      _ = 24 * (p ^ (1 : ℝ) * p ^ (ε * c * (τ - 1))) := by rw [Real.rpow_one]; ring
      _ = 24 * p ^ (1 + ε * c * (τ - 1)) := by rw [← Real.rpow_add hp0]
      _ ≤ 24 * p ^ es := by
          gcongr; unfold ε c τ es κ; norm_num
  -- 3. ℓ d^{λ'}
  have t3 : ℓ * d ^ lam' ≤ 4 * p ^ es := by
    have hdl : d ^ lam' = d * d ^ (lam' - 1) := by
      rw [Real.rpow_sub hd0, Real.rpow_one]; field_simp
    have h := rpow_neg_bound (x := d) (a := 1 / 12) (p := p) (e := ε) (z := lam' - 1)
      (by norm_num) (by norm_num) hp0 (by linarith) (by unfold lam'; norm_num)
      (by unfold lam'; norm_num)
    have hd' : 0 ≤ d ^ (lam' - 1) := (Real.rpow_pos_of_pos hd0 _).le
    calc ℓ * d ^ lam' ≤ p / (3 * d) * (d * d ^ (lam' - 1)) := by
          rw [hdl]; exact mul_le_mul_of_nonneg_right hℓ (by positivity)
      _ = p / 3 * d ^ (lam' - 1) := by field_simp
      _ ≤ p / 3 * ((1 / 12)⁻¹ * p ^ (ε * (lam' - 1))) := by gcongr
      _ = 4 * (p ^ (1 : ℝ) * p ^ (ε * (lam' - 1))) := by rw [Real.rpow_one]; ring
      _ = 4 * p ^ (1 + ε * (lam' - 1)) := by rw [← Real.rpow_add hp0]
      _ ≤ 4 * p ^ es := by gcongr; unfold ε lam' es κ; norm_num
  -- 4. d²(1 + ℓ^τ)
  have t4 : d ^ 2 * (1 + ℓ ^ τ) ≤ 2 * p ^ es := by
    have hτ0 : 0 ≤ τ := by unfold τ; norm_num
    have hd2' : d ^ 2 ≤ p ^ es := by
      calc d ^ 2 ≤ (p ^ ε) ^ 2 := by gcongr
        _ = p ^ (ε * 2) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le]; norm_num
        _ ≤ p ^ es := (by apply pw hp; unfold ε es κ; norm_num)
    have hℓτ : ℓ ^ τ ≤ p ^ τ / d ^ τ := by
      calc ℓ ^ τ ≤ (p / d) ^ τ := by
            apply Real.rpow_le_rpow hℓ0 _ hτ0
            refine hℓ.trans (div_le_div_of_nonneg_left hp0.le hd0 (by linarith))
        _ = p ^ τ / d ^ τ := Real.div_rpow hp0.le hd0.le τ
    have hdτ : 0 < d ^ τ := Real.rpow_pos_of_pos hd0 τ
    have h2 : d ^ 2 * ℓ ^ τ ≤ p ^ es := by
      calc d ^ 2 * ℓ ^ τ ≤ d ^ 2 * (p ^ τ / d ^ τ) := by gcongr
        _ = d ^ ((2 : ℝ) - τ) * p ^ τ := by
            rw [Real.rpow_sub hd0, Real.rpow_two]; ring
        _ ≤ (p ^ ε) ^ ((2 : ℝ) - τ) * p ^ τ := by
            gcongr; unfold τ; norm_num
        _ = p ^ (ε * (2 - τ) + τ) := by
            rw [← Real.rpow_mul hp0.le, Real.rpow_add hp0]
        _ ≤ p ^ es := (by apply pw hp; unfold ε τ es κ; norm_num)
    nlinarith
  -- 5. d p^{1/2+δ} α
  have t5 : d * p ^ (1 / 2 + δ) * α ≤ 4 * p ^ es := by
    calc d * p ^ (1 / 2 + δ) * α ≤ p ^ ε * p ^ (1 / 2 + δ) * (4 * p ^ (1 / 4 + ε / 2)) := by
          gcongr
      _ = 4 * (p ^ ε * p ^ (1 / 2 + δ) * p ^ (1 / 4 + ε / 2)) := by ring
      _ = 4 * p ^ (ε + (1 / 2 + δ) + (1 / 4 + ε / 2)) := by
          rw [← Real.rpow_add hp0, ← Real.rpow_add hp0]
      _ ≤ 4 * p ^ es := by gcongr; unfold ε δ es κ; norm_num
  -- 6. d p^δ
  have t6 : d * p ^ δ ≤ p ^ es := by
    calc d * p ^ δ ≤ p ^ ε * p ^ δ := by gcongr
      _ = p ^ (ε + δ) := (Real.rpow_add hp0 _ _).symm
      _ ≤ p ^ es := (by apply pw hp; unfold ε δ es κ; norm_num)
  -- 7. ℓ + log₂ p
  have t7 : ℓ + Real.logb 2 p ≤ 7 * p ^ es := by
    have hℓ' : ℓ ≤ 4 * p ^ es := by
      calc ℓ ≤ p / (3 * d) := hℓ
        _ ≤ p / (3 * (p ^ ε / 12)) := by
            apply div_le_div_of_nonneg_left hp0.le (by have := hpe ε; positivity); linarith
        _ = 4 * (p ^ (1 : ℝ) / p ^ ε) := by rw [Real.rpow_one]; field_simp; ring
        _ = 4 * p ^ (1 - ε) := by rw [← Real.rpow_sub hp0]
        _ ≤ 4 * p ^ es := by gcongr; unfold ε es κ; norm_num
    have hlog : Real.logb 2 p ≤ 3 * p ^ es := by
      have h1 := Real.log_le_rpow_div hp0.le (show (0 : ℝ) < 1 / 2 by norm_num)
      have hl2 := Real.log_two_gt_d9
      have h2 : p ^ ((1 : ℝ) / 2) ≤ p ^ es := (by apply pw hp; unfold es κ; norm_num)
      have hlp : 0 ≤ Real.log p := Real.log_nonneg hp
      rw [Real.logb, div_le_iff₀ (by linarith)]
      have : p ^ ((1 : ℝ) / 2) / (1 / 2) = 2 * p ^ ((1 : ℝ) / 2) := by field_simp
      rw [this] at h1
      nlinarith
    linarith
  -- 8. p^δ + 1
  have t8 : p ^ δ ≤ p ^ es := (by apply pw hp; unfold δ es κ; norm_num)
  unfold Ncost
  linarith

end IntMul.OpenAI.R154.Pf

section
open IntMul.OpenAI.R154

theorem solution (p d K ℓ α : ℝ) (hp : 1 ≤ p)
    (hd1 : p ^ ε / 12 ≤ d) (hd2 : d ≤ p ^ ε)
    (hK1 : p ^ (ε * c) / 24 ≤ K) (hK2 : K ≤ p ^ (ε * c))
    (hℓ0 : 0 ≤ ℓ) (hℓ : ℓ ≤ p / (3 * d))
    (hα0 : 0 ≤ α) (hα : α ≤ 4 * p ^ (1 / 4 + ε / 2)) :
    Ncost p d K ℓ α ≤ 50 * p ^ es :=
  IntMul.OpenAI.R154.Pf.Ncost_le' p d K ℓ α hp hd1 hd2 hK1 hK2 hℓ0 hℓ hα0 hα

end
