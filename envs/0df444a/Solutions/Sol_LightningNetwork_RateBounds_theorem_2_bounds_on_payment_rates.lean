-- Prove2me | solution 1 for LightningNetwork.RateBounds.theorem_2_bounds_on_payment_rates
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-05T00:12:48.440197+00:00
-- url     : https://prove2.me/submissions/7a7488b0-ddbb-4ca8-b248-7ed561857c2c

import Mathlib
import Definitions.Def_LightningNetwork_RateBounds_uniCost
import Definitions.Def_LightningNetwork_RateBounds_bidiCost
import Definitions.Def_LightningNetwork_RateBounds_onChainCost
import Definitions.Def_LightningNetwork_RateBounds_kappa

set_option autoImplicit false

open Filter Topology Asymptotics

namespace LNRB3c

/-! Elementary inequalities. -/

lemma log_one_add_ge (y : ℝ) (hy : 0 ≤ y) : y - y ^ 2 ≤ Real.log (1 + y) := by
  have h1 : 0 < 1 + y := by linarith
  have h := Real.one_sub_inv_le_log_of_pos h1
  have e : 1 - (1 + y)⁻¹ = y / (1 + y) := by field_simp; ring
  rw [e] at h
  have : y - y ^ 2 ≤ y / (1 + y) := by
    rw [le_div_iff₀ h1]; nlinarith [sq_nonneg y, mul_nonneg hy (sq_nonneg y)]
  linarith

lemma log_one_add_le (y : ℝ) (hy : 0 ≤ y) : Real.log (1 + y) ≤ y := by
  have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 + y by linarith); linarith

lemma six_pow_le_fact (n : ℕ) : 6 ^ n ≤ (2 * n + 1).factorial := by
  induction n with
  | zero => simp
  | succ k ih =>
    have e : 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 := by ring
    rw [e, Nat.factorial_succ, Nat.factorial_succ, pow_succ]
    have h6 : 6 ≤ (2 * k + 1 + 1 + 1) * (2 * k + 1 + 1) := by nlinarith
    calc 6 ^ k * 6 ≤ (2 * k + 1).factorial * ((2 * k + 1 + 1 + 1) * (2 * k + 1 + 1)) :=
          Nat.mul_le_mul ih h6
      _ = (2 * k + 1 + 1 + 1) * ((2 * k + 1 + 1) * (2 * k + 1).factorial) := by ring

lemma sinh_mul_le (a : ℝ) (ha : 0 ≤ a) (h6 : a ^ 2 < 6) :
    Real.sinh a * (1 - a ^ 2 / 6) ≤ a := by
  have hq0 : 0 ≤ a ^ 2 / 6 := by positivity
  have hq1 : a ^ 2 / 6 < 1 := by linarith
  have hg : HasSum (fun n : ℕ => a * (a ^ 2 / 6) ^ n) (a * (1 - a ^ 2 / 6)⁻¹) :=
    (hasSum_geometric_of_lt_one hq0 hq1).mul_left a
  have hle : ∀ n : ℕ, a ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ) ≤ a * (a ^ 2 / 6) ^ n := by
    intro n
    have hf : (0:ℝ) < ((2 * n + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
    have h6n : (6:ℝ) ^ n ≤ ((2 * n + 1).factorial : ℝ) := by exact_mod_cast six_pow_le_fact n
    have h6p : (0:ℝ) < 6 ^ n := by positivity
    rw [div_le_iff₀ hf]
    have e : a ^ (2 * n + 1) = a * (a ^ 2) ^ n := by rw [pow_succ, pow_mul]; ring
    rw [e, div_pow]
    have key : (a ^ 2) ^ n ≤ (a ^ 2) ^ n / 6 ^ n * ((2 * n + 1).factorial : ℝ) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ h6p]
      exact mul_le_mul_of_nonneg_left h6n (by positivity)
    calc a * (a ^ 2) ^ n ≤ a * ((a ^ 2) ^ n / 6 ^ n * ((2 * n + 1).factorial : ℝ)) :=
          mul_le_mul_of_nonneg_left key ha
      _ = a * ((a ^ 2) ^ n / 6 ^ n) * ((2 * n + 1).factorial : ℝ) := by ring
  have hs := hasSum_le hle (Real.hasSum_sinh a) hg
  have hc : 0 < 1 - a ^ 2 / 6 := by linarith
  rw [← div_eq_mul_inv, le_div_iff₀ hc] at hs
  exact hs

lemma key0 (a : ℝ) (ha : 0 < a) :
    (1 + 2 * a ^ 2 / 3) * Real.sinh a ^ 2 ≤ a ^ 2 * Real.cosh a ^ 2 := by
  rw [Real.cosh_sq]
  have hs : 0 ≤ Real.sinh a := Real.sinh_nonneg_iff.mpr ha.le
  suffices h : Real.sinh a ^ 2 * (1 - a ^ 2 / 3) ≤ a ^ 2 by linarith [h]
  rcases le_or_gt 3 (a ^ 2) with h3 | h3
  · have : Real.sinh a ^ 2 * (1 - a ^ 2 / 3) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (by linarith)
    nlinarith [sq_nonneg a]
  · have hb := sinh_mul_le a ha.le (by linarith)
    have hc : 0 < 1 - a ^ 2 / 6 := by linarith
    have h1 : (Real.sinh a * (1 - a ^ 2 / 6)) ^ 2 ≤ a ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg hs hc.le) hb 2
    have h2 : 1 - a ^ 2 / 3 ≤ (1 - a ^ 2 / 6) ^ 2 := by nlinarith [sq_nonneg (a ^ 2)]
    calc Real.sinh a ^ 2 * (1 - a ^ 2 / 3) ≤ Real.sinh a ^ 2 * (1 - a ^ 2 / 6) ^ 2 :=
          mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
      _ = (Real.sinh a * (1 - a ^ 2 / 6)) ^ 2 := by ring
      _ ≤ a ^ 2 := h1

lemma key1 (x : ℝ) (hx : 0 < x) :
    (4 + 2 * x ^ 2 / 3) * (Real.exp x - 1) ^ 2 ≤ x ^ 2 * (Real.exp x + 1) ^ 2 := by
  have h := key0 (x / 2) (by linarith)
  have he : Real.exp x = Real.exp (x / 2) * Real.exp (x / 2) := by
    rw [← Real.exp_add]; ring_nf
  have hpos := Real.exp_pos (x / 2)
  have hs : Real.exp x - 1 = 2 * Real.exp (x / 2) * Real.sinh (x / 2) := by
    rw [Real.sinh_eq, Real.exp_neg, he]; field_simp
  have hc : Real.exp x + 1 = 2 * Real.exp (x / 2) * Real.cosh (x / 2) := by
    rw [Real.cosh_eq, Real.exp_neg, he]; field_simp
  rw [hs, hc]
  have h2 := mul_le_mul_of_nonneg_left h (by positivity : (0:ℝ) ≤ 4 * (2 * Real.exp (x / 2)) ^ 2)
  calc (4 + 2 * x ^ 2 / 3) * (2 * Real.exp (x / 2) * Real.sinh (x / 2)) ^ 2
        = 4 * (2 * Real.exp (x / 2)) ^ 2 * ((1 + 2 * (x / 2) ^ 2 / 3) * Real.sinh (x / 2) ^ 2) := by
          ring
    _ ≤ 4 * (2 * Real.exp (x / 2)) ^ 2 * ((x / 2) ^ 2 * Real.cosh (x / 2) ^ 2) := h2
    _ = x ^ 2 * (2 * Real.exp (x / 2) * Real.cosh (x / 2)) ^ 2 := by ring

lemma key2_alg (x y u v : ℝ) (hx : 0 < x) (hy : 0 < y) (hu : 1 < u) (hv : 1 < v)
    (h1 : (4 + 2 * x ^ 2 / 3) * (u - 1) ^ 2 ≤ x ^ 2 * (u + 1) ^ 2)
    (h2 : (4 + 2 * y ^ 2 / 3) * (v - 1) ^ 2 ≤ y ^ 2 * (v + 1) ^ 2) :
    2 / (x * y) - 1 / 6 ≤ (u + v) / ((u - 1) * (v - 1)) := by
  have hp : 0 < u - 1 := by linarith
  have hq : 0 < v - 1 := by linarith
  have a1 : 4 * (1 + x ^ 2 / 6) * (u - 1) ^ 2 ≤ (x * (u + 1)) ^ 2 := by linarith [h1]
  have a2 : 4 * (1 + y ^ 2 / 6) * (v - 1) ^ 2 ≤ (y * (v + 1)) ^ 2 := by linarith [h2]
  have a3 : (1 + x * y / 6) ^ 2 ≤ (1 + x ^ 2 / 6) * (1 + y ^ 2 / 6) := by
    linarith [sq_nonneg (x - y)]
  have hsq : (4 * (u - 1) * (v - 1) * (1 + x * y / 6)) ^ 2 ≤ (x * (u + 1) * (y * (v + 1))) ^ 2 := by
    calc (4 * (u - 1) * (v - 1) * (1 + x * y / 6)) ^ 2
          = 16 * (u - 1) ^ 2 * (v - 1) ^ 2 * (1 + x * y / 6) ^ 2 := by ring
      _ ≤ 16 * (u - 1) ^ 2 * (v - 1) ^ 2 * ((1 + x ^ 2 / 6) * (1 + y ^ 2 / 6)) := by gcongr
      _ = (4 * (1 + x ^ 2 / 6) * (u - 1) ^ 2) * (4 * (1 + y ^ 2 / 6) * (v - 1) ^ 2) := by ring
      _ ≤ (x * (u + 1)) ^ 2 * (y * (v + 1)) ^ 2 := by
          apply mul_le_mul a1 a2 (by positivity) (by positivity)
      _ = (x * (u + 1) * (y * (v + 1))) ^ 2 := by ring
  have hR : 0 ≤ x * (u + 1) * (y * (v + 1)) := by
    have : 0 < u + 1 := by linarith
    have : 0 < v + 1 := by linarith
    positivity
  have hL : 0 ≤ 4 * (u - 1) * (v - 1) * (1 + x * y / 6) := by positivity
  have hPQ : 4 * (u - 1) * (v - 1) * (1 + x * y / 6) ≤ x * (u + 1) * (y * (v + 1)) :=
    (pow_le_pow_iff_left₀ hL hR two_ne_zero).mp hsq
  have e : 2 / (x * y) - 1 / 6 = (12 - x * y) / (6 * (x * y)) := by field_simp; ring
  rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
  linarith [hPQ]

lemma key2 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    2 / (x * y) - 1 / 6 ≤ (Real.exp x + Real.exp y) / ((Real.exp x - 1) * (Real.exp y - 1)) :=
  key2_alg x y _ _ hx hy (by linarith [Real.add_one_lt_exp hx.ne'])
    (by linarith [Real.add_one_lt_exp hy.ne']) (key1 x hx) (key1 y hy)

lemma one_add_sq_half_le_cosh (x : ℝ) : 1 + x ^ 2 / 2 ≤ Real.cosh x := by
  have h := sum_le_hasSum (Finset.range 2)
    (fun i _ => by rw [pow_mul]; positivity) (Real.hasSum_cosh x)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith

/-! The constant κ. -/

lemma alpha_gt_one (r lam : ℝ) (hlam : 0 < lam) (hr : 0 < r) :
    1 < (r + 2 * lam + Real.sqrt (r * (4 * lam + r))) / (2 * lam) := by
  rw [lt_div_iff₀ (by positivity)]
  have := Real.sqrt_nonneg (r * (4 * lam + r))
  linarith

lemma alpha_inv (r lam : ℝ) (hlam : 0 < lam) (hr : 0 < r) :
    ((r + 2 * lam + Real.sqrt (r * (4 * lam + r))) / (2 * lam))⁻¹
      = (2 * lam + r - Real.sqrt (r * (4 * lam + r))) / (2 * lam) := by
  have hs0 := Real.sqrt_nonneg (r * (4 * lam + r))
  have hss : Real.sqrt (r * (4 * lam + r)) ^ 2 = r * (4 * lam + r) :=
    Real.sq_sqrt (by positivity)
  have hD : 0 < r + 2 * lam + Real.sqrt (r * (4 * lam + r)) := by linarith
  rw [inv_div, div_eq_div_iff hD.ne' (by positivity)]
  linear_combination (1 : ℝ) * hss

lemma exp_kappa (r lam : ℝ) (hlam : 0 < lam) (hr : 0 < r) :
    Real.exp (LightningNetwork.RateBounds.kappa r lam)
      = (r + 2 * lam + Real.sqrt (r * (4 * lam + r))) / (2 * lam) := by
  unfold LightningNetwork.RateBounds.kappa
  exact Real.exp_log (by linarith [alpha_gt_one r lam hlam hr])

lemma kappa_pos (r lam : ℝ) (hlam : 0 < lam) (hr : 0 < r) :
    0 < LightningNetwork.RateBounds.kappa r lam := by
  unfold LightningNetwork.RateBounds.kappa
  exact Real.log_pos (alpha_gt_one r lam hlam hr)

lemma cosh_kappa (r lam : ℝ) (hlam : 0 < lam) (hr : 0 < r) :
    Real.cosh (LightningNetwork.RateBounds.kappa r lam) = 1 + r / lam / 2 := by
  rw [Real.cosh_eq, Real.exp_neg, exp_kappa r lam hlam hr, alpha_inv r lam hlam hr]
  field_simp; ring

lemma kappa_sq_le (r lam : ℝ) (hlam : 0 < lam) (hr : 0 < r) :
    LightningNetwork.RateBounds.kappa r lam ^ 2 ≤ r / lam := by
  have h := one_add_sq_half_le_cosh (LightningNetwork.RateBounds.kappa r lam)
  rw [cosh_kappa r lam hlam hr] at h
  linarith

lemma kappa_sq_ge (r lam : ℝ) (hlam : 0 < lam) (hr : 0 < r) :
    r / lam - (r / lam) ^ 2 / 2 ≤ LightningNetwork.RateBounds.kappa r lam ^ 2 := by
  have h := Real.cosh_le_exp_half_sq (LightningNetwork.RateBounds.kappa r lam)
  rw [cosh_kappa r lam hlam hr] at h
  have ht : 0 ≤ r / lam / 2 := by positivity
  have h1 : Real.log (1 + r / lam / 2) ≤ LightningNetwork.RateBounds.kappa r lam ^ 2 / 2 := by
    have := Real.log_le_log (by linarith) h
    rwa [Real.log_exp] at this
  have h2 := log_one_add_ge (r / lam / 2) ht
  linarith [h1, h2]

/-! The bidirectional cost in symmetric form. -/

lemma alg_bidi (B l1 l2 u v : ℝ) (hu : 1 < u) (hv : 1 < v) :
    l1 + l2 - B * (u⁻¹ * (1 - u * v) - u * (1 - (u * v)⁻¹)) /
        (u⁻¹ * (1 - u * v) - u * (1 - (u * v)⁻¹) + u * v - (u * v)⁻¹)
      = l1 + l2 + B * ((u + v) / ((u - 1) * (v - 1))) := by
  have hu0 : u ≠ 0 := by positivity
  have hv0 : v ≠ 0 := by positivity
  have hu1 : u - 1 ≠ 0 := by linarith
  have hv1 : v - 1 ≠ 0 := by linarith
  have huv : u * v - 1 ≠ 0 := by nlinarith
  have hD : u⁻¹ * (1 - u * v) - u * (1 - (u * v)⁻¹) + u * v - (u * v)⁻¹
      = (u * v - 1) * (u - 1) * (v - 1) / (u * v) := by
    field_simp; ring
  have hN : u⁻¹ * (1 - u * v) - u * (1 - (u * v)⁻¹) = -((u + v) * (u * v - 1)) / (u * v) := by
    field_simp; ring
  rw [hD, hN]
  field_simp
  ring

lemma bidi_eq (B r lam l1 l2 : ℝ) (hlam : 0 < lam) (hr : 0 < r) (hl1 : 0 < l1) (hl2 : 0 < l2) :
    LightningNetwork.RateBounds.bidiCost B r lam lam l1 l2
      = l1 + l2 + B * ((Real.exp (LightningNetwork.RateBounds.kappa r lam * l1)
          + Real.exp (LightningNetwork.RateBounds.kappa r lam * l2))
          / ((Real.exp (LightningNetwork.RateBounds.kappa r lam * l1) - 1)
            * (Real.exp (LightningNetwork.RateBounds.kappa r lam * l2) - 1))) := by
  have hS : (lam - lam) ^ 2 + r ^ 2 + 2 * r * (lam + lam) = r * (4 * lam + r) := by ring
  have hα := alpha_gt_one r lam hlam hr
  have hα0 : 0 < (r + 2 * lam + Real.sqrt (r * (4 * lam + r))) / (2 * lam) := by linarith
  have hap : LightningNetwork.RateBounds.alphaPlus lam lam r
      = (r + 2 * lam + Real.sqrt (r * (4 * lam + r))) / (2 * lam) := by
    unfold LightningNetwork.RateBounds.alphaPlus; rw [hS]; ring_nf
  have ham : LightningNetwork.RateBounds.alphaMinus lam lam r
      = ((r + 2 * lam + Real.sqrt (r * (4 * lam + r))) / (2 * lam))⁻¹ := by
    rw [alpha_inv r lam hlam hr]
    unfold LightningNetwork.RateBounds.alphaMinus; rw [hS]; ring_nf
  have hk : LightningNetwork.RateBounds.kappa r lam
      = Real.log ((r + 2 * lam + Real.sqrt (r * (4 * lam + r))) / (2 * lam)) := rfl
  unfold LightningNetwork.RateBounds.bidiCost
  simp only []
  rw [hap, ham]
  generalize (r + 2 * lam + Real.sqrt (r * (4 * lam + r))) / (2 * lam) = α at hα hα0 hk
  rw [Real.inv_rpow hα0.le, Real.inv_rpow hα0.le, Real.rpow_add hα0,
    alg_bidi B l1 l2 _ _ (Real.one_lt_rpow hα hl1) (Real.one_lt_rpow hα hl2),
    Real.rpow_def_of_pos hα0, Real.rpow_def_of_pos hα0, hk]

/-! The four clauses. -/

open LightningNetwork.RateBounds

lemma clause1 (lam r B C : ℝ) (hlam : 0 < lam) (hr : 0 < r) (hB : 0 ≤ B)
    (h : ∃ m : ℝ, 0 < m ∧ uniCost B r lam m < onChainCost C r lam) :
    Real.log (1 + B * Real.log (1 + r / lam)) < C := by
  obtain ⟨m, hm, hlt⟩ := h
  unfold uniCost onChainCost at hlt
  have ha : (r + lam) / lam = 1 + r / lam := by field_simp; ring
  have ha1 : 0 < 1 + r / lam := by positivity
  rw [ha, Real.rpow_def_of_pos ha1] at hlt
  have hCl : C * lam / r = C / (r / lam) := by field_simp
  rw [hCl] at hlt
  have ht : 0 < r / lam := by positivity
  generalize r / lam = t at ht ha1 hlt ⊢
  have hρpos : 0 < Real.log (1 + t) := Real.log_pos (by linarith)
  have hρt := log_one_add_le t ht.le
  generalize Real.log (1 + t) = ρ at hρpos hρt hlt ⊢
  have hx0 : 0 < ρ * m := mul_pos hρpos hm
  have hT0 : 0 < Real.exp (ρ * m) - 1 := by
    have := Real.add_one_lt_exp hx0.ne'; linarith
  have hxT : Real.log (1 + (Real.exp (ρ * m) - 1)) = ρ * m := by
    rw [show 1 + (Real.exp (ρ * m) - 1) = Real.exp (ρ * m) by ring, Real.log_exp]
  generalize Real.exp (ρ * m) - 1 = T at hT0 hxT hlt
  have hb : 0 ≤ B * ρ := mul_nonneg hB hρpos.le
  have hu0 : 0 ≤ m + B * T⁻¹ := add_nonneg hm.le (mul_nonneg hB (inv_nonneg.mpr hT0.le))
  have h1 : (m + B * T⁻¹) * t < C := by rw [lt_div_iff₀ ht] at hlt; exact hlt
  have h2 : ρ * (m + B * T⁻¹) ≤ t * (m + B * T⁻¹) := mul_le_mul_of_nonneg_right hρt hu0
  have h4 : Real.log (1 + B * ρ) - Real.log (1 + T) ≤ (B * ρ - T) / (1 + T) := by
    rw [← Real.log_div (by positivity) (by positivity)]
    have := Real.log_le_sub_one_of_pos (show 0 < (1 + B * ρ) / (1 + T) by positivity)
    have e : (1 + B * ρ) / (1 + T) - 1 = (B * ρ - T) / (1 + T) := by field_simp; ring
    linarith
  have h5 : (B * ρ - T) / (1 + T) ≤ B * ρ / T := by
    rw [div_le_div_iff₀ (by positivity) hT0]; linarith [hb, sq_nonneg T]
  have h6 : B * ρ / T = ρ * (B * T⁻¹) := by rw [div_eq_mul_inv]; ring
  linarith [h1, h2, h4, h5, h6, hxT]

lemma clause2 (lam B : ℝ) (hlam : 0 < lam) (hB : 0 ≤ B) :
    (fun r : ℝ => Real.log (1 + B * Real.log (1 + r / lam)) - B * r / lam)
      =o[𝓝[>] 0] (fun r : ℝ => r) := by
  have hO : (fun r : ℝ => Real.log (1 + B * Real.log (1 + r / lam)) - B * r / lam)
      =O[𝓝[>] 0] (fun r : ℝ => r ^ 2) := by
    apply IsBigO.of_bound ((B + B ^ 2) / lam ^ 2)
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hr : 0 < r := hr
    have ht : 0 ≤ r / lam := by positivity
    have hL1 := log_one_add_le (r / lam) ht
    have hL2 := log_one_add_ge (r / lam) ht
    have hL0 : 0 ≤ Real.log (1 + r / lam) := Real.log_nonneg (by linarith)
    have hy0 : 0 ≤ B * Real.log (1 + r / lam) := mul_nonneg hB hL0
    have hyle : B * Real.log (1 + r / lam) ≤ B * (r / lam) := mul_le_mul_of_nonneg_left hL1 hB
    have hyge : B * (r / lam - (r / lam) ^ 2) ≤ B * Real.log (1 + r / lam) :=
      mul_le_mul_of_nonneg_left hL2 hB
    have hM1 := log_one_add_le _ hy0
    have hM2 := log_one_add_ge _ hy0
    have hsq : (B * Real.log (1 + r / lam)) ^ 2 ≤ (B * (r / lam)) ^ 2 :=
      pow_le_pow_left₀ hy0 hyle 2
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg r)]
    have e1 : B * r / lam = B * (r / lam) := by ring
    have e2 : (B + B ^ 2) / lam ^ 2 * r ^ 2 = (B + B ^ 2) * (r / lam) ^ 2 := by
      field_simp
    have hpos : 0 ≤ (B + B ^ 2) * (r / lam) ^ 2 := by positivity
    rw [e1, e2, abs_le]
    constructor <;> linarith [hM1, hM2, hyge, hyle, hsq, hpos]
  exact hO.trans_isLittleO ((isLittleO_pow_id (by norm_num : 1 < 2)).mono nhdsWithin_le_nhds)

lemma clause3 (lam r B C : ℝ) (hlam : 0 < lam) (hr : 0 < r) (hB : 0 ≤ B)
    (h : ∃ l1 l2 : ℝ, 0 < l1 ∧ 0 < l2 ∧
        bidiCost B r lam lam l1 l2 < 2 * onChainCost C r lam) :
    3 * (B * kappa r lam ^ 4 / 4) ^ (1 / 3 : ℝ) - B / 12 * kappa r lam ^ 2 < C := by
  obtain ⟨l1, l2, hl1, hl2, hlt⟩ := h
  rw [bidi_eq B r lam l1 l2 hlam hr hl1 hl2] at hlt
  unfold onChainCost at hlt
  have hk := kappa_pos r lam hlam hr
  have hkt := kappa_sq_le r lam hlam hr
  have hK := key2 (kappa r lam * l1) (kappa r lam * l2) (mul_pos hk hl1) (mul_pos hk hl2)
  have he1 := Real.add_one_lt_exp (mul_pos hk hl1).ne'
  have he2 := Real.add_one_lt_exp (mul_pos hk hl2).ne'
  have hx1 := mul_pos hk hl1
  have hx2 := mul_pos hk hl2
  have hE0 : 0 ≤ (Real.exp (kappa r lam * l1) + Real.exp (kappa r lam * l2))
      / ((Real.exp (kappa r lam * l1) - 1) * (Real.exp (kappa r lam * l2) - 1)) :=
    div_nonneg (by positivity) (mul_nonneg (by linarith) (by linarith))
  generalize (Real.exp (kappa r lam * l1) + Real.exp (kappa r lam * l2))
      / ((Real.exp (kappa r lam * l1) - 1) * (Real.exp (kappa r lam * l2) - 1)) = E at hlt hK hE0
  have e0 : 2 * (C * lam / r) = C / (r / lam / 2) := by field_simp
  rw [e0, lt_div_iff₀ (by positivity)] at hlt
  have ht : 0 < r / lam := by positivity
  generalize r / lam = t at hlt hkt ht
  generalize kappa r lam = κ at hk hkt hK ⊢
  have hcost : 0 ≤ l1 + l2 + B * E := by positivity
  have h1 : κ ^ 2 * (l1 + l2 + B * E) ≤ t * (l1 + l2 + B * E) :=
    mul_le_mul_of_nonneg_right hkt hcost
  have h2 : B * (2 / (κ * l1 * (κ * l2)) - 1 / 6) ≤ B * E := mul_le_mul_of_nonneg_left hK hB
  have h2' : κ ^ 2 / 2 * (B * (2 / (κ * l1 * (κ * l2)) - 1 / 6)) ≤ κ ^ 2 / 2 * (B * E) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have e3 : κ ^ 2 / 2 * (B * (2 / (κ * l1 * (κ * l2)) - 1 / 6)) = B / (l1 * l2) - B * κ ^ 2 / 12 := by
    field_simp; ring
  have hp1 : 0 ≤ κ ^ 2 * l1 / 2 := by positivity
  have hp2 : 0 ≤ κ ^ 2 * l2 / 2 := by positivity
  have hp3 : 0 ≤ B / (l1 * l2) := by positivity
  have hAM := Real.geom_mean_le_arith_mean3_weighted (w₁ := 1 / 3) (w₂ := 1 / 3) (w₃ := 1 / 3)
    (by norm_num) (by norm_num) (by norm_num) hp1 hp2 hp3 (by norm_num)
  rw [← Real.mul_rpow hp1 hp2, ← Real.mul_rpow (mul_nonneg hp1 hp2) hp3] at hAM
  have e4 : κ ^ 2 * l1 / 2 * (κ ^ 2 * l2 / 2) * (B / (l1 * l2)) = B * κ ^ 4 / 4 := by
    field_simp; ring
  rw [e4] at hAM
  linarith [h1, h2', e3, hAM, hlt]

lemma cbrt_cube (X : ℝ) (hX : 0 ≤ X) : (X ^ (1 / 3 : ℝ)) ^ 3 = X := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hX]; norm_num

lemma c4_bound (B t q : ℝ) (hB : 0 ≤ B) (ht0 : 0 < t) (ht1 : t < 1) (hk1 : q ≤ t)
    (hk2 : t - t ^ 2 / 2 ≤ q) :
    |3 * (B * q ^ 2 / 4) ^ (1 / 3 : ℝ) - B / 12 * q - (3 * (B * t ^ 2 / 4) ^ (1 / 3 : ℝ) - B / 12 * t)|
      ≤ |3 * t * (B * t ^ 2 / 4) ^ (1 / 3 : ℝ) + B * t ^ 2 / 24| := by
  have hq0 : 0 ≤ q := by nlinarith
  have hX0 : 0 ≤ B * q ^ 2 / 4 := by positivity
  have hq2 : q ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ hq0 hk1 2
  have hXY : B * q ^ 2 / 4 ≤ B * t ^ 2 / 4 := by
    have := mul_le_mul_of_nonneg_left hq2 hB; linarith
  have hq' : (t - t ^ 2 / 2) ^ 2 ≤ q ^ 2 := pow_le_pow_left₀ (by nlinarith) hk2 2
  have hYX : B * t ^ 2 / 4 - B * q ^ 2 / 4 ≤ t * (B * t ^ 2 / 4) := by
    have h3 : t ^ 2 - q ^ 2 ≤ t ^ 3 := by linarith [hq', sq_nonneg (t ^ 2)]
    linarith [mul_le_mul_of_nonneg_left h3 hB]
  have hx3 := cbrt_cube _ hX0
  have hy3 := cbrt_cube _ (hX0.trans hXY)
  have hx0 := Real.rpow_nonneg hX0 (1 / 3 : ℝ)
  have hxy := Real.rpow_le_rpow hX0 hXY (by norm_num : (0:ℝ) ≤ 1 / 3)
  rw [← hx3, ← hy3] at hYX
  generalize (B * q ^ 2 / 4) ^ (1 / 3 : ℝ) = x at hx3 hx0 hxy hYX ⊢
  generalize (B * t ^ 2 / 4) ^ (1 / 3 : ℝ) = y at hy3 hxy hYX ⊢
  have hy0 : 0 ≤ y := hx0.trans hxy
  have hyx : y - x ≤ t * y := by
    rcases hy0.eq_or_lt with h0 | hpos
    · rw [← h0]; linarith
    · have hc : (y - x - t * y) * y ^ 2 ≤ 0 := by
        linarith [mul_nonneg (sub_nonneg.mpr hxy) (add_nonneg (mul_nonneg hx0 hy0) (sq_nonneg x))]
      by_contra hcon
      have := mul_pos (by linarith : 0 < y - x - t * y) (pow_pos hpos 2)
      linarith
  have hR : 0 ≤ 3 * t * y + B * t ^ 2 / 24 := by
    have := mul_nonneg ht0.le hy0; positivity
  rw [abs_of_nonneg hR, abs_le]
  have hBq : 0 ≤ B * (t - q) := mul_nonneg hB (by linarith)
  have hBq2 : B * (t - q) ≤ B * (t ^ 2 / 2) := mul_le_mul_of_nonneg_left (by linarith) hB
  have hty : 0 ≤ t * y := mul_nonneg ht0.le hy0
  have hBt : 0 ≤ B * t ^ 2 := by positivity
  constructor <;> linarith [hyx, hxy, hBq, hBq2, hty, hBt]

lemma clause4 (lam B : ℝ) (hlam : 0 < lam) (hB : 0 ≤ B) :
    (fun r : ℝ => (3 * (B * kappa r lam ^ 4 / 4) ^ (1 / 3 : ℝ) - B / 12 * kappa r lam ^ 2)
        - (3 * (B * r ^ 2 / (4 * lam ^ 2)) ^ (1 / 3 : ℝ) - B * r / (12 * lam)))
      =o[𝓝[>] 0] (fun r : ℝ => r) := by
  have hcont : Continuous (fun r : ℝ =>
      3 * (B * r ^ 2 / (4 * lam ^ 2)) ^ (1 / 3 : ℝ) / lam + B * r / (24 * lam ^ 2)) := by
    have : Continuous (fun r : ℝ => (B * r ^ 2 / (4 * lam ^ 2)) ^ (1 / 3 : ℝ)) :=
      (Real.continuous_rpow_const (by norm_num)).comp (by fun_prop)
    exact ((this.const_mul 3).div_const lam).add (by fun_prop)
  have h0 : 3 * (B * (0:ℝ) ^ 2 / (4 * lam ^ 2)) ^ (1 / 3 : ℝ) / lam + B * 0 / (24 * lam ^ 2) = 0 := by
    rw [show B * (0:ℝ) ^ 2 / (4 * lam ^ 2) = 0 by ring, Real.zero_rpow (by norm_num)]; ring
  have hlim : Tendsto (fun r : ℝ =>
      3 * (B * r ^ 2 / (4 * lam ^ 2)) ^ (1 / 3 : ℝ) / lam + B * r / (24 * lam ^ 2))
      (𝓝[>] 0) (𝓝 0) := by
    have := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
    rwa [h0] at this
  have hsmall : (fun r : ℝ => r * (3 * (B * r ^ 2 / (4 * lam ^ 2)) ^ (1 / 3 : ℝ) / lam
      + B * r / (24 * lam ^ 2))) =o[𝓝[>] 0] (fun r : ℝ => r) := by
    have := (isBigO_refl (fun r : ℝ => r) (𝓝[>] (0:ℝ))).mul_isLittleO
      ((isLittleO_one_iff ℝ).mpr hlim)
    simpa using this
  refine IsBigO.trans_isLittleO ?_ hsmall
  apply IsBigO.of_bound 1
  filter_upwards [Ioo_mem_nhdsGT hlam] with r hr
  obtain ⟨hr0, hrl⟩ := hr
  have ht0 : 0 < r / lam := div_pos hr0 hlam
  have ht1 : r / lam < 1 := (div_lt_one hlam).mpr hrl
  have hk1 := kappa_sq_le r lam hlam hr0
  have hk2 := kappa_sq_ge r lam hlam hr0
  have hYe : B * r ^ 2 / (4 * lam ^ 2) = B * (r / lam) ^ 2 / 4 := by field_simp
  have hre : B * r / (12 * lam) = B / 12 * (r / lam) := by field_simp
  have hhe : r * (3 * (B * r ^ 2 / (4 * lam ^ 2)) ^ (1 / 3 : ℝ) / lam + B * r / (24 * lam ^ 2))
      = 3 * (r / lam) * (B * (r / lam) ^ 2 / 4) ^ (1 / 3 : ℝ) + B * (r / lam) ^ 2 / 24 := by
    rw [hYe]; field_simp
  rw [hhe, hYe, hre]
  have hk4 : kappa r lam ^ 4 = (kappa r lam ^ 2) ^ 2 := by ring
  rw [hk4]
  generalize r / lam = t at ht0 ht1 hk1 hk2 ⊢
  generalize kappa r lam ^ 2 = q at hk1 hk2 ⊢
  rw [Real.norm_eq_abs, Real.norm_eq_abs, one_mul]
  exact c4_bound B t q hB ht0 ht1 hk1 hk2

end LNRB3c

open Filter Topology Asymptotics LightningNetwork.RateBounds in
theorem solution :
    (∀ lam r B C : ℝ, 0 < lam → 0 < r → 0 ≤ B →
        (∃ m : ℝ, 0 < m ∧ uniCost B r lam m < onChainCost C r lam) →
        Real.log (1 + B * Real.log (1 + r / lam)) < C) ∧
    (∀ lam B : ℝ, 0 < lam → 0 ≤ B →
        (fun r : ℝ => Real.log (1 + B * Real.log (1 + r / lam)) - B * r / lam)
          =o[𝓝[>] 0] (fun r : ℝ => r)) ∧
    (∀ lam r B C : ℝ, 0 < lam → 0 < r → 0 ≤ B →
        (∃ l1 l2 : ℝ, 0 < l1 ∧ 0 < l2 ∧
            bidiCost B r lam lam l1 l2 < 2 * onChainCost C r lam) →
        3 * (B * kappa r lam ^ 4 / 4) ^ (1 / 3 : ℝ) - B / 12 * kappa r lam ^ 2 < C) ∧
    (∀ lam B : ℝ, 0 < lam → 0 ≤ B →
        (fun r : ℝ => (3 * (B * kappa r lam ^ 4 / 4) ^ (1 / 3 : ℝ) - B / 12 * kappa r lam ^ 2)
            - (3 * (B * r ^ 2 / (4 * lam ^ 2)) ^ (1 / 3 : ℝ) - B * r / (12 * lam)))
          =o[𝓝[>] 0] (fun r : ℝ => r)) := by
  exact ⟨LNRB3c.clause1, LNRB3c.clause2, LNRB3c.clause3, LNRB3c.clause4⟩
