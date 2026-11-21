-- Prove2me | solution 1 for MasulloRH.bounded_multiplicity_lift_mellin_majorant_summable
-- status  : ACCEPTED   (prove)
-- author  : @Abhishek Anand
-- created : 2026-11-21T04:42:23.87426+00:00
-- url     : https://prove2.me/submissions/72da49aa-a2da-4c1e-8aea-af9b34992b80

import Theorems.Thm_MasulloRH_fixed_log_jet_mellin_decay_on_strip
import Theorems.Thm_MasulloRH_weighted_zero_summability

open MeasureTheory MasulloRH Filter

theorem solution (φ : ℝ → ℂ) (hφ : IsRationalTraceTest φ) (α : ℝ) (hα : 0 < α) (D : ℕ) :
    let n := fun ρ : ZetaZerosInTraceStrip α => analyticOrderNatAt riemannZeta (ρ:ℂ)
    let M := fun (ρ : ZetaZerosInTraceStrip α) (d : ℕ) =>
      ‖∫ y : ℝ, φ (Real.exp y) * (y:ℂ)^d * Complex.exp (((ρ:ℂ)-1/2)*y)‖
    let B := fun ρ => if n ρ ≤ D then
      (n ρ : ℝ) * 2^(n ρ - 1) * ∑ d ∈ Finset.range (n ρ), M ρ d else 0
    Summable B ∧ Summable (fun ρ => B ρ ^ 2) := by
  intro n M B
  have hw := weighted_zero_summability α hα
  have hm (d : ℕ) : Summable fun ρ => (n ρ : ℝ) * M ρ d := by
    obtain ⟨C, hC, Y, hY⟩ := fixed_log_jet_mellin_decay_on_strip φ hφ (-1) 1 (by norm_num) d 2 (by decide)
    let R := max 1 Y
    have hR : 1 ≤ R := le_max_left _ _
    have hr : 0 < 1 / (1+R^2) := by positivity
    apply (hw.mul_left (2*C)).of_norm_bounded_eventually
    filter_upwards [hw.tendsto_cofinite_zero.eventually_lt_const hr] with ρ hρ
    let t := (ρ:ℂ).im
    change (n ρ : ℝ) / (1+t^2) < 1/(1+R^2) at hρ
    change ‖(n ρ : ℝ) * M ρ d‖ ≤ 2*C*((n ρ : ℝ)/(1+t^2))
    by_cases hn : n ρ = 0
    · simp [hn]
    have hn1 : (1:ℝ) ≤ n ρ := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    have ht : R < |t| := by
      by_contra! hf
      have hs : |t|^2 ≤ R^2 := by gcongr
      rw [sq_abs] at hs
      have he := (div_lt_div_iff₀ (by positivity : 0 < 1+t^2) (by positivity : 0 < 1+R^2)).mp hρ
      nlinarith [mul_nonneg (sub_nonneg.mpr hn1) (sq_nonneg R)]
    have ht1 : 1 < |t| := hR.trans_lt ht
    have ht2 : 1 ≤ t^2 := by nlinarith [sq_abs t, sq_nonneg (|t|-1)]
    have hdec : M ρ d ≤ C/t^2 := by
      have h := hY ((ρ:ℂ)-1/2)
      have hz1 := ρ.property.2.1
      have hz2 := ρ.property.2.2.1
      simp only [Complex.sub_re, Complex.sub_im, Complex.div_ofNat_re, Complex.one_re,
        Complex.div_ofNat_im, Complex.one_im, zero_div, sub_zero, sq_abs] at h
      exact h (by linarith) (by linarith) ((le_max_right 1 Y).trans ht.le)
    have hM : 0 ≤ M ρ d := norm_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) hM)]
    calc
      (n ρ : ℝ) * M ρ d ≤ (n ρ : ℝ) * ((2*C)/(1+t^2)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply hdec.trans
        apply (div_le_div_iff₀ (by positivity : 0<t^2) (by positivity : 0<1+t^2)).2
        nlinarith [mul_nonneg hC.le (sub_nonneg.mpr ht2)]
      _ = _ := by ring
  have hall : Summable (fun ρ => ∑ d ∈ Finset.range D, (n ρ : ℝ)*M ρ d) :=
    summable_sum fun d _ => hm d
  have hB (ρ) : 0 ≤ B ρ := by dsimp [B]; split <;> positivity
  have htotal : Summable B := by
    apply (hall.mul_left ((2:ℝ)^D)).of_nonneg_of_le hB
    intro ρ
    dsimp [B]
    split_ifs with hd
    · rw [← Finset.mul_sum]
      have hs : (∑ d ∈ Finset.range (n ρ), M ρ d) ≤ ∑ d ∈ Finset.range D, M ρ d :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hd) (fun i _ _ => norm_nonneg _)
      have hpow : (2:ℝ)^(n ρ-1) ≤ 2^D  := pow_le_pow_right₀ (by norm_num) ((Nat.sub_le _ _).trans hd)
      calc
        _ ≤ (n ρ : ℝ) * (2:ℝ)^D * (∑ d ∈ Finset.range D, M ρ d) := by gcongr
        _ = _ := by ring
    · positivity
  refine ⟨htotal, ?_⟩
  have hb := htotal.tendsto_cofinite_zero.eventually_lt_const (by norm_num : (0:ℝ)<1)
  apply htotal.of_norm_bounded_eventually
  filter_upwards [hb] with ρ hρ
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (B ρ)), pow_two]
  exact mul_le_of_le_one_right (hB ρ) hρ.le
