-- Prove2me | solution 1 for MasulloRH.arithmetic_half_weight_escapes_all_fixed_prime_shells
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T05:23:26.230243+00:00
-- url     : https://prove2.me/submissions/9821fbf7-32c7-4e5e-91a8-fa39ae23afc5

import Mathlib
import Theorems.Thm_MasulloRH_translated_half_weight_prime_power_sum_and_nonvanishing

open Filter MeasureTheory Set
open scoped Topology ArithmeticFunction

theorem solution :
    ∃ f : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧ tsupport f ⊆ Set.Ioo 1 32 ∧
      HasMellin (fun t => (f t : ℂ)) 1 0 ∧ HasMellin (fun t => (f t : ℂ)) (-(1/2) : ℂ) 0 ∧
      ∃ c : ℝ, 0 < c ∧ ∀ P : Finset ℕ, (∀ p ∈ P, 2 ≤ p) →
        (∃ D : ℝ, ∀ (X : ℝ) (J : ℕ → Finset ℕ),
          (∑ p ∈ P, ∑ k ∈ J p, |Real.log (p:ℝ) * (Real.sqrt p)⁻¹ ^ k * f ((p:ℝ)^k/X)|) ≤ D) ∧
        ∀ᶠ X : ℝ in atTop, ∀ J : ℕ → Finset ℕ,
          c * Real.sqrt X ≤
            (∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊32*X⌋₊, ArithmeticFunction.vonMangoldt n / Real.sqrt n * f ((n:ℝ)/X)) -
            ∑ p ∈ P, ∑ k ∈ J p, Real.log (p:ℝ) * (Real.sqrt p)⁻¹ ^ k * f ((p:ℝ)^k/X) := by
  classical
  obtain ⟨f,hf,hc,hs,h1,hm,c,hcpos,hbig⟩ :=
    MasulloRH.translated_half_weight_prime_power_sum_and_nonvanishing.2
  have hK := (hc.isCompact_range hf.continuous).image (continuous_abs : Continuous (abs : ℝ → ℝ))
  obtain ⟨B,hB⟩ := hK.bddAbove
  have hb (t : ℝ) : |f t| ≤ B := hB ⟨f t, ⟨t,rfl⟩,rfl⟩
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hb 0)
  refine ⟨f,hf,hc,hs,h1,hm,c/2,by positivity,?_⟩
  intro P hP
  let D := ∑ p ∈ P, (B * Real.log (p:ℝ)) * ∑' k : ℕ, (Real.sqrt p)⁻¹ ^ k
  have hbound (X : ℝ) (J : ℕ → Finset ℕ) :
      (∑ p ∈ P, ∑ k ∈ J p, |Real.log (p:ℝ) * (Real.sqrt p)⁻¹ ^ k * f ((p:ℝ)^k/X)|) ≤ D := by
    apply Finset.sum_le_sum
    intro p hp
    have hp' : 1 < (p:ℝ) := by exact_mod_cast (show 1 < p by have := hP p hp; omega)
    have hl : 0 ≤ Real.log (p:ℝ) := Real.log_nonneg hp'.le
    have hroot : 1 < Real.sqrt (p:ℝ) := by simpa using Real.sqrt_lt_sqrt (by norm_num : (0:ℝ) ≤ 1) hp'
    have hrat : (Real.sqrt (p:ℝ))⁻¹ < 1 := inv_lt_one_of_one_lt₀ hroot
    have hgeom := summable_geometric_of_lt_one (by positivity : 0 ≤ (Real.sqrt (p:ℝ))⁻¹) hrat
    calc
      _ ≤ ∑ k ∈ J p, (B * Real.log (p:ℝ)) * (Real.sqrt p)⁻¹ ^ k := by
        apply Finset.sum_le_sum
        intro k hk
        rw [abs_mul, abs_of_nonneg (show 0 ≤ Real.log (p:ℝ) * (Real.sqrt p)⁻¹ ^ k by positivity)]
        calc
          _ ≤ Real.log (p:ℝ) * (Real.sqrt p)⁻¹ ^ k * B := mul_le_mul_of_nonneg_left (hb _) (by positivity)
          _ = _ := by ring
      _ = (B * Real.log (p:ℝ)) * ∑ k ∈ J p, (Real.sqrt p)⁻¹ ^ k := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hgeom.sum_le_tsum (J p) (fun k hk => by positivity)) (by positivity)
  refine ⟨⟨D,hbound⟩,?_⟩
  filter_upwards [hbig, eventually_ge_atTop ((2*|D|/c)^2)] with X hx hX
  intro J
  have hsqrt : 2*|D|/c ≤ Real.sqrt X := by
    calc
      _ = Real.sqrt ((2*|D|/c)^2) := (Real.sqrt_sq (by positivity)).symm
      _ ≤ _ := Real.sqrt_le_sqrt hX
  have hcost := (div_le_iff₀ hcpos).mp hsqrt
  have hsg : (∑ p ∈ P, ∑ k ∈ J p, Real.log (p:ℝ) * (Real.sqrt p)⁻¹ ^ k * f ((p:ℝ)^k/X)) ≤ D := by
    refine le_trans (Finset.sum_le_sum (fun p hp => Finset.sum_le_sum (fun k hk => le_abs_self _))) (hbound X J)
  nlinarith [le_abs_self D]
