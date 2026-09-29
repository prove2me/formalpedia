-- Prove2me | solution 1 for NumberField.summable_heightOneSpectrum_tsum_pow_mul_absNorm_rpow_neg_rat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/3849641d-942b-5bc7-bc17-7d5498f25aa8

import Theorems.Thm_NumberField_summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_summable_heightOneSpectrum_tsum_pow_mul_absNorm_rpow_neg_rat

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem solution
    (θ C : ℝ) (hθ : 1 < θ) (hC : 0 ≤ C) (k : ℕ) :
    (∀ v : HeightOneSpectrum (𝓞 ℚ),
        Summable (fun m : ℕ => ((m : ℝ) + 2) ^ k * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-((m : ℝ) + 1) * θ))) ∧
      Summable (fun v : HeightOneSpectrum (𝓞 ℚ) =>
        C * ∑' m : ℕ, ((m : ℝ) + 2) ^ k * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-((m : ℝ) + 1) * θ)) := by

  have hθ0 : 0 < θ := by linarith
  have hN : ∀ v : HeightOneSpectrum (𝓞 ℚ), (2 : ℝ) ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
    intro v
    have h1 : 1 < Ideal.absNorm v.asIdeal := by
      rw [Nat.one_lt_iff_ne_zero_and_ne_one]
      refine ⟨?_, ?_⟩
      · rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
      · rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
    exact_mod_cast h1

  set ρ : ℝ := (2 : ℝ) ^ (-θ) with hρ
  have hρ0 : 0 ≤ ρ := by rw [hρ]; positivity
  have hρ1 : ρ < 1 := by rw [hρ]; exact Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  have hgeo : Summable (fun m : ℕ => ((m : ℝ) + 2) ^ k * ρ ^ m) := by
    have h0 := summable_pow_mul_geometric_of_norm_lt_one k (show ‖ρ‖ < 1 by rw [Real.norm_eq_abs, abs_of_nonneg hρ0]; exact hρ1)
    have h2 := (summable_nat_add_iff 2).mpr h0

    by_cases hρz : ρ = 0
    · refine summable_of_ne_finset_zero (s := {0}) (fun m hm => ?_)
      have hm : m ≠ 0 := by simpa using hm
      rw [hρz, zero_pow hm, mul_zero]
    · have h3 := h2.mul_left (ρ ^ 2)⁻¹
      refine h3.congr (fun m => ?_)
      have hρ2 : ρ ^ 2 ≠ 0 := pow_ne_zero 2 hρz
      push_cast
      field_simp
      ring

  have hterm : ∀ (v : HeightOneSpectrum (𝓞 ℚ)) (m : ℕ),
      ((m : ℝ) + 2) ^ k * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-((m : ℝ) + 1) * θ) =
        ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-θ) *
          (((m : ℝ) + 2) ^ k * (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-θ)) ^ m) := by
    intro v m
    have hN0 : 0 ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by positivity
    have hN1 : 0 < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by linarith [hN v]
    rw [← Real.rpow_natCast (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-θ)) m, ← Real.rpow_mul hN0]
    have e : ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-((m : ℝ) + 1) * θ) =
        ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-θ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-θ * (m : ℝ)) := by
      rw [← Real.rpow_add hN1]; congr 1; ring
    rw [e]; ring
  have hle : ∀ (v : HeightOneSpectrum (𝓞 ℚ)) (m : ℕ),
      ((m : ℝ) + 2) ^ k * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-((m : ℝ) + 1) * θ) ≤
        ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-θ) * (((m : ℝ) + 2) ^ k * ρ ^ m) := by
    intro v m
    rw [hterm]
    have hN0 : 0 < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by linarith [hN v]
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ m) (by positivity))
      (by positivity)
    rw [hρ]
    exact Real.rpow_le_rpow_of_nonpos (by norm_num) (hN v) (by linarith)
  have hnn : ∀ (v : HeightOneSpectrum (𝓞 ℚ)) (m : ℕ),
      0 ≤ ((m : ℝ) + 2) ^ k * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-((m : ℝ) + 1) * θ) := fun v m => by positivity
  have hsum1 : ∀ v : HeightOneSpectrum (𝓞 ℚ),
      Summable (fun m : ℕ => ((m : ℝ) + 2) ^ k * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-((m : ℝ) + 1) * θ)) :=
    fun v => Summable.of_nonneg_of_le (hnn v) (hle v) ((hgeo.mul_left _))
  refine ⟨hsum1, ?_⟩

  have hV := NumberField.summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt ℚ hθ
  have hbig := (hV.mul_left (C * ∑' m : ℕ, ((m : ℝ) + 2) ^ k * ρ ^ m))
  refine Summable.of_nonneg_of_le (fun v => mul_nonneg hC (tsum_nonneg (hnn v))) (fun v => ?_) hbig
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hC
  rw [← tsum_mul_right]
  refine (hsum1 v).tsum_le_tsum (fun m => ?_) (hgeo.mul_right _)
  calc ((m : ℝ) + 2) ^ k * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-((m : ℝ) + 1) * θ)
      ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-θ) * (((m : ℝ) + 2) ^ k * ρ ^ m) := hle v m
    _ = ((m : ℝ) + 2) ^ k * ρ ^ m * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-θ) := by ring

#print axioms solution

end S_NumberField_summable_heightOneSpectrum_tsum_pow_mul_absNorm_rpow_neg_rat
end P2MW
export P2MW.S_NumberField_summable_heightOneSpectrum_tsum_pow_mul_absNorm_rpow_neg_rat (solution)
