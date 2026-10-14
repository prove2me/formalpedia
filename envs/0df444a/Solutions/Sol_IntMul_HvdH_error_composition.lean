-- Prove2me | solution 1 for IntMul.HvdH.error_composition
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-11T22:34:37.029527+00:00
-- url     : https://prove2.me/submissions/19a52273-c141-4550-8664-7335e601a5b9

import Theorems.Thm_IntMul_HvdH_rho_bounds

namespace IntMul.HvdH.Err
open IntMul.HvdH

variable {U V W : Type*} [NormedAddCommGroup U] [NormedSpace ℂ U]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- Lemma 2.7 (error propagation). -/
theorem error_propagation (A : V →L[ℂ] W) (hA : ‖A‖ ≤ 1) (Aa : V → W) (v vt : V) (eA ev : ℝ)
    (hAa : ‖Aa vt - A vt‖ ≤ eA) (hv : ‖vt - v‖ ≤ ev) : ‖Aa vt - A v‖ ≤ eA + ev := by
  have h1 : ‖A vt - A v‖ ≤ ev := by
    rw [← map_sub]
    calc ‖A (vt - v)‖ ≤ ‖A‖ * ‖vt - v‖ := A.le_opNorm _
      _ ≤ 1 * ev := mul_le_mul hA hv (norm_nonneg _) zero_le_one
      _ = ev := one_mul _
  calc ‖Aa vt - A v‖ = ‖(Aa vt - A vt) + (A vt - A v)‖ := by abel_nf
    _ ≤ ‖Aa vt - A vt‖ + ‖A vt - A v‖ := norm_add_le _ _
    _ ≤ eA + ev := add_le_add hAa h1

/-- Corollary 2.8 (composition). -/
theorem error_composition (A : U →L[ℂ] V) (B : V →L[ℂ] W) (hB : ‖B‖ ≤ 1)
    (Aa : U → V) (Bb : V → W) (S : Set U) (T : Set V) (eA eB : ℝ)
    (hAaT : ∀ u ∈ S, Aa u ∈ T) (hAa : ∀ u ∈ S, ‖Aa u - A u‖ ≤ eA)
    (hBb : ∀ v ∈ T, ‖Bb v - B v‖ ≤ eB) :
    ∀ u ∈ S, ‖Bb (Aa u) - B (A u)‖ ≤ eB + eA := fun u hu =>
  error_propagation B hB Bb (A u) (Aa u) eB eA (hBb _ (hAaT u hu)) (hAa u hu)

/-- Lemma 2.9 (bilinear error propagation). -/
theorem bilinear_error_propagation (A : U →L[ℂ] V →L[ℂ] W) (hA : ‖A‖ ≤ 1) (Aa : U → V → W)
    (u ut : U) (v vt : V) (eA eu ev : ℝ) (hu1 : ‖u‖ ≤ 1) (hvt1 : ‖vt‖ ≤ 1)
    (hAa : ‖Aa ut vt - A ut vt‖ ≤ eA) (hu : ‖ut - u‖ ≤ eu) (hv : ‖vt - v‖ ≤ ev) :
    ‖Aa ut vt - A u v‖ ≤ eA + eu + ev := by
  have h1 : ‖A ut vt - A u vt‖ ≤ eu := by
    have : A ut vt - A u vt = A (ut - u) vt := by rw [map_sub]; rfl
    rw [this]
    calc ‖A (ut - u) vt‖ ≤ ‖A‖ * ‖ut - u‖ * ‖vt‖ := A.le_opNorm₂ _ _
      _ ≤ 1 * eu * 1 := by
        have heu : 0 ≤ eu := (norm_nonneg _).trans hu
        exact mul_le_mul (mul_le_mul hA hu (norm_nonneg _) zero_le_one) hvt1 (norm_nonneg _)
          (by positivity)
      _ = eu := by ring
  have h2 : ‖A u vt - A u v‖ ≤ ev := by
    rw [← map_sub]
    calc ‖A u (vt - v)‖ ≤ ‖A‖ * ‖u‖ * ‖vt - v‖ := A.le_opNorm₂ _ _
      _ ≤ 1 * 1 * ev := by
        exact mul_le_mul (mul_le_mul hA hu1 (norm_nonneg _) zero_le_one) hv (norm_nonneg _)
          (by positivity)
      _ = ev := by ring
  calc ‖Aa ut vt - A u v‖ = ‖(Aa ut vt - A ut vt) + (A ut vt - A u vt) + (A u vt - A u v)‖ := by abel_nf
    _ ≤ ‖Aa ut vt - A ut vt‖ + ‖A ut vt - A u vt‖ + ‖A u vt - A u v‖ := norm_add₃_le
    _ ≤ eA + eu + ev := by gcongr

/-- Corollary 2.10: fixed-point product `ρ(utvt)` of approximations of `u, v` in the unit disc. -/
theorem fp_mul_error (p : ℕ) (u v ut v' : ℂ) (hu : ‖u‖ ≤ 1) (hv' : ‖v'‖ ≤ 1)
    (eu ev : ℝ) (hut : (2 : ℝ) ^ p * ‖ut - u‖ ≤ eu) (hvt : (2 : ℝ) ^ p * ‖v' - v‖ ≤ ev) :
    (2 : ℝ) ^ p * ‖rho p (ut * v') - u * v‖ < eu + ev + 2 := by
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  have hr := (rho_bounds p (ut * v')).2
  have hs : Real.sqrt 2 < 2 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have h1 : (2 : ℝ) ^ p * ‖rho p (ut * v') - ut * v'‖ < 2 := by
    have := mul_lt_mul_of_pos_left hr hp
    rw [mul_left_comm, mul_inv_cancel₀ hp.ne', mul_one] at this
    linarith
  have h2 : ‖ut * v' - u * v‖ ≤ ‖ut - u‖ + ‖v' - v‖ := by
    have e : ut * v' - u * v = (ut - u) * v' + u * (v' - v) := by ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    gcongr
    · exact (mul_le_of_le_one_right (norm_nonneg _) hv')
    · exact (mul_le_of_le_one_left (norm_nonneg _) hu)
  calc (2 : ℝ) ^ p * ‖rho p (ut * v') - u * v‖
      ≤ 2 ^ p * (‖rho p (ut * v') - ut * v'‖ + ‖ut * v' - u * v‖) :=
        mul_le_mul_of_nonneg_left (norm_sub_le_norm_sub_add_norm_sub _ _ _) hp.le
    _ ≤ 2 ^ p * ‖rho p (ut * v') - ut * v'‖ + (2 ^ p * ‖ut - u‖ + 2 ^ p * ‖v' - v‖) := by
        rw [mul_add]; gcongr; rw [← mul_add]; exact mul_le_mul_of_nonneg_left h2 hp.le
    _ < 2 + (eu + ev) := by linarith
    _ = eu + ev + 2 := by ring

end IntMul.HvdH.Err

open IntMul.HvdH in
theorem solution {U V W : Type*} [NormedAddCommGroup U] [NormedSpace ℂ U]
    [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]
    (A : U →L[ℂ] V) (B : V →L[ℂ] W) (hB : ‖B‖ ≤ 1)
    (Aa : U → V) (Bb : V → W) (S : Set U) (T : Set V) (eA eB : ℝ)
    (hAaT : ∀ u ∈ S, Aa u ∈ T) (hAa : ∀ u ∈ S, ‖Aa u - A u‖ ≤ eA)
    (hBb : ∀ v ∈ T, ‖Bb v - B v‖ ≤ eB) :
    ∀ u ∈ S, ‖Bb (Aa u) - B (A u)‖ ≤ eB + eA :=
  IntMul.HvdH.Err.error_composition A B hB Aa Bb S T eA eB hAaT hAa hBb
