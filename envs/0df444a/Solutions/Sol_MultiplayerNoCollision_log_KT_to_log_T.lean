-- Prove2me | solution 1 for MultiplayerNoCollision.log_KT_to_log_T
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T00:04:15.711803+00:00
-- url     : https://prove2.me/submissions/310924ba-86a7-43b8-b4aa-4d5e38776c1f

import Mathlib
import Definitions.Def_MultiplayerNoCollision_algorithm1

set_option autoImplicit false

open MultiplayerNoCollision

theorem solution : ∃ C₀ : ℝ, ∀ m K T : ℕ, 2 ≤ m → m + 1 ≤ K → 1 ≤ T →
    ∀ Δ : ℝ, 0 < Δ → Δ ≤ 1 →
      Δ ^ 2 * ((m : ℝ) * ((min T ⌈625 * gParam m K T / Δ ^ 2 +
          4 * m * Real.log ((m : ℝ) ^ 2 * T) / Δ⌉₊ : ℕ) : ℝ)) ≤
        C₀ * m * K * max 1 (Real.log T) := by
  refine ⟨600000, ?_⟩
  intro m K T hm hK hT Δ hΔ hΔ1
  set X := 625 * gParam m K T / Δ ^ 2 + 4 * m * Real.log ((m : ℝ) ^ 2 * T) / Δ with hX
  set N := min T ⌈X⌉₊ with hN
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hKR : (m : ℝ) + 1 ≤ K := by exact_mod_cast hK
  have hTR : (1 : ℝ) ≤ T := by exact_mod_cast hT
  set L := max 1 (Real.log T) with hL
  have hL1 : 1 ≤ L := le_max_left _ _
  have hlogT : Real.log T ≤ L := le_max_right _ _
  have hlogT0 : 0 ≤ Real.log T := Real.log_nonneg hTR
  have hΔ2 : Δ ^ 2 ≤ 1 := by nlinarith
  have hNT : (N : ℝ) ≤ T := by exact_mod_cast min_le_left _ _
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hm0 : (0 : ℝ) ≤ m := by linarith
  have hK0 : (0 : ℝ) < K := by linarith
  have hmKL : 0 ≤ (m : ℝ) * K * L := by positivity
  rcases le_or_gt T K with hTK | hTK
  · have hTKR : (T : ℝ) ≤ K := by exact_mod_cast hTK
    have h1 : (m : ℝ) * N ≤ m * K := mul_le_mul_of_nonneg_left (hNT.trans hTKR) hm0
    have h2 : Δ ^ 2 * (m * N) ≤ 1 * (m * K) :=
      mul_le_mul hΔ2 h1 (by positivity) (by norm_num)
    have h3 : (m : ℝ) * K ≤ m * K * L := by nlinarith [mul_nonneg hm0 hK0.le]
    nlinarith
  · have hTKR : (K : ℝ) < T := by exact_mod_cast hTK
    have hT2 : (3 : ℝ) ≤ (T : ℝ) ^ 2 := by nlinarith
    have hmT : (m : ℝ) ≤ T := by linarith
    have hpos1 : (0 : ℝ) < 3 * K * m ^ 2 * T ^ 2 := by positivity
    have hpos2 : (0 : ℝ) < (m : ℝ) ^ 2 * T := by positivity
    have hlog1 : Real.log (3 * K * m ^ 2 * T ^ 2) ≤ 7 * Real.log T := by
      have e : Real.log ((T : ℝ) ^ 7) = 7 * Real.log T := by
        rw [Real.log_pow]
        norm_num
      rw [← e]
      apply Real.log_le_log hpos1
      have h1 : (3 : ℝ) * K ≤ T ^ 2 * T := mul_le_mul hT2 hTKR.le (by positivity) (by positivity)
      have h2 : (m : ℝ) ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ hm0 hmT 2
      have h3 := mul_le_mul h1 h2 (by positivity) (by positivity)
      have h4 := mul_le_mul_of_nonneg_right h3 (by positivity : (0 : ℝ) ≤ (T : ℝ) ^ 2)
      calc (3 : ℝ) * K * m ^ 2 * T ^ 2 ≤ T ^ 2 * T * T ^ 2 * T ^ 2 := h4
        _ = T ^ 7 := by ring
    have hlog2 : Real.log ((m : ℝ) ^ 2 * T) ≤ 3 * Real.log T := by
      have e : Real.log ((T : ℝ) ^ 3) = 3 * Real.log T := by
        rw [Real.log_pow]
        norm_num
      rw [← e]
      apply Real.log_le_log hpos2
      have h2 : (m : ℝ) ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ hm0 hmT 2
      calc (m : ℝ) ^ 2 * T ≤ T ^ 2 * T := mul_le_mul_of_nonneg_right h2 (by positivity)
        _ = T ^ 3 := by ring
    have hlog1' : 0 ≤ Real.log (3 * K * m ^ 2 * T ^ 2) := by
      apply Real.log_nonneg
      have : (1 : ℝ) ≤ 3 * K * m ^ 2 * T ^ 2 := by
        have : (1 : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith
        have : (1 : ℝ) ≤ (T : ℝ) ^ 2 := by nlinarith
        have : (1 : ℝ) ≤ 3 * K := by linarith
        calc (1 : ℝ) = 1 * 1 * 1 := by ring
          _ ≤ 3 * K * m ^ 2 * T ^ 2 := by gcongr
      exact this
    have hlog2' : 0 ≤ Real.log ((m : ℝ) ^ 2 * T) := by
      apply Real.log_nonneg
      have : (1 : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith
      nlinarith
    have hg0 : 0 ≤ gParam m K T := by unfold gParam; positivity
    have hX0 : 0 ≤ X := by rw [hX]; positivity
    have hceil : (⌈X⌉₊ : ℝ) < X + 1 := Nat.ceil_lt_add_one hX0
    have hNX : (N : ℝ) ≤ X + 1 := (by exact_mod_cast min_le_right _ _ : (N : ℝ) ≤ ⌈X⌉₊).trans hceil.le
    have hXexp : Δ ^ 2 * (X + 1) =
        625 * gParam m K T + 4 * m * Real.log ((m : ℝ) ^ 2 * T) * Δ + Δ ^ 2 := by
      rw [hX]
      field_simp
    have e1 : Δ ^ 2 * N ≤ Δ ^ 2 * (X + 1) := mul_le_mul_of_nonneg_left hNX (by positivity)
    rw [hXexp] at e1
    have hg : gParam m K T ≤ 128 * K * (7 * Real.log T) := by
      unfold gParam
      exact mul_le_mul_of_nonneg_left hlog1 (by positivity)
    have hb1 : Real.log ((m : ℝ) ^ 2 * T) * Δ ≤ 3 * Real.log T := by
      have := mul_le_mul hlog2 hΔ1 hΔ.le (by positivity)
      linarith
    have hb2 : (m : ℝ) * (Real.log ((m : ℝ) ^ 2 * T) * Δ) ≤ K * (3 * Real.log T) :=
      mul_le_mul (by linarith) hb1 (by positivity) hK0.le
    have hKL : (K : ℝ) * Real.log T ≤ K * L := mul_le_mul_of_nonneg_left hlogT hK0.le
    have hKL1 : (1 : ℝ) ≤ K * L := by nlinarith
    have hA : Δ ^ 2 * N ≤ 560013 * K * L := by linarith
    have hB := mul_le_mul_of_nonneg_left hA hm0
    linarith
