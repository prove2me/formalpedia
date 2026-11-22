-- Prove2me | solution 1 for HypercliqueFalse.potential_recursion
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-22T12:58:58.001635+00:00
-- url     : https://prove2.me/submissions/60b5e0f0-04a2-4399-9085-4bd038d4df45

import Mathlib

set_option autoImplicit false

theorem solution (q L : ℕ) (hq : 2 ≤ q) (δ ρ Φ : ℝ)
    (hρ : ρ = (q : ℝ) ^ (-δ) + (1 - 1 / (q : ℝ)) * (2 : ℝ) ^ (-δ)) :
    (q : ℝ) * ((q : ℝ) ^ (1 - δ) * Φ) + (q.choose 2 : ℝ) * ((2 : ℝ) ^ (1 - δ) * Φ) =
        ρ * (q : ℝ) ^ 2 * Φ ∧
      ρ ≤ (2 : ℝ) ^ (-δ) * (1 + (2 / (q : ℝ)) ^ δ) ∧
      (ρ * (q : ℝ) ^ 2) ^ (2 * L) = ((q : ℝ) ^ (2 * L)) ^ 2 * ρ ^ (2 * L) ∧
      ((q : ℝ) ^ (2 * L)) ^ 2 * ρ ^ (2 * L) = ((q : ℝ) ^ (2 * L)) ^ (2 - Real.logb q (1 / ρ)) ∧
      (δ - Real.logb 2 (1 + (2 / (q : ℝ)) ^ δ)) / Real.logb 2 q ≤ Real.logb q (1 / ρ) := by
  have hQ2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hQpos : 0 < (q : ℝ) := by linarith
  have hQ1 : 1 < (q : ℝ) := by linarith
  have hQne : (q : ℝ) ≠ 0 := hQpos.ne'
  have hQne1 : (q : ℝ) ≠ 1 := by linarith
  have hQne1' : (q : ℝ) ≠ -1 := by linarith
  have hQpow_pos : 0 < (q : ℝ) ^ (-δ) := Real.rpow_pos_of_pos hQpos _
  have h2pow_pos : 0 < (2 : ℝ) ^ (-δ) := Real.rpow_pos_of_pos (by norm_num) _
  have h1mQ : 0 ≤ 1 - 1 / (q : ℝ) := by
    have hle : 1 / (q : ℝ) ≤ 1 := by
      rw [div_le_one hQpos]
      linarith
    linarith
  have hρpos : 0 < ρ := by
    rw [hρ]
    exact add_pos_of_pos_of_nonneg hQpow_pos (mul_nonneg h1mQ h2pow_pos.le)
  -- clause 1
  have h1eq : (q : ℝ) * ((q : ℝ) ^ (1 - δ) * Φ) +
      (q.choose 2 : ℝ) * ((2 : ℝ) ^ (1 - δ) * Φ) = ρ * (q : ℝ) ^ 2 * Φ := by
    have hchoose : (q.choose 2 : ℝ) = (q : ℝ) * ((q : ℝ) - 1) / 2 :=
      Nat.cast_choose_two ℝ q
    have hQpow : (q : ℝ) * (q : ℝ) ^ (1 - δ) = (q : ℝ) ^ 2 * (q : ℝ) ^ (-δ) := by
      have h1 : (q : ℝ) * (q : ℝ) ^ (1 - δ) =
          (q : ℝ) ^ (1 : ℝ) * (q : ℝ) ^ (1 - δ) := by rw [Real.rpow_one]
      rw [h1, ← Real.rpow_add hQpos 1 (1 - δ)]
      rw [show (1 : ℝ) + (1 - δ) = 2 + (-δ) by ring]
      simpa [Real.rpow_natCast] using Real.rpow_add hQpos 2 (-δ)
    have h2pow : (2 : ℝ) ^ (1 - δ) = 2 * (2 : ℝ) ^ (-δ) := by
      rw [show (1 : ℝ) - δ = (1 : ℝ) + (-δ) by ring]
      rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2) 1 (-δ), Real.rpow_one]
    rw [hρ, hchoose]
    calc (q : ℝ) * ((q : ℝ) ^ (1 - δ) * Φ) +
          ((q : ℝ) * ((q : ℝ) - 1) / 2) * ((2 : ℝ) ^ (1 - δ) * Φ)
        = Φ * ((q : ℝ) * (q : ℝ) ^ (1 - δ)) +
            Φ * (((q : ℝ) * ((q : ℝ) - 1) / 2) * (2 : ℝ) ^ (1 - δ)) := by ring
      _ = Φ * ((q : ℝ) ^ 2 * (q : ℝ) ^ (-δ)) +
            Φ * (((q : ℝ) * ((q : ℝ) - 1) / 2) * (2 * (2 : ℝ) ^ (-δ))) := by
            rw [hQpow, h2pow]
      _ = ((q : ℝ) ^ (-δ) + (1 - 1 / (q : ℝ)) * (2 : ℝ) ^ (-δ)) * (q : ℝ) ^ 2 * Φ := by
            field_simp
  -- clause 2
  have h2Q : (2 : ℝ) ^ (-δ) * (2 / (q : ℝ)) ^ δ = (q : ℝ) ^ (-δ) := by
    calc (2 : ℝ) ^ (-δ) * (2 / (q : ℝ)) ^ δ
        = (2 : ℝ) ^ (-δ) * ((2 : ℝ) ^ δ / (q : ℝ) ^ δ) := by
            rw [Real.div_rpow (by norm_num : (0 : ℝ) ≤ 2) hQpos.le]
      _ = ((2 : ℝ) ^ (-δ) * (2 : ℝ) ^ δ) / (q : ℝ) ^ δ := by ring
      _ = (2 : ℝ) ^ (-δ + δ) / (q : ℝ) ^ δ := by
            rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      _ = 1 / (q : ℝ) ^ δ := by rw [neg_add_cancel, Real.rpow_zero]
      _ = (q : ℝ) ^ (-δ) := by rw [one_div, Real.rpow_neg hQpos.le]
  have h1mQ_le : 1 - 1 / (q : ℝ) ≤ 1 := by
    have h : 0 < 1 / (q : ℝ) := one_div_pos.mpr hQpos
    linarith
  have h2le : ρ ≤ (2 : ℝ) ^ (-δ) * (1 + (2 / (q : ℝ)) ^ δ) := by
    calc ρ = (q : ℝ) ^ (-δ) + (1 - 1 / (q : ℝ)) * (2 : ℝ) ^ (-δ) := hρ
      _ ≤ (q : ℝ) ^ (-δ) + 1 * (2 : ℝ) ^ (-δ) := by
            exact add_le_add_right
              (mul_le_mul_of_nonneg_right h1mQ_le h2pow_pos.le) _
      _ = (2 : ℝ) ^ (-δ) + (q : ℝ) ^ (-δ) := by ring
      _ = (2 : ℝ) ^ (-δ) * (1 + (2 / (q : ℝ)) ^ δ) := by
            rw [mul_add, mul_one, h2Q]
  -- clause 3
  have h3eq : (ρ * (q : ℝ) ^ 2) ^ (2 * L) = ((q : ℝ) ^ (2 * L)) ^ 2 * ρ ^ (2 * L) := by
    have hQpow2 : ((q : ℝ) ^ 2) ^ (2 * L) = ((q : ℝ) ^ (2 * L)) ^ 2 := by
      rw [← pow_mul, ← pow_mul]
      rw [show 2 * (2 * L) = (2 * L) * 2 by ring]
    rw [mul_pow, hQpow2]
    ring
  -- clause 4
  have h4eq : ((q : ℝ) ^ (2 * L)) ^ 2 * ρ ^ (2 * L) =
      ((q : ℝ) ^ (2 * L)) ^ (2 - Real.logb q (1 / ρ)) := by
    have hApos : 0 < (q : ℝ) ^ (2 * L) := pow_pos hQpos (2 * L)
    have hlogbinv : Real.logb (q : ℝ) (1 / ρ) = -Real.logb (q : ℝ) ρ := by
      rw [one_div, Real.logb_inv]
    have hAexp : ((q : ℝ) ^ (2 * L)) ^ (Real.logb (q : ℝ) ρ) = ρ ^ (2 * L) := by
      rw [← Real.rpow_natCast (q : ℝ) (2 * L)]
      rw [← Real.rpow_mul hQpos.le]
      rw [show ((2 * L : ℕ) : ℝ) * Real.logb (q : ℝ) ρ =
          Real.logb (q : ℝ) ρ * ((2 * L : ℕ) : ℝ) by ring]
      rw [Real.rpow_mul hQpos.le]
      rw [Real.rpow_logb hQpos hQne1 hρpos]
      rw [Real.rpow_natCast]
    rw [hlogbinv]
    rw [show (2 : ℝ) - -Real.logb (q : ℝ) ρ = 2 + Real.logb (q : ℝ) ρ by ring]
    rw [← Real.rpow_natCast ((q : ℝ) ^ (2 * L)) 2]
    rw [Real.rpow_add hApos 2 (Real.logb (q : ℝ) ρ)]
    rw [hAexp]
    rfl
  -- clause 5
  have h5 : (δ - Real.logb 2 (1 + (2 / (q : ℝ)) ^ δ)) / Real.logb 2 (q : ℝ) ≤
      Real.logb (q : ℝ) (1 / ρ) := by
    have hlogQpos : 0 < Real.logb 2 (q : ℝ) :=
      Real.logb_pos (by norm_num : (1 : ℝ) < 2) hQ1
    have hpos2 : 0 < 1 + (2 / (q : ℝ)) ^ δ := by
      have h : 0 ≤ (2 / (q : ℝ)) ^ δ := Real.rpow_nonneg (by positivity) _
      linarith
    have hlogineq : Real.logb 2 ρ ≤ -δ + Real.logb 2 (1 + (2 / (q : ℝ)) ^ δ) := by
      have hmul2 : Real.logb 2 ((2 : ℝ) ^ (-δ) * (1 + (2 / (q : ℝ)) ^ δ)) =
          -δ + Real.logb 2 (1 + (2 / (q : ℝ)) ^ δ) := by
        rw [Real.logb_mul h2pow_pos.ne' hpos2.ne',
          Real.logb_rpow (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)]
      rw [← hmul2]
      exact (Real.logb_le_logb (b := 2) (by norm_num : (1 : ℝ) < 2) hρpos
        (mul_pos h2pow_pos hpos2)).mpr h2le
    have hmul : Real.logb 2 ρ = Real.logb 2 (q : ℝ) * Real.logb (q : ℝ) ρ :=
      (Real.mul_logb hQne hQne1 hQne1').symm
    have hkey : δ - Real.logb 2 (1 + (2 / (q : ℝ)) ^ δ) ≤
        Real.logb 2 (q : ℝ) * Real.logb (q : ℝ) (1 / ρ) := by
      rw [one_div, Real.logb_inv]
      rw [hmul] at hlogineq
      nlinarith
    rw [div_le_iff₀ hlogQpos, mul_comm]
    linarith
  exact ⟨h1eq, h2le, h3eq, h4eq, h5⟩

