-- Prove2me | solution 1 for GoodmanWitten.eq6_strong_rate
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T04:51:21.636948+00:00
-- url     : https://prove2.me/submissions/cea8007a-b710-42f8-90fd-f20c8bb88a5f

import Mathlib
import Definitions.Def_GoodmanWitten_basic
open GoodmanWitten

theorem solution : ∃ C : ℝ, |C / 1.15e14 - 1| ≤ 0.05 ∧
    ∀ A MX ε ρ v : ℝ, 0 < A → 0 < MX →
      strongEventRate A MX ε ρ v =
        C * A ^ (-(1 : ℝ) / 3) * ε * (1 / MX) * (ρ / 1e-24) * (v / 2e7) := by
  refine ⟨6.0e26 * secondsPerDay * 4 * Real.pi * 1.25 ^ 2 * 1e-26 * 1e-24 * 2e7 / gramsPerGeV,
    ?_, ?_⟩
  · have p1 := Real.pi_gt_d6
    have p2 := Real.pi_lt_d6
    unfold secondsPerDay gramsPerGeV
    rw [abs_le]
    constructor
    · rw [le_sub_iff_add_le, le_div_iff₀ (by norm_num), le_div_iff₀ (by norm_num)]; nlinarith
    · rw [sub_le_iff_le_add, div_le_iff₀ (by norm_num), div_le_iff₀ (by norm_num)]; nlinarith
  · intro A MX ε ρ v hA hMX
    unfold strongEventRate eventRatePerKgDay strongCrossSection nuclearRadius targetNucleiPerKg
    have h : (A ^ ((1 : ℝ) / 3)) ^ 2 = A * A ^ (-(1 : ℝ) / 3) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hA.le,
        show A * A ^ (-(1 : ℝ) / 3) = A ^ (1 + (-(1 : ℝ) / 3)) by rw [Real.rpow_add hA, Real.rpow_one]]
      norm_num
    have hg : 0 < gramsPerGeV := by unfold gramsPerGeV; norm_num
    rw [mul_pow, mul_pow, h]
    field_simp
    ring
