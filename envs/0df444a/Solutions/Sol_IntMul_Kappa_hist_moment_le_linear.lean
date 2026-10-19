-- Prove2me | solution 1 for IntMul.Kappa.hist_moment_le_linear
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-16T21:40:13.514977+00:00
-- url     : https://prove2.me/submissions/a244f73e-ddbe-4594-bc02-e99dcaa18eaf

import Mathlib
import Definitions.Def_IntMul_KappaFramework

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open IntMul.Kappa

theorem solution (h : List (ℕ × ℕ)) (m : ℕ)
    (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    histMoment h m (1 - a) ≤
      (h.map fun p => (p.2 : ℝ) * ((p.1 : ℝ) / m + a)).sum := by
  induction h with
  | nil =>
      simp [histMoment]
  | cons p ps ih =>
      change
        (p.2 : ℝ) * ((p.1 : ℝ) / m) ^ (1 - a) +
            histMoment ps m (1 - a) ≤
        (p.2 : ℝ) * ((p.1 : ℝ) / m + a) +
            (ps.map fun r => (r.2 : ℝ) * ((r.1 : ℝ) / m + a)).sum
      have hu : 0 ≤ (p.1 : ℝ) / m :=
        div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      have ham :
          ((p.1 : ℝ) / m) ^ (1 - a) * (1 : ℝ) ^ a ≤
          (1 - a) * ((p.1 : ℝ) / m) + a * 1 := by
        exact Real.geom_mean_le_arith_mean2_weighted
          (by linarith) ha0 hu (by norm_num) (by ring)
      have hr :
          ((p.1 : ℝ) / m) ^ (1 - a) ≤ (p.1 : ℝ) / m + a := by
        have hm : 0 ≤ a * ((p.1 : ℝ) / m) := mul_nonneg ha0 hu
        simp only [Real.one_rpow, mul_one] at ham
        nlinarith [hm]
      exact add_le_add
        (mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg _)) ih
