-- Prove2me | solution 1 for MasulloGRH.sobolev_oscillatory_jet_memLp_iff
-- status  : ACCEPTED   (prove)
-- author  : @ghseeli
-- created : 2026-11-21T00:10:31.176811+00:00
-- url     : https://prove2.me/submissions/0ff00db1-92a1-455b-bce6-ecf2bd3718db

import Theorems.Thm_MasulloGRH_sobolev_jet_weight_integrable_iff
import Mathlib.MeasureTheory.Function.L2Space
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped ENNReal

theorem solution (m : ℕ) (τ s : ℝ) (hs : 1 < s) :
    MemLp (fun t : ℝ => ((1 + (Real.log t) ^ 2) ^ (-s / 4) : ℝ) •
      (Complex.exp (((τ * Real.log t : ℝ) : ℂ) * Complex.I) * (Real.log t : ℂ) ^ m))
      2 (Measure.map Real.exp volume) ↔ 2 * (m : ℝ) + 1 < s := by
  have he : MeasurableEmbedding Real.exp := Real.isOpenEmbedding_exp.measurableEmbedding
  rw [he.memLp_map_measure_iff]
  simp only [Function.comp_def, Real.log_exp]
  let v : ℝ → ℂ := fun x => ((1 + x ^ 2) ^ (-s / 4) : ℝ) •
    (Complex.exp (((τ * x : ℝ) : ℂ) * Complex.I) * (x : ℂ) ^ m)
  have hv : Continuous v := by
    have hw : Continuous (fun x : ℝ => (1 + x ^ 2) ^ (-s / 4)) := by
      apply Continuous.rpow_const (by fun_prop)
      intro x
      exact Or.inl (ne_of_gt (by positivity : 0 < 1 + x ^ 2))
    exact hw.smul (by fun_prop)
  change MemLp v 2 volume ↔ _
  rw [memLp_two_iff_integrable_sq_norm hv.aestronglyMeasurable]
  have hnorm : (fun x => ‖v x‖ ^ 2) =
      (fun x : ℝ => x ^ (2 * m) / (1 + x ^ 2) ^ (s / 2)) := by
    funext x
    have hphase : ‖Complex.exp (((τ * x : ℝ) : ℂ) * Complex.I)‖ = 1 := by
      simp [Complex.norm_exp, Complex.mul_re]
    have hp : ‖(x : ℂ) ^ m‖ ^ 2 = x ^ (2 * m) := by
      rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, ← pow_mul,
        Nat.mul_comm m 2, pow_mul, sq_abs, ← pow_mul]
    have hw : ((1 + x ^ 2) ^ (-s / 4)) ^ 2 = 1 / (1 + x ^ 2) ^ (s / 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : 0 ≤ 1 + x ^ 2)]
      norm_num only [Nat.cast_ofNat]
      have hpow : (-s / 4) * (2 : ℝ) = -(s / 2) := by ring
      rw [hpow, Real.rpow_neg (by positivity : 0 ≤ 1 + x ^ 2), one_div]
    dsimp [v]
    rw [norm_mul, norm_mul, hphase, one_mul, mul_pow, hp,
      Complex.norm_real, Real.norm_eq_abs, sq_abs, hw]
    ring
  rw [hnorm]
  exact MasulloGRH.sobolev_jet_weight_integrable_iff m s hs
