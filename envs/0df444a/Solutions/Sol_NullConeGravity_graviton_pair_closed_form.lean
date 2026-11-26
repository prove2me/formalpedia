-- Prove2me | solution 1 for NullConeGravity.graviton_pair_closed_form
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T18:09:29.32983+00:00
-- url     : https://prove2.me/submissions/e0419bc9-771c-4d2f-af8c-5a4f2de5e6f4

import Definitions.Def_NullConeGravity_dilog
import Definitions.Def_NullConeGravity_pairRadialData
import Mathlib.Analysis.PSeries

open NullConeGravity

private lemma pairTerm_as_power (s : ℝ) (hs : 0 < s) (k : ℕ) :
    pairTerm s k =
      (Complex.exp (-2 * Complex.I / (s : ℂ)) ^ (k + 1) / (k + 1 : ℂ) ^ 2) /
        (2 * (s : ℂ) ^ 2) := by
  have hindex : (k + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  have hscale : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hphase : Complex.exp (-2 * Complex.I * (k + 1 : ℂ) / (s : ℂ)) =
      Complex.exp (-2 * Complex.I / (s : ℂ)) ^ (k + 1) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  unfold pairTerm radialVar
  push_cast
  rw [hphase]
  field_simp [hindex, hscale]

private lemma norm_pairTerm (s : ℝ) (hs : 0 < s) (k : ℕ) :
    ‖pairTerm s k‖ = (1 / (k + 1 : ℝ) ^ 2) / (2 * s ^ 2) := by
  have hphase : ‖Complex.exp (-2 * Complex.I / (s : ℂ))‖ = 1 := by
    rw [Complex.norm_exp, Complex.div_ofReal_re]
    norm_num [Complex.mul_re]
  have hindex : ‖(k + 1 : ℂ)‖ = (k + 1 : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using Complex.norm_natCast (k + 1)
  simp only [pairTerm_as_power s hs k, norm_div, norm_pow, norm_mul, hphase, one_pow,
    hindex, Complex.norm_two, Complex.norm_of_nonneg hs.le]

theorem solution (s : ℝ) (hs : 0 < s) :
    Summable (fun k : ℕ => ‖pairTerm s k‖) ∧
    pairAmplitude s = dilog (Complex.exp (-2 * Complex.I / (s : ℂ))) / (2 * (s : ℂ) ^ 2) := by
  constructor
  · have pSeries : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
      Real.summable_one_div_nat_pow.mpr (by norm_num)
    have shifted : Summable (fun k : ℕ => 1 / (k + 1 : ℝ) ^ 2) := by
      simpa only [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).mpr pSeries
    exact (shifted.div_const (2 * s ^ 2)).congr (fun k => (norm_pairTerm s hs k).symm)
  · unfold pairAmplitude dilog
    simp_rw [pairTerm_as_power s hs]
    exact tsum_div_const
