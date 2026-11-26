-- Prove2me | solution 1 for NullConeGravity.graviton_pair_cutoff_error
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T19:42:17.290014+00:00
-- url     : https://prove2.me/submissions/b24648e0-2359-4a58-8d13-b1a4c35943a0

import Definitions.Def_NullConeGravity_pairRadialData
import Mathlib.Analysis.PSeries

open NullConeGravity

private lemma norm_pairTerm (s : ℝ) (hs : 0 < s) (k : ℕ) :
    ‖pairTerm s k‖ = (1 / (k + 1 : ℝ) ^ 2) / (2 * s ^ 2) := by
  have hk : 0 < (k : ℝ) + 1 := by positivity
  have hv : 0 ≤ radialVar s k := by unfold radialVar; positivity
  have hphase : ‖Complex.exp (-2 * Complex.I * (k + 1 : ℂ) / (s : ℂ))‖ = 1 := by
    rw [Complex.norm_exp, Complex.div_ofReal_re]
    norm_num [Complex.mul_re, Complex.mul_im]
  rw [pairTerm, norm_mul, hphase, mul_one, norm_mul, norm_pow, Complex.norm_two,
    Complex.norm_of_nonneg hv, radialVar]
  field_simp

/-- Truncating Eq. (4.33) after physical modes 1 through N. Lean index k is mode k + 1. -/
theorem solution (s : ℝ) (hs : 0 < s) (N : ℕ) (hN : 1 ≤ N) :
    ‖pairAmplitude s - ∑ k ∈ Finset.range N, pairTerm s k‖ ≤
      1 / (2 * s ^ 2 * (N : ℝ)) := by
  have hp : Summable (fun k : ℕ => 1 / (k : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hshift : Summable (fun k : ℕ => 1 / (k + 1 : ℝ) ^ 2) := by
    simpa only [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).mpr hp
  have habs : Summable (fun k : ℕ => ‖pairTerm s k‖) :=
    (hshift.div_const (2 * s ^ 2)).congr (fun k => (norm_pairTerm s hs k).symm)
  have hsum : Summable (pairTerm s) := habs.of_norm
  let R (k : ℕ) : ℝ := 1 / (2 * s ^ 2 * (k : ℝ))
  have hstep (k : ℕ) (hk : 0 < k) : ‖pairTerm s k‖ ≤ R k - R (k + 1) := by
    have hk' : 0 < (k : ℝ) := by exact_mod_cast hk
    rw [norm_pairTerm s hs k]
    calc
      _ ≤ (1 / ((k : ℝ) * (k + 1))) / (2 * s ^ 2) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        apply one_div_le_one_div_of_le (by positivity)
        nlinarith
      _ = R k - R (k + 1) := by
        dsimp [R]
        push_cast
        field_simp
        ring
  have hfinite (M : ℕ) :
      ‖∑ j ∈ Finset.range M, pairTerm s (j + N)‖ ≤ R N - R (M + N) := by
    induction M with
    | zero => simp
    | succ M ih =>
      rw [Finset.sum_range_succ]
      calc
        _ ≤ _ := norm_add_le _ _
        _ ≤ (R N - R (M + N)) + (R (M + N) - R (M + N + 1)) :=
          add_le_add ih (hstep (M + N) (by omega))
        _ = _ := by rw [Nat.succ_add]; abel
  have htail := (summable_nat_add_iff N).mpr hsum
  rw [pairAmplitude, ← hsum.sum_add_tsum_nat_add N, add_sub_cancel_left]
  apply le_of_tendsto' htail.hasSum.tendsto_sum_nat.norm
  intro M
  exact (hfinite M).trans (sub_le_self _ (by dsimp [R]; positivity))
