-- Prove2me | solution 1 for Kyprianou.Ch03.stableNonnegativeOfBoundedNegExpV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T21:47:46.490802+00:00
-- url     : https://prove2.me/submissions/49000b24-6e46-4136-8114-63a11e279ba2

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P] (Y : Omega → ℝ)
    (hY : AEMeasurable Y P)
    (hi : ∀ n : ℕ, Integrable (fun w => Real.exp (-(n : ℝ) * Y w)) P)
    (hb : ∀ n : ℕ, (∫ w, Real.exp (-(n : ℝ) * Y w) ∂P) ≤ 1) :
    ∀ᵐ w ∂P, 0 ≤ Y w := by
  let Z : Omega → ℝ := hY.mk Y
  have hz : Measurable Z := hY.measurable_mk
  have heq : Y =ᵐ[P] Z := hY.ae_eq_mk
  have hnull (m : ℕ) : P {w | Z w ≤ -(1 / ((m : ℝ) + 1))} = 0 := by
    let a : ℝ := 1 / ((m : ℝ) + 1)
    have ha : 0 < a := by dsimp [a]; positivity
    let B : Set Omega := {w | Z w ≤ -a}
    have hB : MeasurableSet B := measurableSet_le hz measurable_const
    change P B = 0
    by_contra hne
    have hpos : 0 < (P B).toReal := ENNReal.toReal_pos hne (measure_ne_top P B)
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / ((P B).toReal * a))
    let g : Omega → ℝ := B.indicator (fun _ => (n:ℝ) * a)
    have hg : Integrable g P := (integrable_indicator_iff hB).mpr (integrable_const _)
    have hle : (∫ w, g w ∂P) ≤ ∫ w, Real.exp (-(n:ℝ) * Y w) ∂P := by
      apply integral_mono_ae hg (hi n)
      filter_upwards [heq] with w hw
      by_cases hmem : w ∈ B
      · dsimp [g]; rw [indicator_of_mem hmem, hw]
        have hh : Z w ≤ -a := hmem
        have hh' := mul_le_mul_of_nonpos_left hh (neg_nonpos.mpr (Nat.cast_nonneg n))
        linarith [Real.add_one_le_exp (-(n:ℝ)*Z w)]
      · dsimp [g]; rw [indicator_of_notMem hmem]
        exact (Real.exp_pos _).le
    have hle' := hle.trans (hb n)
    dsimp [g] at hle'
    rw [integral_indicator hB, integral_const, smul_eq_mul,
      Measure.real, Measure.restrict_apply_univ] at hle'
    have hgt := (div_lt_iff₀ (mul_pos hpos ha)).mp hn
    nlinarith
  have hae (m : ℕ) : ∀ᵐ w ∂P, -(1 / ((m : ℝ) + 1)) < Z w := by
    rw [ae_iff]
    simpa only [not_lt] using hnull m
  filter_upwards [ae_all_iff.mpr hae, heq] with w hw he
  rw [he]
  by_contra! h
  obtain ⟨m, hm⟩ := exists_nat_gt (1 / (-Z w))
  have hh := (div_lt_iff₀ (neg_pos.mpr h)).mp hm
  have hdiv : 1 / ((m : ℝ) + 1) < -Z w := by
    apply (div_lt_iff₀ (by positivity)).mpr
    nlinarith
  linarith [hw m]
