-- Prove2me | solution 2 for OAI.ShortDraftMellin.mobiusExpSum_norm_le_two
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-05T22:48:49.197794+00:00
-- url     : https://prove2.me/submissions/387b4eb6-3101-4bec-b4a2-1e3a1041d5ec

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinCoordinates
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_ExponentialSmoothing
set_option autoImplicit false
open OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open OAI.ShortDraftMellin

theorem solution
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (t : ℝ) (ht : 1 ≤ t) :
    ‖mobiusExpSum χ t‖ ≤ 2 * Real.exp (-t) := by
  set r : ℝ := Real.exp (-t) with hr
  have hr0 : 0 < r := Real.exp_pos _
  have hr2 : r ≤ 1 / 2 := by
    have h1 : Real.exp (-t) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
    have h2 : Real.exp (-1) = (Real.exp 1)⁻¹ := Real.exp_neg 1
    have h3 : (2 : ℝ) < Real.exp 1 := by
      have := Real.exp_one_gt_d9
      linarith
    calc r ≤ Real.exp (-1) := h1
      _ = (Real.exp 1)⁻¹ := h2
      _ ≤ 1 / 2 := by
        rw [one_div]
        exact inv_anti₀ (by norm_num) h3.le
  have hr1 : r < 1 := by linarith
  have hbound : ∀ n : ℕ,
      ‖χ n * (ArithmeticFunction.moebius n : ℂ) * (Real.exp (-(n : ℝ) * t) : ℂ)‖ ≤ r ^ n := by
    intro n
    have h1 : ‖χ n‖ ≤ 1 := DirichletCharacter.norm_le_one χ n
    have h2 : ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]
      have := ArithmeticFunction.abs_moebius_le_one (n := n)
      exact_mod_cast this
    have h3 : ‖(Real.exp (-(n : ℝ) * t) : ℂ)‖ = r ^ n := by
      rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, hr, ← Real.exp_nat_mul]
      congr 1
      ring
    rw [norm_mul, norm_mul, h3]
    have h4 : 0 ≤ r ^ n := by positivity
    calc ‖χ n‖ * ‖(ArithmeticFunction.moebius n : ℂ)‖ * r ^ n ≤ 1 * 1 * r ^ n := by
          gcongr
      _ = r ^ n := by ring
  have hsum : Summable (fun n : ℕ =>
      χ n * (ArithmeticFunction.moebius n : ℂ) * (Real.exp (-(n : ℝ) * t) : ℂ)) :=
    Summable.of_norm_bounded (summable_geometric_of_lt_one hr0.le hr1) hbound
  unfold mobiusExpSum
  rw [hsum.tsum_eq_zero_add]
  have h0 : χ ((0 : ℕ) : ZMod q) * (ArithmeticFunction.moebius (0 : ℕ) : ℂ) *
      (Real.exp (-((0 : ℕ) : ℝ) * t) : ℂ) = 0 := by
    simp
  rw [h0, zero_add]
  have hg : HasSum (fun n : ℕ => r * r ^ n) (r * (1 - r)⁻¹) :=
    (hasSum_geometric_of_lt_one hr0.le hr1).mul_left r
  have h5 := tsum_of_norm_bounded hg (f := fun n : ℕ =>
      χ ((n + 1 : ℕ) : ZMod q) * (ArithmeticFunction.moebius (n + 1) : ℂ) *
        (Real.exp (-((n + 1 : ℕ) : ℝ) * t) : ℂ)) (fun n => by
    have := hbound (n + 1)
    rw [pow_succ] at this
    linarith [mul_comm (r ^ n) r])
  refine h5.trans ?_
  rw [← div_eq_mul_inv, div_le_iff₀ (by linarith : 0 < 1 - r)]
  nlinarith
