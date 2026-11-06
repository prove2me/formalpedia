-- Prove2me | solution 1 for OAI.ShortDraftMellin.mobius_char_exp_summable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:51:03.533959+00:00
-- url     : https://prove2.me/submissions/c3bf323b-4c42-44d7-95c2-544c41d42862

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
namespace OAI.ShortDraftMellin
theorem _root_.solution
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (t : ℝ) (ht : 0 < t) :
    Summable (fun n : ℕ =>
      χ n * (ArithmeticFunction.moebius n : ℂ) *
        Real.exp (-(n : ℝ) * t)) := by
  have hexp : Summable (fun n : ℕ => Real.exp (-(n : ℝ) * t)) := by
    convert (Real.summable_exp_nat_mul_iff.mpr (neg_lt_zero.mpr ht)) using 1
    ext n
    congr 1
    ring
  apply hexp.of_norm_bounded
  intro n
  rw [norm_mul, norm_mul]
  simp only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  have hχ : ‖χ n‖ ≤ 1 := χ.norm_le_one _
  have hμ : ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))
  have hprod : ‖χ n‖ * ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hχ)
      (norm_nonneg ((ArithmeticFunction.moebius n : ℂ))),
      mul_nonneg (sub_nonneg.mpr hμ) (norm_nonneg (χ n))]
  nlinarith [mul_nonneg (sub_nonneg.mpr hprod)
    (le_of_lt (Real.exp_pos (-(n : ℝ) * t)))]
end OAI.ShortDraftMellin
