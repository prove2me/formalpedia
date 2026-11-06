-- Prove2me | solution 1 for OAI.ShortDraftMellin.mobiusExpSum_norm_le_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:31:25.213198+00:00
-- url     : https://prove2.me/submissions/0afc4ad6-4a2d-4315-878a-82855f8bae97

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinCoordinates
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_ExponentialSmoothing
import Theorems.Thm_OAI_ExpBound_norm_tsum_exp_le_two
import Theorems.Thm_OAI_ShortDraftMellin_mobius_char_exp_summable

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
    (t : ℝ) (ht : 1 ≤ t) :
    ‖mobiusExpSum χ t‖ ≤ 2 * Real.exp (-t) := by
  have hcoeff (n : ℕ) :
      ‖χ n * (ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
    rw [norm_mul]
    have hχ : ‖χ n‖ ≤ 1 := χ.norm_le_one _
    have hμ : ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]
      exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))
    nlinarith [mul_nonneg (sub_nonneg.mpr hχ)
      (norm_nonneg ((ArithmeticFunction.moebius n : ℂ))),
      mul_nonneg (sub_nonneg.mpr hμ) (norm_nonneg (χ n))]
  exact ExpBound.norm_tsum_exp_le_two
    (fun n => χ n * (ArithmeticFunction.moebius n : ℂ))
    (by simp) hcoeff t ht
    (mobius_char_exp_summable χ t (lt_of_lt_of_le zero_lt_one ht))
end OAI.ShortDraftMellin
