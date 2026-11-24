-- Prove2me | solution 1 for GlobalTheory.WpFam.RowsSummed.norm_q_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:17:59.138507+00:00
-- url     : https://prove2.me/submissions/31fc269d-4cfc-4545-a4af-890b6601cb3b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZetaActRefl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasSumLambertDoubleSeriesDivisorsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TsumResidueClassSplitBySignStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TorsionPointRowSumEqQExpansionSeriesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TorsionPointRowsSumEqDivisorSeries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam
open GlobalTheory GlobalTheory.WpFam GlobalTheory.WpFam.RowsSummed
namespace GlobalTheory.WpFam.RowsSummed
theorem _root_.solution (N : ℕ) [NeZero N] (τ : ℍ) :
    ‖Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * τ / N)‖ < 1 := by
  rw [Complex.norm_exp, show (1 : ℝ) = Real.exp 0 from Real.exp_zero.symm, Real.exp_lt_exp]
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hτ := τ.im_pos
  have : ((2 * (Real.pi : ℂ) * Complex.I) * τ / N).re = -(2 * Real.pi * τ.im) / N := by
    simp [Complex.div_re, Complex.mul_re, Complex.mul_im]
    field_simp
  rw [this]
  apply div_neg_of_neg_of_pos _ hN
  have := Real.pi_pos
  nlinarith
end GlobalTheory.WpFam.RowsSummed
