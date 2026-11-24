-- Prove2me | solution 1 for GlobalTheory.LogDerivZeros.norm_one_sub_conj_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:50:17.791828+00:00
-- url     : https://prove2.me/submissions/311e464a-26d5-4aaf-abb5-2e28925f0f65

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsFactorOrder
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NormOneSubConjMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory GlobalTheory.LogDerivZeros
namespace GlobalTheory.LogDerivZeros
theorem _root_.solution {w z : ℂ} (hz : ‖z‖ = 1) :
    ‖1 - (starRingEnd ℂ) w * z‖ = ‖z - w‖ := by
  have h1 : (starRingEnd ℂ) z * z = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]; simp
  have : 1 - (starRingEnd ℂ) w * z = (starRingEnd ℂ) (z - w) * z := by
    rw [map_sub, sub_mul, h1]
  rw [this, norm_mul, hz, mul_one, Complex.norm_conj]
end GlobalTheory.LogDerivZeros
