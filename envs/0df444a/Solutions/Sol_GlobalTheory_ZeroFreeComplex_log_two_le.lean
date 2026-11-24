-- Prove2me | solution 1 for GlobalTheory.ZeroFreeComplex.log_two_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:20:07.073952+00:00
-- url     : https://prove2.me/submissions/a7d41478-1db3-4d10-a181-78fb8f3b4947

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivativeBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NegSumLogDerivNonneg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivDirichletLFunctionLocalZeroSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NegReLogDerivPrincipalLFunctionLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LFunctionConjEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open scoped ComplexConjugate
open GlobalTheory GlobalTheory.ZeroFreeComplex
namespace GlobalTheory.ZeroFreeComplex
theorem _root_.solution (q : ℕ) [NeZero q] (t : ℝ) :
    Real.log (q * (|2 * t| + 2)) ≤ 2 * Real.log (q * (|t| + 2)) := by
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have ht := abs_nonneg t
  rw [show (2 : ℝ) * Real.log (q * (|t| + 2)) = Real.log ((q * (|t| + 2)) ^ 2) by
    rw [Real.log_pow]; norm_num]
  apply Real.log_le_log (by positivity)
  rw [abs_mul, abs_two]
  have h1 : (q : ℝ) ≤ q * q := by nlinarith
  have h2 : 2 * |t| + 2 ≤ (|t| + 2) * (|t| + 2) := by nlinarith
  calc (q : ℝ) * (2 * |t| + 2) ≤ (q * q) * ((|t| + 2) * (|t| + 2)) :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = (q * (|t| + 2)) ^ 2 := by ring
end GlobalTheory.ZeroFreeComplex
