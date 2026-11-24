-- Prove2me | solution 1 for GlobalTheory.ZeroFreeComplex.re_one_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:20:09.508919+00:00
-- url     : https://prove2.me/submissions/f099fea0-8fd1-4f4f-a217-f188fc2f9718

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
theorem _root_.solution (a b : ℝ) : (1 / ((a : ℂ) + b * I)).re = a / (a ^ 2 + b ^ 2) := by
  rw [Complex.div_re, Complex.normSq_apply]
  simp
  ring
end GlobalTheory.ZeroFreeComplex
