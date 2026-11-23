-- Prove2me | solution 1 for GlobalTheory.PrincipalLogDeriv.norm_cpow_neg_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:44:13.215853+00:00
-- url     : https://prove2.me/submissions/3be674d5-f7cb-496a-81d4-cc4b0ba8fe1e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivRiemannZetaLocalZeroSumStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NegReLogDerivPrincipalLFunctionLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory GlobalTheory.PrincipalLogDeriv
namespace GlobalTheory.PrincipalLogDeriv
theorem _root_.solution {p : ℕ} (hp : p.Prime) {s : ℂ} (hs : 1 ≤ s.re) :
    ‖(p : ℂ) ^ (-s)‖ ≤ 1 / 2 := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  rw [Complex.norm_natCast_cpow_of_pos hp.pos, Complex.neg_re]
  calc (p : ℝ) ^ (-s.re) ≤ (p : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
    _ = 1 / p := by rw [Real.rpow_neg_one, one_div]
    _ ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
end GlobalTheory.PrincipalLogDeriv
