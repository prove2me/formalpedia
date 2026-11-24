-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DigammaStrip.norm_sin_le_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:28:51.955325+00:00
-- url     : https://prove2.me/submissions/61703aa4-4ce4-46de-90c0-25d0387f5ee1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivLFunctionStrip
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LGrowthGamma
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_DigammaBoundVerticalStrip

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DigammaStrip
namespace GlobalTheory.CompanionTheory.DigammaStrip
theorem _root_.solution (u : ℂ) : ‖Complex.sin u‖ ≤ Real.exp |u.im| := by
  have h1 : ‖Complex.exp (-u * I)‖ ≤ Real.exp |u.im| := by
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.2 (by simpa using le_abs_self u.im)
  have h2 : ‖Complex.exp (u * I)‖ ≤ Real.exp |u.im| := by
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.2 (by simpa using neg_le_abs u.im)
  rw [Complex.sin, norm_div, norm_mul, Complex.norm_I, mul_one]
  have h3 := norm_sub_le (Complex.exp (-u * I)) (Complex.exp (u * I))
  simp only [Complex.norm_ofNat]
  linarith
end GlobalTheory.CompanionTheory.DigammaStrip
