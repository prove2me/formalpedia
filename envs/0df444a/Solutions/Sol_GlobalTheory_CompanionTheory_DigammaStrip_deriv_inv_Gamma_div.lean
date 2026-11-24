-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DigammaStrip.deriv_inv_Gamma_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:26:26.314997+00:00
-- url     : https://prove2.me/submissions/13bd644c-28dc-4a0d-a038-187c0ca6480a

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
theorem _root_.solution {z : ℂ} (hz : 0 < z.re) :
    deriv (fun w => (Complex.Gamma w)⁻¹) z / (Complex.Gamma z)⁻¹ = -digamma z := by
  have hG : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hz
  have hd : DifferentiableAt ℂ Complex.Gamma z := Complex.differentiableAt_Gamma z (fun m h => by
    have := congrArg Complex.re h
    simp at this
    have h2 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith)
  have h7 : HasDerivAt (fun w => (Complex.Gamma w)⁻¹)
      (-deriv Complex.Gamma z / Complex.Gamma z ^ 2) z := hd.hasDerivAt.inv hG
  rw [h7.deriv, Complex.digamma_def, logDeriv_apply]
  field_simp
end GlobalTheory.CompanionTheory.DigammaStrip
