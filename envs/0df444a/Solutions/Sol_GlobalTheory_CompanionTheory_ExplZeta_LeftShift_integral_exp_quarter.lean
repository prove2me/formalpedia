-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ExplZeta.LeftShift.integral_exp_quarter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:29:59.189263+00:00
-- url     : https://prove2.me/submissions/d21242b5-a462-49af-956b-2abb400db27a

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_IntegralLeftVerticalLineBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ExplZeta GlobalTheory.CompanionTheory.ExplZeta.LeftShift
namespace GlobalTheory.CompanionTheory.ExplZeta.LeftShift
theorem _root_.solution {R : ℝ} :
    ∫ σ : ℝ in (-R)..(-(1 / 2)), Real.exp (σ / 4)
      = 4 * (Real.exp (-(1 / 2) / 4) - Real.exp (-R / 4)) := by
  have hd : ∀ σ ∈ Set.uIcc (-R) (-(1 / 2) : ℝ),
      HasDerivAt (fun σ : ℝ => 4 * Real.exp (σ / 4)) (Real.exp (σ / 4)) σ := by
    intro σ _
    have h := ((hasDerivAt_id' σ).div_const 4).exp.const_mul 4
    exact h.congr_deriv (by ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((Real.continuous_exp.comp (continuous_id.div_const 4)).intervalIntegrable _ _)]
  ring
end GlobalTheory.CompanionTheory.ExplZeta.LeftShift
