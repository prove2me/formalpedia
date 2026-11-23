-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ExplZeta.LeftShift.norm_quot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:16:13.052575+00:00
-- url     : https://prove2.me/submissions/8131b966-9d9e-4865-a04e-8c6dbd719d22

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
theorem _root_.solution {g s : ℂ} {x : ℝ} (hx : 2 ≤ x) :
    ‖g * (x : ℂ) ^ s / s‖ = ‖g‖ * x ^ s.re / ‖s‖ := by
  rw [norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
end GlobalTheory.CompanionTheory.ExplZeta.LeftShift
