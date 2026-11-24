-- Prove2me | solution 1 for MomentComparison.arg_cpow_ofReal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T10:17:40.183249+00:00
-- url     : https://prove2.me/submissions/46aeedee-28db-4fb0-9bd2-f56e581e5075

module
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Definitions.Def_MomentComparison_ComplexPower

set_option autoImplicit true
@[expose] public section
public section
open MomentComparison
namespace MomentComparison
theorem _root_.solution {z : ℂ} (hz : z ≠ 0) {b : ℝ}
    (hl : -Real.pi < z.arg * b) (hu : z.arg * b ≤ Real.pi) :
    (z ^ (b : ℂ)).arg = z.arg * b := by
  rw [Complex.cpow_def_of_ne_zero hz, Complex.arg_exp]
  simp [Complex.mul_im, Complex.log_im, toIocMod_eq_self Real.two_pi_pos (a := -Real.pi),
    show -Real.pi + 2 * Real.pi = Real.pi by ring, hl, hu]
end MomentComparison
