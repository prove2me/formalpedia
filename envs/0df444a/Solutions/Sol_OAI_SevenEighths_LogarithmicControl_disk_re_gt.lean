-- Prove2me | solution 1 for OAI.SevenEighths.LogarithmicControl.disk_re_gt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:14:17.955802+00:00
-- url     : https://prove2.me/submissions/8d2e5f8a-a582-40c6-8762-731979b4927a

import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.Hadamard
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_OAI_NumberTheory_DirichletL_LogarithmicControl

set_option autoImplicit false
open OAI
noncomputable section
open scoped Classical Topology
open Set Filter Metric Complex
open OAI.SevenEighths OAI.SevenEighths.LogarithmicControl
namespace OAI.SevenEighths.LogarithmicControl
theorem _root_.solution {a e t : ℝ} {z : ℂ}
    (hz : z ∈ ball (2 + (t : ℂ) * Complex.I) (2 - a - 2 * e)) :
    a + 2 * e < z.re := by
  have hn : ‖z - (2 + (t : ℂ) * Complex.I)‖ < 2 - a - 2 * e := by
    simpa [mem_ball, dist_eq_norm] using hz
  have hr := Complex.abs_re_le_norm (z - (2 + (t : ℂ) * Complex.I))
  simp only [Complex.sub_re, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.I_re, mul_zero, Complex.ofReal_im,
    Complex.I_im, zero_mul, sub_zero, add_zero] at hr
  norm_num at hr
  linarith [neg_le_abs (z.re - 2)]
end OAI.SevenEighths.LogarithmicControl
