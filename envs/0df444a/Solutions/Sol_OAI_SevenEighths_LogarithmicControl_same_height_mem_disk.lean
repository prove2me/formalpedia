-- Prove2me | solution 1 for OAI.SevenEighths.LogarithmicControl.same_height_mem_disk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:14:18.478716+00:00
-- url     : https://prove2.me/submissions/53587eac-19c4-4f58-b9ad-4772fd4c718a

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
theorem _root_.solution {a e t v x : ℝ} (hev : 8 * e ≤ v)
    (hx : a + v ≤ x) (hx' : x ≤ 2) :
    (x : ℂ) + (t : ℂ) * Complex.I ∈
      closedBall (2 + (t : ℂ) * Complex.I) (2 - a - 8 * e) := by
  rw [mem_closedBall, dist_eq_norm]
  have heq : (x : ℂ) + (t : ℂ) * Complex.I - (2 + (t : ℂ) * Complex.I) =
      ((x - 2 : ℝ) : ℂ) := by push_cast; ring
  rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith : x - 2 ≤ 0)]
  linarith
end OAI.SevenEighths.LogarithmicControl
