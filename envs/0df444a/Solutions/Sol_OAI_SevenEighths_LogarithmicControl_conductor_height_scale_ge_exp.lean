-- Prove2me | solution 1 for OAI.SevenEighths.LogarithmicControl.conductor_height_scale_ge_exp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:14:16.87018+00:00
-- url     : https://prove2.me/submissions/1266feb7-0bb7-4fc7-aa3e-cabbc71d07b9

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
theorem _root_.solution (Q t : ℝ) (hQ : 1 ≤ Q) :
    Real.exp 1 ≤ 2 * Q * (3 + |t|) ^ 2 := by
  have hs : 9 ≤ (3 + |t|) ^ 2 := by nlinarith [abs_nonneg t]
  have hq := mul_le_mul_of_nonneg_right hQ (sq_nonneg (3 + |t|))
  nlinarith [Real.exp_one_lt_three]
end OAI.SevenEighths.LogarithmicControl
