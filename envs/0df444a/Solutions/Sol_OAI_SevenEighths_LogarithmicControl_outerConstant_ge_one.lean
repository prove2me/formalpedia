-- Prove2me | solution 1 for OAI.SevenEighths.LogarithmicControl.outerConstant_ge_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:22:49.332412+00:00
-- url     : https://prove2.me/submissions/c4aa2ef5-caa1-408c-968f-be7ffef06169

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
theorem _root_.solution {e A M : ℝ} (he : 0 < e) (he' : e < 1 / 1000)
    (hA : 1 ≤ A) (hM : 1 ≤ M) : 1 ≤ outerConstant e A M := by
  unfold outerConstant
  apply (le_div_iff₀ he).mpr
  nlinarith
end OAI.SevenEighths.LogarithmicControl
