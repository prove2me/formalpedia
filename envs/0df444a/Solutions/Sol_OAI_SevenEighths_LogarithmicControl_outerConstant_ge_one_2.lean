-- Prove2me | solution 2 for OAI.SevenEighths.LogarithmicControl.outerConstant_ge_one
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-05T22:48:42.622558+00:00
-- url     : https://prove2.me/submissions/62d3a9aa-b97f-46ed-9fcd-4994938296d3

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

theorem solution {e A M : ℝ} (he : 0 < e) (he' : e < 1 / 1000)
    (hA : 1 ≤ A) (hM : 1 ≤ M) : 1 ≤ outerConstant e A M := by
  unfold outerConstant
  rw [le_div_iff₀ he]
  linarith
