-- Prove2me | solution 1 for OAI.SevenEighths.LogarithmicControl.uniformTheta_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:53:00.341133+00:00
-- url     : https://prove2.me/submissions/f8047a8f-cc85-4f43-88d1-c2e586a6cf0f

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
theorem _root_.solution {e : ℝ} (he : 0 < e) (he' : e < 1 / 1000) :
    0 < uniformTheta e ∧ uniformTheta e < 1 := by
  have hD : 0 < Real.log (200 / 49) := Real.log_pos (by norm_num)
  have hn : 0 < Real.log (1 + e) := Real.log_pos (by linarith)
  have hnD : Real.log (1 + e) < Real.log (200 / 49) :=
    Real.log_lt_log (by linarith) (by linarith)
  unfold uniformTheta
  constructor
  · linarith [(div_lt_one hD).mpr hnD]
  · linarith [div_pos hn hD]
end OAI.SevenEighths.LogarithmicControl
