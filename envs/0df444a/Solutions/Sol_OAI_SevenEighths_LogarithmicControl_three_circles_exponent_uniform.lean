-- Prove2me | solution 1 for OAI.SevenEighths.LogarithmicControl.three_circles_exponent_uniform
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:53:00.988194+00:00
-- url     : https://prove2.me/submissions/a646d500-e696-4125-8a4b-f01c8caa3afc

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
theorem _root_.solution {a e : ℝ}
    (ha : 1 / 2 ≤ a) (ha' : a ≤ 1) (he : 0 < e) (he' : e < 1 / 1000) :
    (Real.log (2 - a - 6 * e) - Real.log (49 / 100)) /
      (Real.log (2 - a - 4 * e) - Real.log (49 / 100)) ≤ uniformTheta e := by
  have hr : (0 : ℝ) < 49 / 100 := by norm_num
  have h6 : (49 / 100 : ℝ) < 2 - a - 6 * e := by linarith
  have h4 : (49 / 100 : ℝ) < 2 - a - 4 * e := by linarith
  have h6p : 0 < 2 - a - 6 * e := hr.trans h6
  have h4p : 0 < 2 - a - 4 * e := hr.trans h4
  have hep : 0 < 1 + e := by linarith
  have hD : 0 < Real.log (2 - a - 4 * e) - Real.log (49 / 100) :=
    sub_pos.mpr (Real.log_lt_log hr h4)
  have hU : 0 < Real.log (200 / 49) := Real.log_pos (by norm_num)
  have hDU : Real.log (2 - a - 4 * e) - Real.log (49 / 100) ≤
      Real.log (200 / 49) := by
    rw [← Real.log_div h4p.ne' hr.ne']
    apply Real.log_le_log (div_pos h4p hr)
    apply (div_le_iff₀ hr).mpr
    norm_num
    linarith
  have hprod : (2 - a - 6 * e) * (1 + e) ≤ 2 - a - 4 * e := by
    have : 2 - a - 6 * e ≤ 2 := by linarith
    nlinarith
  have hdiff : Real.log (1 + e) ≤ Real.log (2 - a - 4 * e) -
      Real.log (2 - a - 6 * e) := by
    have h := Real.log_le_log (mul_pos h6p hep) hprod
    rw [Real.log_mul h6p.ne' hep.ne'] at h
    linarith
  have hfrac : Real.log (1 + e) / Real.log (200 / 49) ≤
      (Real.log (2 - a - 4 * e) - Real.log (2 - a - 6 * e)) /
      (Real.log (2 - a - 4 * e) - Real.log (49 / 100)) := by
    gcongr
    exact (Real.log_pos (by linarith : 1 < 1 + e)).le.trans hdiff
  calc
    _ = 1 - (Real.log (2 - a - 4 * e) - Real.log (2 - a - 6 * e)) /
        (Real.log (2 - a - 4 * e) - Real.log (49 / 100)) := by
      apply eq_sub_iff_add_eq.mpr
      rw [← add_div]
      convert div_self hD.ne' using 1
      ring
    _ ≤ uniformTheta e := sub_le_sub_left hfrac 1
end OAI.SevenEighths.LogarithmicControl
