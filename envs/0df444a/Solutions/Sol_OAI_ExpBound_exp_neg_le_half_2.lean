-- Prove2me | solution 2 for OAI.ExpBound.exp_neg_le_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:29:30.3318+00:00
-- url     : https://prove2.me/submissions/5ba0d1b0-ab29-4b9a-9923-0d939ac229c4

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinCoordinates
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_ExponentialSmoothing

set_option autoImplicit false
open OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open OAI.ExpBound
namespace OAI.ExpBound
theorem _root_.solution {t : ℝ} (ht : 1 ≤ t) :
    Real.exp (-t) ≤ (1 : ℝ) / 2 := by
  have he : (2 : ℝ) ≤ Real.exp 1 := by
    nlinarith [Real.add_one_le_exp (1 : ℝ)]
  have hinv : Real.exp (-1) ≤ (1 : ℝ) / 2 := by
    rw [Real.exp_neg]
    simpa only [one_div] using
      (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) he)
  exact (Real.exp_le_exp.mpr (by linarith)).trans hinv
end OAI.ExpBound
