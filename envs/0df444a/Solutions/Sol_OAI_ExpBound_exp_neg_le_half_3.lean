-- Prove2me | solution 3 for OAI.ExpBound.exp_neg_le_half
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-05T23:06:14.466102+00:00
-- url     : https://prove2.me/submissions/f40755c7-077d-4a9c-ad97-77f0d5033e0c

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
theorem solution {t : ℝ} (ht : 1 ≤ t) :
    Real.exp (-t) ≤ (1 : ℝ) / 2 := by
  have h1 : Real.exp (-t) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
  have h2 : (2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h3 : (Real.exp 1)⁻¹ < 2⁻¹ := inv_strictAnti₀ (by norm_num) h2
  rw [Real.exp_neg 1] at h1
  have h4 : (2 : ℝ)⁻¹ = 1 / 2 := by norm_num
  linarith
