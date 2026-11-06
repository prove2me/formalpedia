-- Prove2me | solution 1 for OAI.ExpBound.exp_neg_le_half
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T21:57:56.471006+00:00
-- url     : https://prove2.me/submissions/1ac09ac7-1c1c-4720-ac01-a3284ab20f4e

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
  rw [Real.exp_neg, ← one_div]
  apply (div_le_div_iff₀ (Real.exp_pos t) (by norm_num : (0 : ℝ) < 2)).2
  nlinarith [Real.add_one_le_exp t]
