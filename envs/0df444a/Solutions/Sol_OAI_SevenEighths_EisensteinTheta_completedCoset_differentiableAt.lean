-- Prove2me | solution 1 for OAI.SevenEighths.EisensteinTheta.completedCoset_differentiableAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:10:15.870718+00:00
-- url     : https://prove2.me/submissions/97072718-762d-485b-bac8-bd52a36e6f19

import Definitions.Def_OAI_NumberTheory_DirichletL_ThetaProduct
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FieldSimp
import Definitions.Def_OAI_NumberTheory_DirichletL_EisensteinTheta
import Theorems.Thm_OAI_SevenEighths_ThetaProduct_rectangularPair_differentiableAt


set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open MeasureTheory
open OAI.SevenEighths OAI.SevenEighths.EisensteinTheta
open ThetaProduct
namespace OAI.SevenEighths.EisensteinTheta
theorem _root_.solution (a b L : ℝ) (hL : 0 < L)
    {s : ℂ} (hs₀ : s ≠ 0) (hs₁ : s ≠ 1) :
    DifferentiableAt ℂ (completedCoset a b L hL) s := by
  apply DifferentiableAt.fun_sum
  intro e _
  exact rectangularPair_differentiableAt (xShift a b L e) (yShift b L e)
    (L ^ 2) (3 * L ^ 2) _ _ hs₀ hs₁
end OAI.SevenEighths.EisensteinTheta
