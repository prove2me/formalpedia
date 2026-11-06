-- Prove2me | solution 1 for OAI.SevenEighths.CenteredMomentCorrelation.shiftCorrelation_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:44:00.780672+00:00
-- url     : https://prove2.me/submissions/af1712bb-cb46-417a-a3fb-caee5a4ab139

import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.Analysis.Normed.Ring.Finite
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.GroupTheory.Index
import Definitions.Def_OAI_NumberTheory_DirichletL_Moments_Correlation

set_option autoImplicit false
open OAI
open scoped BigOperators Classical
open OAI.SevenEighths OAI.SevenEighths.CenteredMomentCorrelation
noncomputable section
variable {R X Y : Type*} [CommRing R] [Fintype R] [Fintype X] [Fintype Y]
variable {F : Type*} [Field F] [Fintype F]
namespace OAI.SevenEighths.CenteredMomentCorrelation
theorem _root_.solution (χ : MulChar F ℂ) :
    shiftCorrelation χ 1 = χ⁻¹ (-1) * jacobiSum χ χ⁻¹ := by
  simp only [shiftCorrelation, jacobiSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [MulChar.star_apply', show x - 1 = (-1) * (1 - x) by ring, map_mul]
  ring
end OAI.SevenEighths.CenteredMomentCorrelation
