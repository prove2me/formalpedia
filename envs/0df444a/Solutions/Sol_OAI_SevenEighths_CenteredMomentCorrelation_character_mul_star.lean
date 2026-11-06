-- Prove2me | solution 1 for OAI.SevenEighths.CenteredMomentCorrelation.character_mul_star
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:27:49.287307+00:00
-- url     : https://prove2.me/submissions/e0d24704-cbc3-4fb0-a825-fc9aed6648f5

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
theorem _root_.solution (χ : MulChar F ℂ) {a : F} (ha : a ≠ 0) :
    χ a * star (χ a) = 1 := by
  rw [MulChar.star_apply', MulChar.inv_apply_eq_inv']
  exact mul_inv_cancel₀ (χ.apply_ne_zero_iff.mpr (isUnit_iff_ne_zero.mpr ha))
end OAI.SevenEighths.CenteredMomentCorrelation
