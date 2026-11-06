-- Prove2me | solution 2 for OAI.SevenEighths.CenteredMomentCorrelation.shiftCorrelation_zero
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-05T23:06:37.877847+00:00
-- url     : https://prove2.me/submissions/16b859f7-9b58-47bf-8988-7719f90ef095

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
theorem OA1Aux.character_mul_star {F : Type*} [Field F] [Fintype F] (χ : MulChar F ℂ) {a : F}
    (ha : a ≠ 0) : χ a * star (χ a) = 1 := by
  rw [MulChar.star_apply', ← MulChar.mul_apply, mul_inv_cancel]
  obtain ⟨u, rfl⟩ := Ne.isUnit ha
  exact MulChar.one_apply_coe u

theorem solution (χ : MulChar F ℂ) :
    shiftCorrelation χ 0 = (Fintype.card F : ℂ) - 1 := by
  unfold shiftCorrelation
  calc ∑ x : F, χ x * star (χ (x - 0)) = ∑ x : F, ((1 : ℂ) - if x = 0 then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [sub_zero]
        by_cases hx : x = 0
        · subst hx
          rw [MulChar.map_nonunit χ not_isUnit_zero]
          simp
        · have := OA1Aux.character_mul_star χ hx
          simp only [if_neg hx, sub_zero]
          exact this
    _ = (Fintype.card F : ℂ) - 1 := by
        rw [Finset.sum_sub_distrib]
        simp
