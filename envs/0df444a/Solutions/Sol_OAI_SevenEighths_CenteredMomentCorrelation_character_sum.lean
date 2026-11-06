-- Prove2me | solution 1 for OAI.SevenEighths.CenteredMomentCorrelation.character_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:44:09.432865+00:00
-- url     : https://prove2.me/submissions/5c57ab43-5940-403a-b76c-0845cd74cd41

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
    (∑ x : F, χ x) = if χ = 1 then (Fintype.card F : ℂ) - 1 else 0 := by
  classical
  by_cases hχ : χ = 1
  · subst χ
    rw [MulChar.sum_one_eq_card_units, Fintype.card_eq_card_units_add_one (α := F)]
    simp
  · simp [hχ, MulChar.sum_eq_zero_of_ne_one hχ]
end OAI.SevenEighths.CenteredMomentCorrelation
