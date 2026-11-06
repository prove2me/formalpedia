-- Prove2me | solution 1 for OAI.SevenEighths.CenteredMomentCorrelation.localCorrelation_second_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:27:53.755927+00:00
-- url     : https://prove2.me/submissions/2ffe9e1c-8ef2-4662-8468-0b6473b31bfe

import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.Analysis.Normed.Ring.Finite
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.GroupTheory.Index
import Definitions.Def_OAI_NumberTheory_DirichletL_Moments_Correlation
import Theorems.Thm_OAI_SevenEighths_CenteredMomentCorrelation_character_sum

set_option autoImplicit false
open OAI
open scoped BigOperators Classical
open OAI.SevenEighths OAI.SevenEighths.CenteredMomentCorrelation
noncomputable section
variable {R X Y : Type*} [CommRing R] [Fintype R] [Fintype X] [Fintype Y]
variable {F : Type*} [Field F] [Fintype F]
namespace OAI.SevenEighths.CenteredMomentCorrelation
theorem _root_.solution (χ : MulChar F ℂ) {n₁ : F} (h₁ : n₁ ≠ 0) (k : F) :
    localCorrelation χ n₁ 0 k =
      if χ = 1 ∧ k ≠ 0 then (Fintype.card F : ℂ) - 1 else 0 := by
  classical
  have hsolve (y : F) : -(n₁ * y) = k ↔ y = -k / n₁ := by
    rw [eq_div_iff h₁]
    constructor <;> intro h <;> linear_combination -h
  have hsum : localCorrelation χ n₁ 0 k = (∑ x : F, χ x) * star (χ (-k / n₁)) := by
    unfold localCorrelation fullCorrelation
    simp only [zero_mul, zero_sub, hsolve, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
      ← Finset.sum_mul]
  rw [hsum, character_sum]
  by_cases hχ : χ = 1
  · subst χ
    by_cases hk : k = 0
    · simp [hk, MulChar.map_zero]
    · rw [MulChar.one_apply (isUnit_iff_ne_zero.mpr (div_ne_zero (neg_ne_zero.mpr hk) h₁))]
      simp [hk]
  · simp [hχ]
end OAI.SevenEighths.CenteredMomentCorrelation
