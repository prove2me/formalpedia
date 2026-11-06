-- Prove2me | solution 1 for OAI.SevenEighths.CenteredMomentCorrelation.localCorrelation_first_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:27:52.988278+00:00
-- url     : https://prove2.me/submissions/499e7a0a-4bfd-418d-b551-dc2898b8d177

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
theorem _root_.solution (χ : MulChar F ℂ) {n₂ : F} (h₂ : n₂ ≠ 0) (k : F) :
    localCorrelation χ 0 n₂ k =
      if χ = 1 ∧ k ≠ 0 then (Fintype.card F : ℂ) - 1 else 0 := by
  classical
  have hsolve (x : F) : n₂ * x = k ↔ x = k / n₂ := by
    rw [eq_div_iff h₂, mul_comm]
  have hsum : localCorrelation χ 0 n₂ k = χ (k / n₂) * star (∑ y : F, χ y) := by
    unfold localCorrelation fullCorrelation
    simp only [zero_mul, sub_zero, hsolve]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, ← Finset.mul_sum, ← star_sum]
  rw [hsum, character_sum]
  by_cases hχ : χ = 1
  · subst χ
    by_cases hk : k = 0
    · simp [hk, MulChar.map_zero]
    · rw [MulChar.one_apply (isUnit_iff_ne_zero.mpr (div_ne_zero hk h₂))]
      simp [hk]
  · simp [hχ]
end OAI.SevenEighths.CenteredMomentCorrelation
