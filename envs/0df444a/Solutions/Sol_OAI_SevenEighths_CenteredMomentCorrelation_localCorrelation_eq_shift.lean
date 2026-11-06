-- Prove2me | solution 1 for OAI.SevenEighths.CenteredMomentCorrelation.localCorrelation_eq_shift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:27:52.220223+00:00
-- url     : https://prove2.me/submissions/0a8514a8-8443-46ab-853a-9906e5605176

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
theorem _root_.solution (χ : MulChar F ℂ) {n₁ n₂ : F}
    (h₁ : n₁ ≠ 0) (h₂ : n₂ ≠ 0) (k : F) :
    localCorrelation χ n₁ n₂ k = χ (n₁ / n₂) * shiftCorrelation χ (k / n₁) := by
  classical
  have hsolve (x y : F) : n₂ * x - n₁ * y = k ↔ y = (n₂ * x - k) / n₁ := by
    rw [eq_div_iff h₁]
    constructor <;> intro h <;> linear_combination -h
  unfold localCorrelation fullCorrelation
  simp only [hsolve, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [← (Equiv.mulLeft₀ (n₁ / n₂) (div_ne_zero h₁ h₂)).sum_comp]
  swap
  · simp
  simp only [Equiv.mulLeft₀_apply, shiftCorrelation, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [map_mul]
  have heq : (n₂ * (n₁ / n₂ * x) - k) / n₁ = x - k / n₁ := by
    field_simp
  rw [heq, mul_assoc]
end OAI.SevenEighths.CenteredMomentCorrelation
