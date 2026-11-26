-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_cosine_remainder_scalar
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T20:26:07.888124+00:00
-- url     : https://prove2.me/submissions/61b7ba51-3ae6-41bc-81b8-2b9bb6cbe2f9

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_ito43_cosine_scaled_cubic
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution (a : ℝ) (ha : 0 < a) :
    let r : ℝ → ℝ := fun z => z^2/2-(1-Real.cos (a*z))/a^2
    Continuous r ∧ (∀ z, |r z| ≤ z^2/2) ∧
      ∀ e : ℝ, 0 < e → ∃ δ : ℝ, 0 < δ ∧ ∀ z, |z| ≤ δ → |r z| ≤ e*z^2 := by
  intro r
  have ha2 : 0 < a^2 := by positivity
  refine ⟨by dsimp [r]; fun_prop,?_,?_⟩
  · intro z
    have hq : (1-Real.cos (a*z))/a^2 ≤ z^2/2 := by
      apply (div_le_iff₀ ha2).mpr
      nlinarith [Real.one_sub_sq_div_two_le_cos (x := a*z)]
    have hq0 : 0 ≤ (1-Real.cos (a*z))/a^2 :=
      div_nonneg (sub_nonneg.mpr (Real.cos_le_one _)) ha2.le
    dsimp [r]
    rw [abs_of_nonneg (sub_nonneg.mpr hq)]
    linarith
  · intro e he
    refine ⟨e/a,by positivity,fun z hz => ?_⟩
    have h := Kyprianou.Ch04.ito43_cosine_scaled_cubic a z ha
    have haZ : a*|z| ≤ e := by nlinarith [(le_div_iff₀ ha).mp hz]
    have hh := mul_le_mul_of_nonneg_right haZ (sq_nonneg z)
    exact h.trans (by nlinarith [mul_nonneg he.le (sq_nonneg z)])
