-- Prove2me | solution 1 for Kyprianou.Ch04.discountedTestFunctionDerivatives
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T09:06:00.383019+00:00
-- url     : https://prove2.me/submissions/b35ff267-e426-482b-bec5-a3fc14c58c2a

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The two directional derivatives of the discounted spatial test function. -/
theorem solution (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (l s y : ℝ) :
    let g : ℝ × ℝ → ℝ := fun p => Real.exp (-l*p.1)*f p.2
    ContDiff ℝ 1 g ∧
      fderiv ℝ g (s,y) (1,0) = -l * Real.exp (-l*s)*f y ∧
      fderiv ℝ g (s,y) (0,1) = Real.exp (-l*s)*deriv f y := by
  let g : ℝ × ℝ → ℝ := fun p => Real.exp (-l*p.1)*f p.2
  have hdiff : Differentiable ℝ f := hf.differentiable (by norm_num)
  have h₁ := (hasFDerivAt_fst (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := (s,y))).const_mul (-l)
  have h₂ := (hdiff y).hasDerivAt.comp_hasFDerivAt (s,y)
    (hasFDerivAt_snd (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := (s,y)))
  have h := h₁.exp.mul h₂
  refine ⟨?_,?_,?_⟩
  · exact ((Real.contDiff_exp.comp (contDiff_const.mul contDiff_fst)).mul
      (hf.comp contDiff_snd))
  · change fderiv ℝ ((fun p : ℝ × ℝ => Real.exp (-l*p.1)) * (f ∘ Prod.snd)) (s,y) _ = _
    rw [h.fderiv]
    simp
    ring
  · change fderiv ℝ ((fun p : ℝ × ℝ => Real.exp (-l*p.1)) * (f ∘ Prod.snd)) (s,y) _ = _
    rw [h.fderiv]
    simp
