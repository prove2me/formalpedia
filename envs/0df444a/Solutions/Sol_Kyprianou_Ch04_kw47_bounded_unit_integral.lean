-- Prove2me | solution 1 for Kyprianou.Ch04.kw47_bounded_unit_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T10:20:30.403563+00:00
-- url     : https://prove2.me/submissions/448dce92-59b1-4158-882b-ff488f153919

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (f : Real → Real) (t : NNReal) (hf : ∀ x : Real, 0 ≤ f x ∧ f x ≤ 1) :
    0 ≤ (∫ r in Icc (0 : Real) (t : Real), f r ∂volume) ∧
    (∫ r in Icc (0 : Real) (t : Real), f r ∂volume) ≤ (t : Real) := by 
  let mu : Measure Real := volume.restrict (Icc 0 (t : Real))
  letI : IsFiniteMeasure mu := ⟨by
    dsimp [mu]
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Icc]
    exact ENNReal.ofReal_lt_top⟩
  refine ⟨integral_nonneg (fun r => (hf r).1), ?_⟩
  calc
    _ ≤ ∫ _ : Real, (1 : Real) ∂mu := integral_mono_of_nonneg
      (Eventually.of_forall fun r => (hf r).1) (integrable_const 1)
      (Eventually.of_forall fun r => (hf r).2)
    _ = (t : Real) := by
      simp [mu, integral_const, Measure.real, Measure.restrict_apply,
        Real.volume_Icc, NNReal.coe_nonneg]
