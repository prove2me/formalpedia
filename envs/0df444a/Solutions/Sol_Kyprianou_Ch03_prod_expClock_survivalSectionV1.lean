-- Prove2me | solution 1 for Kyprianou.Ch03.prod_expClock_survivalSectionV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T17:57:23.449923+00:00
-- url     : https://prove2.me/submissions/7d55a16c-2ecd-4230-a9a3-753835c12e20

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    {OmegaE : Type} [MeasurableSpace OmegaE]
    (Q : Measure OmegaE) [IsProbabilityMeasure Q]
    (q : ℝ) (e : OmegaE → NNReal)
    (hExponential : ∀ t : NNReal,
      (Q {z : OmegaE | t < e z}).toReal = Real.exp (-q * (t : ℝ)))
    (a : WithTop NNReal) :
    Q {z : OmegaE | a < (e z : WithTop NNReal)} =
      ENNReal.ofReal (if a = ⊤ then (0 : ℝ)
        else Real.exp (-q * ((a.untopD (0 : NNReal) : NNReal) : ℝ))) := by
  cases a using WithTop.recTopCoe with
  | top =>
    have he : {z : OmegaE | (⊤ : WithTop NNReal) < (e z : WithTop NNReal)} = ∅ := by
      ext z; simp only [mem_setOf_eq, mem_empty_iff_false]; exact iff_false_intro (not_lt_of_ge le_top)
    rw [he]; simp
  | coe a =>
    have hs : {z : OmegaE | (a : WithTop NNReal) < (e z : WithTop NNReal)} =
        {z : OmegaE | a < e z} := by
      ext z
      exact WithTop.coe_lt_coe
    rw [hs]
    simp only [WithTop.coe_ne_top, if_false, WithTop.untopD_coe]
    rw [← hExponential a, ENNReal.ofReal_toReal (measure_ne_top Q _)]
