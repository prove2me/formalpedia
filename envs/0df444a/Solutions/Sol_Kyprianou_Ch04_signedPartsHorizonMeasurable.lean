-- Prove2me | solution 1 for Kyprianou.Ch04.signedPartsHorizonMeasurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T08:12:13.228706+00:00
-- url     : https://prove2.me/submissions/cb53bc02-cf2b-4b6d-8c1c-1bd433841223

import Mathlib
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The positive and negative parts of a signed past-horizon cutoff are jointly measurable. -/
theorem solution {Omega : Type} [MeasurableSpace Omega]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (k : ℝ → ℝ → Omega → ℝ) (t : NNReal)
    (hm : Measurable[(F t).prod inferInstance] (fun z : Omega × (ℝ × ℝ) =>
      if z.2.1 ∈ Set.Icc (0 : ℝ) (t : ℝ) then k z.2.1 z.2.2 z.1 else 0)) :
    Measurable[(F t).prod inferInstance] (fun z : Omega × (ℝ × ℝ) =>
      if z.2.1 ∈ Set.Icc (0 : ℝ) (t : ℝ) then max (k z.2.1 z.2.2 z.1) 0 else 0) ∧
    Measurable[(F t).prod inferInstance] (fun z : Omega × (ℝ × ℝ) =>
      if z.2.1 ∈ Set.Icc (0 : ℝ) (t : ℝ) then max (-k z.2.1 z.2.2 z.1) 0 else 0) := by
  constructor
  · convert hm.max (measurable_const : Measurable[(F t).prod inferInstance] (fun _ : Omega × (ℝ × ℝ) => (0 : ℝ))) using 1
    ext z
    by_cases hz : z.2.1 ∈ Set.Icc (0 : ℝ) (t : ℝ)
    · simp only [Pi.neg_apply, if_pos hz]
    · simp only [Pi.neg_apply, if_neg hz, neg_zero, max_self]
  · convert hm.neg.max (measurable_const : Measurable[(F t).prod inferInstance] (fun _ : Omega × (ℝ × ℝ) => (0 : ℝ))) using 1
    ext z
    by_cases hz : z.2.1 ∈ Set.Icc (0 : ℝ) (t : ℝ)
    · simp only [Pi.neg_apply, if_pos hz]
    · simp only [Pi.neg_apply, if_neg hz, neg_zero, max_self]
