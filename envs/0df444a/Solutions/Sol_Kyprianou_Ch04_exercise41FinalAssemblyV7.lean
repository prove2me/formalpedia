-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41FinalAssemblyV7
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:19:49.159851+00:00
-- url     : https://prove2.me/submissions/cc71e491-a482-4c16-aea6-8013ff493e78

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise41LedgerCombineV2
import Theorems.Thm_Kyprianou_Ch04_exercise41BoundarySplitV1
import Theorems.Thm_Kyprianou_Ch04_exercise41CorrectionExpansionV7
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators Classical
set_option autoImplicit false
open Kyprianou.Ch04
theorem solution
    {Z : Type} [MeasurableSpace Z] (μ : Measure Z)
    (f fLeft fRight : ℝ → ℝ)
    (hLeft : ∀ x : ℝ, x < 0 → f x = fLeft x)
    (hRight : ∀ x : ℝ, 0 < x → f x = fRight x)
    (x0 xt D : ℝ) (pre post : Z → ℝ)
    (l : NNReal → ℝ) (t : NNReal) (S : Finset NNReal)
    (hC : let g := fun x : ℝ => if x < 0 then fLeft x - fLeft 0
          else if 0 < x then fRight x - fRight 0 else 0
      Integrable (fun z => g (post z) - g (pre z)) μ ∧
      g xt = g x0 + D + ∫ z, (g (post z) - g (pre z)) ∂μ)
    (hB : let a := fun x : ℝ => if 0 ≤ x then (1 : ℝ) else 0
      let b := fun x : ℝ => if 0 < x then (1 : ℝ) else 0
      Integrable (fun z => a (post z) - a (pre z)) μ ∧
      Integrable (fun z => b (post z) - b (pre z)) μ ∧
      a xt = a x0 + (∫ z, (a (post z) - a (pre z)) ∂μ) +
        (∑ s ∈ S, if l s = 0 then 1 else 0) ∧
      b xt = b x0 + (∫ z, (b (post z) - b (pre z)) ∂μ) +
        ((if 0 < t then 1 else 0) + ∑ s ∈ S, if s < t then 1 else 0)) :
    f xt = f x0 + D + (∫ z, (f (post z) - f (pre z)) ∂μ) +
      (if 0 < t then fRight 0 - f 0 else 0) +
      ∑ s ∈ S, ((if l s = 0 then f 0 - fLeft 0 else 0) +
        (if s < t then fRight 0 - f 0 else 0)) := by
  classical
  let g : ℝ → ℝ := fun x => if x < 0 then fLeft x - fLeft 0
    else if 0 < x then fRight x - fRight 0 else 0
  let a : ℝ → ℝ := fun x => if 0 ≤ x then 1 else 0
  let b : ℝ → ℝ := fun x => if 0 < x then 1 else 0
  let α := f 0 - fLeft 0
  let β := fRight 0 - f 0
  let A : ℝ := ∑ s ∈ S, if l s = 0 then 1 else 0
  let B : ℝ := (if 0 < t then 1 else 0) + ∑ s ∈ S, if s < t then 1 else 0
  obtain ⟨hg,hG⟩ := hC
  obtain ⟨ha,hb,hA,hB'⟩ := hB
  have hSplit : ∀ x, f x = g x + fLeft 0 + α * a x + β * b x := by
    intro x
    simpa only [g, a, b, α, β, mul_ite, mul_one, mul_zero]
      using exercise41BoundarySplitV1 f fLeft fRight hLeft hRight x
  have H := exercise41LedgerCombineV2 μ f g a b (fLeft 0)
    α β x0 xt D A B pre post hSplit hg ha hb hG hA hB'
  have hc := exercise41CorrectionExpansionV7 α β l t S
  rw [H, add_assoc _ (α * A) (β * B)]
  change _ + (α * A + β * B) = _
  change α * A + β * B = _ at hc
  rw [hc]
  simp only [α, β, add_assoc]
