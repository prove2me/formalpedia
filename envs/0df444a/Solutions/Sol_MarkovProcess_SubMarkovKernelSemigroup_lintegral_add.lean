-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.lintegral_add
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T13:29:37.63033+00:00
-- url     : https://prove2.me/submissions/ca45801f-4110-409e-adb0-281fa8e75596

import Mathlib.Probability.Kernel.Composition.Comp
import Definitions.Def_MarkovProcess_SubMarkovKernelSemigroup

open Set MeasureTheory ProbabilityTheory MarkovProcess
open MarkovProcess.SubMarkovKernelSemigroup
open scoped ENNReal ProbabilityTheory
variable {α : Type*} [MeasurableSpace α]
variable (P : SubMarkovKernelSemigroup α)
theorem solution (s t : NNReal) (x : α) {f : α → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ y, f y ∂P (s + t) x = ∫⁻ y, ∫⁻ z, f z ∂P t y ∂P s x := by
  change ∫⁻ y, f y ∂P.kernel (s + t) x = ∫⁻ y, ∫⁻ z, f z ∂P.kernel t y ∂P.kernel s x
  rw [P.kernel_add, Kernel.lintegral_comp _ _ _ hf]
