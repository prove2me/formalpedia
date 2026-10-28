-- Prove2me | solution 1 for MarkovProcess.IsSubMarkovKernel.comp
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T14:41:26.078032+00:00
-- url     : https://prove2.me/submissions/3b8c779a-e8e8-437f-9ec6-8c1b5e366358

import Mathlib.Probability.Kernel.Composition.Comp
import Definitions.Def_MarkovProcess_IsSubMarkovKernel

open MeasureTheory ProbabilityTheory MarkovProcess
open scoped ENNReal ProbabilityTheory
variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
variable {κ : Kernel α β} {η : Kernel β γ}
theorem solution (hη : IsSubMarkovKernel η) (hκ : IsSubMarkovKernel κ) :
    IsSubMarkovKernel (η ∘ₖ κ) := by
  intro x
  rw [Kernel.comp_apply' _ _ _ MeasurableSet.univ]
  calc ∫⁻ b, η b Set.univ ∂κ x ≤ ∫⁻ _, 1 ∂κ x := lintegral_mono fun b => hη b
    _ = κ x Set.univ := by simp
    _ ≤ 1 := hκ x
