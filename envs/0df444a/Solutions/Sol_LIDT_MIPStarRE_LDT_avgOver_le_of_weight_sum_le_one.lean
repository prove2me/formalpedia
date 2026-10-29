-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.avgOver_le_of_weight_sum_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T13:43:40.480641+00:00
-- url     : https://prove2.me/submissions/505a6938-efb7-47d1-8579-c4ae04eab86a

-- Generated proof for MIPStarRE.LDT.avgOver_le_of_weight_sum_le_one.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionUniformSums
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFUniformAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace LIDT

end LIDT

open LIDT
/-!
# Average lemmas for finite-support distributions

This module contains the finite-sum and uniform-average lemmas for the project
`Distribution` type.  The primitive distribution definitions, uniform
distributions, and total variation distance live in
`MIPStarRE.LDT.Basic.Distribution`.

## Main declarations

The main results are the algebraic rules for `avgOver`, scalar and
operator-valued forms of the module-valued finite-sum rules for uniform
distributions, and the comparison between finite uniform averages and Mathlib
uniform probability mass functions.

## References

These are formalization-internal finite probability lemmas for the low
individual degree test development.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

open LIDT.MIPStarRE.LDT

/-! ### Averaging infrastructure

Linearity proofs use `Distribution.weightedSumLinearMap`; order and support
estimates use Mathlib's `Finset.sum` API. -/

theorem solution {α : Type*} (𝒟 : _root_.LIDT.MIPStarRE.LDT.Distribution α)
    (f : α → _root_.LIDT.MIPStarRE.LDT.Error) (δ : _root_.LIDT.MIPStarRE.LDT.Error)
    (h𝒟 : ∑ a ∈ 𝒟.support, 𝒟.weight a ≤ 1)
    (hδ_nonneg : 0 ≤ δ)
    (hf : ∀ a, f a ≤ δ) :
    _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 f ≤ δ := by
  calc
    _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 f ≤ _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 (fun _ : α => δ) := by
      exact _root_.LIDT.MIPStarRE.LDT.avgOver_mono 𝒟 f (fun _ : α => δ) hf
    _ = (∑ a ∈ 𝒟.support, 𝒟.weight a) * δ := _root_.LIDT.MIPStarRE.LDT.avgOver_const 𝒟 δ
    _ ≤ 1 * δ := mul_le_mul_of_nonneg_right h𝒟 hδ_nonneg
    _ = δ := one_mul δ
