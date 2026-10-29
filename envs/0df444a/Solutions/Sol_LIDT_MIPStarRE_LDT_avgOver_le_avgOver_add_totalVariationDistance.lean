-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.avgOver_le_avgOver_add_totalVariationDistance
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T13:45:04.685995+00:00
-- url     : https://prove2.me/submissions/d66c52a4-6337-46aa-be3e-65515ad68f29

-- Generated proof for MIPStarRE.LDT.avgOver_le_avgOver_add_totalVariationDistance.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
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
import Theorems.Thm_LIDT_MIPStarRE_LDT_totalVariationDistance_eq_sum_max_sub

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

theorem solution {α : Type*} [DecidableEq α]
    (μ ν : _root_.LIDT.MIPStarRE.LDT.Distribution α) (hμ : μ.IsProbability) (hν : ν.IsProbability)
    (f : α → _root_.LIDT.MIPStarRE.LDT.Error)
    (hf_nonneg : ∀ a, 0 ≤ f a)
    (hf_le_one : ∀ a, f a ≤ 1) :
    _root_.LIDT.MIPStarRE.LDT.avgOver ν f ≤ _root_.LIDT.MIPStarRE.LDT.avgOver μ f + _root_.LIDT.MIPStarRE.LDT.totalVariationDistance μ ν := by
  classical
  let u : Finset α := μ.support ∪ ν.support
  have hμ_avg :
      _root_.LIDT.MIPStarRE.LDT.avgOver μ f = ∑ a ∈ u, μ.weight a * f a := by
    unfold _root_.LIDT.MIPStarRE.LDT.avgOver
    have hsubset : μ.support ⊆ u := by
      intro a ha
      exact Finset.mem_union_left ν.support ha
    exact Finset.sum_subset hsubset (fun a _ ha => by rw [μ.outsideSupport a ha, zero_mul])
  have hν_avg :
      _root_.LIDT.MIPStarRE.LDT.avgOver ν f = ∑ a ∈ u, ν.weight a * f a := by
    unfold _root_.LIDT.MIPStarRE.LDT.avgOver
    have hsubset : ν.support ⊆ u := by
      intro a ha
      exact Finset.mem_union_right μ.support ha
    exact Finset.sum_subset hsubset (fun a _ ha => by rw [ν.outsideSupport a ha, zero_mul])
  have hpoint :
      ∀ a, ν.weight a * f a ≤ μ.weight a * f a + max 0 (ν.weight a - μ.weight a) := by
    intro a
    by_cases hle : ν.weight a ≤ μ.weight a
    · have hmul : ν.weight a * f a ≤ μ.weight a * f a := by
        exact mul_le_mul_of_nonneg_right hle (hf_nonneg a)
      have hmax : max 0 (ν.weight a - μ.weight a) = 0 := by
        rw [max_eq_left]
        linarith
      rw [hmax]
      linarith
    · have hμν : μ.weight a ≤ ν.weight a := le_of_not_ge hle
      have hdiff_nonneg : 0 ≤ ν.weight a - μ.weight a := by linarith
      have hmul :
          (ν.weight a - μ.weight a) * f a ≤ ν.weight a - μ.weight a := by
        have := mul_le_mul_of_nonneg_left (hf_le_one a) hdiff_nonneg
        simpa [one_mul] using this
      have hsplit :
          ν.weight a * f a =
            μ.weight a * f a + (ν.weight a - μ.weight a) * f a := by
        ring
      have hmax : max 0 (ν.weight a - μ.weight a) =
          ν.weight a - μ.weight a := max_eq_right hdiff_nonneg
      rw [hsplit, hmax]
      linarith
  have hsum :
      ∑ a ∈ u, ν.weight a * f a ≤
        ∑ a ∈ u, (μ.weight a * f a + max 0 (ν.weight a - μ.weight a)) :=
    Finset.sum_le_sum fun a _ => hpoint a
  have htv :
      _root_.LIDT.MIPStarRE.LDT.totalVariationDistance μ ν =
        ∑ a ∈ u, max 0 (ν.weight a - μ.weight a) := by
    exact _root_.LIDT.MIPStarRE.LDT.totalVariationDistance_eq_sum_max_sub μ ν hμ hν
  rw [hμ_avg, hν_avg]
  calc
    ∑ a ∈ u, ν.weight a * f a
        ≤ ∑ a ∈ u, (μ.weight a * f a + max 0 (ν.weight a - μ.weight a)) :=
          hsum
    _ = ∑ a ∈ u, μ.weight a * f a +
          ∑ a ∈ u, max 0 (ν.weight a - μ.weight a) := by
          rw [Finset.sum_add_distrib]
    _ = ∑ a ∈ u, μ.weight a * f a + _root_.LIDT.MIPStarRE.LDT.totalVariationDistance μ ν := by
          rw [← htv]
