-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.totalVariationDistance_eq_sum_max_sub
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T13:43:40.493435+00:00
-- url     : https://prove2.me/submissions/a1638035-0384-45e2-aebc-8981979b4dbb

-- Generated proof for MIPStarRE.LDT.totalVariationDistance_eq_sum_max_sub.
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
    (μ ν : _root_.LIDT.MIPStarRE.LDT.Distribution α) (hμ : μ.IsProbability) (hν : ν.IsProbability) :
    _root_.LIDT.MIPStarRE.LDT.totalVariationDistance μ ν =
      ∑ a ∈ μ.support ∪ ν.support, max 0 (ν.weight a - μ.weight a) := by
  classical
  let u : Finset α := μ.support ∪ ν.support
  have hμ_union :
      ∑ a ∈ u, μ.weight a = 1 := by
    have hsubset : μ.support ⊆ u := by
      intro a ha
      exact Finset.mem_union_left ν.support ha
    have hsum :
        ∑ a ∈ μ.support, μ.weight a = ∑ a ∈ u, μ.weight a :=
      Finset.sum_subset hsubset (fun a _ ha => μ.outsideSupport a ha)
    exact hsum ▸ hμ.weight_sum_eq_one
  have hν_union :
      ∑ a ∈ u, ν.weight a = 1 := by
    have hsubset : ν.support ⊆ u := by
      intro a ha
      exact Finset.mem_union_right μ.support ha
    have hsum :
        ∑ a ∈ ν.support, ν.weight a = ∑ a ∈ u, ν.weight a :=
      Finset.sum_subset hsubset (fun a _ ha => ν.outsideSupport a ha)
    exact hsum ▸ hν.weight_sum_eq_one
  have hdiff_sum :
      ∑ a ∈ u, (ν.weight a - μ.weight a) = 0 := by
    rw [Finset.sum_sub_distrib, hν_union, hμ_union, sub_self]
  have hmax_abs :
      ∀ a, max 0 (ν.weight a - μ.weight a) =
        ((ν.weight a - μ.weight a) + |μ.weight a - ν.weight a|) / 2 := by
    intro a
    by_cases hle : ν.weight a - μ.weight a ≤ 0
    · have hmax : max 0 (ν.weight a - μ.weight a) = 0 := max_eq_left hle
      have habs : |μ.weight a - ν.weight a| = μ.weight a - ν.weight a := by
        rw [abs_of_nonneg]
        linarith
      rw [hmax, habs]
      ring
    · have hnonneg : 0 ≤ ν.weight a - μ.weight a := le_of_not_ge hle
      have hmax : max 0 (ν.weight a - μ.weight a) =
          ν.weight a - μ.weight a := max_eq_right hnonneg
      have habs : |μ.weight a - ν.weight a| = ν.weight a - μ.weight a := by
        have hμν : μ.weight a ≤ ν.weight a := by linarith
        rw [abs_of_nonpos (sub_nonpos.mpr hμν)]
        ring
      rw [hmax, habs]
      ring
  calc
    _root_.LIDT.MIPStarRE.LDT.totalVariationDistance μ ν
        = (1 / 2) * ∑ a ∈ u, |μ.weight a - ν.weight a| := by
            rfl
    _ = (∑ a ∈ u, (ν.weight a - μ.weight a) +
          ∑ a ∈ u, |μ.weight a - ν.weight a|) / 2 := by
            rw [hdiff_sum]
            ring
    _ = (∑ a ∈ u,
          ((ν.weight a - μ.weight a) + |μ.weight a - ν.weight a|)) / 2 := by
            rw [Finset.sum_add_distrib]
    _ = ∑ a ∈ u,
          ((ν.weight a - μ.weight a) + |μ.weight a - ν.weight a|) / 2 := by
            rw [Finset.sum_div]
    _ = ∑ a ∈ u, max 0 (ν.weight a - μ.weight a) := by
            exact Finset.sum_congr rfl fun a _ => (hmax_abs a).symm
