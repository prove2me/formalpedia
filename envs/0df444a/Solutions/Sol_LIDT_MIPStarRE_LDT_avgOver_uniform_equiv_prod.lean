-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.avgOver_uniform_equiv_prod
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T13:45:04.889074+00:00
-- url     : https://prove2.me/submissions/8c1cd730-13c6-43b4-8edf-23089c2b6df9

-- Generated proof for MIPStarRE.LDT.avgOver_uniform_equiv_prod.
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

/- Source helpers from MIPStarRE/LDT/Basic/DistributionUniformSums.lean. -/
/-!
# Module-valued uniform finite sums for project distributions

This module contains the module-valued finite-sum algebra for the project
`Distribution` type.  The statements keep the paper-facing
`uniformDistribution` notation, but their proofs reduce the probability
calculation to the finite-expectation API for Mathlib probability mass
functions.

## Main declarations

* `Distribution.sum_smul_eq_toPMF_support_sum`
* `Distribution.sum_smul_eq_toPMF_sum`
* `uniformDistribution_sum_smul_eq_pmf_sum`
* `uniformDistribution_sum_smul_equiv`
* `uniformDistribution_sum_smul_prod`
* `uniformDistribution_sum_smul_comm`
* `uniformDistribution_sum_smul_prod_swap`
* `uniformDistribution_sum_smul_equiv_prod`
* `uniformDistribution_sum_smul_equiv_fst`
* `uniformDistribution_sum_smul_equiv_snd`
* `uniformDistribution_map_sum_smul_eq_uniform_of_factor_equiv`
* `uniformOnFinset_sum_smul_eq_subtype`
* `uniformOnFinset_filter_sum_smul_equiv`

## References

These are formalization-internal finite probability lemmas for the low
individual degree test development.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.LDT

namespace Distribution





end Distribution















/-- Transport a uniform module-valued average through an equivalence whose
target is a product, then split the product average. -/
theorem uniformDistribution_sum_smul_equiv_prod {γ α β M : Type*}
    [Fintype γ] [DecidableEq γ] [Nonempty γ]
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    [AddCommMonoid M] [Module Error M]
    (e : γ ≃ α × β) (f : γ → M) :
    ∑ x ∈ (uniformDistribution γ).support, (uniformDistribution γ).weight x • f x =
      ∑ a ∈ (uniformDistribution α).support, (uniformDistribution α).weight a •
        ∑ b ∈ (uniformDistribution β).support,
          (uniformDistribution β).weight b • f (e.symm (a, b)) := by
  rw [uniformDistribution_sum_smul_eq_pmf_sum (α := γ)]
  rw [uniformDistribution_sum_smul_eq_pmf_sum (α := α)]
  simp_rw [uniformDistribution_sum_smul_eq_pmf_sum (α := β)]
  simpa [PMF.realWeightedSum] using
    PMF.realWeightedSum_uniformOfFintype_equiv_prod (e := e) (f := f)



























end MIPStarRE.LDT

end

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

theorem solution
    {γ α β : Type*}
    [Fintype γ] [DecidableEq γ] [Nonempty γ]
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    (e : γ ≃ α × β) (f : γ → _root_.LIDT.MIPStarRE.LDT.Error) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution γ) f =
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution α)
        (fun a => _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution β) (fun b => f (e.symm (a, b)))) := by
  simpa [_root_.LIDT.MIPStarRE.LDT.avgOver, smul_eq_mul] using
    (_root_.LIDT.MIPStarRE.LDT.uniformDistribution_sum_smul_equiv_prod (M := _root_.LIDT.MIPStarRE.LDT.Error) (e := e) (f := f))
