-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.avgOver_uniform_sum_eq_card_mul_prod
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T13:43:40.411122+00:00
-- url     : https://prove2.me/submissions/66038552-9ed7-414e-9521-c4d5a0d7452f

-- Generated proof for MIPStarRE.LDT.avgOver_uniform_sum_eq_card_mul_prod.
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

/- Source helpers from MIPStarRE/LDT/Basic/PMFUniformAverages.lean. -/
/-!
# Uniform PMF finite-expectation identities

This module contains high-level uniform-expectation identities for Mathlib
probability mass functions.  The statements are phrased in terms of
`PMF.realWeightedSum`, rather than finite sums, so that product,
marginalization, equivalence-transport, and finite push-forward arguments can
be carried out directly in the probability-mass-function language.

## Main declarations

* `PMF.realWeightedSum_uniformOfFintype_comm`
* `PMF.realWeightedSum_uniformOfFintype_prod_swap`
* `PMF.realWeightedSum_uniformOfFintype_equiv_prod`
* `PMF.realWeightedSum_uniformOfFintype_equiv_prod_swap`
* `PMF.realWeightedSum_uniformOfFintype_equiv_fst`
* `PMF.realWeightedSum_uniformOfFintype_equiv_snd`
* `PMF.realWeightedSum_uniformOfFintype_fst`
* `PMF.realWeightedSum_uniformOfFintype_snd`
* `PMF.realWeightedSum_map_uniformOfFintype_factor_equiv`
* `PMF.realWeightedSum_map_uniformOfFintype_factor_equiv_fst`
* `PMF.realWeightedSum_map_uniformOfFintype_factor_equiv_snd`

## References

These are formalization-internal finite probability lemmas for the low
individual degree test development.
-/

@[expose] public section

open scoped BigOperators

namespace PMF



/-- Split a finite expectation against the uniform PMF on a product into
iterated finite expectations, with the second coordinate averaged first. -/
theorem realWeightedSum_uniformOfFintype_prod_swap {α β M : Type*}
    [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    [AddCommMonoid M] [Module MIPStarRE.LDT.Error M]
    (f : α → β → M) :
    realWeightedSum (PMF.uniformOfFintype (α × β)) (fun ab => f ab.1 ab.2) =
      realWeightedSum (PMF.uniformOfFintype β)
        (fun b => realWeightedSum (PMF.uniformOfFintype α) (fun a => f a b)) := by
  rw [realWeightedSum_uniformOfFintype_prod (f := f)]
  exact realWeightedSum_uniformOfFintype_comm f



















end PMF

end

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













/-- Split a uniform module-valued average over a product into iterated uniform
module-valued averages, with the second coordinate averaged first. -/
theorem uniformDistribution_sum_smul_prod_swap {α β M : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    [AddCommMonoid M] [Module Error M]
    (f : α → β → M) :
    ∑ ab ∈ (uniformDistribution (α × β)).support,
        (uniformDistribution (α × β)).weight ab • f ab.1 ab.2 =
      ∑ b ∈ (uniformDistribution β).support, (uniformDistribution β).weight b •
        ∑ a ∈ (uniformDistribution α).support,
          (uniformDistribution α).weight a • f a b := by
  rw [uniformDistribution_sum_smul_eq_pmf_sum (α := α × β)]
  rw [uniformDistribution_sum_smul_eq_pmf_sum (α := β)]
  simp_rw [uniformDistribution_sum_smul_eq_pmf_sum (α := α)]
  simpa [PMF.realWeightedSum] using
    PMF.realWeightedSum_uniformOfFintype_prod_swap (f := f)





























end MIPStarRE.LDT

end

/- Source helpers from MIPStarRE/LDT/Basic/DistributionAvg.lean. -/
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

namespace MIPStarRE.LDT

/-! ### Averaging infrastructure

Linearity proofs use `Distribution.weightedSumLinearMap`; order and support
estimates use Mathlib's `Finset.sum` API. -/













































namespace Distribution.IsProbability



end Distribution.IsProbability

















































/-- Split a uniform average over a product into iterated uniform averages, with
the second coordinate averaged first. -/
theorem avgOver_uniform_prod_swap
    {α β : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    (f : α → β → Error) :
    avgOver (uniformDistribution (α × β)) (fun ab => f ab.1 ab.2) =
      avgOver (uniformDistribution β)
        (fun b => avgOver (uniformDistribution α) (fun a => f a b)) := by
  simpa [avgOver, smul_eq_mul] using
    (uniformDistribution_sum_smul_prod_swap (M := Error) (f := f))















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
    {α β : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    (f : α → β → _root_.LIDT.MIPStarRE.LDT.Error) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution α) (fun a => ∑ b : β, f a b) =
      (Fintype.card β : _root_.LIDT.MIPStarRE.LDT.Error) *
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (α × β)) (fun ab => f ab.1 ab.2) := by
  let c : _root_.LIDT.MIPStarRE.LDT.Error := Fintype.card β
  have hc : c ≠ 0 := by
    dsimp [c]
    exact_mod_cast Fintype.card_ne_zero
  calc
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution α) (fun a => ∑ b : β, f a b)
        = ∑ b : β, _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution α) (fun a => f a b) := by
          exact _root_.LIDT.MIPStarRE.LDT.avgOver_sum (_root_.LIDT.MIPStarRE.LDT.uniformDistribution α) f
    _ = c * _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution β)
          (fun b => _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution α) (fun a => f a b)) := by
          symm
          calc
            c * _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution β)
                (fun b => _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution α) (fun a => f a b))
                = c * ((1 / c) *
                    ∑ b : β, _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution α) (fun a => f a b)) := by
                  simp [c, _root_.LIDT.MIPStarRE.LDT.avgOver, _root_.LIDT.MIPStarRE.LDT.uniformDistribution, Finset.mul_sum, hc]
            _ = ∑ b : β, _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution α) (fun a => f a b) := by
                field_simp [hc]
    _ = c * _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (α × β)) (fun ab => f ab.1 ab.2) := by
          rw [← _root_.LIDT.MIPStarRE.LDT.avgOver_uniform_prod_swap]
