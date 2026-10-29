-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.avgOver_eq_toPMF_realWeightedSum
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T13:45:04.89951+00:00
-- url     : https://prove2.me/submissions/e11b8175-4a49-45ec-b5db-69f894e70077

-- Generated proof for MIPStarRE.LDT.avgOver_eq_toPMF_realWeightedSum.
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
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace LIDT

/- Source helpers from MIPStarRE/LDT/Basic/DistributionPMF.lean. -/
/-!
# PMF expectations associated to project distributions

This module relates the project `Distribution` averaging notation to the finite
expectation `PMF.realWeightedSum` on Mathlib probability mass functions.  The
statements keep the project-facing averages available while allowing later
probability arguments to cite the associated Mathlib `PMF` object directly.
The module-valued finite-sum algebra for uniform project distributions lives in
`MIPStarRE.LDT.Basic.DistributionUniformSums`; this file records the additional
comparison with `PMF.realWeightedSum`.

## Main declarations

* `avgOver_eq_toPMF_realWeightedSum`
* `averageOperatorOverDistribution_eq_toPMF_realWeightedSum`
* `Distribution.weightedSumLinearMap_eq_toPMF_realWeightedSum`
* `Distribution.weightedSumLinearMap_eq_toPMF_realWeightedSumLinearMap`
* `uniformDistribution_sum_smul_eq_pmf_realWeightedSum`
* `avgOver_uniform_eq_pmf_realWeightedSum`
* `averageOperatorOverDistribution_uniform_eq_pmf_realWeightedSum`

## References

These are formalization-internal finite probability lemmas for the low
individual degree test development.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT

namespace Distribution

/-- The module-valued weighted sum against a probabilistic `Distribution` agrees
with finite expectation against its associated Mathlib probability mass
function. -/
theorem weightedSumLinearMap_eq_toPMF_realWeightedSum {α M : Type*} [Fintype α]
    [AddCommMonoid M] [Module Error M]
    (𝒟 : Distribution α) (h𝒟 : 𝒟.IsProbability) (f : α → M) :
    𝒟.weightedSumLinearMap M f = PMF.realWeightedSum (𝒟.toPMF h𝒟) f := by
  simpa [PMF.realWeightedSum] using
    Distribution.sum_smul_eq_toPMF_sum 𝒟 h𝒟 f



end Distribution











end MIPStarRE.LDT

end

end LIDT

open LIDT
/-!
# PMF expectations associated to project distributions

This module relates the project `Distribution` averaging notation to the finite
expectation `PMF.realWeightedSum` on Mathlib probability mass functions.  The
statements keep the project-facing averages available while allowing later
probability arguments to cite the associated Mathlib `PMF` object directly.
The module-valued finite-sum algebra for uniform project distributions lives in
`MIPStarRE.LDT.Basic.DistributionUniformSums`; this file records the additional
comparison with `PMF.realWeightedSum`.

## Main declarations

* `avgOver_eq_toPMF_realWeightedSum`
* `averageOperatorOverDistribution_eq_toPMF_realWeightedSum`
* `Distribution.weightedSumLinearMap_eq_toPMF_realWeightedSum`
* `Distribution.weightedSumLinearMap_eq_toPMF_realWeightedSumLinearMap`
* `uniformDistribution_sum_smul_eq_pmf_realWeightedSum`
* `avgOver_uniform_eq_pmf_realWeightedSum`
* `averageOperatorOverDistribution_uniform_eq_pmf_realWeightedSum`

## References

These are formalization-internal finite probability lemmas for the low
individual degree test development.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

open LIDT.MIPStarRE.LDT

theorem solution {α : Type*} [Fintype α]
    (𝒟 : _root_.LIDT.MIPStarRE.LDT.Distribution α) (h𝒟 : 𝒟.IsProbability) (f : α → _root_.LIDT.MIPStarRE.LDT.Error) :
    _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟 f = PMF.realWeightedSum (𝒟.toPMF h𝒟) f := by
  simpa [_root_.LIDT.MIPStarRE.LDT.Distribution.avgOver_eq_weightedSumLinearMap] using
    _root_.LIDT.MIPStarRE.LDT.Distribution.weightedSumLinearMap_eq_toPMF_realWeightedSum 𝒟 h𝒟 f
