-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.CommutativityPoints.avgOver_pointPairSharedDiagonalLine_ignore_second
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T14:15:26.343353+00:00
-- url     : https://prove2.me/submissions/e2e2d50c-8da3-4c43-a50e-50b74780cdba

-- Generated proof for MIPStarRE.LDT.CommutativityPoints.avgOver_pointPairSharedDiagonalLine_ignore_second.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionUniformSums
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_MeasurementLift
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OperatorExpectations
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFUniformAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_TensorPlacement
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_Approximation
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_SharedHelpers_SharedLine
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_QuantumNonneg
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyFailures
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyRole_Algebra
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyRole_Core
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.CommutativityPoints
end LIDT.MIPStarRE.LDT.CommutativityPoints

namespace LIDT

/- Source helpers from MIPStarRE/LDT/Basic/PMFAverages.lean. -/
/-!
# PMF-weighted finite expectation identities

This module contains finite expectation identities stated directly for
Mathlib probability mass functions.  They connect `PMF.map` and
`PMF.bind` to the real-weighted finite sums used by the
low individual degree test averaging layer.

## Main declarations

* `PMF.map_apply_toReal`
* `PMF.realWeightedSum`
* `PMF.realWeightedSumLinearMap`
* `PMF.realWeightedSum_map`
* `PMF.realWeightedSum_bind`
* `PMF.map_sum_smul`
* `PMF.bind_apply_toReal`
* `PMF.bind_sum_smul`
* `PMF.sum_toReal_eq_one`
* `PMF.sum_const_smul`
* `PMF.totalVariationDistance`
* `PMF.totalVariationDistance_eq_sum_max_sub`
* `PMF.totalVariationDistance_uniformOfFintype_uniformOfFinset_eq`
* `PMF.sum_le_sum_add_totalVariationDistance`
* `PMF.sum_rpow_one_div_le_rpow_sum`
* `PMF.realWeightedSum_rpow_one_div_le_rpow`
* `PMF.uniformOfFintype_map_equiv`
* `PMF.uniformOfFintype_prod_apply_toReal`
* `PMF.uniformOfFintype_prod_eq_bind`
* `PMF.uniformOfFintype_sum_equiv_smul`
* `PMF.uniformOfFintype_prod_sum_smul`
* `PMF.uniformOfFintype_sum_equiv_fst_smul`
* `PMF.uniformOfFintype_sum_equiv_snd_smul`
* `PMF.uniformOfFintype_sum_factor_equiv_smul`
* `PMF.uniformOfFintype_sum_factor_equiv_fst_smul`
* `PMF.uniformOfFintype_sum_factor_equiv_snd_smul`

## References

These are formalization-internal finite probability lemmas for the low
individual degree test development.
-/

@[expose] public section

open scoped BigOperators

namespace PMF









end PMF

namespace PMF





























/-- A uniform PMF-weighted sum pushed forward through a map has the uniform
average of an equivalent observed coordinate. -/
theorem uniformOfFintype_sum_factor_equiv_smul {α β γ M : Type*}
    [Fintype α] [Nonempty α]
    [Fintype γ] [Nonempty γ]
    [AddCommMonoid M] [Module MIPStarRE.LDT.Error M]
    (m : α → β) (g : β → γ) (e : α ≃ γ)
    (h : ∀ a, g (m a) = e a) (f : γ → M) :
    ∑ a : α, (PMF.uniformOfFintype α a).toReal • f (g (m a)) =
      ∑ c : γ, (PMF.uniformOfFintype γ c).toReal • f c := by
  calc
    ∑ a : α, (PMF.uniformOfFintype α a).toReal • f (g (m a))
        = ∑ a : α, (PMF.uniformOfFintype α a).toReal • f (e a) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          rw [h a]
    _ = ∑ c : γ, (PMF.uniformOfFintype γ c).toReal • f c := by
          simpa using
            (uniformOfFintype_sum_equiv_smul
              (e := e) (f := fun a : α => f (e a)))





end PMF

namespace PMF











/-- A uniform finite expectation pushed forward through a map has the uniform
expectation of an equivalent observed coordinate. -/
theorem realWeightedSum_uniformOfFintype_factor_equiv {α β γ M : Type*}
    [Fintype α] [Nonempty α]
    [Fintype γ] [Nonempty γ]
    [AddCommMonoid M] [Module MIPStarRE.LDT.Error M]
    (m : α → β) (g : β → γ) (e : α ≃ γ)
    (h : ∀ a, g (m a) = e a) (f : γ → M) :
    realWeightedSum (PMF.uniformOfFintype α) (fun a => f (g (m a))) =
      realWeightedSum (PMF.uniformOfFintype γ) f := by
  simpa [realWeightedSum] using
    uniformOfFintype_sum_factor_equiv_smul
      (m := m) (g := g) (e := e) (h := h) (f := f)













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























/-- A uniformly sampled seed has the uniform module-valued average of an
equivalent observed coordinate. -/
theorem uniformDistribution_sum_smul_factor_equiv {α β γ M : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype γ] [DecidableEq γ] [Nonempty γ]
    [AddCommMonoid M] [Module Error M]
    (m : α → β) (g : β → γ) (e : α ≃ γ)
    (h : ∀ a, g (m a) = e a) (f : γ → M) :
    ∑ a ∈ (uniformDistribution α).support,
        (uniformDistribution α).weight a • f (g (m a)) =
      ∑ c ∈ (uniformDistribution γ).support, (uniformDistribution γ).weight c • f c := by
  rw [uniformDistribution_sum_smul_eq_pmf_sum (α := α)]
  rw [uniformDistribution_sum_smul_eq_pmf_sum (α := γ)]
  simpa [PMF.realWeightedSum] using
    PMF.realWeightedSum_uniformOfFintype_factor_equiv
      (m := m) (g := g) (e := e) (h := h) (f := f)





/-- A uniform push-forward has the uniform module-valued average induced by an
equivalent observed coordinate. -/
theorem uniformDistribution_map_sum_smul_eq_uniform_of_factor_equiv
    {α β γ M : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [DecidableEq β]
    [Fintype γ] [DecidableEq γ] [Nonempty γ]
    [AddCommMonoid M] [Module Error M]
    (m : α → β) (g : β → γ) (e : α ≃ γ)
    (h : ∀ a, g (m a) = e a) (f : γ → M) :
    ∑ b ∈ ((uniformDistribution α).map m).support,
        ((uniformDistribution α).map m).weight b • f (g b) =
      ∑ c ∈ (uniformDistribution γ).support, (uniformDistribution γ).weight c • f c := by
  rw [Distribution.map_sum_smul]
  exact uniformDistribution_sum_smul_factor_equiv
    (m := m) (g := g) (e := e) (h := h) (f := f)













end MIPStarRE.LDT

end

/- Source helpers from MIPStarRE/LDT/Basic/DistributionMapAverages.lean. -/
/-!
# Uniform push-forward averaging lemmas

This file contains shared averaging lemmas for uniformly sampled finite seeds
that are pushed forward to a question distribution.  The main use case is a
random seed `a : α`, a pushed-forward value `m a : β`, and an observed
coordinate `g (m a)` which is identified with a uniform coordinate by an
equivalence.

## Main declarations

* `avgOver_uniform_map_eq_uniform_of_factor_equiv`
* `averageOperatorOverDistribution_uniform_map_eq_uniform_of_factor_equiv`
* `avgOver_uniform_map_eq_uniform_fst_of_factor_equiv`
* `avgOver_uniform_map_eq_uniform_snd_of_factor_equiv`
* `averageOperatorOverDistribution_uniform_map_eq_uniform_fst_of_factor_equiv`
* `averageOperatorOverDistribution_uniform_map_eq_uniform_snd_of_factor_equiv`

## References

These are formalization-internal finite probability lemmas for the low
individual degree test development.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT

/-! ### Project-distribution map averages -/

/-- A uniform push-forward has the uniform average induced by an equivalent
observed coordinate.

The map `m` is the finite random seed map, `g` is the observed coordinate on
the pushed-forward value, and `e` records that this observed coordinate is
equivalent to a uniform sample of `γ`. -/
theorem avgOver_uniform_map_eq_uniform_of_factor_equiv
    {α β γ : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [DecidableEq β]
    [Fintype γ] [DecidableEq γ] [Nonempty γ]
    (m : α → β) (g : β → γ) (e : α ≃ γ)
    (h : ∀ a, g (m a) = e a) (f : γ → Error) :
    avgOver ((uniformDistribution α).map m) (fun b => f (g b)) =
      avgOver (uniformDistribution γ) f := by
  simpa [avgOver, smul_eq_mul] using
    uniformDistribution_map_sum_smul_eq_uniform_of_factor_equiv
      (m := m) (g := g) (e := e) (h := h) (f := f)











end MIPStarRE.LDT

end

end LIDT

open LIDT
/-!
# Section 10 commutativity points: shared-line helpers

Compatibility lemmas between sampled point pairs and shared-diagonal line
questions, used by both the lift and drop comparisons.

## References

- `references/ldt-paper/commutativity-points.tex`
- `blueprint/src/chapter/ch08_commutativity.tex`
-/

@[expose] public section

open LIDT.MIPStarRE.LDT.CommutativityPoints

open MIPStarRE.LDT.GlobalVariance (PointPairQuestion)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open scoped _root_.Matrix MatrixOrder ComplexOrder BigOperators

theorem solution
    (params : _root_.LIDT.MIPStarRE.LDT.Parameters)
    [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    (f : _root_.LIDT.MIPStarRE.LDT.CommutativityPoints.PointDiagonalLineQuestion params → _root_.LIDT.MIPStarRE.LDT.Error) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointPairSharedDiagonalLineDistribution params)
      (fun q => f (q.1, q.2.1)) =
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointWithDiagonalLineDistribution params) f := by
  calc
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointPairSharedDiagonalLineDistribution params)
        (fun q => f (q.1, q.2.1))
      = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.PointDiagonalLineQuestion params)) f := by
          simpa [_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointPairSharedDiagonalLineDistribution] using
            (_root_.LIDT.MIPStarRE.LDT.avgOver_uniform_map_eq_uniform_of_factor_equiv
              (m := _root_.LIDT.MIPStarRE.LDT.CommutativityPoints.sharedDiagonalLineQuestionOfPointPair params)
              (g := fun q : _root_.LIDT.MIPStarRE.LDT.CommutativityPoints.PointPairDiagonalLineQuestion params => (q.1, q.2.1))
              (e := pointPairSharedDiagonalLine_ignore_second_equiv params)
              (h := by
                intro s
                rfl)
              (f := f))
    _ = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointWithDiagonalLineDistribution params) f := by
          simp [_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointWithDiagonalLineDistribution]
