-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.MainInductionStep.weighted_axisParallel_bound
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T14:53:11.176986+00:00
-- url     : https://prove2.me/submissions/d7171f2c-ed65-42e1-870e-66d00301796d

-- Generated proof for MIPStarRE.LDT.MainInductionStep.weighted_axisParallel_bound.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Statements
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Theorems_RestrictedProbabilities_Axis
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Theorems_RestrictedProbabilities_Base
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_AvgCongr
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_QuantumNonneg
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyFailures
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyPolynomialFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyRole_Algebra
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyRole_Core
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Lean.Elab.Tactic
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Theorems.Thm_LIDT_MIPStarRE_LDT_MainInductionStep_weighted_embedded_average_le_full_average

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

/- Source helpers from MIPStarRE/LDT/MainInductionStep/Theorems/RestrictedProbabilities/Axis.lean. -/
/-!
# Section 6 -- Axis-Parallel Restricted Probability Bounds

This module contains the axis-parallel part of the restricted-probability
bookkeeping for the main induction step.

## References

- `blueprint/src/chapter/ch10_induction.tex`
-/

@[expose] public section

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open scoped MatrixOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private lemma restrictedAxisSampleError_eq
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (x : Fq params)
    (u : Point params)
    (i : Fin params.m) :
    qBipartiteConsDefect strategy.state
      (RestrictedSymStrat.axisParallelPointAnswerFamily
        (xRestrictedStrategy params strategy x) (u, i))
      (RestrictedSymStrat.axisParallelLineAnswerFamily
        (xRestrictedStrategy params strategy x) (u, i)) =
    qBipartiteConsDefect strategy.state
      (axisParallelPointAnswerFamily strategy (appendPoint params u x, embedCoord params i))
      (axisParallelLineAnswerFamily strategy (appendPoint params u x, embedCoord params i)) := by
  let ℓ : AxisParallelLine params := { base := u, direction := i }
  have hpost :
      postprocess ((restrictAxisParallelMeasurement params strategy x ℓ).toSubMeas)
        (· zeroCoord) =
      postprocess
          ((strategy.axisParallelMeasurement
            (AxisParallelLine.appendAtHeight params ℓ x)).toSubMeas)
          (fun f : AxisLinePolynomial params.next => f zeroCoord) := by
    have htransport :
        (restrictAxisParallelMeasurement params strategy x ℓ).toSubMeas =
          SubMeas.transport (axisLinePolynomialEquiv params x).symm
            ((strategy.axisParallelMeasurement
              (AxisParallelLine.appendAtHeight params ℓ x)).toSubMeas) := by
      refine SubMeas.ext ?_ ?_
      · intro f
        rfl
      · simpa [SubMeas.transport,
          (strategy.axisParallelMeasurement
            (AxisParallelLine.appendAtHeight params ℓ x)).total_eq_one] using
          (restrictAxisParallelMeasurement params strategy x ℓ).total_eq_one
    rw [htransport]
    rw [SubMeas.postprocess_transport]
    have hreadout :
        (fun a : AxisLinePolynomial params.next =>
            ((axisLinePolynomialEquiv params x).symm a) zeroCoord) =
          (fun f : AxisLinePolynomial params.next => f zeroCoord) := by
      funext a
      cases a
      rfl
    rw [hreadout]
  change
    qBipartiteConsDefect strategy.state
      ((strategy.pointMeasurement (appendPoint params u x)).toSubMeas)
      (postprocess ((restrictAxisParallelMeasurement params strategy x ℓ).toSubMeas)
        (fun f : AxisLinePolynomial params => f.toFun zeroCoord)) =
    qBipartiteConsDefect strategy.state
      ((strategy.pointMeasurement (appendPoint params u x)).toSubMeas)
      (postprocess
        ((strategy.axisParallelMeasurement
          (AxisParallelLine.appendAtHeight params ℓ x)).toSubMeas)
        (fun f : AxisLinePolynomial params.next => f.toFun zeroCoord))
  exact
    congrArg
      (fun B =>
        qBipartiteConsDefect strategy.state
          ((strategy.pointMeasurement (appendPoint params u x)).toSubMeas) B)
      hpost





private lemma sliceAxisDirectionErrorAverage_eq_axisDirectionError
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (i : Fin params.m) :
    avgOver (uniformDistribution (Fq params))
      (fun x => sliceAxisDirectionError params strategy x i) =
      axisDirectionError params strategy (embedCoord params i) := by
  let g : Point params.next → Error := fun u =>
    qBipartiteConsDefect strategy.state
      (axisParallelPointAnswerFamily strategy (u, embedCoord params i))
      (axisParallelLineAnswerFamily strategy (u, embedCoord params i))
  calc
    avgOver (uniformDistribution (Fq params))
        (fun x => sliceAxisDirectionError params strategy x i)
      = avgOver (uniformDistribution (Fq params))
          (fun x => avgOver (uniformDistribution (Point params))
            (fun u => g (appendPoint params u x))) := by
              unfold sliceAxisDirectionError
              refine _root_.LIDT.MIPStarRE.LDT.avgOver_congr _ _ _ ?_; intro x; refine _root_.LIDT.MIPStarRE.LDT.avgOver_congr _ _ _ ?_; intro u
              simpa [g] using restrictedAxisSampleError_eq params strategy x u i
    _ = avgOver (uniformDistribution (Point params.next)) g := by
          simpa using (CommutativityPoints.avgOver_uniform_pointNext_decompose params g).symm
    _ = axisDirectionError params strategy (embedCoord params i) := by
          rfl

private lemma averageRestrictedAxisFailure_eq_embeddedAxisDirections
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι) :
    avgOver (uniformDistribution (Fq params))
      (fun x => (xRestrictedStrategy params strategy x).axisParallelFailureProbability) =
    avgOver (uniformDistribution (Fin params.m))
      (fun i => axisDirectionError params strategy (embedCoord params i)) := by
  calc
    avgOver (uniformDistribution (Fq params))
        (fun x => (xRestrictedStrategy params strategy x).axisParallelFailureProbability)
      = avgOver (uniformDistribution (Fq params))
          (fun x => avgOver (uniformDistribution (Fin params.m))
            (fun i => sliceAxisDirectionError params strategy x i)) := by
              refine avgOver_congr _ _ _ ?_
              intro x
              unfold RestrictedSymStrat.axisParallelFailureProbability bipartiteConsError
              calc
                avgOver (uniformDistribution (Point params × Fin params.m))
                    (fun s =>
                      qBipartiteConsDefect strategy.state
                        (RestrictedSymStrat.axisParallelPointAnswerFamily
                          (xRestrictedStrategy params strategy x) s)
                        (RestrictedSymStrat.axisParallelLineAnswerFamily
                          (xRestrictedStrategy params strategy x) s))
                  = avgOver (uniformDistribution (Fin params.m))
                      (fun i => avgOver (uniformDistribution (Point params))
                        (fun u =>
                          qBipartiteConsDefect strategy.state
                            (RestrictedSymStrat.axisParallelPointAnswerFamily
                              (xRestrictedStrategy params strategy x) (u, i))
                            (RestrictedSymStrat.axisParallelLineAnswerFamily
                              (xRestrictedStrategy params strategy x) (u, i)))) := by
                                exact avgOver_uniform_prod_swap
                                  (α := Point params) (β := Fin params.m)
                                  (f := fun u i =>
                                    qBipartiteConsDefect strategy.state
                                      (RestrictedSymStrat.axisParallelPointAnswerFamily
                                        (xRestrictedStrategy params strategy x) (u, i))
                                      (RestrictedSymStrat.axisParallelLineAnswerFamily
                                        (xRestrictedStrategy params strategy x) (u, i)))
                _ = avgOver (uniformDistribution (Fin params.m))
                      (fun i => sliceAxisDirectionError params strategy x i) := by
                                rfl
    _ = avgOver (uniformDistribution (Fin params.m))
          (fun i => avgOver (uniformDistribution (Fq params))
            (fun x => sliceAxisDirectionError params strategy x i)) := by
            exact avgOver_uniform_comm
              (fun x i => sliceAxisDirectionError params strategy x i)
    _ = avgOver (uniformDistribution (Fin params.m))
          (fun i => axisDirectionError params strategy (embedCoord params i)) := by
            refine avgOver_congr _ _ _ ?_
            intro i
            exact sliceAxisDirectionErrorAverage_eq_axisDirectionError params strategy i



end MIPStarRE.LDT.MainInductionStep

end

end LIDT

open LIDT
/-!
# Section 6 -- Axis-Parallel Restricted Probability Bounds

This module contains the axis-parallel part of the restricted-probability
bookkeeping for the main induction step.

## References

- `blueprint/src/chapter/ch10_induction.tex`
-/

@[expose] public section

open LIDT.MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open scoped MatrixOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem solution
    (params : _root_.LIDT.MIPStarRE.LDT.Parameters)
    [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    (strategy : _root_.LIDT.MIPStarRE.LDT.SymStrat params.next ι)
    (eps delta gamma : _root_.LIDT.MIPStarRE.LDT.Error)
    (hgood : strategy.IsGood eps delta gamma) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params))
        (fun x => _root_.LIDT.MIPStarRE.LDT.MainInductionStep.sliceTransverseDirectionWeight params *
          (_root_.LIDT.MIPStarRE.LDT.MainInductionStep.xRestrictedStrategy params strategy x).axisParallelFailureProbability) ≤ eps := by
  calc
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params))
        (fun x => _root_.LIDT.MIPStarRE.LDT.MainInductionStep.sliceTransverseDirectionWeight params *
          (_root_.LIDT.MIPStarRE.LDT.MainInductionStep.xRestrictedStrategy params strategy x).axisParallelFailureProbability)
      = _root_.LIDT.MIPStarRE.LDT.MainInductionStep.sliceTransverseDirectionWeight params *
          _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params))
            (fun x => (_root_.LIDT.MIPStarRE.LDT.MainInductionStep.xRestrictedStrategy params strategy x).axisParallelFailureProbability) := by
              rw [_root_.LIDT.MIPStarRE.LDT.avgOver_const_mul]
    _ = _root_.LIDT.MIPStarRE.LDT.MainInductionStep.sliceTransverseDirectionWeight params *
          _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin params.m))
            (fun i => axisDirectionError params strategy (_root_.LIDT.MIPStarRE.LDT.embedCoord params i)) := by
              rw [averageRestrictedAxisFailure_eq_embeddedAxisDirections params strategy]
    _ ≤ _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin params.next.m))
          (axisDirectionError params strategy) :=
        _root_.LIDT.MIPStarRE.LDT.MainInductionStep.weighted_embedded_average_le_full_average params
          (f := axisDirectionError params strategy)
          (hf := by
            intro i
            unfold axisDirectionError
            refine _root_.LIDT.MIPStarRE.LDT.avgOver_nonneg (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params.next)) _ ?_
            intro u
            exact _root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect_nonneg strategy.state
              (_root_.LIDT.MIPStarRE.LDT.axisParallelPointAnswerFamily strategy (u, i))
              (_root_.LIDT.MIPStarRE.LDT.axisParallelLineAnswerFamily strategy (u, i)))
    _ = strategy.axisParallelFailureProbability := by
        let err : _root_.LIDT.MIPStarRE.LDT.Point params.next → Fin params.next.m → _root_.LIDT.MIPStarRE.LDT.Error := fun u i =>
          _root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect strategy.state
            (_root_.LIDT.MIPStarRE.LDT.axisParallelPointAnswerFamily strategy (u, i))
            (_root_.LIDT.MIPStarRE.LDT.axisParallelLineAnswerFamily strategy (u, i))
        calc
          _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin params.next.m)) (axisDirectionError params strategy)
            = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin params.next.m))
                (fun i => _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params.next))
                  (fun u => err u i)) := by
                    refine _root_.LIDT.MIPStarRE.LDT.avgOver_congr _ _ _ ?_; intro i; rfl
          _ = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params.next × Fin params.next.m))
                (fun ui => err ui.1 ui.2) := by
                  exact (_root_.LIDT.MIPStarRE.LDT.avgOver_uniform_prod_swap
                    (α := _root_.LIDT.MIPStarRE.LDT.Point params.next) (β := Fin params.next.m) (f := err)).symm
          _ = strategy.axisParallelFailureProbability := by
                rfl
    _ ≤ eps := hgood.axisParallelTest
