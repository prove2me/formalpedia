-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.MainInductionStep.weighted_diagonal_bound
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T15:06:22.852019+00:00
-- url     : https://prove2.me/submissions/c7f469e0-6c6a-417c-b81c-b565c9c56736

-- Generated proof for MIPStarRE.LDT.MainInductionStep.weighted_diagonal_bound.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Theorems_RestrictedProbabilities_Base
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Theorems_RestrictedProbabilities_Diagonal
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
import Theorems.Thm_LIDT_MIPStarRE_LDT_MainInductionStep_avgOver_uniform_restrictedDiagonalSample_append
import Theorems.Thm_LIDT_MIPStarRE_LDT_MainInductionStep_weighted_embedded_average_le_full_average

namespace LIDT

/- Source helpers from MIPStarRE/LDT/MainInductionStep/Theorems/RestrictedProbabilities/Diagonal.lean. -/
/-!
# Section 6 -- Diagonal Restricted Probability Bounds

This module contains the diagonal-line part of the restricted-probability
bookkeeping for the main induction step.

## References

- `blueprint/src/chapter/ch10_induction.tex`
-/

@[expose] public section

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open scoped MatrixOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private lemma restrictedDiagonalSampleError_eq
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (x : Fq params)
    (j : Fin params.m)
    (s : RestrictedDiagonalSample params j) :
    qBipartiteConsDefect strategy.state
      (RestrictedSymStrat.restrictedDiagonalPointAnswerFamily
        (xRestrictedStrategy params strategy x) j s)
      (RestrictedSymStrat.restrictedDiagonalLineAnswerFamily
        (xRestrictedStrategy params strategy x) j s) =
    qBipartiteConsDefect strategy.state
      (diagonalPointAnswerFamily strategy (embedCoord params j)
        (appendPoint params s.1 x, s.2))
      (diagonalLineAnswerFamily strategy (embedCoord params j)
        (appendPoint params s.1 x, s.2)) := by
  have hdir :
      appendPoint params (extendRestrictedDirection j s.2) zeroCoord =
        extendRestrictedDirection (params := params.next) (embedCoord params j) s.2 := by
    funext k
    by_cases hkm : k.1 < params.m
    · by_cases hk : k.1 ≤ j.1
      · simp [appendPoint, extendRestrictedDirection, embedCoord, hkm, hk]
      · simp [appendPoint, extendRestrictedDirection, embedCoord, hkm, hk]
        rfl
    · have hnotle : ¬ k.1 ≤ j.1 := by
          intro hk
          exact hkm (lt_of_le_of_lt hk j.2)
      simp [appendPoint, extendRestrictedDirection, embedCoord, hkm, hnotle]
      rfl
  have hline :
      DiagonalLine.appendAtHeight params
          { base := s.1, direction := extendRestrictedDirection j s.2 } x =
        ({ base := appendPoint params s.1 x,
           direction :=
             extendRestrictedDirection (params := params.next) (embedCoord params j) s.2 } :
          DiagonalLine params.next) := by
    simp [DiagonalLine.appendAtHeight, hdir]
  simp [RestrictedSymStrat.restrictedDiagonalPointAnswerFamily,
    RestrictedSymStrat.restrictedDiagonalLineAnswerFamily, diagonalPointAnswerFamily,
    diagonalLineAnswerFamily, xRestrictedStrategy]
  simp [diagonalPointAnswerFamilyOf, diagonalLineAnswerFamilyOf, hline]





private lemma diagonalSliceIndexErrorAverage_eq_diagonalIndexError
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (j : Fin params.m) :
    avgOver (uniformDistribution (Fq params))
      (fun x => diagonalSliceIndexError params strategy x j) =
      diagonalIndexError params strategy (embedCoord params j) := by
  let g : RestrictedDiagonalSample params.next (embedCoord params j) → Error := fun s =>
    qBipartiteConsDefect strategy.state
      (diagonalPointAnswerFamily strategy (embedCoord params j) s)
      (diagonalLineAnswerFamily strategy (embedCoord params j) s)
  calc
    avgOver (uniformDistribution (Fq params))
        (fun x => diagonalSliceIndexError params strategy x j)
      = avgOver (uniformDistribution (Fq params))
          (fun x => avgOver (uniformDistribution (RestrictedDiagonalSample params j))
            (fun s => g (appendPoint params s.1 x, s.2))) := by
              refine avgOver_congr _ _ _ ?_
              intro x
              unfold diagonalSliceIndexError bipartiteConsError
              refine avgOver_congr _ _ _ ?_
              intro s
              simpa [g] using restrictedDiagonalSampleError_eq params strategy x j s
    _ = avgOver (uniformDistribution (Fq params × RestrictedDiagonalSample params j))
          (fun xs => g (appendPoint params xs.2.1 xs.1, xs.2.2)) := by
            simpa using
              (avgOver_uniform_prod (α := Fq params)
                (β := RestrictedDiagonalSample params j)
                (f := fun x s => g (appendPoint params s.1 x, s.2))).symm
    _ = avgOver
          (uniformDistribution (RestrictedDiagonalSample params.next (embedCoord params j)))
          g := by
            exact avgOver_uniform_restrictedDiagonalSample_append params j g
    _ = diagonalIndexError params strategy (embedCoord params j) := by
            rfl

private lemma averageRestrictedDiagonalFailure_eq_embeddedDiagonalIndices
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι) :
    avgOver (uniformDistribution (Fq params))
      (fun x => (xRestrictedStrategy params strategy x).diagonalFailureProbability) =
    avgOver (uniformDistribution (Fin params.m))
      (fun j => diagonalIndexError params strategy (embedCoord params j)) := by
  calc
    avgOver (uniformDistribution (Fq params))
        (fun x => (xRestrictedStrategy params strategy x).diagonalFailureProbability)
      = avgOver (uniformDistribution (Fq params))
          (fun x => avgOver (uniformDistribution (Fin params.m))
            (fun j => diagonalSliceIndexError params strategy x j)) := by
              refine avgOver_congr _ _ _ ?_
              intro x
              unfold RestrictedSymStrat.diagonalFailureProbability diagonalSliceIndexError
              calc
                (1 / (params.m : Error)) *
                    ∑ j : Fin params.m,
                      bipartiteConsError strategy.state
                        (uniformDistribution (RestrictedDiagonalSample params j))
                        ((xRestrictedStrategy params strategy
                          x).restrictedDiagonalPointAnswerFamily j)
                        ((xRestrictedStrategy params strategy
                          x).restrictedDiagonalLineAnswerFamily j)
                  = ∑ j : Fin params.m,
                      (1 / (params.m : Error)) *
                        bipartiteConsError strategy.state
                          (uniformDistribution (RestrictedDiagonalSample params j))
                          ((xRestrictedStrategy params strategy
                            x).restrictedDiagonalPointAnswerFamily j)
                          ((xRestrictedStrategy params strategy
                            x).restrictedDiagonalLineAnswerFamily j) := by
                              rw [Finset.mul_sum]
                _ = avgOver (uniformDistribution (Fin params.m))
                      (fun j => diagonalSliceIndexError params strategy x j) := by
                              simp [avgOver, uniformDistribution, Fintype.card_fin,
                                diagonalSliceIndexError]
    _ = avgOver (uniformDistribution (Fin params.m))
          (fun j => avgOver (uniformDistribution (Fq params))
            (fun x => diagonalSliceIndexError params strategy x j)) := by
            exact avgOver_uniform_comm
              (fun x j => diagonalSliceIndexError params strategy x j)
    _ = avgOver (uniformDistribution (Fin params.m))
          (fun j => diagonalIndexError params strategy (embedCoord params j)) := by
            refine avgOver_congr _ _ _ ?_
            intro j
            exact diagonalSliceIndexErrorAverage_eq_diagonalIndexError params strategy j



end MIPStarRE.LDT.MainInductionStep

end

end LIDT

open LIDT
/-!
# Section 6 -- Diagonal Restricted Probability Bounds

This module contains the diagonal-line part of the restricted-probability
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
          (_root_.LIDT.MIPStarRE.LDT.MainInductionStep.xRestrictedStrategy params strategy x).diagonalFailureProbability) ≤ gamma := by
  calc
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params))
        (fun x => _root_.LIDT.MIPStarRE.LDT.MainInductionStep.sliceTransverseDirectionWeight params *
          (_root_.LIDT.MIPStarRE.LDT.MainInductionStep.xRestrictedStrategy params strategy x).diagonalFailureProbability)
      = _root_.LIDT.MIPStarRE.LDT.MainInductionStep.sliceTransverseDirectionWeight params *
          _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params))
            (fun x => (_root_.LIDT.MIPStarRE.LDT.MainInductionStep.xRestrictedStrategy params strategy x).diagonalFailureProbability) := by
              rw [_root_.LIDT.MIPStarRE.LDT.avgOver_const_mul]
    _ = _root_.LIDT.MIPStarRE.LDT.MainInductionStep.sliceTransverseDirectionWeight params *
          _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin params.m))
            (fun j => diagonalIndexError params strategy (_root_.LIDT.MIPStarRE.LDT.embedCoord params j)) := by
              rw [averageRestrictedDiagonalFailure_eq_embeddedDiagonalIndices params strategy]
    _ ≤ _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin params.next.m))
          (diagonalIndexError params strategy) :=
        _root_.LIDT.MIPStarRE.LDT.MainInductionStep.weighted_embedded_average_le_full_average params
          (f := diagonalIndexError params strategy)
          (hf := by
            intro j
            unfold diagonalIndexError
            exact _root_.LIDT.MIPStarRE.LDT.bipartiteConsError_nonneg strategy.state
              (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.RestrictedDiagonalSample params.next j))
              (_root_.LIDT.MIPStarRE.LDT.diagonalPointAnswerFamily strategy j)
              (_root_.LIDT.MIPStarRE.LDT.diagonalLineAnswerFamily strategy j))
    _ = strategy.diagonalFailureProbability := by
        unfold diagonalIndexError _root_.LIDT.MIPStarRE.LDT.SymStrat.diagonalFailureProbability
        calc
          _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin params.next.m))
              (fun j =>
                _root_.LIDT.MIPStarRE.LDT.bipartiteConsError strategy.state
                  (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.RestrictedDiagonalSample params.next j))
                  (_root_.LIDT.MIPStarRE.LDT.diagonalPointAnswerFamily strategy j)
                  (_root_.LIDT.MIPStarRE.LDT.diagonalLineAnswerFamily strategy j))
            = ∑ j : Fin params.next.m,
                (1 / (params.next.m : _root_.LIDT.MIPStarRE.LDT.Error)) *
                  _root_.LIDT.MIPStarRE.LDT.bipartiteConsError strategy.state
                    (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.RestrictedDiagonalSample params.next j))
                    (_root_.LIDT.MIPStarRE.LDT.diagonalPointAnswerFamily strategy j)
                    (_root_.LIDT.MIPStarRE.LDT.diagonalLineAnswerFamily strategy j) := by
                      simp [_root_.LIDT.MIPStarRE.LDT.avgOver, _root_.LIDT.MIPStarRE.LDT.uniformDistribution, Fintype.card_fin]
          _ = (1 / (params.next.m : _root_.LIDT.MIPStarRE.LDT.Error)) *
                ∑ j : Fin params.next.m,
                  _root_.LIDT.MIPStarRE.LDT.bipartiteConsError strategy.state
                    (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.RestrictedDiagonalSample params.next j))
                    (_root_.LIDT.MIPStarRE.LDT.diagonalPointAnswerFamily strategy j)
                    (_root_.LIDT.MIPStarRE.LDT.diagonalLineAnswerFamily strategy j) := by
                      symm
                      rw [Finset.mul_sum]
          _ = strategy.diagonalFailureProbability := by
                rfl
    _ ≤ gamma := hgood.diagonalLineTest
