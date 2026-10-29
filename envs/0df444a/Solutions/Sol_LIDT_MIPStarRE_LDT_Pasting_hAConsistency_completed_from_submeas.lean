-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.hAConsistency_completed_from_submeas
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T17:11:33.192148+00:00
-- url     : https://prove2.me/submissions/50b7c8dc-d287-4842-aa8b-1f13e23715ab

-- Generated proof for MIPStarRE.LDT.Pasting.hAConsistency_completed_from_submeas.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionUniformSums
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomialEmbedding
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Normalization
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Stability
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_EvaluatedSliceBounds_PhaseOneThree
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_GCommStability_Scalar_First
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_GCommStability_Scalar_RawSecond
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Main_Auxiliary_HEvalTransport
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Main_Auxiliary_ScalarMarginalization
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Products
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_PaperChainPhaseFive
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_ProcessedG_MainChain
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_ProcessedG_PhaseTwo
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Averages
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Machinery_Marginalization_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Machinery_Marginalization_Y
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Machinery_Normalization
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Transport_Pullback
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_MoveChain_BackChain
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_MoveChain_Base
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_MoveChain_Chain
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_MoveChain_FlatChain
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_MoveChain_Lifting
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_Setup_Definitions
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LdSandwichLineOnePoint_CSSetup
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LdSandwichLineOnePoint_Endpoint
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LdSandwichLineOnePoint_EndpointEquivs
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LdSandwichLineOnePoint_PrefixMoved
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LineInterpolation_BadLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LineInterpolation_BadMass
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LineInterpolation_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Core_LdGbcon
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Families
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Interpolation
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Tuples
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Sandwich_GHatSandwich
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Sandwich_PastedFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Sandwich_Switcheroo
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Statements
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_SwitcherooContraction_ScalarTerms
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_SwitcherooContraction_Split
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_SwitcherooSetup_Centers
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_SwitcherooSetup_Terms
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Completion
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Local
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_CauchySchwarz
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_CompletionTransfer
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_PolynomialAgreement
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Polynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SelfConsistency_Extensions
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichMain_Completeness
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_ApproxDelta
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_InnerProduct
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Triangles_Core
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
import Mathlib
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.RingTheory.MvPolynomial.Basic
import Theorems.Thm_LIDT_MIPStarRE_LDT_Preliminaries_evaluateAt_completeAtOutcome
import Theorems.Thm_LIDT_MIPStarRE_LDT_Preliminaries_qBipartiteConsDefect_completeAtOutcome_right_le

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.Commutativity
end LIDT.MIPStarRE.LDT.Commutativity
namespace LIDT.MIPStarRE.LDT.Commutativity.GCommStability.Scalar
end LIDT.MIPStarRE.LDT.Commutativity.GCommStability.Scalar
namespace LIDT.MIPStarRE.LDT.CommutativityPoints
end LIDT.MIPStarRE.LDT.CommutativityPoints
namespace LIDT.MIPStarRE.LDT.Pasting
end LIDT.MIPStarRE.LDT.Pasting
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries

namespace LIDT

end LIDT

open LIDT
/-!
# Section 12 pasting: H-A consistency

Vertical-line to point-consistency transport and completed-measurement statement for
`cor:h-a-consistency`.

## References

- `references/ldt-paper/ld-pasting.tex`
- `blueprint/src/chapter/ch09_pasting.tex`
-/

@[expose] public section

open LIDT.MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem solution
    (params : _root_.LIDT.MIPStarRE.LDT.Parameters)
    [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    (strategy : _root_.LIDT.MIPStarRE.LDT.SymStrat params.next ι)
    (eps delta gamma kappa zeta : _root_.LIDT.MIPStarRE.LDT.Error)
    (H : _root_.LIDT.MIPStarRE.LDT.SubMeas (_root_.LIDT.MIPStarRE.LDT.Polynomial params.next) ι)
    (k : ℕ)
    (hsubmeas :
      _root_.LIDT.MIPStarRE.LDT.ConsRel strategy.state (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params.next))
        (_root_.LIDT.MIPStarRE.LDT.IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (_root_.LIDT.MIPStarRE.LDT.polynomialEvaluationFamily params.next H)
        (_root_.LIDT.MIPStarRE.LDT.MainInductionStep.ldPastingInInductionNu params k
          eps delta gamma zeta))
    (hcomplete :
      _root_.LIDT.MIPStarRE.LDT.CompletenessAtLeast strategy.state H.liftLeft
        (_root_.LIDT.MIPStarRE.LDT.Pasting.ldPastingCompletenessLowerBound params kappa
          (_root_.LIDT.MIPStarRE.LDT.MainInductionStep.ldPastingInInductionNu params k
            eps delta gamma zeta) k)) :
    _root_.LIDT.MIPStarRE.LDT.ConsRel strategy.state (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params.next))
      (_root_.LIDT.MIPStarRE.LDT.IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (_root_.LIDT.MIPStarRE.LDT.polynomialEvaluationFamily params.next
        (_root_.LIDT.MIPStarRE.LDT.Preliminaries.completeAtOutcome H (_root_.LIDT.MIPStarRE.LDT.Pasting.pastedFallbackOutcome params)).toSubMeas)
      (_root_.LIDT.MIPStarRE.LDT.MainInductionStep.ldPastingInInductionError params k
        eps delta gamma kappa zeta) := by
  let ν := _root_.LIDT.MIPStarRE.LDT.MainInductionStep.ldPastingInInductionNu params k eps delta gamma zeta
  let completedEval : _root_.LIDT.MIPStarRE.LDT.IdxSubMeas (_root_.LIDT.MIPStarRE.LDT.Point params.next) (_root_.LIDT.MIPStarRE.LDT.Fq params.next) ι :=
    fun u => (_root_.LIDT.MIPStarRE.LDT.Preliminaries.completeAtOutcome (_root_.LIDT.MIPStarRE.LDT.evaluateAt params.next u H)
      ((_root_.LIDT.MIPStarRE.LDT.Pasting.pastedFallbackOutcome params) u)).toSubMeas
  have hcompletedEval :
      completedEval =
        _root_.LIDT.MIPStarRE.LDT.polynomialEvaluationFamily params.next
          (_root_.LIDT.MIPStarRE.LDT.Preliminaries.completeAtOutcome H (_root_.LIDT.MIPStarRE.LDT.Pasting.pastedFallbackOutcome params)).toSubMeas := by
    funext u
    simpa [completedEval, _root_.LIDT.MIPStarRE.LDT.Pasting.pastedFallbackOutcome, _root_.LIDT.MIPStarRE.LDT.polynomialEvaluationFamily] using
      (_root_.LIDT.MIPStarRE.LDT.Preliminaries.evaluateAt_completeAtOutcome params.next H
        (_root_.LIDT.MIPStarRE.LDT.Pasting.pastedFallbackOutcome params) u).symm
  have hresidualMass :
      _root_.LIDT.MIPStarRE.LDT.ev strategy.state (_root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (1 - H.total)) ≤
        kappa * (1 + 1 / (100 * (params.m : _root_.LIDT.MIPStarRE.LDT.Error))) + ν +
          Real.exp (-((k : _root_.LIDT.MIPStarRE.LDT.Error) / (80000 * ((params.m : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ))))) := by
    have hmass :
        _root_.LIDT.MIPStarRE.LDT.ev strategy.state (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) H.total) ≥
          _root_.LIDT.MIPStarRE.LDT.Pasting.ldPastingCompletenessLowerBound params kappa ν k := by
      simpa [ν, _root_.LIDT.MIPStarRE.LDT.subMeasMass, _root_.LIDT.MIPStarRE.LDT.SubMeas.liftLeft] using hcomplete.lowerBound
    calc
      _root_.LIDT.MIPStarRE.LDT.ev strategy.state (_root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (1 - H.total))
        = _root_.LIDT.MIPStarRE.LDT.ev strategy.state (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (1 - H.total)) := by
            simpa using (strategy.permInvState.swap_ev (1 - H.total)).symm
      _ = 1 - _root_.LIDT.MIPStarRE.LDT.ev strategy.state (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) H.total) := by
            have hleftSub :
                _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (1 - H.total) =
                  1 - _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) H.total := by
              ext i j
              rcases i with ⟨i₁, i₂⟩
              rcases j with ⟨j₁, j₂⟩
              by_cases h₁ : i₁ = j₁ <;> by_cases h₂ : i₂ = j₂ <;>
                simp [_root_.LIDT.MIPStarRE.LDT.leftTensor, h₁, h₂, sub_eq_add_neg]
            rw [hleftSub, _root_.LIDT.MIPStarRE.LDT.ev_sub]
            simp [_root_.LIDT.MIPStarRE.LDT.ev_one_of_isNormalized strategy.state strategy.isNormalized]
      _ ≤ 1 - _root_.LIDT.MIPStarRE.LDT.Pasting.ldPastingCompletenessLowerBound params kappa ν k := by
            linarith
      _ = kappa * (1 + 1 / (100 * (params.m : _root_.LIDT.MIPStarRE.LDT.Error))) + ν +
            Real.exp (-((k : _root_.LIDT.MIPStarRE.LDT.Error) / (80000 * ((params.m : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ))))) := by
            simp [_root_.LIDT.MIPStarRE.LDT.Pasting.ldPastingCompletenessLowerBound, ν]
            ring
  have hcompleted :
      _root_.LIDT.MIPStarRE.LDT.ConsRel strategy.state (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params.next))
        (_root_.LIDT.MIPStarRE.LDT.IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        completedEval
        (ν + (kappa * (1 + 1 / (100 * (params.m : _root_.LIDT.MIPStarRE.LDT.Error))) + ν +
          Real.exp (-((k : _root_.LIDT.MIPStarRE.LDT.Error) / (80000 * ((params.m : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ))))))) := by
    constructor
    calc
      _root_.LIDT.MIPStarRE.LDT.bipartiteConsError strategy.state (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params.next))
          (_root_.LIDT.MIPStarRE.LDT.IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          completedEval
        ≤ _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params.next)) (fun u =>
            _root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect strategy.state
                ((strategy.pointMeasurement u).toSubMeas)
                (_root_.LIDT.MIPStarRE.LDT.evaluateAt params.next u H) +
              _root_.LIDT.MIPStarRE.LDT.ev strategy.state (_root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (1 - H.total))) := by
                unfold _root_.LIDT.MIPStarRE.LDT.bipartiteConsError completedEval
                apply _root_.LIDT.MIPStarRE.LDT.avgOver_mono
                intro u
                simpa [_root_.LIDT.MIPStarRE.LDT.evaluateAt, _root_.LIDT.MIPStarRE.LDT.IdxProjMeas.toIdxSubMeas, _root_.LIDT.MIPStarRE.LDT.postprocess_total, ν] using
                  _root_.LIDT.MIPStarRE.LDT.Preliminaries.qBipartiteConsDefect_completeAtOutcome_right_le
                    strategy.state (strategy.pointMeasurement u).toMeasurement
                    (_root_.LIDT.MIPStarRE.LDT.evaluateAt params.next u H)
                    ((_root_.LIDT.MIPStarRE.LDT.Pasting.pastedFallbackOutcome params) u)
      _ = _root_.LIDT.MIPStarRE.LDT.bipartiteConsError strategy.state (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params.next))
            (_root_.LIDT.MIPStarRE.LDT.IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
            (_root_.LIDT.MIPStarRE.LDT.polynomialEvaluationFamily params.next H) +
          _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params.next))
            (fun _ => _root_.LIDT.MIPStarRE.LDT.ev strategy.state (_root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (1 - H.total))) := by
              unfold _root_.LIDT.MIPStarRE.LDT.bipartiteConsError
              rw [_root_.LIDT.MIPStarRE.LDT.avgOver_add]
              simp [_root_.LIDT.MIPStarRE.LDT.IdxProjMeas.toIdxSubMeas, _root_.LIDT.MIPStarRE.LDT.polynomialEvaluationFamily]
      _ ≤ ν + _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params.next))
            (fun _ => _root_.LIDT.MIPStarRE.LDT.ev strategy.state (_root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (1 - H.total))) := by
              exact add_le_add hsubmeas.offDiagonalBound le_rfl
      _ = ν + _root_.LIDT.MIPStarRE.LDT.ev strategy.state (_root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (1 - H.total)) := by
            simpa using _root_.LIDT.MIPStarRE.LDT.avgOver_uniform_const (α := _root_.LIDT.MIPStarRE.LDT.Point params.next)
              (_root_.LIDT.MIPStarRE.LDT.ev strategy.state (_root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι) (1 - H.total)))
      _ ≤ ν + (kappa * (1 + 1 / (100 * (params.m : _root_.LIDT.MIPStarRE.LDT.Error))) + ν +
            Real.exp (-((k : _root_.LIDT.MIPStarRE.LDT.Error) / (80000 * ((params.m : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)))))) := by
              gcongr
  have hsigma :
      ν + (kappa * (1 + 1 / (100 * (params.m : _root_.LIDT.MIPStarRE.LDT.Error))) + ν +
        Real.exp (-((k : _root_.LIDT.MIPStarRE.LDT.Error) / (80000 * ((params.m : _root_.LIDT.MIPStarRE.LDT.Error) ^ (2 : ℕ)))))) =
        _root_.LIDT.MIPStarRE.LDT.MainInductionStep.ldPastingInInductionError params k
          eps delta gamma kappa zeta := by
    simp [_root_.LIDT.MIPStarRE.LDT.MainInductionStep.ldPastingInInductionError, ν]
    ring
  exact ⟨by
    simpa [hcompletedEval] using le_trans hcompleted.offDiagonalBound hsigma.le⟩
