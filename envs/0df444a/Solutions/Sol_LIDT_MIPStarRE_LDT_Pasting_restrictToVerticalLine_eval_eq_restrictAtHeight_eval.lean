-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Pasting.restrictToVerticalLine_eval_eq_restrictAtHeight_eval
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T16:48:09.733645+00:00
-- url     : https://prove2.me/submissions/36d42bdd-bc10-4640-8e1c-542e9c23ec98

-- Generated proof for MIPStarRE.LDT.Pasting.restrictToVerticalLine_eval_eq_restrictAtHeight_eval.
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
import Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_verticalLine_pointAt_appendPoint

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

/- Source helpers from MIPStarRE/LDT/Pasting/ComparisonLemmas/LineInterpolation/Core.lean. -/
/-!
# Line interpolation: core API

Interpolation-support, vertical-line restriction, and completed-slice
interpolation lemmas from `ld-pasting.tex` that form the foundation for the
line-interpolation estimates.

## References

- `references/ldt-paper/ld-pasting.tex`
- `blueprint/src/chapter/ch09_pasting.tex`
-/

@[expose] public section

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]











lemma restrictToAxisParallelLine_apply
    (params : Parameters) [FieldModel params.q]
    (h : Polynomial params.next)
    (ℓ : AxisParallelLine params.next)
    (t : Fq params.next) :
    (Polynomial.restrictToAxisParallelLine params.next h ℓ) t =
      h (AxisParallelLine.pointAt ℓ t) := by
  exact Polynomial.restrictToAxisParallelLine_apply params.next h ℓ t







end MIPStarRE.LDT.Pasting

end

end LIDT

open LIDT
/-!
# Line interpolation: core API

Interpolation-support, vertical-line restriction, and completed-slice
interpolation lemmas from `ld-pasting.tex` that form the foundation for the
line-interpolation estimates.

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
    (params : _root_.LIDT.MIPStarRE.LDT.Parameters) [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    (h : _root_.LIDT.MIPStarRE.LDT.Polynomial params.next)
    (u : _root_.LIDT.MIPStarRE.LDT.Point params)
    (x : _root_.LIDT.MIPStarRE.LDT.Fq params) :
    (_root_.LIDT.MIPStarRE.LDT.Polynomial.restrictToAxisParallelLine params.next h
        ({ base := _root_.LIDT.MIPStarRE.LDT.appendPoint params u _root_.LIDT.MIPStarRE.LDT.zeroCoord
           direction := _root_.LIDT.MIPStarRE.LDT.lastCoord params } : _root_.LIDT.MIPStarRE.LDT.AxisParallelLine params.next)) x =
      (_root_.LIDT.MIPStarRE.LDT.Polynomial.restrictAtHeight params h x) u := by
  let coord := _root_.LIDT.MIPStarRE.LDT.Polynomial.restrictAtHeightCoordinateMap params x
  have hconst :
      (MvPolynomial.eval (_root_.LIDT.MIPStarRE.LDT.decodePoint u)).comp MvPolynomial.C = RingHom.id _ := by
    ext r
    simp
  have hcoord :
      (fun i => MvPolynomial.eval (_root_.LIDT.MIPStarRE.LDT.decodePoint u) (coord i)) =
        _root_.LIDT.MIPStarRE.LDT.decodePoint (_root_.LIDT.MIPStarRE.LDT.appendPoint params u x) := by
    funext i
    by_cases hi : i.1 < params.m
    · simp [coord, _root_.LIDT.MIPStarRE.LDT.Polynomial.restrictAtHeightCoordinateMap, _root_.LIDT.MIPStarRE.LDT.decodePoint, _root_.LIDT.MIPStarRE.LDT.appendPoint, hi]
      rfl
    · simp [coord, _root_.LIDT.MIPStarRE.LDT.Polynomial.restrictAtHeightCoordinateMap, _root_.LIDT.MIPStarRE.LDT.decodePoint, _root_.LIDT.MIPStarRE.LDT.appendPoint, hi]
      rfl
  have hEval := MvPolynomial.eval_eval₂ (x := _root_.LIDT.MIPStarRE.LDT.decodePoint u)
    (f := MvPolynomial.C) (g := coord) (p := h.poly)
  calc
    (_root_.LIDT.MIPStarRE.LDT.Polynomial.restrictToAxisParallelLine params.next h
        ({ base := _root_.LIDT.MIPStarRE.LDT.appendPoint params u _root_.LIDT.MIPStarRE.LDT.zeroCoord
           direction := _root_.LIDT.MIPStarRE.LDT.lastCoord params } : _root_.LIDT.MIPStarRE.LDT.AxisParallelLine params.next)) x
      = h (_root_.LIDT.MIPStarRE.LDT.appendPoint params u x) := by
          rw [_root_.LIDT.MIPStarRE.LDT.Pasting.restrictToAxisParallelLine_apply]
          exact congrArg (fun y => h y) (_root_.LIDT.MIPStarRE.LDT.Pasting.verticalLine_pointAt_appendPoint params u x)
    _ = (_root_.LIDT.MIPStarRE.LDT.Polynomial.restrictAtHeight params h x) u := by
          symm
          calc
            (_root_.LIDT.MIPStarRE.LDT.Polynomial.restrictAtHeight params h x) u
              = _root_.LIDT.MIPStarRE.LDT.encodeScalar
                  (MvPolynomial.eval (_root_.LIDT.MIPStarRE.LDT.decodePoint u)
                    (MvPolynomial.eval₂Hom MvPolynomial.C coord h.poly)) := by
                      rfl
            _ = _root_.LIDT.MIPStarRE.LDT.encodeScalar
                  (MvPolynomial.eval₂
                    ((MvPolynomial.eval (_root_.LIDT.MIPStarRE.LDT.decodePoint u)).comp MvPolynomial.C)
                    (fun i => MvPolynomial.eval (_root_.LIDT.MIPStarRE.LDT.decodePoint u) (coord i)) h.poly) := by
                      have hEval' :=
                        congrArg (_root_.LIDT.MIPStarRE.LDT.encodeScalar (params := params)) hEval
                      simpa [MvPolynomial.eval₂Hom] using hEval'
            _ = _root_.LIDT.MIPStarRE.LDT.encodeScalar
                  (MvPolynomial.eval₂ (RingHom.id _)
                    (_root_.LIDT.MIPStarRE.LDT.decodePoint (_root_.LIDT.MIPStarRE.LDT.appendPoint params u x)) h.poly) := by
                      rw [hconst]
                      change (_root_.LIDT.MIPStarRE.LDT.encodeScalar (params := params.next)
                          (MvPolynomial.eval₂ (RingHom.id _) (fun i =>
                            MvPolynomial.eval (_root_.LIDT.MIPStarRE.LDT.decodePoint u) (coord i)) h.poly)) =
                        _root_.LIDT.MIPStarRE.LDT.encodeScalar (MvPolynomial.eval₂ (RingHom.id _)
                          (_root_.LIDT.MIPStarRE.LDT.decodePoint (_root_.LIDT.MIPStarRE.LDT.appendPoint params u x)) h.poly)
                      simpa using congrArg
                        (fun g => _root_.LIDT.MIPStarRE.LDT.encodeScalar (params := params.next)
                          (MvPolynomial.eval₂ (RingHom.id _) g h.poly)) hcoord
             _ = h (_root_.LIDT.MIPStarRE.LDT.appendPoint params u x) := by
                   rfl
