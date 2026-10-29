-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Test.projectiveEvaluationConsistency_ofFullPolynomialConsistency_heterogeneous
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T17:30:45.167986+00:00
-- url     : https://prove2.me/submissions/5ba9fbd6-e2e4-4eb0-acf2-d07e9d69e8a8

-- Generated proof for MIPStarRE.LDT.Test.projectiveEvaluationConsistency_ofFullPolynomialConsistency_heterogeneous.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_QuantumNonneg
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyPolynomialFamilies
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Theorems.Thm_LIDT_MIPStarRE_LDT_Preliminaries_approxToSimeq_heterogeneous
import Theorems.Thm_LIDT_MIPStarRE_LDT_Test_consRel_constPolynomialEvaluation_heterogeneous

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries
namespace LIDT.MIPStarRE.LDT.Test
end LIDT.MIPStarRE.LDT.Test

namespace LIDT

end LIDT

open LIDT
/-!
# Projective consistency evaluation

This module contains the data-processing lemmas which turn polynomial-level
projective consistency into pointwise consistency after evaluation at a sampled
point.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

open LIDT.MIPStarRE.LDT

open LIDT.MIPStarRE.LDT.Test

theorem solution
    {params : _root_.LIDT.MIPStarRE.LDT.Parameters} [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    {ψ : _root_.LIDT.MIPStarRE.LDT.QuantumState (ιA × ιB)}
    (Q_A : _root_.LIDT.MIPStarRE.LDT.ProjMeas (_root_.LIDT.MIPStarRE.LDT.Polynomial params) ιA) (Q_B : _root_.LIDT.MIPStarRE.LDT.ProjMeas (_root_.LIDT.MIPStarRE.LDT.Polynomial params) ιB)
    {ζ₃ : _root_.LIDT.MIPStarRE.LDT.Error}
    (hline : _root_.LIDT.MIPStarRE.LDT.SDDRel ψ (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
      (_root_.LIDT.MIPStarRE.LDT.constSubMeasFamily (_root_.LIDT.MIPStarRE.LDT.leftPlacedSubMeas (ιB := ιB) Q_A.toSubMeas))
      (_root_.LIDT.MIPStarRE.LDT.constSubMeasFamily (_root_.LIDT.MIPStarRE.LDT.rightPlacedSubMeas (ιA := ιA) Q_B.toSubMeas)) ζ₃) :
    _root_.LIDT.MIPStarRE.LDT.ConsRel ψ (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params))
      (_root_.LIDT.MIPStarRE.LDT.polynomialEvaluationFamily params Q_A.toSubMeas)
      (_root_.LIDT.MIPStarRE.LDT.polynomialEvaluationFamily params Q_B.toSubMeas) (ζ₃ / 2) := by
  let leftConst : _root_.LIDT.MIPStarRE.LDT.IdxProjMeas Unit (_root_.LIDT.MIPStarRE.LDT.Polynomial params) ιA := fun _ => Q_A
  let rightConst : _root_.LIDT.MIPStarRE.LDT.IdxProjMeas Unit (_root_.LIDT.MIPStarRE.LDT.Polynomial params) ιB := fun _ => Q_B
  have happrox :
      _root_.LIDT.MIPStarRE.LDT.SDDRel ψ (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
        (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.placeLeft (ιB := ιB) (_root_.LIDT.MIPStarRE.LDT.IdxProjMeas.toIdxSubMeas leftConst))
        (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.placeRight (ιA := ιA) (_root_.LIDT.MIPStarRE.LDT.IdxProjMeas.toIdxSubMeas rightConst))
        (2 * (ζ₃ / 2)) := by
    change _root_.LIDT.MIPStarRE.LDT.SDDRel ψ (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
      (_root_.LIDT.MIPStarRE.LDT.constSubMeasFamily (_root_.LIDT.MIPStarRE.LDT.leftPlacedSubMeas (ιB := ιB) Q_A.toSubMeas))
      (_root_.LIDT.MIPStarRE.LDT.constSubMeasFamily (_root_.LIDT.MIPStarRE.LDT.rightPlacedSubMeas (ιA := ιA) Q_B.toSubMeas))
      (2 * (ζ₃ / 2))
    convert hline using 1
    ring
  have hcons :=
    _root_.LIDT.MIPStarRE.LDT.Preliminaries.approxToSimeq_heterogeneous ψ (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
      leftConst rightConst (ζ₃ / 2) happrox
  simpa [leftConst, rightConst, _root_.LIDT.MIPStarRE.LDT.constSubMeasFamily, _root_.LIDT.MIPStarRE.LDT.IdxProjMeas.toIdxSubMeas]
    using
      _root_.LIDT.MIPStarRE.LDT.Test.consRel_constPolynomialEvaluation_heterogeneous ψ
        Q_A.toMeasurement Q_B.toMeasurement hcons
