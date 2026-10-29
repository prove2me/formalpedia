-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Test.consRel_constPolynomialEvaluation_heterogeneous
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T17:26:51.729232+00:00
-- url     : https://prove2.me/submissions/b4117db0-2bb4-4418-a28c-d3d7c7f13ecb

-- Generated proof for MIPStarRE.LDT.Test.consRel_constPolynomialEvaluation_heterogeneous.
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
    (ψ : _root_.LIDT.MIPStarRE.LDT.QuantumState (ιA × ιB))
    (A : _root_.LIDT.MIPStarRE.LDT.Measurement (_root_.LIDT.MIPStarRE.LDT.Polynomial params) ιA) (B : _root_.LIDT.MIPStarRE.LDT.Measurement (_root_.LIDT.MIPStarRE.LDT.Polynomial params) ιB)
    {δ : _root_.LIDT.MIPStarRE.LDT.Error}
    (h : _root_.LIDT.MIPStarRE.LDT.ConsRel ψ (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
      (_root_.LIDT.MIPStarRE.LDT.constSubMeasFamily A.toSubMeas)
      (_root_.LIDT.MIPStarRE.LDT.constSubMeasFamily B.toSubMeas) δ) :
    _root_.LIDT.MIPStarRE.LDT.ConsRel ψ (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params))
      (_root_.LIDT.MIPStarRE.LDT.polynomialEvaluationFamily params A.toSubMeas)
      (_root_.LIDT.MIPStarRE.LDT.polynomialEvaluationFamily params B.toSubMeas) δ := by
  classical
  let Aconst : _root_.LIDT.MIPStarRE.LDT.IdxSubMeas (_root_.LIDT.MIPStarRE.LDT.Point params) (_root_.LIDT.MIPStarRE.LDT.Polynomial params) ιA := fun _ => A.toSubMeas
  let Bconst : _root_.LIDT.MIPStarRE.LDT.IdxSubMeas (_root_.LIDT.MIPStarRE.LDT.Point params) (_root_.LIDT.MIPStarRE.LDT.Polynomial params) ιB := fun _ => B.toSubMeas
  have hconstPoint :
      _root_.LIDT.MIPStarRE.LDT.ConsRel ψ (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params)) Aconst Bconst δ := by
    rcases h with ⟨hbound⟩
    constructor
    have hpoint_avg :
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params))
            (fun _ : _root_.LIDT.MIPStarRE.LDT.Point params => _root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect ψ A.toSubMeas B.toSubMeas) =
          _root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect ψ A.toSubMeas B.toSubMeas := by
      have : Nonempty (_root_.LIDT.MIPStarRE.LDT.Point params) := by infer_instance
      simpa using
        (_root_.LIDT.MIPStarRE.LDT.avgOver_uniform_const (α := _root_.LIDT.MIPStarRE.LDT.Point params)
          (_root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect ψ A.toSubMeas B.toSubMeas))
    have hunit_eq :
        _root_.LIDT.MIPStarRE.LDT.bipartiteConsError ψ (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
            (_root_.LIDT.MIPStarRE.LDT.constSubMeasFamily A.toSubMeas) (_root_.LIDT.MIPStarRE.LDT.constSubMeasFamily B.toSubMeas) =
          _root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect ψ A.toSubMeas B.toSubMeas := by
      have hunit_avg :
          _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
              (fun _ : Unit => _root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect ψ A.toSubMeas B.toSubMeas) =
            _root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect ψ A.toSubMeas B.toSubMeas := by
        simpa using
          (_root_.LIDT.MIPStarRE.LDT.avgOver_uniform_const (α := Unit)
            (_root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect ψ A.toSubMeas B.toSubMeas))
      simpa [_root_.LIDT.MIPStarRE.LDT.bipartiteConsError, _root_.LIDT.MIPStarRE.LDT.constSubMeasFamily] using hunit_avg
    calc
      _root_.LIDT.MIPStarRE.LDT.bipartiteConsError ψ (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params)) Aconst Bconst
          = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params))
              (fun _ : _root_.LIDT.MIPStarRE.LDT.Point params => _root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect ψ A.toSubMeas B.toSubMeas) := by
            rfl
      _ = _root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect ψ A.toSubMeas B.toSubMeas := hpoint_avg
      _ = _root_.LIDT.MIPStarRE.LDT.bipartiteConsError ψ (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
            (_root_.LIDT.MIPStarRE.LDT.constSubMeasFamily A.toSubMeas) (_root_.LIDT.MIPStarRE.LDT.constSubMeasFamily B.toSubMeas) :=
            hunit_eq.symm
      _ ≤ δ := hbound
  have hprocessed :=
    _root_.LIDT.MIPStarRE.LDT.Preliminaries.consRelDataProcessing_questionDependent ψ
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params)) Aconst Bconst δ (fun u g => g u) hconstPoint
  change _root_.LIDT.MIPStarRE.LDT.ConsRel ψ (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params))
    (fun u => _root_.LIDT.MIPStarRE.LDT.postprocess A.toSubMeas (fun g : _root_.LIDT.MIPStarRE.LDT.Polynomial params => g.toFun u))
    (fun u => _root_.LIDT.MIPStarRE.LDT.postprocess B.toSubMeas (fun g : _root_.LIDT.MIPStarRE.LDT.Polynomial params => g.toFun u)) δ
  simpa [Aconst, Bconst] using hprocessed
