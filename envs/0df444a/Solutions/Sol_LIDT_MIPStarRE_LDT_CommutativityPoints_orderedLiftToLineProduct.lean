-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.CommutativityPoints.orderedLiftToLineProduct
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T14:37:59.418371+00:00
-- url     : https://prove2.me/submissions/da9ade86-8bca-491e-a4e7-67c5a0db7a1c

-- Generated proof for MIPStarRE.LDT.CommutativityPoints.orderedLiftToLineProduct.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
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
import Theorems.Thm_LIDT_MIPStarRE_LDT_CommutativityPoints_sampledDiagonalLineApproximation_ignore_second
import Theorems.Thm_LIDT_MIPStarRE_LDT_CommutativityPoints_sddOpRel_congr_outcome
import Theorems.Thm_LIDT_MIPStarRE_LDT_CommutativityPoints_subMeas_sum_adjoint_mul_le_one

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.CommutativityPoints
end LIDT.MIPStarRE.LDT.CommutativityPoints

namespace LIDT

/- Source helpers from MIPStarRE/LDT/CommutativityPoints/SharedHelpers/Core.lean. -/
/-!
# Section 10 commutativity points: shared helpers core

Shared reindexing and tensor-placement helpers used by the Section 10
commutativity-of-points argument.

## References

- `references/ldt-paper/commutativity-points.tex`
- `blueprint/src/chapter/ch08_commutativity.tex`
-/

@[expose] public section

namespace MIPStarRE.LDT.CommutativityPoints

open MIPStarRE.LDT.GlobalVariance (PointPairQuestion)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open scoped _root_.Matrix MatrixOrder ComplexOrder BigOperators
/-! ## Shared reindexing and tensor-placement helpers -/















/-- Multiplying a right lift with a left-placed family gives the tensor product. -/
lemma liftRight_mul_leftPlaced_outcome
    {α β : Type*}
    [Fintype α] [Fintype β]
    (A : SubMeas α ι) (B : SubMeas β ι)
    (a : α) (b : β) :
    (A.liftRight).outcome a * (OpFamily.leftPlacedOpFamily B.toOpFamily).outcome b =
      opTensor (B.outcome b) (A.outcome a) := by
  calc
    (A.liftRight).outcome a * (OpFamily.leftPlacedOpFamily B.toOpFamily).outcome b
      = rightTensor (A.outcome a) * leftTensor (B.outcome b) := by
          rfl
    _ = opTensor (B.outcome b) (A.outcome a) := by
          rw [rightTensor_mul_leftTensor_eq_opTensor]

/-- Multiplying a right lift with a right-placed family stays on the right tensor factor. -/
lemma liftRight_mul_rightPlaced_outcome
    {α β : Type*}
    [Fintype α] [Fintype β]
    (A : SubMeas α ι) (B : SubMeas β ι)
    (a : α) (b : β) :
    (A.liftRight).outcome a * (OpFamily.rightPlacedOpFamily B.toOpFamily).outcome b =
      rightTensor (A.outcome a * B.outcome b) := by
  calc
    (A.liftRight).outcome a * (OpFamily.rightPlacedOpFamily B.toOpFamily).outcome b
      = rightTensor (A.outcome a) * rightTensor (B.outcome b) := by
          rfl
    _ = rightTensor (A.outcome a * B.outcome b) := by
          rw [rightTensor_mul_rightTensor]

end MIPStarRE.LDT.CommutativityPoints

end

/- Source helpers from MIPStarRE/LDT/CommutativityPoints/SharedHelpers/SharedLine.lean. -/
/-!
# Section 10 commutativity points: shared-line helpers

Compatibility lemmas between sampled point pairs and shared-diagonal line
questions, used by both the lift and drop comparisons.

## References

- `references/ldt-paper/commutativity-points.tex`
- `blueprint/src/chapter/ch08_commutativity.tex`
-/

@[expose] public section

namespace MIPStarRE.LDT.CommutativityPoints

open MIPStarRE.LDT.GlobalVariance (PointPairQuestion)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open scoped _root_.Matrix MatrixOrder ComplexOrder BigOperators


















lemma pointDiagonalLineMixedProductLeft_outcome
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (q : PointPairDiagonalLineQuestion params)
    (a b : Fq params) :
    ((IdxSubMeas.toIdxOpFamily
        (pointDiagonalLineMixedProductLeft params strategy) q).outcome (a, b)) =
      opTensor
        ((strategy.pointMeasurement (q.1.pointAt q.2.1)).outcome a)
        ((sampledDiagonalLineEvaluation params strategy (q.1, q.2.2)).outcome b) := by
  simp [pointDiagonalLineMixedProductLeft, tensorProductSubMeas,
    sampledDiagonalLineEvaluation, IdxSubMeas.toIdxOpFamily, SubMeas.toOpFamily,
    leftTensor_mul_rightTensor_eq_opTensor]



lemma diagonalLineProductOrdered_outcome
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (q : PointPairDiagonalLineQuestion params)
    (a b : Fq params) :
    (diagonalLineProductOrdered params strategy q).outcome (a, b) =
      rightTensor
        ((sampledDiagonalLineEvaluation params strategy (q.1, q.2.2)).outcome b *
          (sampledDiagonalLineEvaluation params strategy (q.1, q.2.1)).outcome a) := by
  simp [diagonalLineProductOrdered, sampledDiagonalLineEvaluation,
    OpFamily.rightPlacedOpFamily, reversedProductOpFamily]







end MIPStarRE.LDT.CommutativityPoints

end

end LIDT

open LIDT
/-!
# Section 10 commutativity points: lift comparisons

Comparison lemmas lifting the ordered shared-line point product to the mixed
line family, used in the lift direction of the Section 10 point-commutativity
argument.

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
    (strategy : _root_.LIDT.MIPStarRE.LDT.SymStrat params ι)
    (eps delta gamma : _root_.LIDT.MIPStarRE.LDT.Error)
    (hgood : strategy.IsGood eps delta gamma) :
    _root_.LIDT.MIPStarRE.LDT.SDDOpRel strategy.state
      (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointPairSharedDiagonalLineDistribution params)
      (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.toIdxOpFamily (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointDiagonalLineMixedProductLeft params strategy))
      (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.diagonalLineProductOrdered params strategy)
      (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointDiagonalLineApproxError params gamma) := by
  /-
  Second replacement step:
  `A^u_a ⊗ L^ℓ_[f(v)=b] ≈ I ⊗ (L^ℓ_[f(v)=b] L^ℓ_[f(u)=a])`.
  -/
  let Araw : _root_.LIDT.MIPStarRE.LDT.IdxOpFamily (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.PointPairDiagonalLineQuestion params) (_root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.Fq params)
      (ι × ι) :=
    fun q =>
      let Lv := _root_.LIDT.MIPStarRE.LDT.CommutativityPoints.sampledDiagonalLineEvaluation params strategy (q.1, q.2.2)
      ({ outcome := fun ab : _root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.Fq params =>
           _root_.LIDT.MIPStarRE.LDT.opTensor
             ((strategy.pointMeasurement (q.1.pointAt q.2.1)).outcome ab.1)
             (Lv.outcome ab.2)
         total := ∑ ab : _root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.Fq params,
           _root_.LIDT.MIPStarRE.LDT.opTensor
             ((strategy.pointMeasurement (q.1.pointAt q.2.1)).outcome ab.1)
             (Lv.outcome ab.2)
       } : _root_.LIDT.MIPStarRE.LDT.OpFamily (_root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.Fq params) (ι × ι))
  let Braw : _root_.LIDT.MIPStarRE.LDT.IdxOpFamily (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.PointPairDiagonalLineQuestion params) (_root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.Fq params)
      (ι × ι) :=
    fun q =>
      let Lu := _root_.LIDT.MIPStarRE.LDT.CommutativityPoints.sampledDiagonalLineEvaluation params strategy (q.1, q.2.1)
      let Lv := _root_.LIDT.MIPStarRE.LDT.CommutativityPoints.sampledDiagonalLineEvaluation params strategy (q.1, q.2.2)
      ({ outcome := fun ab : _root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.Fq params =>
           _root_.LIDT.MIPStarRE.LDT.rightTensor (Lv.outcome ab.2 * Lu.outcome ab.1)
         total := ∑ ab : _root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.Fq params,
           _root_.LIDT.MIPStarRE.LDT.rightTensor (Lv.outcome ab.2 * Lu.outcome ab.1)
       } : _root_.LIDT.MIPStarRE.LDT.OpFamily (_root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.Fq params) (ι × ι))
  let hbase :=
    _root_.LIDT.MIPStarRE.LDT.CommutativityPoints.sampledDiagonalLineApproximation_ignore_second params strategy eps delta gamma hgood
  have hcab :=
    _root_.LIDT.MIPStarRE.LDT.Preliminaries.cabApproxDelta_raw
      strategy.state
      (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointPairSharedDiagonalLineDistribution params)
      (fun q =>
        _root_.LIDT.MIPStarRE.LDT.OpFamily.leftPlacedOpFamily (ιB := ι)
          ((strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas))
      (fun q =>
        _root_.LIDT.MIPStarRE.LDT.OpFamily.rightPlacedOpFamily (ιA := ι)
          (_root_.LIDT.MIPStarRE.LDT.SubMeas.toOpFamily (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.sampledDiagonalLineEvaluation params strategy (q.1, q.2.1))))
      (fun q _a b =>
        ((_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.sampledDiagonalLineEvaluation params strategy (q.1, q.2.2)).liftRight).outcome b)
      (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointDiagonalLineApproxError params gamma)
      hbase
      (by
        intro q a
        exact _root_.LIDT.MIPStarRE.LDT.CommutativityPoints.subMeas_sum_adjoint_mul_le_one
          ((_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.sampledDiagonalLineEvaluation params strategy (q.1, q.2.2)).liftRight))
  let Astep : _root_.LIDT.MIPStarRE.LDT.IdxOpFamily (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.PointPairDiagonalLineQuestion params) (_root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.Fq params)
      (ι × ι) :=
    fun q =>
      let Au := (strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas
      let Lv := _root_.LIDT.MIPStarRE.LDT.CommutativityPoints.sampledDiagonalLineEvaluation params strategy (q.1, q.2.2)
      ({ outcome := fun ab : _root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.Fq params =>
           (Lv.liftRight).outcome ab.2 *
             (_root_.LIDT.MIPStarRE.LDT.OpFamily.leftPlacedOpFamily (ιB := ι) Au).outcome ab.1
         total := ∑ ab : _root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.Fq params,
           (Lv.liftRight).outcome ab.2 *
             (_root_.LIDT.MIPStarRE.LDT.OpFamily.leftPlacedOpFamily (ιB := ι) Au).outcome ab.1
       } : _root_.LIDT.MIPStarRE.LDT.OpFamily (_root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.Fq params) (ι × ι))
  let Bstep : _root_.LIDT.MIPStarRE.LDT.IdxOpFamily (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.PointPairDiagonalLineQuestion params) (_root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.Fq params)
      (ι × ι) :=
    fun q =>
      let Lu := _root_.LIDT.MIPStarRE.LDT.CommutativityPoints.sampledDiagonalLineEvaluation params strategy (q.1, q.2.1)
      let Lv := _root_.LIDT.MIPStarRE.LDT.CommutativityPoints.sampledDiagonalLineEvaluation params strategy (q.1, q.2.2)
      ({ outcome := fun ab : _root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.Fq params =>
           (Lv.liftRight).outcome ab.2 *
             (_root_.LIDT.MIPStarRE.LDT.OpFamily.rightPlacedOpFamily (ιA := ι) (_root_.LIDT.MIPStarRE.LDT.SubMeas.toOpFamily Lu)).outcome ab.1
         total := ∑ ab : _root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.Fq params,
           (Lv.liftRight).outcome ab.2 *
             (_root_.LIDT.MIPStarRE.LDT.OpFamily.rightPlacedOpFamily (ιA := ι) (_root_.LIDT.MIPStarRE.LDT.SubMeas.toOpFamily Lu)).outcome ab.1
       } : _root_.LIDT.MIPStarRE.LDT.OpFamily (_root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.Fq params) (ι × ι))
  exact _root_.LIDT.MIPStarRE.LDT.CommutativityPoints.sddOpRel_congr_outcome strategy.state
    (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointPairSharedDiagonalLineDistribution params)
    Astep Bstep
    (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.toIdxOpFamily (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointDiagonalLineMixedProductLeft params strategy))
    (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.diagonalLineProductOrdered params strategy)
    (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointDiagonalLineApproxError params gamma)
    (by
      intro q ab
      rcases ab with ⟨a, b⟩
      calc
        (Astep q).outcome (a, b)
          = _root_.LIDT.MIPStarRE.LDT.opTensor
              ((strategy.pointMeasurement (q.1.pointAt q.2.1)).outcome a)
              ((_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.sampledDiagonalLineEvaluation params strategy (q.1, q.2.2)).outcome b) := by
                  simpa [Astep] using
                    _root_.LIDT.MIPStarRE.LDT.CommutativityPoints.liftRight_mul_leftPlaced_outcome
                      (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.sampledDiagonalLineEvaluation params strategy (q.1, q.2.2))
                      ((strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas)
                      b a
        _ =
            ((_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.toIdxOpFamily
                (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointDiagonalLineMixedProductLeft params strategy)) q).outcome (a, b) := by
              symm
              exact _root_.LIDT.MIPStarRE.LDT.CommutativityPoints.pointDiagonalLineMixedProductLeft_outcome params strategy q a b)
    (by
      intro q ab
      rcases ab with ⟨a, b⟩
      calc
        (Bstep q).outcome (a, b)
          = _root_.LIDT.MIPStarRE.LDT.rightTensor
              ((_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.sampledDiagonalLineEvaluation params strategy (q.1, q.2.2)).outcome b *
                (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.sampledDiagonalLineEvaluation params strategy (q.1, q.2.1)).outcome a) := by
                  simpa [Bstep] using
                    _root_.LIDT.MIPStarRE.LDT.CommutativityPoints.liftRight_mul_rightPlaced_outcome
                      (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.sampledDiagonalLineEvaluation params strategy (q.1, q.2.2))
                      (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.sampledDiagonalLineEvaluation params strategy (q.1, q.2.1))
                      b a
        _ = (_root_.LIDT.MIPStarRE.LDT.CommutativityPoints.diagonalLineProductOrdered params strategy q).outcome (a, b) := by
              symm
              exact _root_.LIDT.MIPStarRE.LDT.CommutativityPoints.diagonalLineProductOrdered_outcome params strategy q a b)
    hcab
