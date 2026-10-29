-- Prove2me | solution 1 for LIDT.MIPStarRE.LDT.Preliminaries.simeqToApprox_heterogeneous
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T17:06:53.192025+00:00
-- url     : https://prove2.me/submissions/1767a6e2-d82a-4658-9874-3756ba679ed5

-- Generated proof for MIPStarRE.LDT.Preliminaries.simeqToApprox_heterogeneous.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_QuantumNonneg
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
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

end LIDT

open LIDT
/-!
# Preliminary comparison theorems: core layer

Core comparison lemmas and measurement-agreement translations for the
preliminaries chapter.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder


open LIDT.MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT

theorem solution {Question Outcome : Type*}
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome]
    (ψ : _root_.LIDT.MIPStarRE.LDT.QuantumState (ιA × ιB)) (𝒟 : _root_.LIDT.MIPStarRE.LDT.Distribution Question)
    (A : _root_.LIDT.MIPStarRE.LDT.IdxMeas Question Outcome ιA) (B : _root_.LIDT.MIPStarRE.LDT.IdxMeas Question Outcome ιB)
    (δ : _root_.LIDT.MIPStarRE.LDT.Error) :
    _root_.LIDT.MIPStarRE.LDT.ConsRel ψ 𝒟
        (_root_.LIDT.MIPStarRE.LDT.IdxMeas.toIdxSubMeas A)
        (_root_.LIDT.MIPStarRE.LDT.IdxMeas.toIdxSubMeas B) δ →
      _root_.LIDT.MIPStarRE.LDT.SDDRel ψ 𝒟
        (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.placeLeft (ιB := ιB) (_root_.LIDT.MIPStarRE.LDT.IdxMeas.toIdxSubMeas A))
        (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.placeRight (ιA := ιA) (_root_.LIDT.MIPStarRE.LDT.IdxMeas.toIdxSubMeas B))
        (2 * δ) := by
  intro ⟨hcons⟩
  rw [_root_.LIDT.MIPStarRE.LDT.bipartiteConsError_eq_consError_placed] at hcons
  constructor
  unfold _root_.LIDT.MIPStarRE.LDT.sddError _root_.LIDT.MIPStarRE.LDT.consError at *
  calc
    _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟
        (fun q =>
          _root_.LIDT.MIPStarRE.LDT.qSDD ψ
            ((_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.placeLeft (ιB := ιB) (_root_.LIDT.MIPStarRE.LDT.IdxMeas.toIdxSubMeas A)) q)
            ((_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.placeRight (ιA := ιA) (_root_.LIDT.MIPStarRE.LDT.IdxMeas.toIdxSubMeas B)) q))
      ≤ _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟
          (fun q =>
            2 * _root_.LIDT.MIPStarRE.LDT.qConsDefect ψ
              ((_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.placeLeft (ιB := ιB) (_root_.LIDT.MIPStarRE.LDT.IdxMeas.toIdxSubMeas A)) q)
              ((_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.placeRight (ιA := ιA) (_root_.LIDT.MIPStarRE.LDT.IdxMeas.toIdxSubMeas B)) q)) := by
          apply _root_.LIDT.MIPStarRE.LDT.avgOver_mono
          intro q
          let A' : _root_.LIDT.MIPStarRE.LDT.Measurement Outcome (ιA × ιB) :=
            _root_.LIDT.MIPStarRE.LDT.leftLiftedMeasurement (ιB := ιB) (A q)
          let B' : _root_.LIDT.MIPStarRE.LDT.Measurement Outcome (ιA × ιB) :=
            _root_.LIDT.MIPStarRE.LDT.rightLiftedMeasurement (ιA := ιA) (B q)
          simpa [A', B', _root_.LIDT.MIPStarRE.LDT.leftLiftedMeasurement, _root_.LIDT.MIPStarRE.LDT.rightLiftedMeasurement,
            _root_.LIDT.MIPStarRE.LDT.IdxSubMeas.placeLeft, _root_.LIDT.MIPStarRE.LDT.IdxSubMeas.placeRight, _root_.LIDT.MIPStarRE.LDT.leftPlacedSubMeas, _root_.LIDT.MIPStarRE.LDT.rightPlacedSubMeas,
            _root_.LIDT.MIPStarRE.LDT.IdxMeas.toIdxSubMeas] using
            questionSDD_le_two_questionConsistency ψ A' B'
    _ = 2 * _root_.LIDT.MIPStarRE.LDT.avgOver 𝒟
          (fun q =>
            _root_.LIDT.MIPStarRE.LDT.qConsDefect ψ
              ((_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.placeLeft (ιB := ιB) (_root_.LIDT.MIPStarRE.LDT.IdxMeas.toIdxSubMeas A)) q)
              ((_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.placeRight (ιA := ιA) (_root_.LIDT.MIPStarRE.LDT.IdxMeas.toIdxSubMeas B)) q)) := by
          rw [_root_.LIDT.MIPStarRE.LDT.avgOver_const_mul]
    _ ≤ 2 * δ := by
          exact mul_le_mul_of_nonneg_left hcons (by norm_num)
