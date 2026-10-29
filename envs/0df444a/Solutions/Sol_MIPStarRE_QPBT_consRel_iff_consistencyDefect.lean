-- Prove2me | solution 1 for MIPStarRE.QPBT.consRel_iff_consistencyDefect
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:06:36.886923+00:00
-- url     : https://prove2.me/submissions/eda324c8-1491-4637-ac7b-d5156df0e83b

-- Generated proof for MIPStarRE.QPBT.consRel_iff_consistencyDefect.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OperatorExpectations
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementCore
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Families
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Interpolation
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_AvgCongr
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Consistency_Measurements
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_TensorSupport
import Mathlib
import Theorems.Thm_LIDT_MIPStarRE_LDT_PureState_toQuantumState_isNormalized
import Theorems.Thm_LIDT_MIPStarRE_LDT_qBipartiteConsDefect_of_measurements
import Theorems.Thm_MIPStarRE_QPBT_DistanceCalculus_consistencyDefect_eq_one_sub_overlap

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
end LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus

/- Source helpers from QPBT/Games/DistanceTheorems/TensorSupport.lean. -/
/-!
# Tensor-placement and marginal identities

This module collects tensor-placement, marginal, and finite-fiber identities
used in data processing and the commutator estimate.

## References

- `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:397-461`
- Blueprint `fact:triangle-for-simeq`, `fact:data-processing`, and
  `lem:commutation-analysis`
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.DistanceCalculus

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum
open LIDT.MIPStarRE.LDT.MakingMeasurementsProjective





/-- Formalization-only auxiliary lemma for Fact 4.26: products of left and right
placements evaluate as a Kronecker product. -/
theorem placed_product_stateQForm_eq {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (A : _root_.LIDT.MIPStarRE.Quantum.Op ιA) (B : _root_.LIDT.MIPStarRE.Quantum.Op ιB) :
    _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron A 1 * _root_.MIPStarRE.QPBT.heteroKron 1 B) =
      _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron A B) := by
  congr 1
  exact _root_.LIDT.MIPStarRE.LDT.leftTensor_mul_rightTensor_eq_opTensor A B































end MIPStarRE.QPBT.DistanceCalculus

/-!
# State conversion and direct point readout

This module contains the pure-state conversion and direct point-readout
portion of the low-degree consistency transport.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:393-458`
- `references/ldt-paper/test_definition.tex:180-202`
- `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.LDT.Preliminaries
open LIDT.MIPStarRE.Quantum



/-! ## Equality of the two consistency formulations -/

-- The following identities identify pure-state expectation with the
-- Euclidean quadratic form used in the consistency calculations below.  They
-- send a pure state to its Euclidean coordinate vector and identify the
-- quadratic form of that vector with evaluation in the associated density
-- state; they are stated for an arbitrary finite index type in
-- `MIPStarRE/QPBT/Games/DistanceTheorems/Support.lean`.

theorem solution
    {Question Outcome iotaA iotaB : Type*}
    [Fintype Question] [DecidableEq Question]
    [Fintype Outcome] [DecidableEq Outcome]
    [Fintype iotaA] [DecidableEq iotaA]
    [Fintype iotaB] [DecidableEq iotaB]
    [Nonempty (iotaA × iotaB)]
    (psi : _root_.LIDT.MIPStarRE.LDT.PureState (iotaA × iotaB))
    (mu : _root_.LIDT.MIPStarRE.LDT.Distribution Question) (hmu : mu.IsProbability)
    (A : Question → _root_.LIDT.MIPStarRE.LDT.ProjMeas Outcome iotaA)
    (B : Question → _root_.LIDT.MIPStarRE.LDT.ProjMeas Outcome iotaB) (delta : ℝ) :
    _root_.LIDT.MIPStarRE.LDT.ConsRel (psi : _root_.LIDT.MIPStarRE.LDT.QuantumState (iotaA × iotaB)) mu
        (fun x => (A x).toSubMeas) (fun x => (B x).toSubMeas) delta ↔
      _root_.MIPStarRE.QPBT.consistencyDefect mu
        (fun x a => _root_.MIPStarRE.QPBT.heteroKron ((A x).outcome a) 1)
        (fun x a => _root_.MIPStarRE.QPBT.heteroKron 1 ((B x).outcome a))
        (_root_.MIPStarRE.QPBT.DistanceCalculus.pureStateEuclideanVector psi) ≤ delta := by
  let AM : Question → _root_.LIDT.MIPStarRE.Quantum.Measurement Outcome (iotaA × iotaB) :=
    fun x => _root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement
      (_root_.MIPStarRE.QPBT.ldtMeasurementToMatrixMeasurement (A x).toMeasurement)
  let BM : Question → _root_.LIDT.MIPStarRE.Quantum.Measurement Outcome (iotaA × iotaB) :=
    fun x => _root_.MIPStarRE.QPBT.DistanceCalculus.rightPlacedMeasurement
      (_root_.MIPStarRE.QPBT.ldtMeasurementToMatrixMeasurement (B x).toMeasurement)
  have hAM (x : Question) (a : Outcome) :
      (AM x).effect a = _root_.MIPStarRE.QPBT.heteroKron ((A x).outcome a) 1 := rfl
  have hBM (x : Question) (a : Outcome) :
      (BM x).effect a = _root_.MIPStarRE.QPBT.heteroKron 1 ((B x).outcome a) := rfl
  have hdefect :
      _root_.MIPStarRE.QPBT.consistencyDefect mu
          (fun x a => _root_.MIPStarRE.QPBT.heteroKron ((A x).outcome a) 1)
          (fun x a => _root_.MIPStarRE.QPBT.heteroKron 1 ((B x).outcome a))
          (_root_.MIPStarRE.QPBT.DistanceCalculus.pureStateEuclideanVector psi) =
        _root_.LIDT.MIPStarRE.LDT.bipartiteConsError (psi : _root_.LIDT.MIPStarRE.LDT.QuantumState (iotaA × iotaB)) mu
          (fun x => (A x).toSubMeas) (fun x => (B x).toSubMeas) := by
    calc
      _root_.MIPStarRE.QPBT.consistencyDefect mu
          (fun x a => _root_.MIPStarRE.QPBT.heteroKron ((A x).outcome a) 1)
          (fun x a => _root_.MIPStarRE.QPBT.heteroKron 1 ((B x).outcome a))
          (_root_.MIPStarRE.QPBT.DistanceCalculus.pureStateEuclideanVector psi) =
          1 - _root_.LIDT.MIPStarRE.LDT.avgOver mu (fun x => ∑ a,
            _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm (_root_.MIPStarRE.QPBT.DistanceCalculus.pureStateEuclideanVector psi)
              ((AM x).effect a * (BM x).effect a)) := by
            simpa only [hAM, hBM] using
              _root_.MIPStarRE.QPBT.DistanceCalculus.consistencyDefect_eq_one_sub_overlap
                mu AM BM (_root_.MIPStarRE.QPBT.DistanceCalculus.pureStateEuclideanVector psi) hmu
                  (_root_.MIPStarRE.QPBT.DistanceCalculus.pureStateEuclideanVector_norm psi)
      _ = _root_.LIDT.MIPStarRE.LDT.avgOver mu (fun x => 1 - ∑ a,
            _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm (_root_.MIPStarRE.QPBT.DistanceCalculus.pureStateEuclideanVector psi)
              ((AM x).effect a * (BM x).effect a)) := by
            rw [_root_.LIDT.MIPStarRE.LDT.avgOver_sub, _root_.LIDT.MIPStarRE.LDT.avgOver_const_of_isProbability mu hmu]
      _ = _root_.LIDT.MIPStarRE.LDT.bipartiteConsError (psi : _root_.LIDT.MIPStarRE.LDT.QuantumState (iotaA × iotaB)) mu
          (fun x => (A x).toSubMeas) (fun x => (B x).toSubMeas) := by
            unfold _root_.LIDT.MIPStarRE.LDT.bipartiteConsError
            apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
            intro x
            rw [_root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect_of_measurements
              (psi : _root_.LIDT.MIPStarRE.LDT.QuantumState (iotaA × iotaB))
              (A x).toMeasurement (B x).toMeasurement]
            rw [_root_.LIDT.MIPStarRE.LDT.ev_one_of_isNormalized (psi : _root_.LIDT.MIPStarRE.LDT.QuantumState (iotaA × iotaB))
              psi.toQuantumState_isNormalized]
            congr 1
            apply Finset.sum_congr rfl
            intro a _
            rw [hAM, hBM]
            rw [_root_.MIPStarRE.QPBT.DistanceCalculus.placed_product_stateQForm_eq]
            exact _root_.MIPStarRE.QPBT.DistanceCalculus.pureState_stateQForm_eq_ev psi
              (_root_.LIDT.MIPStarRE.LDT.opTensor ((A x).outcome a) ((B x).outcome a))
  constructor
  · intro h
    rw [hdefect]
    exact h.offDiagonalBound
  · intro h
    refine ⟨?_⟩
    rw [← hdefect]
    exact h
