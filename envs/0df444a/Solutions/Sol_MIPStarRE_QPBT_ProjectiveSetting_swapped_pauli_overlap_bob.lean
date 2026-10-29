-- Prove2me | solution 1 for MIPStarRE.QPBT.ProjectiveSetting.swapped_pauli_overlap_bob
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T01:16:53.787181+00:00
-- url     : https://prove2.me/submissions/1ecada9e-58be-47ef-989f-5be1180ca1a2

-- Generated proof for MIPStarRE.QPBT.ProjectiveSetting.swapped_pauli_overlap_bob.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_TensorPlacement
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Families
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Interpolation
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_AvgCongr
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Algebra_Decoding
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCode
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
import Definitions.Def_QPBT_QPBT_Extraction_Defs
import Definitions.Def_QPBT_QPBT_Extraction_EncodingSupport
import Definitions.Def_QPBT_QPBT_Extraction_Observables
import Definitions.Def_QPBT_QPBT_Extraction_PauliTransport
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_TensorSupport
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_Setup
import Definitions.Def_QPBT_QPBT_State
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_ProjectiveSetting_swapped_block_overlap_eq
import Theorems.Thm_MIPStarRE_QPBT_sum_tildeM_eq_one
import Theorems.Thm_MIPStarRE_QPBT_swapUnitary_conj_tildeM
import Theorems.Thm_MIPStarRE_QPBT_tildeM_isProj

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus
namespace MIPStarRE.QPBT.ProjectiveSetting
end MIPStarRE.QPBT.ProjectiveSetting

/- Source helpers from QPBT/Extraction/PointConsistency.lean. -/
/-!
# Point consistency after decoding polynomial outcomes

This module expands the overlap of an original point measurement with a
pulled-apart measurement. The decoded polynomial is kept explicit, so the
calculation does not use the decoder identity outside the encoding image.

## References

These are auxiliary identities for blueprint `lem:qld-construct-the-paulis`,
paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1483-1492`.
The restriction on the decoder identity is recorded in
`docs/paper-gaps/qpbt_decoding-identity.tex`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum DistanceCalculus

noncomputable section

namespace ProjectiveSetting

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {epsilon : ℝ}

/-- Placing a tensor with an identity on Bob's last register recovers `BB'`. -/
theorem placeSide_bob_tensor_one (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon)
    (B : _root_.LIDT.MIPStarRE.Quantum.Op (S.ExpandedLocalSpace .bob)) :
    S.placeSide .bob (_root_.MIPStarRE.QPBT.heteroKron B (1 : _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.PauliRegister P))) = S.place .BB' B := by
  ext row col
  simp [_root_.MIPStarRE.QPBT.ProjectiveSetting.placeSide, _root_.MIPStarRE.QPBT.sixRegExtractionEquiv, _root_.MIPStarRE.QPBT.reindexOp, _root_.MIPStarRE.QPBT.heteroKron, Matrix.kronecker,
    _root_.MIPStarRE.QPBT.ProjectiveSetting.place, Matrix.one_apply, Prod.ext_iff, ite_and, mul_ite, ite_mul]
  split_ifs <;> rfl







end ProjectiveSetting









end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Extraction/PointConsistencyPrime.lean. -/
/-!
# Point consistency with Alice's pulled-apart measurement

This module proves the register-interchanged overlap calculation for Item 1 of
blueprint `lem:qld-construct-the-paulis`. Polynomial evaluation is replaced by
decoded evaluation only on encoding outcomes; the remaining loss is bounded
by the mass of the non-encoding outcomes.

## References

* `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1463-1492`.
* `docs/paper-gaps/qpbt_decoding-identity.tex` records the necessary restriction
  on the decoder identity.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum DistanceCalculus

noncomputable section

namespace ProjectiveSetting

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {epsilon : ℝ}

/-- Placing a tensor with an identity on Alice's last register recovers `AA'`. -/
theorem placeSide_alice_tensor_one (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon)
    (B : _root_.LIDT.MIPStarRE.Quantum.Op (S.ExpandedLocalSpace .alice)) :
    S.placeSide .alice (_root_.MIPStarRE.QPBT.heteroKron B (1 : _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.PauliRegister P))) = S.place .AA' B := by
  ext row col
  simp [_root_.MIPStarRE.QPBT.ProjectiveSetting.placeSide, _root_.MIPStarRE.QPBT.sixRegExtractionEquiv, _root_.MIPStarRE.QPBT.reindexOp, _root_.MIPStarRE.QPBT.heteroKron, Matrix.kronecker,
    _root_.MIPStarRE.QPBT.ProjectiveSetting.place, Matrix.one_apply, Prod.ext_iff, ite_and, mul_ite]
  split_ifs <;> rfl





end ProjectiveSetting









end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Extraction/PauliTransport.lean. -/
/-!
# Total Pauli measurements under the extraction swaps

The evaluated overlap on the swapped state is the original evaluated-Pauli
consistency overlap. Both player orientations retain their six-register
placements. These identities instantiate the ideal-state Pauli comparison.

## References

Blueprint `lem:qld-unitary`; paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1785-1858`,
especially `eq:qld-unitary-6` and `eq:qld-unitary-9`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder Classical

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.Quantum DistanceCalculus
open LIDT.MIPStarRE.LDT hiding Measurement

noncomputable section



namespace ProjectiveSetting

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {epsilon deltaG : ℝ}
    (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon)



/-- Coarse-graining commutes with extending and conjugating the Pauli POVM. -/
theorem swappedPauliMeas_eval_effect (w : _root_.MIPStarRE.QPBT.GlobalPairWitness S deltaG)
    (side : _root_.MIPStarRE.QPBT.PlayerSide) (W : _root_.MIPStarRE.QPBT.PauliKind) (u : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)
    (a : _root_.MIPStarRE.QPBT.PauliScalar P) :
    ((S.swappedPauliMeas w side W).postprocess
      (fun h => _root_.MIPStarRE.QPBT.evalPoly (_root_.MIPStarRE.QPBT.encodingPoly h) u)).effect a =
      _root_.MIPStarRE.QPBT.conjBy (_root_.MIPStarRE.QPBT.swapUnitary w side) (S.onPlayer side ((S.pauliEvalMeas side W u).effect a)) := by
  simp only [_root_.MIPStarRE.QPBT.ProjectiveSetting.swappedPauliMeas, _root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect, _root_.LIDT.MIPStarRE.Quantum.Measurement.ofSumEqOne,
    _root_.MIPStarRE.QPBT.ProjectiveSetting.pauliEvalMeas, _root_.MIPStarRE.QPBT.conjBy, _root_.MIPStarRE.QPBT.ProjectiveSetting.onPlayer, ← Finset.sum_mul, ← Matrix.mul_sum,
    ← _root_.MIPStarRE.QPBT.DistanceCalculus.heteroKron_finset_sum_left]
  rfl

/-- Original-player placement agrees with extension to the whole local block. -/
theorem placeSide_onPlayer (side : _root_.MIPStarRE.QPBT.PlayerSide) (A : _root_.LIDT.MIPStarRE.Quantum.Op (S.LocalSpace side)) :
    S.placeSide side (S.onPlayer side A) = S.placePlayer side A := by
  cases side
  · exact S.placeSide_alice_tensor_one _
  · exact S.placeSide_bob_tensor_one _







/-- The evaluated canonical block measurement is the swap-conjugated
pulled-apart measurement, by `eq:qld-unitary-6`. -/
theorem canonical_eval_eq_conj_tildeM (w : _root_.MIPStarRE.QPBT.GlobalPairWitness S deltaG)
    (side : _root_.MIPStarRE.QPBT.PlayerSide) (W : _root_.MIPStarRE.QPBT.PauliKind) (u : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)
    (a : _root_.MIPStarRE.QPBT.PauliScalar P) :
    ((_root_.MIPStarRE.QPBT.DistanceCalculus.rightPlacedMeasurement (ιA := S.ExpandedLocalSpace side)
      (_root_.MIPStarRE.QPBT.pauliRegisterMeas (params := P) W)).postprocess
      (fun h => _root_.MIPStarRE.QPBT.evalPoly (_root_.MIPStarRE.QPBT.encodingPoly h) u)).effect a =
      _root_.MIPStarRE.QPBT.conjBy (_root_.MIPStarRE.QPBT.swapUnitary w side) (_root_.MIPStarRE.QPBT.tildeM w side W (_root_.MIPStarRE.QPBT.indicatorVec u) a) := by
  rw [_root_.MIPStarRE.QPBT.swapUnitary_conj_tildeM]
  simp only [_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect, _root_.MIPStarRE.QPBT.DistanceCalculus.rightPlacedMeasurement,
    _root_.LIDT.MIPStarRE.Quantum.Measurement.ofSumEqOne, _root_.MIPStarRE.QPBT.pauliRegisterMeas, _root_.MIPStarRE.QPBT.bracketOp, ← _root_.MIPStarRE.QPBT.DistanceCalculus.heteroKron_finset_sum_right]
  rfl









end ProjectiveSetting

end

end MIPStarRE.QPBT

/-!
# Total Pauli measurements under the extraction swaps

The evaluated overlap on the swapped state is the original evaluated-Pauli
consistency overlap. Both player orientations retain their six-register
placements. These identities instantiate the ideal-state Pauli comparison.

## References

Blueprint `lem:qld-unitary`; paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1785-1858`,
especially `eq:qld-unitary-6` and `eq:qld-unitary-9`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder Classical

open MIPStarRE.QPBT

open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus
open LIDT.MIPStarRE.LDT hiding Measurement





open MIPStarRE.QPBT.ProjectiveSetting

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {epsilon deltaG : ℝ}
    (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon)

set_option maxHeartbeats 800000 in

theorem solution (w : _root_.MIPStarRE.QPBT.GlobalPairWitness S deltaG) (W : _root_.MIPStarRE.QPBT.PauliKind) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)) (fun u =>
      ∑ a : _root_.MIPStarRE.QPBT.PauliScalar P, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm
        (_root_.MIPStarRE.QPBT.reindexState (_root_.MIPStarRE.QPBT.sixRegExtractionEquiv P S.toStrategy.ιA S.toStrategy.ιB)
          (S.applyBoth (_root_.MIPStarRE.QPBT.swapUnitary w .alice) (_root_.MIPStarRE.QPBT.swapUnitary w .bob) S.psiHat))
        (_root_.MIPStarRE.QPBT.heteroKron (((_root_.MIPStarRE.QPBT.DistanceCalculus.rightPlacedMeasurement (ιA := S.ExpandedLocalSpace .alice)
            (_root_.MIPStarRE.QPBT.pauliRegisterMeas (params := P) W)).postprocess
            (fun h => _root_.MIPStarRE.QPBT.evalPoly (_root_.MIPStarRE.QPBT.encodingPoly h) u)).effect a)
          (((S.swappedPauliMeas w .bob W).postprocess
            (fun h => _root_.MIPStarRE.QPBT.evalPoly (_root_.MIPStarRE.QPBT.encodingPoly h) u)).effect a))) =
      1 - _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P))
        (fun u a => S.placeSide .alice (_root_.MIPStarRE.QPBT.tildeM w .alice W (_root_.MIPStarRE.QPBT.indicatorVec u) a))
        (fun u a => S.placePlayer .bob ((S.pauliEvalMeas .bob W u).effect a)) S.psiHat := by
  simp only [S.swappedPauliMeas_eval_effect]
  simp_rw [S.canonical_eval_eq_conj_tildeM w .alice]
  have h := S.swapped_block_overlap_eq w _ (_root_.LIDT.MIPStarRE.LDT.uniformDistribution_isProbability _)
    (fun u => _root_.LIDT.MIPStarRE.Quantum.Measurement.ofSumEqOne (_root_.MIPStarRE.QPBT.tildeM w .alice W (_root_.MIPStarRE.QPBT.indicatorVec u))
      (fun a => (_root_.MIPStarRE.QPBT.tildeM_isProj w .alice W (_root_.MIPStarRE.QPBT.indicatorVec u) a).nonneg)
      (_root_.MIPStarRE.QPBT.sum_tildeM_eq_one w .alice W (_root_.MIPStarRE.QPBT.indicatorVec u)))
    (fun u => _root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement (_root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement (S.pauliEvalMeas .bob W u)))
  have hplace (u : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) (a : _root_.MIPStarRE.QPBT.PauliScalar P) :=
    S.placeSide_onPlayer .bob ((S.pauliEvalMeas .bob W u).effect a)
  convert
    (h.trans (congrArg (fun f => 1 - _root_.MIPStarRE.QPBT.consistencyDefect _ _ f S.psiHat)
      (funext fun u => funext fun a => hplace u a))) using 1 <;> rfl
