-- Prove2me | solution 1 for MIPStarRE.QPBT.evaluated_pauli_tilde_consistency_of_global_pair_witness_explicit
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T03:09:24.876987+00:00
-- url     : https://prove2.me/submissions/2de183a8-934b-4c15-8b6a-1e0309222778

-- Generated proof for MIPStarRE.QPBT.evaluated_pauli_tilde_consistency_of_global_pair_witness_explicit.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Families
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Interpolation
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_AvgCongr
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCode
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Combining_Points_PlacementSupport
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
import Definitions.Def_QPBT_QPBT_Extraction_BlockMeasurement
import Definitions.Def_QPBT_QPBT_Extraction_Defs
import Definitions.Def_QPBT_QPBT_Extraction_Observables
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_TensorSupport
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_Setup
import Definitions.Def_QPBT_QPBT_State
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_ProjectiveSetting_consistencyDefect_placePlayers
import Theorems.Thm_MIPStarRE_QPBT_WinImplications_win_pauli_basis_cons_explicit
import Theorems.Thm_MIPStarRE_QPBT_WinImplications_win_pauli_basis_cons_interchanged_explicit
import Theorems.Thm_MIPStarRE_QPBT_consistencyDefect_measurement_symm
import Theorems.Thm_MIPStarRE_QPBT_consistencyDefect_trans_le
import Theorems.Thm_MIPStarRE_QPBT_point_self_consistency_le
import Theorems.Thm_MIPStarRE_QPBT_sum_tildeM_eq_one
import Theorems.Thm_MIPStarRE_QPBT_tildeM_isProj
import Theorems.Thm_MIPStarRE_QPBT_tilde_m_consistent_point_meas_of_global_pair_witness_explicit
import Theorems.Thm_MIPStarRE_QPBT_tilde_m_consistent_point_meas_prime_of_global_pair_witness_explicit

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

/- Source helpers from QPBT/Observables/ExpandedPlacement.lean. -/
/-!
# Placing operators on the expanded state

The four register placements of `def:symmetric-equivalents` put an operator of
one player's expanded local space on one of the register pairs `AA'`, `BA''`,
`BB'` and `AB''` of the expanded state `psiHat`.  This module records how such
a placement acts on `psiHat`: after the shuffle of `eq:def-psihat` the placed
operator is a threefold tensor product, so a factorized operator whose Pauli
factor is an isometry has the same state-dependent norm as its strategy factor
placed on the original state.  No symmetry between the two players is used;
each of the four placements is treated explicitly.

## References

The declarations support `def:symmetric-equivalents` and `lem:qld-comm-cons`
in `blueprint/src/chapter/ch14_qpbt_observables.tex:1002-1031` and
`blueprint/src/chapter/ch14_qpbt_observables.tex:1139-1178`.  Their paper source
is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:420-505`.
-/

@[expose] public section

-- The unshuffled six-register index type of `eq:def-psihat` is a fourfold
-- iterated product; instance search for its `Fintype` and `DecidableEq`
-- structure needs a larger budget than the default.
set_option synthInstance.maxSize 400

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

/-! ## Coordinate tensors -/











namespace ProjectiveSetting





variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}

/-! ## The strategy factor of a placement -/





/-! ## The action of a placement on the expanded state -/

/-- The expanded state is the shuffle of the coordinate tensor of the strategy
state with the two EPR ancillas. This is `eq:def-psihat`, paper
`14_analysis_of_the_pauli_basis_test.tex:367-372`, blueprint
`ch14_qpbt_observables.tex:895-918`. -/
theorem psiHat_eq_reindexState (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) :
    S.psiHat = _root_.MIPStarRE.QPBT.reindexState (_root_.MIPStarRE.QPBT.sixRegShuffle P S.toStrategy.ιA S.toStrategy.ιB)
      (_root_.MIPStarRE.QPBT.vecTensor (_root_.MIPStarRE.QPBT.vecTensor S.toStrategy.ψ (_root_.MIPStarRE.QPBT.eprState (_root_.MIPStarRE.QPBT.PauliRegister P)))
        (_root_.MIPStarRE.QPBT.eprState (_root_.MIPStarRE.QPBT.PauliRegister P))) := rfl

/-- The expanded strategy state is normalized. -/
theorem psiHat_norm (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) : ‖S.psiHat‖ = 1 := by
  rw [_root_.MIPStarRE.QPBT.ProjectiveSetting.psiHat_eq_reindexState, _root_.MIPStarRE.QPBT.reindexState_norm_eq, _root_.MIPStarRE.QPBT.vecTensor_norm_eq,
    _root_.MIPStarRE.QPBT.vecTensor_norm_eq, S.toStrategy.ψ_norm, _root_.MIPStarRE.QPBT.eprState_norm]
  norm_num

/-! ## Opposite-placement bipartitions -/













/-! ## The four placements -/



























end ProjectiveSetting

end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Test/PauliBasisTest.lean. -/
/-!
# The Pauli basis test

This file supplies the finite question and answer alphabets, the typed
conditionally-linear question sampler, and the Boolean win predicate for the
Pauli basis test.  The quantitative soundness theorem is isolated in
`Soundness.lean`.

## References

The source-facing nodes are blueprint `def:admissible`,
`def:pauli-question-distribution`, and `def:pauli-win-predicate`; their paper origin is
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:908-1225`.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT

noncomputable section



















/- The nested sum is the fixed register order
`V_X ⊕ V_Z ⊕ V_I ⊕ V_V ⊕ V_{R_X} ⊕ V_{R_Z}` from the blueprint. -/


















































set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
-- Deciding the cardinality unfolds the nested finite sum and product alphabets.
/-- The ordered carrier of the Pauli question graph has `86` edges: its
`26` loops occur once, while its `30` non-loop undirected edges occur in both
orientations. This finite computation supports the explicit quantitative
baseline for `thm:pauli`; the graph itself is unchanged. -/
theorem pauli_edge_card : Fintype.card _root_.MIPStarRE.QPBT.PauliEdge = 86 := by
  decide





































end

end MIPStarRE.QPBT

/-!
# Evaluated total-Pauli consistency before extraction

The supplied-witness point estimates combine with point self-consistency and
the two orientations of the game's Pauli-basis check. All estimates act on the
original six-register state, before conjugation by the swaps.

## References

Blueprint `lem:qld-unitary`; paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1785-1810`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder Classical

open MIPStarRE.QPBT

open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus
open LIDT.MIPStarRE.LDT hiding Measurement

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
-- Both pulled-measurement comparisons expand nested finite averages and matrix products.

theorem solution :
    ∀ (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (epsilon deltaG : ℝ),
      0 ≤ epsilon → epsilon ≤ 1 → 0 ≤ deltaG →
      ∀ (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon) (w : _root_.MIPStarRE.QPBT.GlobalPairWitness S deltaG) (W : _root_.MIPStarRE.QPBT.PauliKind),
      _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P))
          (fun u a => S.placePlayer .alice ((S.pauliEvalMeas .alice W u).effect a))
          (fun u a => S.placeSide .bob (_root_.MIPStarRE.QPBT.tildeM w .bob W (_root_.MIPStarRE.QPBT.indicatorVec u) a)) S.psiHat ≤
        _root_.MIPStarRE.QPBT.deltaConstructPaulis (2 + 4 * Real.sqrt 172)
          epsilon deltaG P.m P.d P.q ∧
      _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P))
          (fun u a => S.placeSide .alice (_root_.MIPStarRE.QPBT.tildeM w .alice W (_root_.MIPStarRE.QPBT.indicatorVec u) a))
          (fun u a => S.placePlayer .bob ((S.pauliEvalMeas .bob W u).effect a)) S.psiHat ≤
        _root_.MIPStarRE.QPBT.deltaConstructPaulis (2 + 4 * Real.sqrt 172)
          epsilon deltaG P.m P.d P.q := by
  intro P epsilon deltaG he he1 hd S w W
  let mu := _root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)
  let PA := fun u => S.placedMeasurement .AA' (_root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement (S.pointMeas .alice W u))
  let PB := fun u => S.placedMeasurement .BB' (_root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement (S.pointMeas .bob W u))
  let QA := fun u => S.placedMeasurement .AA'
    (_root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement (S.pauliEvalMeas .alice W u))
  let QB := fun u => S.placedMeasurement .BB'
    (_root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement (S.pauliEvalMeas .bob W u))
  let T := fun (side : _root_.MIPStarRE.QPBT.PlayerSide) (u : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) =>
    S.blockMeasurement side (_root_.LIDT.MIPStarRE.Quantum.Measurement.ofSumEqOne
      (_root_.MIPStarRE.QPBT.tildeM w side W (_root_.MIPStarRE.QPBT.indicatorVec u))
      (fun a => (_root_.MIPStarRE.QPBT.tildeM_isProj w side W (_root_.MIPStarRE.QPBT.indicatorVec u) a).nonneg)
      (_root_.MIPStarRE.QPBT.sum_tildeM_eq_one w side W (_root_.MIPStarRE.QPBT.indicatorVec u)))
  have hpointsCard : _root_.MIPStarRE.QPBT.consistencyDefect mu (fun u a => (PA u).effect a)
      (fun u a => (PB u).effect a) S.psiHat ≤
        (Fintype.card _root_.MIPStarRE.QPBT.PauliEdge : ℝ) * epsilon := by
    change _root_.MIPStarRE.QPBT.consistencyDefect mu (fun u a => S.placePlayer .alice _)
      (fun u a => S.placePlayer .bob _) S.psiHat ≤ _
    rw [S.consistencyDefect_placePlayers]
    exact _root_.MIPStarRE.QPBT.point_self_consistency_le S W
  have hpoints : _root_.MIPStarRE.QPBT.consistencyDefect mu (fun u a => (PA u).effect a)
      (fun u a => (PB u).effect a) S.psiHat ≤ 86 * epsilon := by
    simpa only [_root_.MIPStarRE.QPBT.pauli_edge_card, Nat.cast_ofNat] using hpointsCard
  have hforward : _root_.MIPStarRE.QPBT.consistencyDefect mu (fun u a => (PA u).effect a)
      (fun u a => (QB u).effect a) S.psiHat ≤ 86 * epsilon := by
    change _root_.MIPStarRE.QPBT.consistencyDefect mu (fun u a => S.placePlayer .alice _)
      (fun u a => S.placePlayer .bob _) S.psiHat ≤ _
    rw [S.consistencyDefect_placePlayers]
    exact _root_.MIPStarRE.QPBT.WinImplications.win_pauli_basis_cons_explicit P epsilon S he W
  have hreverse : _root_.MIPStarRE.QPBT.consistencyDefect mu (fun u a => (QA u).effect a)
      (fun u a => (PB u).effect a) S.psiHat ≤ 86 * epsilon := by
    change _root_.MIPStarRE.QPBT.consistencyDefect mu (fun u a => S.placePlayer .alice _)
      (fun u a => S.placePlayer .bob _) S.psiHat ≤ _
    rw [S.consistencyDefect_placePlayers]
    exact _root_.MIPStarRE.QPBT.WinImplications.win_pauli_basis_cons_interchanged_explicit P epsilon S he W
  have hleft : _root_.MIPStarRE.QPBT.consistencyDefect mu (fun u a => (T .alice u).effect a)
      (fun u a => (PB u).effect a) S.psiHat ≤
        _root_.MIPStarRE.QPBT.deltaConstructPaulis (2 + 2 * Real.sqrt 172)
          epsilon deltaG P.m P.d P.q := by
    change _root_.MIPStarRE.QPBT.consistencyDefect mu
      (fun u a => S.placeSide .alice (_root_.MIPStarRE.QPBT.tildeM w .alice W (_root_.MIPStarRE.QPBT.indicatorVec u) a))
      (fun u a => S.placePlayer .bob ((S.pointMeas .bob W u).effect a)) S.psiHat ≤ _
    exact _root_.MIPStarRE.QPBT.tilde_m_consistent_point_meas_prime_of_global_pair_witness_explicit
      P epsilon deltaG he he1 hd S w W
  have hright : _root_.MIPStarRE.QPBT.consistencyDefect mu (fun u a => (PA u).effect a)
      (fun u a => (T .bob u).effect a) S.psiHat ≤
        _root_.MIPStarRE.QPBT.deltaConstructPaulis (2 + 2 * Real.sqrt 172)
          epsilon deltaG P.m P.d P.q := by
    change _root_.MIPStarRE.QPBT.consistencyDefect mu
      (fun u a => S.placePlayer .alice ((S.pointMeas .alice W u).effect a))
      (fun u a => S.placeSide .bob (_root_.MIPStarRE.QPBT.tildeM w .bob W (_root_.MIPStarRE.QPBT.indicatorVec u) a)) S.psiHat ≤ _
    exact _root_.MIPStarRE.QPBT.tilde_m_consistent_point_meas_of_global_pair_witness_explicit
      P epsilon deltaG he he1 hd S w W
  have hscalar :
      _root_.MIPStarRE.QPBT.deltaConstructPaulis (2 + 2 * Real.sqrt 172)
          epsilon deltaG P.m P.d P.q +
        2 * Real.sqrt (86 * epsilon + 86 * epsilon) ≤
      _root_.MIPStarRE.QPBT.deltaConstructPaulis (2 + 4 * Real.sqrt 172)
        epsilon deltaG P.m P.d P.q := by
    rw [← add_mul, show (86 : ℝ) + 86 = 172 by norm_num,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 172)]
    unfold _root_.MIPStarRE.QPBT.deltaConstructPaulis
    have hr : 0 ≤ ((P.m * P.d : ℕ) : ℝ) / P.q := by positivity
    nlinarith [Real.sqrt_nonneg (172 : ℝ), Real.sqrt_nonneg epsilon]
  constructor
  · change _root_.MIPStarRE.QPBT.consistencyDefect mu (fun u a => (QA u).effect a)
      (fun u a => (T .bob u).effect a) S.psiHat ≤ _
    rw [_root_.MIPStarRE.QPBT.consistencyDefect_measurement_symm]
    apply (_root_.MIPStarRE.QPBT.consistencyDefect_trans_le mu (T .bob) PA PB QA S.psiHat _ _ _
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution_isProbability _) S.psiHat_norm ?_ ?_ ?_).trans hscalar
    · rw [_root_.MIPStarRE.QPBT.consistencyDefect_measurement_symm]; exact hright
    · rw [_root_.MIPStarRE.QPBT.consistencyDefect_measurement_symm]; exact hpoints
    · rw [_root_.MIPStarRE.QPBT.consistencyDefect_measurement_symm]; exact hreverse
  · exact (_root_.MIPStarRE.QPBT.consistencyDefect_trans_le mu (T .alice) PB PA QB S.psiHat _ _ _
      (_root_.LIDT.MIPStarRE.LDT.uniformDistribution_isProbability _) S.psiHat_norm hleft hpoints hforward).trans hscalar
