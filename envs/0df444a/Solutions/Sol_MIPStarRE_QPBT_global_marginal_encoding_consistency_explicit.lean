-- Prove2me | solution 1 for MIPStarRE.QPBT.global_marginal_encoding_consistency_explicit
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T02:57:54.433043+00:00
-- url     : https://prove2.me/submissions/6dee310f-7c60-4322-88e7-facd85c20c8c

-- Generated proof for MIPStarRE.QPBT.global_marginal_encoding_consistency_explicit.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Polynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_AvgCongr
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Algebra_Decoding
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCode
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Combining_Defs
import Definitions.Def_QPBT_QPBT_Combining_ExtendedLineGame
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
import Definitions.Def_QPBT_QPBT_Extraction_EncodingSupport
import Definitions.Def_QPBT_QPBT_Extraction_Observables
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_TensorSupport
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_Setup
import Definitions.Def_QPBT_QPBT_State
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGameMeasurements
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_LIDT_MIPStarRE_Quantum_Measurement_postprocess_comp
import Theorems.Thm_MIPStarRE_QPBT_ProjectiveSetting_consistencyDefect_pairState_eq_AA_prime_BA_prime_prime
import Theorems.Thm_MIPStarRE_QPBT_ProjectiveSetting_consistencyDefect_pairState_eq_AB_prime_prime_BB_prime
import Theorems.Thm_MIPStarRE_QPBT_ProjectiveSetting_place_comm
import Theorems.Thm_MIPStarRE_QPBT_ProjectiveSetting_tauPointProj_mul_tauPointProj
import Theorems.Thm_MIPStarRE_QPBT_WinImplications_win_pauli_basis_cons_explicit
import Theorems.Thm_MIPStarRE_QPBT_WinImplications_win_pauli_basis_cons_interchanged_explicit
import Theorems.Thm_MIPStarRE_QPBT_consistencyDefect_convolution_eq_of_perfect
import Theorems.Thm_MIPStarRE_QPBT_consistencyDefect_trans_le
import Theorems.Thm_MIPStarRE_QPBT_point_self_consistency_le
import Theorems.Thm_MIPStarRE_QPBT_tensorMeasurement_postprocess

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus
namespace MIPStarRE.QPBT.ProjectiveSetting
end MIPStarRE.QPBT.ProjectiveSetting
namespace MIPStarRE.QPBT.WinImplications
end MIPStarRE.QPBT.WinImplications

/- Source helpers from QPBT/Extraction/EncodingSupport.lean. -/
/-! # Encoding-supported Pauli reference measurements

The reference measurement measures the strategy's Pauli answer and an independent
ideal Pauli answer, then returns the bounded encoding of their sum. Its effects
vanish outside the encoding image. Evaluation of its polynomial outcome is the
convolution of the evaluated strategy measurement and the ideal point projectors.

These are internal auxiliary constructions for blueprint `eq:qld-nonencoding-mass`
and `lem:qld-nonencoding-mass-bound`, not the quantitative support estimate. No
winning premise or global polynomial-pair witness is used or constructed here.

## References

The encoding is paper `eq:low-degree-encoding-definition` in
`references/qpbt-paper/04_preliminaries.tex:882-897`. The convolution is the Pauli
answer replacement of the expanded point measurement at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:383-418`.
The corrected use in `lem:qld-construct-the-paulis` is recorded in blueprint
`eq:qld-nonencoding-mass` and `docs/paper-gaps/qpbt_decoding-identity.tex`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.Quantum

variable {params : _root_.MIPStarRE.QPBT.AdmissibleParams} {error : ℝ}





namespace ProjectiveSetting











/-- Evaluating the reference polynomial is equivalent to evaluating the two Pauli
answers separately and adding their values. This uses linearity of the encoding,
not the decoder/evaluation identity for arbitrary polynomial representatives. -/
theorem encodingPauliMeas_postprocess_eval (setting : _root_.MIPStarRE.QPBT.ProjectiveSetting params error)
    (side : _root_.MIPStarRE.QPBT.PlayerSide) (basis : _root_.MIPStarRE.QPBT.PauliKind) (point : Fin params.m → _root_.MIPStarRE.QPBT.PauliScalar params) :
    (setting.encodingPauliMeas side basis).postprocess (fun poly => _root_.MIPStarRE.QPBT.evalPoly poly point) =
      (_root_.MIPStarRE.QPBT.tensorMeasurement (setting.pauliEvalMeas side basis point)
        ((_root_.MIPStarRE.QPBT.pauliRegisterMeas basis).postprocess
          (fun answer => _root_.MIPStarRE.QPBT.lowDegreeEnc answer point))).postprocess
        (fun values => values.1 + values.2) := by
  unfold _root_.MIPStarRE.QPBT.ProjectiveSetting.encodingPauliMeas _root_.MIPStarRE.QPBT.ProjectiveSetting.pauliEvalMeas
  rw [_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_comp, _root_.MIPStarRE.QPBT.tensorMeasurement_postprocess,
    _root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_comp]
  apply congrArg ((_root_.MIPStarRE.QPBT.tensorMeasurement (setting.pauliMeas side basis)
    (_root_.MIPStarRE.QPBT.pauliRegisterMeas basis)).postprocess)
  funext answers
  change _root_.MIPStarRE.QPBT.lowDegreeEnc (answers.1 + answers.2) point =
    _root_.MIPStarRE.QPBT.lowDegreeEnc answers.1 point + _root_.MIPStarRE.QPBT.lowDegreeEnc answers.2 point
  simp only [_root_.MIPStarRE.QPBT.lowDegreeEnc_eq_dotProduct, add_dotProduct]

/-- The evaluated reference effects are exactly the Pauli-answer convolution
`K^u_a` in the proof of blueprint `eq:qld-nonencoding-mass`. This identity makes no
approximation or assertion of consistency with the strategy's point measurement. -/
theorem encodingPauliMeas_eval_effect_eq_convolution
    (setting : _root_.MIPStarRE.QPBT.ProjectiveSetting params error) (side : _root_.MIPStarRE.QPBT.PlayerSide) (basis : _root_.MIPStarRE.QPBT.PauliKind)
    (point : Fin params.m → _root_.MIPStarRE.QPBT.PauliScalar params) (value : _root_.MIPStarRE.QPBT.PauliScalar params) :
    ((setting.encodingPauliMeas side basis).postprocess
      (fun poly => _root_.MIPStarRE.QPBT.evalPoly poly point)).effect value =
      ∑ values ∈ Finset.univ.filter
          (fun values : _root_.MIPStarRE.QPBT.PauliScalar params × _root_.MIPStarRE.QPBT.PauliScalar params => values.1 + values.2 = value),
        _root_.MIPStarRE.QPBT.heteroKron ((setting.pauliEvalMeas side basis point).effect values.1)
          (_root_.MIPStarRE.QPBT.ProjectiveSetting.tauPointProj basis point values.2) := by
  rw [_root_.MIPStarRE.QPBT.ProjectiveSetting.encodingPauliMeas_postprocess_eval, _root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect]
  apply Finset.sum_congr rfl
  intro values _
  change _root_.MIPStarRE.QPBT.heteroKron ((setting.pauliEvalMeas side basis point).effect values.1)
    (((_root_.MIPStarRE.QPBT.pauliRegisterMeas basis).postprocess
      (fun answer => _root_.MIPStarRE.QPBT.lowDegreeEnc answer point)).effect values.2) = _
  simp only [_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect, _root_.MIPStarRE.QPBT.lowDegreeEnc_eq_dotProduct]
  rfl

end ProjectiveSetting

end MIPStarRE.QPBT

/- Source helpers from QPBT/Observables/ExpandedDefs.lean. -/
/-!
# Expanded registers and point measurements

This module adjoins two EPR pairs to a heterogeneous Pauli-basis-test strategy,
records the four register placements used in the analysis, and defines the
expanded point observables and measurements. Fourier inversion identifies their
effects with a convolution of projectors and proves completeness and projectivity.

## References

The constructions formalize blueprint `def:expanded-state`,
`def:expanded-observables`, `def:expanded-point-measurement`, and
`def:expanded-point-trace-projection`. Their paper source is
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:367-418`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum
open LIDT.MIPStarRE.LDT.Preliminaries

noncomputable section













namespace ProjectiveSetting

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}













/-- The point coarse-graining of the generalized Pauli projectors is symmetric.
This is the EPR-transport identity used for the perfect ancilla consistency in
item 1 of `lem:qld-comm-cons`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:455-465`. -/
theorem tauPointProj_transpose (W : _root_.MIPStarRE.QPBT.PauliKind)
    (u : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) (a : _root_.MIPStarRE.QPBT.PauliScalar P) :
    (_root_.MIPStarRE.QPBT.ProjectiveSetting.tauPointProj W u a)ᵀ = _root_.MIPStarRE.QPBT.ProjectiveSetting.tauPointProj W u a := by
  classical
  simp only [_root_.MIPStarRE.QPBT.ProjectiveSetting.tauPointProj, Matrix.transpose_sum, _root_.MIPStarRE.QPBT.pauliProj_transpose]



























































end ProjectiveSetting

end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Observables/WinImplications/FactorTransport.lean. -/
/-!
# Transport of the winning implications to the interchanged tensor factor

This module carries the state-dependent functionals of the winning
implications across the interchange of the two tensor factors.  The
factor-interchanged conclusions of `lem:qld-win-implications` are stated with
the second player on the left factor and the reindexed state
`ProjectiveSetting.swappedState`; the lemmas here identify those quantities
with the ones proved on `S.toStrategy.psi`, so that the second pass of
`lem:qld-win-implications-obs` can reuse the first pass verbatim on the
interchanged side.

## References

The declarations support the trailing clause of `lem:qld-win-implications` and
the second assertion of `lem:qld-win-implications-obs` in
`blueprint/src/chapter/ch14_qpbt_observables.tex:761-794` and
`blueprint/src/chapter/ch14_qpbt_observables.tex:701-703`.  Their paper source
is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:227,309-362`.
-/

@[expose] public section

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

namespace WinImplications

/-! ## Reindexing the identity and the strategy state -/





/-! ## Transport of the consistency defect -/

/-- Left and right placements of local operators commute.  Formalization-only
support for `def:consistency`, blueprint `ch12_qpbt_games.tex:210-223`. -/
theorem heteroKron_left_right_comm {ιA ιB : Type*} [Fintype ιA]
    [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB] (A : _root_.LIDT.MIPStarRE.Quantum.Op ιA) (B : _root_.LIDT.MIPStarRE.Quantum.Op ιB) :
    _root_.MIPStarRE.QPBT.heteroKron A (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιB) * _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιA) B =
      _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op ιA) B * _root_.MIPStarRE.QPBT.heteroKron A 1 := by
  rw [_root_.MIPStarRE.QPBT.heteroKron_mul, _root_.MIPStarRE.QPBT.heteroKron_mul, mul_one, one_mul, one_mul, mul_one]







/-! ## Transport of the phase-signed operator distance -/





end WinImplications

end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Test/MagicSquareTheorems/PerfectStrategy/Observables.lean. -/
/-!
# Observables of the perfect Magic Square strategy

This module builds the operator table of `thm:ms-from-ac`.  It records the EPR
state carried by the perfect strategy, the binary reflection effects attached
to a Hermitian involution, the real Pauli matrices on the auxiliary qubit, and
the nine cell observables together with their Hermiticity, involutivity,
commutation, and constraint-product identities.

## References

The source statement is blueprint
`thm:ms-from-ac`, from
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:654-722`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section







/-- Formalization-only auxiliary lemma for
`exists_ms_perfect_strategy_of_anticommuting` (blueprint
`thm:ms-from-ac`): a symmetric operator acting on the first factor
of the EPR state acts on it exactly as it does on the second factor. -/
theorem epr_action_eq_of_transpose
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (E : _root_.LIDT.MIPStarRE.Quantum.Op V) (hE : Eᵀ = E) :
    (_root_.MIPStarRE.QPBT.heteroKron E 1).mulVec (_root_.MIPStarRE.QPBT.eprState V) =
      (_root_.MIPStarRE.QPBT.heteroKron 1 E).mulVec (_root_.MIPStarRE.QPBT.eprState V) := by
  ext p
  rcases p with ⟨i, j⟩
  simpa [_root_.MIPStarRE.QPBT.heteroKron, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    _root_.MIPStarRE.QPBT.eprState, Matrix.one_apply] using congrFun (congrFun hE j) i























local notation "qubitX" => (_root_.MIPStarRE.QPBT.tauShift (K := ZMod 2) 1)
local notation "qubitZ" => (_root_.MIPStarRE.QPBT.tauPhase (K := ZMod 2) 1)











































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

/- Source helpers from QPBT/Observables/IdealPointConsistency.lean. -/
/-!
# Perfect consistency of ideal point measurements

The ideal point projectors on the two halves of one EPR state have zero joint
weight for distinct outcomes. This follows from the reality and orthogonality
of the characteristic-two Pauli basis projectors, with no strategy hypothesis.

The transpose identities are supplied by `pauliProj_transpose` in
`Algebra.Pauli` and `ProjectiveSetting.tauPointProj_transpose` in
`Observables.ExpandedDefs`. Orthogonality of the Pauli eigenspace projectors and
of the point fibers is likewise reused from `pauliProj_mul_pauliProj` and
`ProjectiveSetting.tauPointProj_mul_tauPointProj` in those two modules. The
latter module also supplies the actual measurement
`ProjectiveSetting.tauPointMeas`, whose effects are `tauPointProj`.

## References

- `references/qpbt-paper/04_preliminaries.tex:1101-1161`: Pauli eigenbases.
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex`,
  `eq:def-psihat`, `eq:qld-point-obs-def`, and the proof of `lem:qld-comm-cons`
  at line 489: perfect consistency of the ancillary point projectors.

These are auxiliary identities for the expanded-state construction, not the
approximate consistency theorem for the original strategy.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.Quantum

noncomputable section

namespace ProjectiveSetting

open LIDT.MIPStarRE.LDT hiding Measurement
open DistanceCalculus

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams}

/-- Distinct point fibers annihilate one another. This is the off-diagonal case
of the existing `tauPointProj_mul_tauPointProj` in `Observables.ExpandedDefs`. -/
theorem tauPointProj_mul_eq_zero_of_ne (W : _root_.MIPStarRE.QPBT.PauliKind)
    (u : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) {a b : _root_.MIPStarRE.QPBT.PauliScalar P} (hab : a ≠ b) :
    _root_.MIPStarRE.QPBT.ProjectiveSetting.tauPointProj W u a * _root_.MIPStarRE.QPBT.ProjectiveSetting.tauPointProj W u b = 0 := by
  simp only [_root_.MIPStarRE.QPBT.ProjectiveSetting.tauPointProj_mul_tauPointProj, if_neg hab]

/-- The ideal point projector has the same action on either half of one EPR
pair, as used in the proof of `lem:qld-comm-cons`, paper line 489. -/
theorem tauPointProj_epr_action (W : _root_.MIPStarRE.QPBT.PauliKind)
    (u : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) (a : _root_.MIPStarRE.QPBT.PauliScalar P) :
    (_root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.ProjectiveSetting.tauPointProj W u a) 1).mulVec (_root_.MIPStarRE.QPBT.eprState (_root_.MIPStarRE.QPBT.PauliRegister P)) =
      (_root_.MIPStarRE.QPBT.heteroKron 1 (_root_.MIPStarRE.QPBT.ProjectiveSetting.tauPointProj W u a)).mulVec (_root_.MIPStarRE.QPBT.eprState (_root_.MIPStarRE.QPBT.PauliRegister P)) :=
  _root_.MIPStarRE.QPBT.epr_action_eq_of_transpose _ (_root_.MIPStarRE.QPBT.ProjectiveSetting.tauPointProj_transpose W u a)

/-- Two distinct ideal point outcomes annihilate the actual EPR vector.
Move the second effect to the first half and use orthogonality of point fibers. -/
theorem tauPointProj_epr_mulVec_eq_zero_of_ne (W : _root_.MIPStarRE.QPBT.PauliKind)
    (u : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) {a b : _root_.MIPStarRE.QPBT.PauliScalar P} (hab : a ≠ b) :
    (_root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.ProjectiveSetting.tauPointProj W u a) (_root_.MIPStarRE.QPBT.ProjectiveSetting.tauPointProj W u b)).mulVec
      (_root_.MIPStarRE.QPBT.eprState (_root_.MIPStarRE.QPBT.PauliRegister P)) = 0 := by
  have hprod : _root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.ProjectiveSetting.tauPointProj W u a) (_root_.MIPStarRE.QPBT.ProjectiveSetting.tauPointProj W u b) =
      _root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.ProjectiveSetting.tauPointProj W u a) (1 : _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.PauliRegister P)) *
        _root_.MIPStarRE.QPBT.heteroKron (1 : _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.PauliRegister P)) (_root_.MIPStarRE.QPBT.ProjectiveSetting.tauPointProj W u b) := by
    rw [_root_.MIPStarRE.QPBT.heteroKron_mul, mul_one, one_mul]
  rw [hprod, ← Matrix.mulVec_mulVec, ← _root_.MIPStarRE.QPBT.ProjectiveSetting.tauPointProj_epr_action W u b,
    Matrix.mulVec_mulVec, _root_.MIPStarRE.QPBT.heteroKron_mul, _root_.MIPStarRE.QPBT.ProjectiveSetting.tauPointProj_mul_eq_zero_of_ne W u hab]
  simp [_root_.MIPStarRE.QPBT.heteroKron]

/-- Every off-diagonal joint weight of the ideal point measurement on one EPR
pair is zero. The Pauli basis and the point are arbitrary. -/
theorem tauPointProj_epr_joint_eq_zero_of_ne (W : _root_.MIPStarRE.QPBT.PauliKind)
    (u : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) {a b : _root_.MIPStarRE.QPBT.PauliScalar P} (hab : a ≠ b) :
    _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm (_root_.MIPStarRE.QPBT.eprState (_root_.MIPStarRE.QPBT.PauliRegister P))
      (_root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.ProjectiveSetting.tauPointProj W u a) (_root_.MIPStarRE.QPBT.ProjectiveSetting.tauPointProj W u b)) = 0 := by
  unfold _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm _root_.MIPStarRE.QPBT.applyOperatorToState
  change (inner ℂ (_root_.MIPStarRE.QPBT.eprState (_root_.MIPStarRE.QPBT.PauliRegister P))
    ((EuclideanSpace.equiv _ ℂ).symm
      ((_root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.ProjectiveSetting.tauPointProj W u a) (_root_.MIPStarRE.QPBT.ProjectiveSetting.tauPointProj W u b)).mulVec
        (_root_.MIPStarRE.QPBT.eprState (_root_.MIPStarRE.QPBT.PauliRegister P))))).re = 0
  rw [_root_.MIPStarRE.QPBT.ProjectiveSetting.tauPointProj_epr_mulVec_eq_zero_of_ne W u hab, map_zero, inner_zero_right]
  rfl

/-- Perfect ancillary consistency in the proof of `lem:qld-comm-cons`:
the off-diagonal joint mass is zero on the two halves of the same EPR state.
This auxiliary identity assumes no original strategy or consistency bound. -/
theorem tauPointProj_epr_offDiagonal_eq_zero (W : _root_.MIPStarRE.QPBT.PauliKind)
    (u : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) :
    (∑ a : _root_.MIPStarRE.QPBT.PauliScalar P, ∑ b : _root_.MIPStarRE.QPBT.PauliScalar P, if a = b then 0 else
      _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm (_root_.MIPStarRE.QPBT.eprState (_root_.MIPStarRE.QPBT.PauliRegister P))
        (_root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.ProjectiveSetting.tauPointProj W u a) (_root_.MIPStarRE.QPBT.ProjectiveSetting.tauPointProj W u b))) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro a _
  apply Finset.sum_eq_zero
  intro b _
  split_ifs with hab
  · rfl
  · exact _root_.MIPStarRE.QPBT.ProjectiveSetting.tauPointProj_epr_joint_eq_zero_of_ne W u hab



end ProjectiveSetting

end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Extraction/NonencodingSupport.lean. -/
/-!
# Consistency with encoding-supported reference measurements

The Pauli-basis check remains a consistency estimate after adjoining the
perfectly correlated ideal point measurement. Schwartz-Zippel then controls
mass outside the encoding image by evaluated reference inconsistency.

## References

- Blueprint `eq:qld-nonencoding-mass` and `lem:qld-nonencoding-mass-bound`.
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:197-264,383-418`.
- `docs/paper-gaps/qpbt_decoding-identity.tex`.
- The reference measurements and comparison estimates express the convolution
  with the ideal Pauli point projectors.
- These are auxiliary estimates for a supplied witness, not its construction.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder
open scoped Classical

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum DistanceCalculus ProjectiveSetting

noncomputable section

/-- For commuting families, reversing the order of the measurements preserves
the consistency defect. This is finite-sum algebra for opposite placements. -/
theorem consistencyDefect_comm_of_commute {X A I : Type*}
    [Fintype X] [DecidableEq X] [Fintype A] [DecidableEq A]
    [Fintype I] [DecidableEq I] (mu : _root_.LIDT.MIPStarRE.LDT.Distribution X)
    (first second : X → A → _root_.LIDT.MIPStarRE.Quantum.Op I) (psi : EuclideanSpace ℂ I)
    (hcomm : ∀ x a b, first x a * second x b = second x b * first x a) :
    _root_.MIPStarRE.QPBT.consistencyDefect mu first second psi = _root_.MIPStarRE.QPBT.consistencyDefect mu second first psi := by
  unfold _root_.MIPStarRE.QPBT.consistencyDefect
  apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
  intro x
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  simp only [hcomm x a b, eq_comm]



namespace ProjectiveSetting

/-- Adjoining the ideal point outcomes preserves the Pauli-basis check on the
two-player expanded state, in the point--Pauli orientation. -/
theorem point_encodingPauli_consistency_eq {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {epsilon : ℝ}
    (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon) (W : _root_.MIPStarRE.QPBT.PauliKind) :
    _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P))
        (fun u a => _root_.MIPStarRE.QPBT.heteroKron ((S.pointMeasExp .alice W u).effect a) 1)
        (fun u a => _root_.MIPStarRE.QPBT.heteroKron 1 (((S.encodingPauliMeas .bob W).postprocess
          (fun g => _root_.MIPStarRE.QPBT.evalPoly g u)).effect a)) (_root_.MIPStarRE.QPBT.ExtendedLineGame.pairState S) =
      _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P))
        (fun u a => _root_.MIPStarRE.QPBT.heteroKron ((S.pointMeas .alice W u).effect a) 1)
        (fun u a => _root_.MIPStarRE.QPBT.heteroKron 1 ((S.pauliEvalMeas .bob W u).effect a))
        S.toStrategy.ψ := by
  have h := _root_.MIPStarRE.QPBT.consistencyDefect_convolution_eq_of_perfect
    (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P))
    (S.pointMeas .alice W) (S.pauliEvalMeas .bob W)
    (_root_.MIPStarRE.QPBT.ProjectiveSetting.tauPointMeas W) (_root_.MIPStarRE.QPBT.ProjectiveSetting.tauPointMeas W) S.toStrategy.ψ
    (_root_.MIPStarRE.QPBT.eprState (_root_.MIPStarRE.QPBT.PauliRegister P)) (_root_.MIPStarRE.QPBT.eprState_norm _)
    (_root_.MIPStarRE.QPBT.ProjectiveSetting.tauPointProj_epr_offDiagonal_eq_zero W)
  simp_rw [_root_.MIPStarRE.QPBT.ProjectiveSetting.encodingPauliMeas_eval_effect_eq_convolution S .bob W]
  simpa only [_root_.MIPStarRE.QPBT.ProjectiveSetting.pointMeasExp, _root_.LIDT.MIPStarRE.Quantum.Measurement.ofSumEqOne, _root_.MIPStarRE.QPBT.ProjectiveSetting.expPointOp_eq_convolution,
    _root_.MIPStarRE.QPBT.ProjectiveSetting.tauPointMeas, _root_.MIPStarRE.QPBT.ExtendedLineGame.pairState] using h

/-- The same exact preservation holds in the Pauli--point orientation. -/
theorem encodingPauli_point_consistency_eq {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {epsilon : ℝ}
    (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon) (W : _root_.MIPStarRE.QPBT.PauliKind) :
    _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P))
        (fun u a => _root_.MIPStarRE.QPBT.heteroKron (((S.encodingPauliMeas .alice W).postprocess
          (fun g => _root_.MIPStarRE.QPBT.evalPoly g u)).effect a) 1)
        (fun u a => _root_.MIPStarRE.QPBT.heteroKron 1 ((S.pointMeasExp .bob W u).effect a))
        (_root_.MIPStarRE.QPBT.ExtendedLineGame.pairState S) =
      _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P))
        (fun u a => _root_.MIPStarRE.QPBT.heteroKron ((S.pauliEvalMeas .alice W u).effect a) 1)
        (fun u a => _root_.MIPStarRE.QPBT.heteroKron 1 ((S.pointMeas .bob W u).effect a))
        S.toStrategy.ψ := by
  have h := _root_.MIPStarRE.QPBT.consistencyDefect_convolution_eq_of_perfect
    (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P))
    (S.pauliEvalMeas .alice W) (S.pointMeas .bob W)
    (_root_.MIPStarRE.QPBT.ProjectiveSetting.tauPointMeas W) (_root_.MIPStarRE.QPBT.ProjectiveSetting.tauPointMeas W) S.toStrategy.ψ
    (_root_.MIPStarRE.QPBT.eprState (_root_.MIPStarRE.QPBT.PauliRegister P)) (_root_.MIPStarRE.QPBT.eprState_norm _)
    (_root_.MIPStarRE.QPBT.ProjectiveSetting.tauPointProj_epr_offDiagonal_eq_zero W)
  simp_rw [_root_.MIPStarRE.QPBT.ProjectiveSetting.encodingPauliMeas_eval_effect_eq_convolution S .alice W]
  simpa only [_root_.MIPStarRE.QPBT.ProjectiveSetting.pointMeasExp, _root_.LIDT.MIPStarRE.Quantum.Measurement.ofSumEqOne, _root_.MIPStarRE.QPBT.ProjectiveSetting.expPointOp_eq_convolution,
    _root_.MIPStarRE.QPBT.ProjectiveSetting.tauPointMeas, _root_.MIPStarRE.QPBT.ExtendedLineGame.pairState] using h

/-- Adjoining the same ideal point measurements also preserves point
self-consistency exactly. -/
theorem expanded_point_consistency_eq {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {epsilon : ℝ}
    (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon) (W : _root_.MIPStarRE.QPBT.PauliKind) :
    _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P))
        (fun u a => _root_.MIPStarRE.QPBT.heteroKron ((S.pointMeasExp .alice W u).effect a) 1)
        (fun u a => _root_.MIPStarRE.QPBT.heteroKron 1 ((S.pointMeasExp .bob W u).effect a))
        (_root_.MIPStarRE.QPBT.ExtendedLineGame.pairState S) =
      _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P))
        (fun u a => _root_.MIPStarRE.QPBT.heteroKron ((S.pointMeas .alice W u).effect a) 1)
        (fun u a => _root_.MIPStarRE.QPBT.heteroKron 1 ((S.pointMeas .bob W u).effect a))
        S.toStrategy.ψ := by
  have h := _root_.MIPStarRE.QPBT.consistencyDefect_convolution_eq_of_perfect
    (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P))
    (S.pointMeas .alice W) (S.pointMeas .bob W)
    (_root_.MIPStarRE.QPBT.ProjectiveSetting.tauPointMeas W) (_root_.MIPStarRE.QPBT.ProjectiveSetting.tauPointMeas W) S.toStrategy.ψ
    (_root_.MIPStarRE.QPBT.eprState (_root_.MIPStarRE.QPBT.PauliRegister P)) (_root_.MIPStarRE.QPBT.eprState_norm _)
    (_root_.MIPStarRE.QPBT.ProjectiveSetting.tauPointProj_epr_offDiagonal_eq_zero W)
  simpa only [_root_.MIPStarRE.QPBT.ProjectiveSetting.pointMeasExp, _root_.LIDT.MIPStarRE.Quantum.Measurement.ofSumEqOne, _root_.MIPStarRE.QPBT.ProjectiveSetting.expPointOp_eq_convolution,
    _root_.MIPStarRE.QPBT.ProjectiveSetting.tauPointMeas, _root_.MIPStarRE.QPBT.ExtendedLineGame.pairState] using h

end ProjectiveSetting











end

end MIPStarRE.QPBT

/-!
# Consistency with encoding-supported reference measurements

The Pauli-basis check remains a consistency estimate after adjoining the
perfectly correlated ideal point measurement. Schwartz-Zippel then controls
mass outside the encoding image by evaluated reference inconsistency.

## References

- Blueprint `eq:qld-nonencoding-mass` and `lem:qld-nonencoding-mass-bound`.
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:197-264,383-418`.
- `docs/paper-gaps/qpbt_decoding-identity.tex`.
- The reference measurements and comparison estimates express the convolution
  with the ideal Pauli point projectors.
- These are auxiliary estimates for a supplied witness, not its construction.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder
open scoped Classical

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus MIPStarRE.QPBT.ProjectiveSetting







open MIPStarRE.QPBT.ProjectiveSetting

theorem solution :
    ∀ (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (epsilon deltaG : ℝ),
      0 ≤ epsilon → ∀ (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon)
        (w : _root_.MIPStarRE.QPBT.GlobalPairWitness S deltaG) (W : _root_.MIPStarRE.QPBT.PauliKind),
      _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P))
          (fun u a => _root_.MIPStarRE.QPBT.heteroKron (((w.marginalPoly .alice W).postprocess
            (fun g => _root_.MIPStarRE.QPBT.evalPoly g u)).effect a) 1)
          (fun u a => _root_.MIPStarRE.QPBT.heteroKron 1 (((S.encodingPauliMeas .bob W).postprocess
            (fun g => _root_.MIPStarRE.QPBT.evalPoly g u)).effect a)) (_root_.MIPStarRE.QPBT.ExtendedLineGame.pairState S) ≤
        deltaG + (1 + 2 * Real.sqrt 172) * Real.sqrt epsilon ∧
      _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P))
          (fun u a => _root_.MIPStarRE.QPBT.heteroKron (((S.encodingPauliMeas .alice W).postprocess
            (fun g => _root_.MIPStarRE.QPBT.evalPoly g u)).effect a) 1)
          (fun u a => _root_.MIPStarRE.QPBT.heteroKron 1 (((w.marginalPoly .bob W).postprocess
            (fun g => _root_.MIPStarRE.QPBT.evalPoly g u)).effect a)) (_root_.MIPStarRE.QPBT.ExtendedLineGame.pairState S) ≤
        deltaG + (1 + 2 * Real.sqrt 172) * Real.sqrt epsilon := by
  intro P epsilon deltaG hepsilon S w W
  let mu := _root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P)
  let psi := _root_.MIPStarRE.QPBT.ExtendedLineGame.pairState S
  let pointA := fun u => _root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement (ιB := S.ExpandedLocalSpace .bob)
    (S.pointMeasExp .alice W u)
  let pointB := fun u => _root_.MIPStarRE.QPBT.DistanceCalculus.rightPlacedMeasurement (ιA := S.ExpandedLocalSpace .alice)
    (S.pointMeasExp .bob W u)
  let refA := fun u => _root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement (ιB := S.ExpandedLocalSpace .bob)
    ((S.encodingPauliMeas .alice W).postprocess (fun g => _root_.MIPStarRE.QPBT.evalPoly g u))
  let refB := fun u => _root_.MIPStarRE.QPBT.DistanceCalculus.rightPlacedMeasurement (ιA := S.ExpandedLocalSpace .alice)
    ((S.encodingPauliMeas .bob W).postprocess (fun g => _root_.MIPStarRE.QPBT.evalPoly g u))
  let margA := fun u => _root_.MIPStarRE.QPBT.DistanceCalculus.leftPlacedMeasurement (ιB := S.ExpandedLocalSpace .bob)
    ((w.marginalPoly .alice W).postprocess (fun g => _root_.MIPStarRE.QPBT.evalPoly g u))
  let margB := fun u => _root_.MIPStarRE.QPBT.DistanceCalculus.rightPlacedMeasurement (ιA := S.ExpandedLocalSpace .alice)
    ((w.marginalPoly .bob W).postprocess (fun g => _root_.MIPStarRE.QPBT.evalPoly g u))
  have hpost (side : _root_.MIPStarRE.QPBT.PlayerSide) (u : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) :
      (w.marginalPoly side W).postprocess (fun g => _root_.MIPStarRE.QPBT.evalPoly g u) =
        (w.Smeas side).postprocess (_root_.MIPStarRE.QPBT.evalAt W u) := by
    rw [_root_.MIPStarRE.QPBT.GlobalPairWitness.marginalPoly, _root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_comp]
    cases W <;> rfl
  have hab : _root_.MIPStarRE.QPBT.consistencyDefect mu (fun u a => (margA u).effect a)
      (fun u a => (pointB u).effect a) psi ≤ deltaG := by
    change _root_.MIPStarRE.QPBT.consistencyDefect mu
      (fun u a => _root_.MIPStarRE.QPBT.heteroKron (((w.marginalPoly .alice W).postprocess
        (fun g => _root_.MIPStarRE.QPBT.evalPoly g u)).effect a) 1)
      (fun u a => _root_.MIPStarRE.QPBT.heteroKron 1 ((S.pointMeasExp .bob W u).effect a)) psi ≤ deltaG
    rw [S.consistencyDefect_pairState_eq_AA_prime_BA_prime_prime]
    simpa only [hpost] using w.point_consistent_alice W
  have hba : _root_.MIPStarRE.QPBT.consistencyDefect mu (fun u a => (margB u).effect a)
      (fun u a => (pointA u).effect a) psi ≤ deltaG := by
    rw [_root_.MIPStarRE.QPBT.consistencyDefect_comm_of_commute _ _ _ _ (by
      intro u a b
      exact (_root_.MIPStarRE.QPBT.WinImplications.heteroKron_left_right_comm _ _).symm)]
    change _root_.MIPStarRE.QPBT.consistencyDefect mu
      (fun u a => _root_.MIPStarRE.QPBT.heteroKron ((S.pointMeasExp .alice W u).effect a) 1)
      (fun u a => _root_.MIPStarRE.QPBT.heteroKron 1 (((w.marginalPoly .bob W).postprocess
        (fun g => _root_.MIPStarRE.QPBT.evalPoly g u)).effect a)) psi ≤ deltaG
    rw [S.consistencyDefect_pairState_eq_AB_prime_prime_BB_prime,
      _root_.MIPStarRE.QPBT.consistencyDefect_comm_of_commute _ _ _ _ (by
        intro u a b
        exact S.place_comm .AB'' .BB' trivial _ _)]
    simpa only [hpost] using w.point_consistent_bob W
  have hpoints : _root_.MIPStarRE.QPBT.consistencyDefect mu (fun u a => (pointA u).effect a)
      (fun u a => (pointB u).effect a) psi ≤ 86 * epsilon := by
    change _root_.MIPStarRE.QPBT.consistencyDefect mu
      (fun u a => _root_.MIPStarRE.QPBT.heteroKron ((S.pointMeasExp .alice W u).effect a) 1)
      (fun u a => _root_.MIPStarRE.QPBT.heteroKron 1 ((S.pointMeasExp .bob W u).effect a)) psi ≤ _
    rw [S.expanded_point_consistency_eq]
    simpa only [_root_.MIPStarRE.QPBT.pauli_edge_card, Nat.cast_ofNat] using _root_.MIPStarRE.QPBT.point_self_consistency_le S W
  have hpoints' : _root_.MIPStarRE.QPBT.consistencyDefect mu (fun u a => (pointB u).effect a)
      (fun u a => (pointA u).effect a) psi ≤ 86 * epsilon := by
    rw [_root_.MIPStarRE.QPBT.consistencyDefect_comm_of_commute _ _ _ _ (by
      intro u a b
      exact (_root_.MIPStarRE.QPBT.WinImplications.heteroKron_left_right_comm _ _).symm)]
    exact hpoints
  have hpb : _root_.MIPStarRE.QPBT.consistencyDefect mu (fun u a => (pointA u).effect a)
      (fun u a => (refB u).effect a) psi ≤ 86 * epsilon := by
    change _root_.MIPStarRE.QPBT.consistencyDefect mu
      (fun u a => _root_.MIPStarRE.QPBT.heteroKron ((S.pointMeasExp .alice W u).effect a) 1)
      (fun u a => _root_.MIPStarRE.QPBT.heteroKron 1 (((S.encodingPauliMeas .bob W).postprocess
        (fun g => _root_.MIPStarRE.QPBT.evalPoly g u)).effect a)) psi ≤ _
    rw [S.point_encodingPauli_consistency_eq]
    exact _root_.MIPStarRE.QPBT.WinImplications.win_pauli_basis_cons_explicit P epsilon S hepsilon W
  have hpa : _root_.MIPStarRE.QPBT.consistencyDefect mu (fun u a => (pointB u).effect a)
      (fun u a => (refA u).effect a) psi ≤ 86 * epsilon := by
    rw [_root_.MIPStarRE.QPBT.consistencyDefect_comm_of_commute _ _ _ _ (by
      intro u a b
      exact (_root_.MIPStarRE.QPBT.WinImplications.heteroKron_left_right_comm _ _).symm)]
    change _root_.MIPStarRE.QPBT.consistencyDefect mu
      (fun u a => _root_.MIPStarRE.QPBT.heteroKron (((S.encodingPauliMeas .alice W).postprocess
        (fun g => _root_.MIPStarRE.QPBT.evalPoly g u)).effect a) 1)
      (fun u a => _root_.MIPStarRE.QPBT.heteroKron 1 ((S.pointMeasExp .bob W u).effect a)) psi ≤ _
    rw [S.encodingPauli_point_consistency_eq]
    exact _root_.MIPStarRE.QPBT.WinImplications.win_pauli_basis_cons_interchanged_explicit
      P epsilon S hepsilon W
  have hscalar : deltaG + 2 * Real.sqrt (86 * epsilon + 86 * epsilon) ≤
      deltaG + (1 + 2 * Real.sqrt 172) * Real.sqrt epsilon := by
    rw [← add_mul, show (86 : ℝ) + 86 = 172 by norm_num,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 172)]
    nlinarith [Real.sqrt_nonneg epsilon]
  constructor
  · exact (_root_.MIPStarRE.QPBT.consistencyDefect_trans_le mu margA pointB pointA refB psi
      deltaG (86 * epsilon) (86 * epsilon) (_root_.LIDT.MIPStarRE.LDT.uniformDistribution_isProbability _)
      (_root_.MIPStarRE.QPBT.ExtendedLineGame.pairState_norm S) hab hpoints hpb).trans hscalar
  · have h := (_root_.MIPStarRE.QPBT.consistencyDefect_trans_le mu margB pointA pointB refA psi
      deltaG (86 * epsilon) (86 * epsilon) (_root_.LIDT.MIPStarRE.LDT.uniformDistribution_isProbability _)
      (_root_.MIPStarRE.QPBT.ExtendedLineGame.pairState_norm S) hba hpoints' hpa).trans hscalar
    rw [_root_.MIPStarRE.QPBT.consistencyDefect_comm_of_commute _ _ _ _ (by
      intro u a b
      exact (_root_.MIPStarRE.QPBT.WinImplications.heteroKron_left_right_comm _ _).symm)] at h
    exact h
