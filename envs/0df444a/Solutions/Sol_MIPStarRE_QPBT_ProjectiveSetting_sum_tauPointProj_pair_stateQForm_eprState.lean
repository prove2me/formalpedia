-- Prove2me | solution 1 for MIPStarRE.QPBT.ProjectiveSetting.sum_tauPointProj_pair_stateQForm_eprState
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:56:25.756744+00:00
-- url     : https://prove2.me/submissions/457866cc-6751-4944-8023-dfe0e8e2516c

-- Generated proof for MIPStarRE.QPBT.ProjectiveSetting.sum_tauPointProj_pair_stateQForm_eprState.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
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
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Theorems.Thm_MIPStarRE_QPBT_ProjectiveSetting_tauPointProj_mul_tauPointProj

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.ProjectiveSetting
end MIPStarRE.QPBT.ProjectiveSetting
namespace MIPStarRE.QPBT.WinImplications
end MIPStarRE.QPBT.WinImplications

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

/- Source helpers from QPBT/Observables/WinImplications/Interchange.lean. -/
/-!
# Interchange of the tensor factors in the winning implications

This module collects the statements shared by the operator-distance companions
of the winning implications and by their factor-interchanged forms: transport of
the state-dependent distance along the interchange of the two tensor factors,
the constant-factor passage from consistency to distance, the reversed
verifier edges, and the clause-by-clause symmetry of the Pauli win predicate
on the ordered type pairs that the implications use.

## References

The declarations support the trailing clause of `lem:qld-win-implications` in
`blueprint/src/chapter/ch14_qpbt_observables.tex:616-706`. Their paper source
is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:192-267`,
whose closing sentences at lines 227 and 263-264 state both companions.
-/

@[expose] public section

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

namespace WinImplications

/-! ## Transport of the distance functional along the factor interchange -/

/-- The identity operator acts trivially on a state. Formalization-only support
for blueprint `def:strategy-observables`. -/
theorem applyOperatorToState_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) : _root_.MIPStarRE.QPBT.applyOperatorToState (1 : _root_.LIDT.MIPStarRE.Quantum.Op ι) ψ = ψ := by
  ext i
  simp [_root_.MIPStarRE.QPBT.applyOperatorToState]















/-! ## Reversed verifier edges

The Pauli type graph is a set of unordered pairs, so every ordered edge used by
the exact implications has its reverse in the graph. The reversed edges carry
the interchanged conclusions of `lem:qld-win-implications`, blueprint
`ch14_qpbt_observables.tex:701-703`. -/













/-! ## Symmetry of the win predicate on the subtests used here

`def:pauli-win-predicate` lists every clause together with its mirror image, so
on each ordered type pair occurring in `lem:qld-win-implications` exchanging the
two questions and the two answers leaves the predicate unchanged. Paper
`08_classical_and_quantum_low_degree_tests.tex:1126-1225`, blueprint
`ch13_qpbt_test.tex:410-449`. -/













/-! ## Numeric bookkeeping -/





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

/-- Acting with the same Pauli point projector on both halves of the EPR state
equals acting on one half. Symmetry transports the right action to the left,
where idempotence absorbs the repeated projector. This is the perfect
ancillary consistency used in item 1 of `lem:qld-comm-cons`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:455-465`. -/
theorem tauPointProj_pair_mulVec_eprState {P : _root_.MIPStarRE.QPBT.AdmissibleParams}
    (W : _root_.MIPStarRE.QPBT.PauliKind) (u : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) (a : _root_.MIPStarRE.QPBT.PauliScalar P) :
    (_root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.ProjectiveSetting.tauPointProj W u a) (_root_.MIPStarRE.QPBT.ProjectiveSetting.tauPointProj W u a)).mulVec
        (_root_.MIPStarRE.QPBT.eprState (_root_.MIPStarRE.QPBT.PauliRegister P)) =
      (_root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.ProjectiveSetting.tauPointProj W u a) 1).mulVec
        (_root_.MIPStarRE.QPBT.eprState (_root_.MIPStarRE.QPBT.PauliRegister P)) := by
  let T := _root_.MIPStarRE.QPBT.ProjectiveSetting.tauPointProj W u a
  have hfactor : _root_.MIPStarRE.QPBT.heteroKron T T = _root_.MIPStarRE.QPBT.heteroKron T 1 * _root_.MIPStarRE.QPBT.heteroKron 1 T := by
    rw [_root_.MIPStarRE.QPBT.heteroKron_mul, Matrix.mul_one, Matrix.one_mul]
  rw [hfactor, ← Matrix.mulVec_mulVec,
    ← _root_.MIPStarRE.QPBT.epr_action_eq_of_transpose T (_root_.MIPStarRE.QPBT.ProjectiveSetting.tauPointProj_transpose W u a),
    Matrix.mulVec_mulVec, _root_.MIPStarRE.QPBT.heteroKron_mul, Matrix.mul_one,
    _root_.MIPStarRE.QPBT.ProjectiveSetting.tauPointProj_mul_tauPointProj, if_pos rfl]



variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}

/-! ## The strategy factor of a placement -/





/-! ## The action of a placement on the expanded state -/





/-! ## Opposite-placement bipartitions -/













/-! ## The four placements -/



























end ProjectiveSetting

end

end MIPStarRE.QPBT

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



-- The unshuffled six-register index type of `eq:def-psihat` is a fourfold
-- iterated product; instance search for its `Fintype` and `DecidableEq`
-- structure needs a larger budget than the default.
set_option synthInstance.maxSize 400

open scoped BigOperators Matrix ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum



/-! ## Coordinate tensors -/











open MIPStarRE.QPBT.ProjectiveSetting

theorem solution {P : _root_.MIPStarRE.QPBT.AdmissibleParams}
    (W : _root_.MIPStarRE.QPBT.PauliKind) (u : Fin P.m → _root_.MIPStarRE.QPBT.PauliScalar P) :
    ∑ a : _root_.MIPStarRE.QPBT.PauliScalar P,
        _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm (_root_.MIPStarRE.QPBT.eprState (_root_.MIPStarRE.QPBT.PauliRegister P))
          (_root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.ProjectiveSetting.tauPointProj W u a) (_root_.MIPStarRE.QPBT.ProjectiveSetting.tauPointProj W u a)) = 1 := by
  have hterm (a : _root_.MIPStarRE.QPBT.PauliScalar P) :
      _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm (_root_.MIPStarRE.QPBT.eprState (_root_.MIPStarRE.QPBT.PauliRegister P))
          (_root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.ProjectiveSetting.tauPointProj W u a) (_root_.MIPStarRE.QPBT.ProjectiveSetting.tauPointProj W u a)) =
        _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm (_root_.MIPStarRE.QPBT.eprState (_root_.MIPStarRE.QPBT.PauliRegister P))
          (_root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.ProjectiveSetting.tauPointProj W u a) (1 : _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.PauliRegister P))) := by
    unfold _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm
    congr 2
    ext p
    simpa [_root_.MIPStarRE.QPBT.applyOperatorToState] using
      congrFun (_root_.MIPStarRE.QPBT.ProjectiveSetting.tauPointProj_pair_mulVec_eprState W u a) p
  simp_rw [hterm]
  have hsumop :
      (∑ a : _root_.MIPStarRE.QPBT.PauliScalar P,
          _root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.ProjectiveSetting.tauPointProj W u a) (1 : _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.PauliRegister P))) =
        _root_.MIPStarRE.QPBT.heteroKron (∑ a : _root_.MIPStarRE.QPBT.PauliScalar P, _root_.MIPStarRE.QPBT.ProjectiveSetting.tauPointProj W u a)
          (1 : _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.PauliRegister P)) := by
    ext i j
    rcases i with ⟨i₁, i₂⟩
    rcases j with ⟨j₁, j₂⟩
    unfold _root_.MIPStarRE.QPBT.heteroKron Matrix.kronecker Matrix.kroneckerMap
    simp only [Matrix.of_apply, Matrix.sum_apply]
    rw [Finset.sum_mul]
  have htausum : ∑ a : _root_.MIPStarRE.QPBT.PauliScalar P, _root_.MIPStarRE.QPBT.ProjectiveSetting.tauPointProj W u a = 1 :=
    (_root_.MIPStarRE.QPBT.ProjectiveSetting.tauPointMeas W u).sum_eq_one
  rw [← show _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm (_root_.MIPStarRE.QPBT.eprState (_root_.MIPStarRE.QPBT.PauliRegister P))
      (∑ a : _root_.MIPStarRE.QPBT.PauliScalar P,
        _root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.ProjectiveSetting.tauPointProj W u a) (1 : _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.PauliRegister P))) =
        ∑ a : _root_.MIPStarRE.QPBT.PauliScalar P,
          _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm (_root_.MIPStarRE.QPBT.eprState (_root_.MIPStarRE.QPBT.PauliRegister P))
            (_root_.MIPStarRE.QPBT.heteroKron (_root_.MIPStarRE.QPBT.ProjectiveSetting.tauPointProj W u a) (1 : _root_.LIDT.MIPStarRE.Quantum.Op (_root_.MIPStarRE.QPBT.PauliRegister P))) by
    simp [_root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm, _root_.MIPStarRE.QPBT.applyOperatorToState]]
  rw [hsumop, htausum, _root_.MIPStarRE.QPBT.heteroKron_one_one]
  unfold _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm
  rw [_root_.MIPStarRE.QPBT.WinImplications.applyOperatorToState_one]
  calc
    (inner ℂ (_root_.MIPStarRE.QPBT.eprState (_root_.MIPStarRE.QPBT.PauliRegister P))
        (_root_.MIPStarRE.QPBT.eprState (_root_.MIPStarRE.QPBT.PauliRegister P))).re =
      ‖_root_.MIPStarRE.QPBT.eprState (_root_.MIPStarRE.QPBT.PauliRegister P)‖ ^ 2 := by
        simpa using (inner_self_eq_norm_sq (𝕜 := ℂ)
          (_root_.MIPStarRE.QPBT.eprState (_root_.MIPStarRE.QPBT.PauliRegister P)))
    _ = 1 := by rw [_root_.MIPStarRE.QPBT.eprState_norm]; norm_num
