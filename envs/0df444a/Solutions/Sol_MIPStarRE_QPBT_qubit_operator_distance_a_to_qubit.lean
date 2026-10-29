-- Prove2me | solution 1 for MIPStarRE.QPBT.qubit_operator_distance_a_to_qubit
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T01:37:43.717574+00:00
-- url     : https://prove2.me/submissions/7bf30c13-ae17-41cf-b6be-3329b129b6c1

-- Generated proof for MIPStarRE.QPBT.qubit_operator_distance_a_to_qubit.
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
import Definitions.Def_QPBT_QPBT_Algebra_PauliTheorems
import Definitions.Def_QPBT_QPBT_Algebra_SelfDualBasisTheorems
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_State
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Definitions.Def_QPBT_QPBT_Test_QubitForm
import Definitions.Def_QPBT_QPBT_Test_SoundnessDefs
import Mathlib
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic
import Theorems.Thm_MIPStarRE_QPBT_pauliProj_reindex_quditQubitLabelEquiv

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.BinaryWitnessTransport
end MIPStarRE.QPBT.BinaryWitnessTransport

/- Source helpers from QPBT/Test/QubitForm.lean. -/
/-!
# Qubit form of Pauli basis test soundness

The fixed self-dual normal basis converts the qudit EPR register and generalized
Pauli projectors into qubit coordinates. The conversion uses only the basis
stored in the canonical `FixedFieldModel`.

`PauliSoundnessWitness.toQubit` transports supplied existential data, and the
three `qubit_*_to_qubit` identities preserve its comparison quantities exactly.
These are Lean-only transport results, not soundness existence theorems. This
module derives `pauli_soundness_qubit` from `pauli_soundness` using those identities.
`pauli_soundness` itself is now proved, so the corollary is complete: its
axiom closure is `propext`, `Classical.choice` and `Quot.sound`. The
composition that discharged it is recorded in issue Dengnifer/MIPStarRE-QPBT-bak#614, under the
umbrella issue Dengnifer/MIPStarRE-QPBT-bak#529.

## References

The conversion is blueprint
`lem:pauli-binary`, from
`references/qpbt-paper/04_preliminaries.tex:1163-1208`. The resulting
statement is blueprint `cor:pauli-binary`,
from `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1450-1491`.
-/

@[expose] public section

open scoped BigOperators Matrix

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum

noncomputable section







attribute [instance] _root_.MIPStarRE.QPBT.QubitSoundnessWitness.ιAFintype
  _root_.MIPStarRE.QPBT.QubitSoundnessWitness.ιBFintype _root_.MIPStarRE.QPBT.QubitSoundnessWitness.ιADecidableEq
  _root_.MIPStarRE.QPBT.QubitSoundnessWitness.ιBDecidableEq













namespace BinaryWitnessTransport

/-- Exact forward transport of a generalized Pauli projector to the existing
binary projector. This reorients the shared arbitrary-index calculation
`pauliProj_reindex_quditQubitLabelEquiv` from `lem:pauli-binary`, without a
second Fourier-inversion proof or a soundness hypothesis. -/
theorem pauli_projector_reindex {q : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (F : _root_.MIPStarRE.QPBT.FixedFieldModel q)
    (W : _root_.MIPStarRE.QPBT.PauliKind) (label : ι → F.K) :
    Matrix.reindex (_root_.MIPStarRE.QPBT.quditQubitLabelEquiv F) (_root_.MIPStarRE.QPBT.quditQubitLabelEquiv F) (_root_.MIPStarRE.QPBT.pauliProj W label) =
      _root_.MIPStarRE.QPBT.qubitPauliProj W (_root_.MIPStarRE.QPBT.kappaVec F label) := by
  classical
  have hinverse := _root_.MIPStarRE.QPBT.pauliProj_reindex_quditQubitLabelEquiv F W label
  ext row col
  simpa only [Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_symm, Equiv.apply_symm_apply] using
    congrFun (congrFun hinverse ((_root_.MIPStarRE.QPBT.quditQubitLabelEquiv F).symm row))
      ((_root_.MIPStarRE.QPBT.quditQubitLabelEquiv F).symm col)



/-- Simultaneous coordinate transport intertwines matrix action on a state. -/
theorem operator_action_reindex {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (equiv : ι ≃ κ) (operator : _root_.LIDT.MIPStarRE.Quantum.Op ι)
    (state : EuclideanSpace ℂ ι) :
    _root_.MIPStarRE.QPBT.applyOperatorToState (Matrix.reindex equiv equiv operator) (_root_.MIPStarRE.QPBT.reindexState equiv state) =
      _root_.MIPStarRE.QPBT.reindexState equiv (_root_.MIPStarRE.QPBT.applyOperatorToState operator state) := by
  ext position
  change (operator.submatrix equiv.symm equiv.symm *ᵥ
      (fun index => state (equiv.symm index))) position =
    (operator *ᵥ (fun index => state index)) (equiv.symm position)
  rw [Matrix.submatrix_mulVec_equiv]
  simp [Function.comp_def]

/-- Simultaneous transport of two operators and their reference state preserves
the norm of their difference applied to that state. -/
theorem operator_error_reindex {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (equiv : ι ≃ κ) (left right : _root_.LIDT.MIPStarRE.Quantum.Op ι)
    (state : EuclideanSpace ℂ ι) :
    ‖_root_.MIPStarRE.QPBT.applyOperatorToState (Matrix.reindex equiv equiv left -
        Matrix.reindex equiv equiv right) (_root_.MIPStarRE.QPBT.reindexState equiv state)‖ =
      ‖_root_.MIPStarRE.QPBT.applyOperatorToState (left - right) state‖ := by
  change ‖_root_.MIPStarRE.QPBT.applyOperatorToState (Matrix.reindex equiv equiv (left - right))
    (_root_.MIPStarRE.QPBT.reindexState equiv state)‖ = _
  rw [_root_.MIPStarRE.QPBT.BinaryWitnessTransport.operator_action_reindex, _root_.MIPStarRE.QPBT.reindexState_norm_eq]

/-- The paired EPR vector is invariant under simultaneous computational-basis
relabeling. This uses a permutation, not an arbitrary complex unitary. -/
theorem epr_reindex {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Fintype κ] [DecidableEq κ] [Nonempty κ] (equiv : ι ≃ κ) :
    _root_.MIPStarRE.QPBT.reindexState (Equiv.prodCongr equiv equiv) (_root_.MIPStarRE.QPBT.eprState ι) = _root_.MIPStarRE.QPBT.eprState κ := by
  ext position
  change (if equiv.symm position.1 = equiv.symm position.2 then
      (Real.sqrt (Fintype.card ι : ℝ) : ℂ)⁻¹ else 0) =
    if position.1 = position.2 then (Real.sqrt (Fintype.card κ : ℝ) : ℂ)⁻¹ else 0
  rw [Fintype.card_congr equiv]
  simp only [Equiv.apply_eq_iff_eq]



/-- Conjugation by a post-composed local coordinate permutation is matrix
reindexing of the original conjugated effect. -/
theorem conjugate_reindex_comp {ι κ ν : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [Fintype ν] [DecidableEq ν] (equiv : κ ≃ ν)
    (map : EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ κ) (operator : _root_.LIDT.MIPStarRE.Quantum.Op ι) :
    _root_.MIPStarRE.QPBT.conjIsometry
        ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ equiv).toLinearIsometry.comp map)
        operator = Matrix.reindex equiv equiv (_root_.MIPStarRE.QPBT.conjIsometry map operator) := by
  ext row col
  rfl





/-- Binary reindexing preserves the auxiliary factor and transports the EPR
factor exactly after the four-factor shuffle into local-player order. -/
theorem ideal_state_reindex (P : _root_.MIPStarRE.QPBT.AdmissibleParams)
    {auxA auxB : Type*} [Fintype auxA] [DecidableEq auxA]
    [Fintype auxB] [DecidableEq auxB] (aux : EuclideanSpace ℂ (auxA × auxB)) :
    _root_.MIPStarRE.QPBT.reindexState (_root_.MIPStarRE.QPBT.BinaryWitnessTransport.jointEquiv P auxA auxB) (_root_.MIPStarRE.QPBT.idealState P aux) = _root_.MIPStarRE.QPBT.idealQubitState P aux := by
  ext position
  exact congrArg (fun state : EuclideanSpace ℂ (_root_.MIPStarRE.QPBT.QubitRegister P × _root_.MIPStarRE.QPBT.QubitRegister P) =>
    aux (position.1.1, position.2.1) * state (position.1.2, position.2.2))
    (_root_.MIPStarRE.QPBT.BinaryWitnessTransport.epr_reindex (_root_.MIPStarRE.QPBT.quditQubitLabelEquiv (ι := _root_.MIPStarRE.QPBT.Cube P.m) P.model))

/-- Forward binary transport of Alice's lifted effect, including the identity
on Bob's entire local register. -/
theorem lifted_effect_a_reindex {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {G : _root_.MIPStarRE.QPBT.Game} (S : _root_.MIPStarRE.QPBT.Strategy G)
    {auxA auxB : Type*} [Fintype auxA] [DecidableEq auxA]
    [Fintype auxB] [DecidableEq auxB]
    (mapA : EuclideanSpace ℂ S.ιA →ₗᵢ[ℂ] EuclideanSpace ℂ (auxA × _root_.MIPStarRE.QPBT.PauliRegister P))
    (operator : _root_.LIDT.MIPStarRE.Quantum.Op S.ιA) :
    Matrix.reindex (_root_.MIPStarRE.QPBT.BinaryWitnessTransport.jointEquiv P auxA auxB) (_root_.MIPStarRE.QPBT.BinaryWitnessTransport.jointEquiv P auxA auxB)
        (_root_.MIPStarRE.QPBT.liftedAEffect S mapA operator) =
      _root_.MIPStarRE.QPBT.liftedQubitAEffect S
        ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
          (_root_.MIPStarRE.QPBT.BinaryWitnessTransport.localEquiv P auxA)).toLinearIsometry.comp mapA) operator := by
  classical
  rw [_root_.MIPStarRE.QPBT.liftedQubitAEffect, _root_.MIPStarRE.QPBT.BinaryWitnessTransport.conjugate_reindex_comp]
  ext row col
  change (if (_root_.MIPStarRE.QPBT.BinaryWitnessTransport.localEquiv P auxB).symm row.2 = (_root_.MIPStarRE.QPBT.BinaryWitnessTransport.localEquiv P auxB).symm col.2 then
      _root_.MIPStarRE.QPBT.conjIsometry mapA operator ((_root_.MIPStarRE.QPBT.BinaryWitnessTransport.localEquiv P auxA).symm row.1)
        ((_root_.MIPStarRE.QPBT.BinaryWitnessTransport.localEquiv P auxA).symm col.1) else 0) =
    _root_.MIPStarRE.QPBT.conjIsometry mapA operator ((_root_.MIPStarRE.QPBT.BinaryWitnessTransport.localEquiv P auxA).symm row.1)
      ((_root_.MIPStarRE.QPBT.BinaryWitnessTransport.localEquiv P auxA).symm col.1) * (if row.2 = col.2 then 1 else 0)
  simp only [Equiv.apply_eq_iff_eq, mul_ite, mul_one, mul_zero]



/-- Forward binary transport of the ideal projector on Alice's extracted
register, with the other three tensor factors fixed. -/
theorem ideal_projector_a_reindex (P : _root_.MIPStarRE.QPBT.AdmissibleParams)
    {auxA auxB : Type*} [Fintype auxA] [DecidableEq auxA]
    [Fintype auxB] [DecidableEq auxB] (W : _root_.MIPStarRE.QPBT.PauliKind) (label : _root_.MIPStarRE.QPBT.PauliRegister P) :
    Matrix.reindex (_root_.MIPStarRE.QPBT.BinaryWitnessTransport.jointEquiv P auxA auxB) (_root_.MIPStarRE.QPBT.BinaryWitnessTransport.jointEquiv P auxA auxB)
        (_root_.MIPStarRE.QPBT.pauliProjOnA'' P W label) = _root_.MIPStarRE.QPBT.qubitProjOnA'' P W label := by
  classical
  ext row col
  change (if row.1.1 = col.1.1 ∧
      (_root_.MIPStarRE.QPBT.BinaryWitnessTransport.localEquiv P auxB).symm row.2 = (_root_.MIPStarRE.QPBT.BinaryWitnessTransport.localEquiv P auxB).symm col.2 then
      (Matrix.reindex (_root_.MIPStarRE.QPBT.quditQubitLabelEquiv P.model) (_root_.MIPStarRE.QPBT.quditQubitLabelEquiv P.model)
        (_root_.MIPStarRE.QPBT.pauliProj W label)) row.1.2 col.1.2 else 0) =
    if row.1.1 = col.1.1 ∧ row.2 = col.2 then
      _root_.MIPStarRE.QPBT.qubitPauliProj W (_root_.MIPStarRE.QPBT.kappaVec P.model label) row.1.2 col.1.2 else 0
  rw [_root_.MIPStarRE.QPBT.BinaryWitnessTransport.pauli_projector_reindex]
  simp only [Equiv.apply_eq_iff_eq]



end BinaryWitnessTransport













end

end MIPStarRE.QPBT

/-!
# Qubit form of Pauli basis test soundness

The fixed self-dual normal basis converts the qudit EPR register and generalized
Pauli projectors into qubit coordinates. The conversion uses only the basis
stored in the canonical `FixedFieldModel`.

`PauliSoundnessWitness.toQubit` transports supplied existential data, and the
three `qubit_*_to_qubit` identities preserve its comparison quantities exactly.
These are Lean-only transport results, not soundness existence theorems. This
module derives `pauli_soundness_qubit` from `pauli_soundness` using those identities.
`pauli_soundness` itself is now proved, so the corollary is complete: its
axiom closure is `propext`, `Classical.choice` and `Quot.sound`. The
composition that discharged it is recorded in issue Dengnifer/MIPStarRE-QPBT-bak#614, under the
umbrella issue Dengnifer/MIPStarRE-QPBT-bak#529.

## References

The conversion is blueprint
`lem:pauli-binary`, from
`references/qpbt-paper/04_preliminaries.tex:1163-1208`. The resulting
statement is blueprint `cor:pauli-binary`,
from `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1450-1491`.
-/



open scoped BigOperators Matrix

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum









attribute [instance] _root_.MIPStarRE.QPBT.QubitSoundnessWitness.ιAFintype
  _root_.MIPStarRE.QPBT.QubitSoundnessWitness.ιBFintype _root_.MIPStarRE.QPBT.QubitSoundnessWitness.ιADecidableEq
  _root_.MIPStarRE.QPBT.QubitSoundnessWitness.ιBDecidableEq













open MIPStarRE.QPBT.BinaryWitnessTransport

theorem solution
    (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (S : _root_.MIPStarRE.QPBT.Strategy (_root_.MIPStarRE.QPBT.pauliBasisTest P))
    (w : _root_.MIPStarRE.QPBT.PauliSoundnessWitness P S) (W : _root_.MIPStarRE.QPBT.PauliKind) :
    _root_.MIPStarRE.QPBT.qubitOperatorDistanceA P S w.toQubit W = _root_.MIPStarRE.QPBT.rawPauliOperatorDistanceA P S w W := by
  unfold _root_.MIPStarRE.QPBT.qubitOperatorDistanceA _root_.MIPStarRE.QPBT.rawPauliOperatorDistanceA
  refine Finset.sum_congr rfl fun label _ => ?_
  have hnorm := _root_.MIPStarRE.QPBT.BinaryWitnessTransport.operator_error_reindex
    (_root_.MIPStarRE.QPBT.BinaryWitnessTransport.jointEquiv P w.ιA' w.ιB')
    (_root_.MIPStarRE.QPBT.liftedAEffect S w.φA
      ((S.A (_root_.MIPStarRE.QPBT.pauliQuestion P W)).effect (.pauliOutcome label)))
    (_root_.MIPStarRE.QPBT.pauliProjOnA'' P W label) (_root_.MIPStarRE.QPBT.idealState P w.aux)
  rw [_root_.MIPStarRE.QPBT.BinaryWitnessTransport.lifted_effect_a_reindex,
    _root_.MIPStarRE.QPBT.BinaryWitnessTransport.ideal_projector_a_reindex,
    _root_.MIPStarRE.QPBT.BinaryWitnessTransport.ideal_state_reindex] at hnorm
  exact congrArg (fun error : ℝ => error ^ 2) hnorm
