-- Prove2me | solution 1 for MIPStarRE.QPBT.Palomar.pauli_soundness_qubit
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T04:02:47.771551+00:00
-- url     : https://prove2.me/submissions/4a414d39-8950-4cfa-b347-0995eba97ef8

-- Generated proof for MIPStarRE.QPBT.Palomar.pauli_soundness_qubit.
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
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCode
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Algebra_PauliTheorems
import Definitions.Def_QPBT_QPBT_Algebra_SelfDualBasis
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Palomar_Definitions
import Definitions.Def_QPBT_QPBT_Palomar_PauliExtractionBridge
import Definitions.Def_QPBT_QPBT_Palomar_PauliGameBridge
import Definitions.Def_QPBT_QPBT_Palomar_PauliGameStrategyBridge
import Definitions.Def_QPBT_QPBT_State
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Definitions.Def_QPBT_QPBT_Test_QubitForm
import Definitions.Def_QPBT_QPBT_Test_SoundnessDefs
import Mathlib
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic
import Theorems.Thm_MIPStarRE_QPBT_Palomar_pauliStrategyToLibrary_value
import Theorems.Thm_MIPStarRE_QPBT_exists_arbitrary_strategy_raw_isometry_bounds
import Theorems.Thm_MIPStarRE_QPBT_qubit_operator_distance_a_to_qubit
import Theorems.Thm_MIPStarRE_QPBT_qubit_operator_distance_b_to_qubit

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.BinaryWitnessTransport
end MIPStarRE.QPBT.BinaryWitnessTransport
namespace MIPStarRE.QPBT.Palomar
end MIPStarRE.QPBT.Palomar

/- Source helpers from QPBT/Palomar/PauliExtractionBridge.lean. -/
attribute [local instance] _root_.MIPStarRE.QPBT.Palomar.compactPauliQuestionDecidableEq
/-!
# Exact bridges for compact Pauli extraction quantities

This module identifies the compact Pauli parameter record, prescribed-answer
effects, ideal projectors, witnesses, and extraction errors with the registered
QPBT definitions.  Every comparison is an equality; no quantitative estimate
or soundness assumption is introduced here.

The legacy import form is required because the registered soundness modules
have not yet been converted to Lean's module system.

## References

`references/qpbt-paper/04_preliminaries.tex:1052-1208`;
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1229-1491`.
-/

@[expose] public section

namespace MIPStarRE.QPBT.Palomar

noncomputable section

attribute [local instance] _root_.MIPStarRE.QPBT.Palomar.compactPauliQuestionDecidableEq

































/-- Alice's compact qubit sum is exactly the registered field-indexed distance. -/
theorem rawQubitAliceError_ofQubitSoundnessWitness {P : _root_.MIPStarRE.QPBT.Palomar.PauliParams}
    {S : _root_.MIPStarRE.QPBT.Palomar.PauliStrategy P
      (_root_.MIPStarRE.QPBT.fixedFieldModel P.q P.is_admissible_size).K}
    (w : _root_.MIPStarRE.QPBT.QubitSoundnessWitness P.toAdmissibleParams
      (_root_.MIPStarRE.QPBT.Palomar.pauliStrategyToLibrary P.toAdmissibleParams S)) (W : _root_.MIPStarRE.QPBT.Palomar.PauliKind) :
    _root_.MIPStarRE.QPBT.Palomar.rawQubitAliceError P S (_root_.MIPStarRE.QPBT.Palomar.ExtractionWitness.ofQubitSoundnessWitness w)
        (_root_.MIPStarRE.QPBT.fixedFieldModel P.q P.is_admissible_size).binaryCoordinates W =
      _root_.MIPStarRE.QPBT.qubitOperatorDistanceA P.toAdmissibleParams
        (_root_.MIPStarRE.QPBT.Palomar.pauliStrategyToLibrary P.toAdmissibleParams S) w (_root_.MIPStarRE.QPBT.Palomar.pauliKindEquiv W) := by
  cases W <;> rfl

/-- Bob's compact qubit sum is exactly the registered field-indexed distance. -/
theorem rawQubitBobError_ofQubitSoundnessWitness {P : _root_.MIPStarRE.QPBT.Palomar.PauliParams}
    {S : _root_.MIPStarRE.QPBT.Palomar.PauliStrategy P
      (_root_.MIPStarRE.QPBT.fixedFieldModel P.q P.is_admissible_size).K}
    (w : _root_.MIPStarRE.QPBT.QubitSoundnessWitness P.toAdmissibleParams
      (_root_.MIPStarRE.QPBT.Palomar.pauliStrategyToLibrary P.toAdmissibleParams S)) (W : _root_.MIPStarRE.QPBT.Palomar.PauliKind) :
    _root_.MIPStarRE.QPBT.Palomar.rawQubitBobError P S (_root_.MIPStarRE.QPBT.Palomar.ExtractionWitness.ofQubitSoundnessWitness w)
        (_root_.MIPStarRE.QPBT.fixedFieldModel P.q P.is_admissible_size).binaryCoordinates W =
      _root_.MIPStarRE.QPBT.qubitOperatorDistanceB P.toAdmissibleParams
        (_root_.MIPStarRE.QPBT.Palomar.pauliStrategyToLibrary P.toAdmissibleParams S) w (_root_.MIPStarRE.QPBT.Palomar.pauliKindEquiv W) := by
  cases W <;> rfl

end

end MIPStarRE.QPBT.Palomar

/- Source helpers from QPBT/Test/Soundness.lean. -/
/-!
# Pauli basis test soundness

This module states the source-shaped soundness theorem and provides auxiliary
range-projection estimates, ancilla isometries, and the transfer of supplied
extraction data to the three soundness estimates.
The scalar square-root error bound is in `MIPStarRE.QPBT.Combining.RootErrorBounds`.
The completed-family estimates are supplied by the Naimark reduction. The
final transfer bounds the rejected wrong-form mass and restores the raw Pauli
effects required by the paper before extending the result to the full error
domain.

## References

The main declaration is blueprint
`thm:pauli`, with paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1426-1447`.
-/

@[expose] public section

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.Quantum

noncomputable section



/-- `thm:pauli`: every sufficiently successful Pauli basis test strategy admits
local isometries and an auxiliary unit state for which the state and both
operator families are close at scale `deltaQld`.  The theorem uses the
once-and-for-all self-dual-normal field model selected by `fixedFieldModel` for
each admissible size, rather than a freshly quantified field identification.
Blueprint
`thm:pauli`; paper origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1426-1447`.

The paper's asymptotic constants are encoded by the explicit `deltaQld`
functional; the squared operator distances use the quantitative convention of
blueprint `def:povm-distance`.
-/
theorem pauli_soundness :
    ∃ a b : ℝ, 1 ≤ a ∧ 0 < b ∧ b < 1 ∧
      ∀ (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (ε : ℝ), 0 ≤ ε →
        ∀ S : _root_.MIPStarRE.QPBT.Strategy (_root_.MIPStarRE.QPBT.pauliBasisTest P), 1 - ε ≤ S.value →
          ∃ w : _root_.MIPStarRE.QPBT.PauliSoundnessWitness P S,
            ‖_root_.MIPStarRE.QPBT.isometryTensor w.φA w.φB S.ψ - _root_.MIPStarRE.QPBT.idealState P w.aux‖ ≤
                _root_.MIPStarRE.QPBT.deltaQld a b ε P.m P.d P.q ∧
            (∀ W : _root_.MIPStarRE.QPBT.PauliKind,
              _root_.MIPStarRE.QPBT.rawPauliOperatorDistanceA P S w W ≤ _root_.MIPStarRE.QPBT.deltaQld a b ε P.m P.d P.q) ∧
            (∀ W : _root_.MIPStarRE.QPBT.PauliKind,
              _root_.MIPStarRE.QPBT.rawPauliOperatorDistanceB P S w W ≤ _root_.MIPStarRE.QPBT.deltaQld a b ε P.m P.d P.q) := by
  exact _root_.MIPStarRE.QPBT.exists_arbitrary_strategy_raw_isometry_bounds

end

end MIPStarRE.QPBT

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



/-- Reindexing a vector agrees with Mathlib's Euclidean permutation isometry. -/
theorem reindex_state_eq {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (equiv : ι ≃ κ) (state : EuclideanSpace ℂ ι) :
    _root_.MIPStarRE.QPBT.reindexState equiv state = LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ equiv state := rfl





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

/-- Post-composing both local maps with coordinate permutations reindexes their
joint image. This is the permutation specialization of local isometry composition. -/
theorem tensor_reindex_comp {ιA ιB κA κB νA νB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype κA] [DecidableEq κA] [Fintype κB] [DecidableEq κB]
    [Fintype νA] [DecidableEq νA] [Fintype νB] [DecidableEq νB]
    (equivA : κA ≃ νA) (equivB : κB ≃ νB)
    (mapA : EuclideanSpace ℂ ιA →ₗᵢ[ℂ] EuclideanSpace ℂ κA)
    (mapB : EuclideanSpace ℂ ιB →ₗᵢ[ℂ] EuclideanSpace ℂ κB)
    (state : EuclideanSpace ℂ (ιA × ιB)) :
    _root_.MIPStarRE.QPBT.isometryTensor
        ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ equivA).toLinearIsometry.comp mapA)
        ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ equivB).toLinearIsometry.comp mapB)
        state = _root_.MIPStarRE.QPBT.reindexState (Equiv.prodCongr equivA equivB)
          (_root_.MIPStarRE.QPBT.isometryTensor mapA mapB state) := rfl







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









end BinaryWitnessTransport



/-- Exact preservation of state error for a supplied witness. This Lean-only
transport identity has no success assumption or error bound and does not assert
the existence conclusion of `cor:pauli-binary`. -/
theorem qubit_state_error_to_qubit
    (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (S : _root_.MIPStarRE.QPBT.Strategy (_root_.MIPStarRE.QPBT.pauliBasisTest P))
    (w : _root_.MIPStarRE.QPBT.PauliSoundnessWitness P S) :
    ‖_root_.MIPStarRE.QPBT.isometryTensor w.toQubit.φA w.toQubit.φB S.ψ -
        _root_.MIPStarRE.QPBT.idealQubitState P w.toQubit.aux‖ =
      ‖_root_.MIPStarRE.QPBT.isometryTensor w.φA w.φB S.ψ - _root_.MIPStarRE.QPBT.idealState P w.aux‖ := by
  change ‖_root_.MIPStarRE.QPBT.isometryTensor
      ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
        (_root_.MIPStarRE.QPBT.BinaryWitnessTransport.localEquiv P w.ιA')).toLinearIsometry.comp w.φA)
      ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
        (_root_.MIPStarRE.QPBT.BinaryWitnessTransport.localEquiv P w.ιB')).toLinearIsometry.comp w.φB)
      S.ψ - _root_.MIPStarRE.QPBT.idealQubitState P w.aux‖ = _
  rw [_root_.MIPStarRE.QPBT.BinaryWitnessTransport.tensor_reindex_comp,
    ← _root_.MIPStarRE.QPBT.BinaryWitnessTransport.ideal_state_reindex]
  rw [_root_.MIPStarRE.QPBT.BinaryWitnessTransport.reindex_state_eq, _root_.MIPStarRE.QPBT.BinaryWitnessTransport.reindex_state_eq]
  rw [_root_.MIPStarRE.QPBT.BinaryWitnessTransport.jointEquiv, ← map_sub, LinearIsometryEquiv.norm_map]







/-- `cor:pauli-binary`: soundness of the Pauli basis test in qubit
coordinates. Blueprint `cor:pauli-binary`, paper
`08_classical_and_quantum_low_degree_tests.tex:1450-1491`.

The theorem assumes a nonnegative error parameter, as in the source, and uses
only `P.model` and its stored basis dimension.

**Proof dependency:** The coordinate change and all three error identities are
proved, and the source theorem `pauli_soundness` is proved as well, so this
corollary is complete: its axiom closure is `propext`, `Classical.choice` and
`Quot.sound`. The composition that closed `pauli_soundness` is recorded in
issue Dengnifer/MIPStarRE-QPBT-bak#614, under the umbrella issue Dengnifer/MIPStarRE-QPBT-bak#529.
-/
theorem pauli_soundness_qubit :
    ∃ a b : ℝ, 1 ≤ a ∧ 0 < b ∧ b < 1 ∧
      ∀ (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (ε : ℝ), 0 ≤ ε →
        ∀ S : _root_.MIPStarRE.QPBT.Strategy (_root_.MIPStarRE.QPBT.pauliBasisTest P), 1 - ε ≤ S.value →
          ∃ w : _root_.MIPStarRE.QPBT.QubitSoundnessWitness P S,
            ‖_root_.MIPStarRE.QPBT.isometryTensor w.φA w.φB S.ψ - _root_.MIPStarRE.QPBT.idealQubitState P w.aux‖ ≤
                _root_.MIPStarRE.QPBT.deltaQld a b ε P.m P.d P.q ∧
            (∀ W : _root_.MIPStarRE.QPBT.PauliKind,
              _root_.MIPStarRE.QPBT.qubitOperatorDistanceA P S w W ≤
                _root_.MIPStarRE.QPBT.deltaQld a b ε P.m P.d P.q) ∧
            ∀ W : _root_.MIPStarRE.QPBT.PauliKind,
              _root_.MIPStarRE.QPBT.qubitOperatorDistanceB P S w W ≤
                _root_.MIPStarRE.QPBT.deltaQld a b ε P.m P.d P.q := by
  obtain ⟨a, b, ha, hb, hb_one, hsound⟩ := _root_.MIPStarRE.QPBT.pauli_soundness
  refine ⟨a, b, ha, hb, hb_one, ?_⟩
  intro P ε hε S hS
  obtain ⟨w, hstate, hA, hB⟩ := hsound P ε hε S hS
  refine ⟨w.toQubit, ?_, ?_, ?_⟩
  · exact (_root_.MIPStarRE.QPBT.qubit_state_error_to_qubit P S w).trans_le hstate
  · intro W
    exact (_root_.MIPStarRE.QPBT.qubit_operator_distance_a_to_qubit P S w W).trans_le (hA W)
  · intro W
    exact (_root_.MIPStarRE.QPBT.qubit_operator_distance_b_to_qubit P S w W).trans_le (hB W)

end

end MIPStarRE.QPBT

/-!
# Compact Pauli basis test soundness

This module transports the registered qudit and qubit soundness theorems to the
compact Palomar game.  The statements use the once-and-for-all field model,
arbitrary compact strategies, raw prescribed-answer effects, the unsquared
state norm, and separate unaveraged Alice and Bob squared operator sums.

## References

`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1431-1491`,
paper `thm:pauli` and `cor:pauli-binary`;
`references/qpbt-paper/04_preliminaries.tex:1163-1208`.
-/



open MIPStarRE.QPBT.Palomar

theorem solution :
    ∃ a b : ℝ, 1 ≤ a ∧ 0 < b ∧ b < 1 ∧
      ∀ (P : _root_.MIPStarRE.QPBT.Palomar.PauliParams) (epsilon : ℝ), 0 ≤ epsilon →
        ∀ S : _root_.MIPStarRE.QPBT.Palomar.PauliStrategy P
            (_root_.MIPStarRE.QPBT.fixedFieldModel P.q P.is_admissible_size).K,
          1 - epsilon ≤ S.value
            (_root_.MIPStarRE.QPBT.Palomar.pauliGame P
              (_root_.MIPStarRE.QPBT.binaryRepresentation
                (_root_.MIPStarRE.QPBT.fixedFieldModel P.q P.is_admissible_size))
              (_root_.MIPStarRE.QPBT.fixedBinTrace
                (_root_.MIPStarRE.QPBT.fixedFieldModel P.q P.is_admissible_size))) →
          ∃ w : _root_.MIPStarRE.QPBT.Palomar.ExtractionWitness
              (R := _root_.MIPStarRE.QPBT.Palomar.QubitRegister P
                (_root_.MIPStarRE.QPBT.fixedFieldModel P.q
                  P.is_admissible_size).basisDim) S,
            _root_.MIPStarRE.QPBT.Palomar.stateError w ≤ _root_.MIPStarRE.QPBT.Palomar.deltaQld a b epsilon P.m P.d P.q ∧
            (∀ W : _root_.MIPStarRE.QPBT.Palomar.PauliKind,
              _root_.MIPStarRE.QPBT.Palomar.rawQubitAliceError P S w
                  (_root_.MIPStarRE.QPBT.fixedFieldModel P.q
                    P.is_admissible_size).binaryCoordinates W ≤
                _root_.MIPStarRE.QPBT.Palomar.deltaQld a b epsilon P.m P.d P.q) ∧
            ∀ W : _root_.MIPStarRE.QPBT.Palomar.PauliKind,
              _root_.MIPStarRE.QPBT.Palomar.rawQubitBobError P S w
                  (_root_.MIPStarRE.QPBT.fixedFieldModel P.q
                    P.is_admissible_size).binaryCoordinates W ≤
                _root_.MIPStarRE.QPBT.Palomar.deltaQld a b epsilon P.m P.d P.q := by
  obtain ⟨a, b, ha, hb, hb_one, hsound⟩ :=
    _root_.MIPStarRE.QPBT.pauli_soundness_qubit
  refine ⟨a, b, ha, hb, hb_one, ?_⟩
  intro P epsilon hepsilon S hvalue
  have hvalue' : 1 - epsilon ≤
      (_root_.MIPStarRE.QPBT.Palomar.pauliStrategyToLibrary P.toAdmissibleParams S).value :=
    hvalue.trans_eq
      (_root_.MIPStarRE.QPBT.Palomar.pauliStrategyToLibrary_value P.toAdmissibleParams S).symm
  obtain ⟨w, hstate, hAlice, hBob⟩ :=
    hsound P.toAdmissibleParams epsilon hepsilon
      (_root_.MIPStarRE.QPBT.Palomar.pauliStrategyToLibrary P.toAdmissibleParams S) hvalue'
  refine ⟨_root_.MIPStarRE.QPBT.Palomar.ExtractionWitness.ofQubitSoundnessWitness w, ?_, ?_, ?_⟩
  · exact (_root_.MIPStarRE.QPBT.Palomar.stateError_ofQubitSoundnessWitness w).trans_le hstate
  · intro W
    exact (_root_.MIPStarRE.QPBT.Palomar.rawQubitAliceError_ofQubitSoundnessWitness w W).trans_le
      (hAlice (_root_.MIPStarRE.QPBT.Palomar.pauliKindEquiv W))
  · intro W
    exact (_root_.MIPStarRE.QPBT.Palomar.rawQubitBobError_ofQubitSoundnessWitness w W).trans_le
      (hBob (_root_.MIPStarRE.QPBT.Palomar.pauliKindEquiv W))
