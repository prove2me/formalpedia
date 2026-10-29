-- Prove2me | solution 1 for MIPStarRE.QPBT.Palomar.pauli_soundness
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T04:02:48.06184+00:00
-- url     : https://prove2.me/submissions/2032d954-5c03-4900-a125-b1657148da43

-- Generated proof for MIPStarRE.QPBT.Palomar.pauli_soundness.
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
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Palomar_Definitions
import Definitions.Def_QPBT_QPBT_Palomar_PauliExtractionBridge
import Definitions.Def_QPBT_QPBT_Palomar_PauliGameBridge
import Definitions.Def_QPBT_QPBT_Palomar_PauliGameStrategyBridge
import Definitions.Def_QPBT_QPBT_State
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Definitions.Def_QPBT_QPBT_Test_SoundnessDefs
import Mathlib
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic
import Theorems.Thm_MIPStarRE_QPBT_Palomar_pauliStrategyToLibrary_value
import Theorems.Thm_MIPStarRE_QPBT_exists_arbitrary_strategy_raw_isometry_bounds

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
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





























/-- Alice's compact qudit sum is exactly the registered raw-effect distance. -/
theorem rawPauliAliceError_ofPauliSoundnessWitness {P : _root_.MIPStarRE.QPBT.Palomar.PauliParams}
    {S : _root_.MIPStarRE.QPBT.Palomar.PauliStrategy P
      (_root_.MIPStarRE.QPBT.fixedFieldModel P.q P.is_admissible_size).K}
    (w : _root_.MIPStarRE.QPBT.PauliSoundnessWitness P.toAdmissibleParams
      (_root_.MIPStarRE.QPBT.Palomar.pauliStrategyToLibrary P.toAdmissibleParams S)) (W : _root_.MIPStarRE.QPBT.Palomar.PauliKind) :
    _root_.MIPStarRE.QPBT.Palomar.rawPauliAliceError P S (_root_.MIPStarRE.QPBT.Palomar.ExtractionWitness.ofPauliSoundnessWitness w)
        (_root_.MIPStarRE.QPBT.fixedBinTrace
          (_root_.MIPStarRE.QPBT.fixedFieldModel P.q P.is_admissible_size)) W =
      _root_.MIPStarRE.QPBT.rawPauliOperatorDistanceA P.toAdmissibleParams
        (_root_.MIPStarRE.QPBT.Palomar.pauliStrategyToLibrary P.toAdmissibleParams S) w (_root_.MIPStarRE.QPBT.Palomar.pauliKindEquiv W) := by
  cases W <;> rfl

/-- Bob's compact qudit sum is exactly the registered raw-effect distance. -/
theorem rawPauliBobError_ofPauliSoundnessWitness {P : _root_.MIPStarRE.QPBT.Palomar.PauliParams}
    {S : _root_.MIPStarRE.QPBT.Palomar.PauliStrategy P
      (_root_.MIPStarRE.QPBT.fixedFieldModel P.q P.is_admissible_size).K}
    (w : _root_.MIPStarRE.QPBT.PauliSoundnessWitness P.toAdmissibleParams
      (_root_.MIPStarRE.QPBT.Palomar.pauliStrategyToLibrary P.toAdmissibleParams S)) (W : _root_.MIPStarRE.QPBT.Palomar.PauliKind) :
    _root_.MIPStarRE.QPBT.Palomar.rawPauliBobError P S (_root_.MIPStarRE.QPBT.Palomar.ExtractionWitness.ofPauliSoundnessWitness w)
        (_root_.MIPStarRE.QPBT.fixedBinTrace
          (_root_.MIPStarRE.QPBT.fixedFieldModel P.q P.is_admissible_size)) W =
      _root_.MIPStarRE.QPBT.rawPauliOperatorDistanceB P.toAdmissibleParams
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
              (R := _root_.MIPStarRE.QPBT.Palomar.PauliRegister P
                (_root_.MIPStarRE.QPBT.fixedFieldModel P.q P.is_admissible_size).K) S,
            _root_.MIPStarRE.QPBT.Palomar.stateError w ≤ _root_.MIPStarRE.QPBT.Palomar.deltaQld a b epsilon P.m P.d P.q ∧
            (∀ W : _root_.MIPStarRE.QPBT.Palomar.PauliKind,
              _root_.MIPStarRE.QPBT.Palomar.rawPauliAliceError P S w
                  (_root_.MIPStarRE.QPBT.fixedBinTrace
                    (_root_.MIPStarRE.QPBT.fixedFieldModel P.q P.is_admissible_size)) W ≤
                _root_.MIPStarRE.QPBT.Palomar.deltaQld a b epsilon P.m P.d P.q) ∧
            ∀ W : _root_.MIPStarRE.QPBT.Palomar.PauliKind,
              _root_.MIPStarRE.QPBT.Palomar.rawPauliBobError P S w
                  (_root_.MIPStarRE.QPBT.fixedBinTrace
                    (_root_.MIPStarRE.QPBT.fixedFieldModel P.q P.is_admissible_size)) W ≤
                _root_.MIPStarRE.QPBT.Palomar.deltaQld a b epsilon P.m P.d P.q := by
  obtain ⟨a, b, ha, hb, hb_one, hsound⟩ := _root_.MIPStarRE.QPBT.pauli_soundness
  refine ⟨a, b, ha, hb, hb_one, ?_⟩
  intro P epsilon hepsilon S hvalue
  have hvalue' : 1 - epsilon ≤
      (_root_.MIPStarRE.QPBT.Palomar.pauliStrategyToLibrary P.toAdmissibleParams S).value :=
    hvalue.trans_eq
      (_root_.MIPStarRE.QPBT.Palomar.pauliStrategyToLibrary_value P.toAdmissibleParams S).symm
  obtain ⟨w, hstate, hAlice, hBob⟩ :=
    hsound P.toAdmissibleParams epsilon hepsilon
      (_root_.MIPStarRE.QPBT.Palomar.pauliStrategyToLibrary P.toAdmissibleParams S) hvalue'
  refine ⟨_root_.MIPStarRE.QPBT.Palomar.ExtractionWitness.ofPauliSoundnessWitness w, ?_, ?_, ?_⟩
  · exact (_root_.MIPStarRE.QPBT.Palomar.stateError_ofPauliSoundnessWitness w).trans_le hstate
  · intro W
    exact (_root_.MIPStarRE.QPBT.Palomar.rawPauliAliceError_ofPauliSoundnessWitness w W).trans_le
      (hAlice (_root_.MIPStarRE.QPBT.Palomar.pauliKindEquiv W))
  · intro W
    exact (_root_.MIPStarRE.QPBT.Palomar.rawPauliBobError_ofPauliSoundnessWitness w W).trans_le
      (hBob (_root_.MIPStarRE.QPBT.Palomar.pauliKindEquiv W))
