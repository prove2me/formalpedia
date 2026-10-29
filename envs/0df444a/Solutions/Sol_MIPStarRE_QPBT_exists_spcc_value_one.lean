-- Prove2me | solution 1 for MIPStarRE.QPBT.exists_spcc_value_one
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T03:27:40.456287+00:00
-- url     : https://prove2.me/submissions/7d73c36e-5bf0-448b-bff4-fc7965845f98

-- Generated proof for MIPStarRE.QPBT.exists_spcc_value_one.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_AvgCongr
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCode
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_StrategyClasses
import Definitions.Def_QPBT_QPBT_Test_Completeness
import Definitions.Def_QPBT_QPBT_Test_Completeness_HonestStrategy_MeasurementFamily
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Theorems.Thm_MIPStarRE_QPBT_heteroKron_mulVec_epr_eq_zero_of_mul_eq_zero
import Theorems.Thm_MIPStarRE_QPBT_honestMeasurement_commuting
import Theorems.Thm_MIPStarRE_QPBT_honestMeasurement_rejected_mul
import Theorems.Thm_MIPStarRE_QPBT_outcomeWeight_sum_eq_one

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
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

/- Source helpers from QPBT/Test/Completeness/HonestStrategy/MeasurementFamily.lean. -/
/-!
# The honest Pauli measurement family

This module collects the measurements of
`MIPStarRE.QPBT.Test.Completeness.HonestStrategy` into a single measurement
family indexed by the question type of the Pauli basis test.  Each honest
measurement acts on the tensor product of the Pauli register with the qubit
supplied to the Magic Square construction, and every outcome is relabelled into
the common answer alphabet of the test.  The results recorded here are the
projectivity and the symmetry of every effect of that family.

## References

The measurement family described here is the one displayed in the proof of
`lem:pauli-completeness`,
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1237-1360`;
blueprint `lem:pauli-completeness`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

/-! ### Tensor placement and relabeling -/

































/-! ### The total honest measurement family -/



































/-- The global honest measurement is consistent on the maximally entangled
state of the honest local space, every effect being symmetric. -/
theorem honestMeasurement_isConsistentOn (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (t : _root_.MIPStarRE.QPBT.PauliType)
    (z : _root_.MIPStarRE.QPBT.PauliSpace P) :
    _root_.MIPStarRE.QPBT.Measurement.IsConsistentOn (_root_.MIPStarRE.QPBT.honestMeasurement P t z)
      (_root_.MIPStarRE.QPBT.eprState (_root_.MIPStarRE.QPBT.HonestIndex P)) := fun a =>
  _root_.MIPStarRE.QPBT.epr_action_eq_of_transpose _ (_root_.MIPStarRE.QPBT.honestMeasurement_effect_transpose P t z a)





end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Test/Completeness.lean. -/
/-!
# Completeness of the Pauli basis test

The Pauli basis test admits a symmetric presentation and a value-one SPCC
strategy.

## References

The source statement is blueprint
`lem:pauli-completeness`, from
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1229-1421`.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT

noncomputable section

/-! ### Auxiliary facts about the Pauli question sampler

The two lemmas of this section are formalization-only.  They record that the
uniform law on the Pauli edge type, and the typed bind seeded by it, do not
depend on the finiteness and decidability data used to form them.  The general
identities about finite weighted distributions that this file uses are stated
in `MIPStarRE/QPBT/Games/DistributionAux.lean`.
-/





/-! ### The Pauli question sampler as a typed conditionally linear distribution -/





/-! ### Symmetry of the Pauli basis test -/











/-- Every measurement of the honest strategy is projective. -/
theorem honestStrategy_projective (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (x : _root_.MIPStarRE.QPBT.PauliQuestion P) :
    _root_.MIPStarRE.QPBT.Measurement.IsProjective ((_root_.MIPStarRE.QPBT.honestStrategy P).M x) :=
  _root_.MIPStarRE.QPBT.honestMeasurement_projective P x.1 x.2

/-- The honest strategy is consistent on its maximally entangled state. -/
theorem honestStrategy_isConsistent (P : _root_.MIPStarRE.QPBT.AdmissibleParams) :
    (_root_.MIPStarRE.QPBT.honestStrategy P).IsConsistent :=
  fun x => _root_.MIPStarRE.QPBT.honestMeasurement_isConsistentOn P x.1 x.2

/-- The honest strategy is a symmetric projective consistent commuting
strategy: every measurement is projective, the family is consistent on the
maximally entangled state, and the effects commute on every question pair of
positive weight. -/
theorem honestStrategy_isSPCC (P : _root_.MIPStarRE.QPBT.AdmissibleParams) :
    (_root_.MIPStarRE.QPBT.honestStrategy P).IsSPCC :=
  ⟨_root_.MIPStarRE.QPBT.honestStrategy_projective P, _root_.MIPStarRE.QPBT.honestStrategy_isConsistent P,
    _root_.MIPStarRE.QPBT.honestMeasurement_commuting P⟩





end

end MIPStarRE.QPBT

/-!
# Completeness of the Pauli basis test

The Pauli basis test admits a symmetric presentation and a value-one SPCC
strategy.

## References

The source statement is blueprint
`lem:pauli-completeness`, from
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1229-1421`.
-/



open scoped BigOperators

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT



/-! ### Auxiliary facts about the Pauli question sampler

The two lemmas of this section are formalization-only.  They record that the
uniform law on the Pauli edge type, and the typed bind seeded by it, do not
depend on the finiteness and decidability data used to form them.  The general
identities about finite weighted distributions that this file uses are stated
in `MIPStarRE/QPBT/Games/DistributionAux.lean`.
-/





/-! ### The Pauli question sampler as a typed conditionally linear distribution -/





/-! ### Symmetry of the Pauli basis test -/

theorem solution (P : _root_.MIPStarRE.QPBT.AdmissibleParams) :
    ∃ S : _root_.MIPStarRE.QPBT.SymmetricStrategy (_root_.MIPStarRE.QPBT.pauliBasisTestSymm P),
      S.IsSPCC ∧ S.toStrategy.value = 1 := by
  classical
  refine ⟨_root_.MIPStarRE.QPBT.honestStrategy P, _root_.MIPStarRE.QPBT.honestStrategy_isSPCC P, ?_⟩
  have hborn : ∀ x y : _root_.MIPStarRE.QPBT.PauliQuestion P,
      0 < (_root_.MIPStarRE.QPBT.pauliQuestionDistribution P).weight (x, y) →
      ∀ a b : _root_.MIPStarRE.QPBT.PauliAnswer P, _root_.MIPStarRE.QPBT.pauliWinPredicate P x y a b = false →
        _root_.MIPStarRE.QPBT.outcomeWeight (_root_.MIPStarRE.QPBT.honestStrategy P).toStrategy x y a b = 0 := by
    intro x y hxy a b hrej
    have hmul := _root_.MIPStarRE.QPBT.honestMeasurement_rejected_mul P x y hxy a b hrej
    have hzero := _root_.MIPStarRE.QPBT.heteroKron_mulVec_epr_eq_zero_of_mul_eq_zero
      ((_root_.MIPStarRE.QPBT.honestMeasurement P x.1 x.2).effect a)
      ((_root_.MIPStarRE.QPBT.honestMeasurement P y.1 y.2).effect b)
      (_root_.MIPStarRE.QPBT.honestMeasurement_effect_transpose P y.1 y.2 b) hmul
    have hacted : _root_.MIPStarRE.QPBT.applyOperatorToState
        (_root_.MIPStarRE.QPBT.heteroKron ((_root_.MIPStarRE.QPBT.honestMeasurement P x.1 x.2).effect a)
          ((_root_.MIPStarRE.QPBT.honestMeasurement P y.1 y.2).effect b))
        (_root_.MIPStarRE.QPBT.eprState (_root_.MIPStarRE.QPBT.HonestIndex P)) = 0 := by
      rw [_root_.MIPStarRE.QPBT.applyOperatorToState, Matrix.toLpLin_apply, hzero]
      rfl
    change (inner ℂ (_root_.MIPStarRE.QPBT.eprState (_root_.MIPStarRE.QPBT.HonestIndex P))
      (_root_.MIPStarRE.QPBT.applyOperatorToState
        (_root_.MIPStarRE.QPBT.heteroKron ((_root_.MIPStarRE.QPBT.honestMeasurement P x.1 x.2).effect a)
          ((_root_.MIPStarRE.QPBT.honestMeasurement P y.1 y.2).effect b))
        (_root_.MIPStarRE.QPBT.eprState (_root_.MIPStarRE.QPBT.HonestIndex P)))).re = 0
    rw [hacted]
    simp
  have hone : ∀ x y : _root_.MIPStarRE.QPBT.PauliQuestion P,
      0 < (_root_.MIPStarRE.QPBT.pauliQuestionDistribution P).weight (x, y) →
      (∑ a : _root_.MIPStarRE.QPBT.PauliAnswer P, ∑ b : _root_.MIPStarRE.QPBT.PauliAnswer P,
        if _root_.MIPStarRE.QPBT.pauliWinPredicate P x y a b then
          _root_.MIPStarRE.QPBT.outcomeWeight (_root_.MIPStarRE.QPBT.honestStrategy P).toStrategy x y a b else 0) = 1 := by
    intro x y hxy
    have hcong : (∑ a : _root_.MIPStarRE.QPBT.PauliAnswer P, ∑ b : _root_.MIPStarRE.QPBT.PauliAnswer P,
        if _root_.MIPStarRE.QPBT.pauliWinPredicate P x y a b then
          _root_.MIPStarRE.QPBT.outcomeWeight (_root_.MIPStarRE.QPBT.honestStrategy P).toStrategy x y a b else 0) =
        ∑ a : _root_.MIPStarRE.QPBT.PauliAnswer P, ∑ b : _root_.MIPStarRE.QPBT.PauliAnswer P,
          _root_.MIPStarRE.QPBT.outcomeWeight (_root_.MIPStarRE.QPBT.honestStrategy P).toStrategy x y a b := by
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      by_cases hab : _root_.MIPStarRE.QPBT.pauliWinPredicate P x y a b = true
      · simp [hab]
      · have hab' := Bool.eq_false_of_not_eq_true hab
        rw [hborn x y hxy a b hab']
        simp [hab']
    rw [hcong]
    exact _root_.MIPStarRE.QPBT.outcomeWeight_sum_eq_one (_root_.MIPStarRE.QPBT.honestStrategy P).toStrategy x y
  change _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.pauliQuestionDistribution P) (fun xy =>
    ∑ a : _root_.MIPStarRE.QPBT.PauliAnswer P, ∑ b : _root_.MIPStarRE.QPBT.PauliAnswer P,
      if _root_.MIPStarRE.QPBT.pauliWinPredicate P xy.1 xy.2 a b then
        _root_.MIPStarRE.QPBT.outcomeWeight (_root_.MIPStarRE.QPBT.honestStrategy P).toStrategy xy.1 xy.2 a b else 0) = 1
  have hcongr : _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.pauliQuestionDistribution P) (fun xy =>
      ∑ a : _root_.MIPStarRE.QPBT.PauliAnswer P, ∑ b : _root_.MIPStarRE.QPBT.PauliAnswer P,
        if _root_.MIPStarRE.QPBT.pauliWinPredicate P xy.1 xy.2 a b then
          _root_.MIPStarRE.QPBT.outcomeWeight (_root_.MIPStarRE.QPBT.honestStrategy P).toStrategy xy.1 xy.2 a b else 0) =
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.pauliQuestionDistribution P) (fun _ => 1) := by
    simp only [_root_.LIDT.MIPStarRE.LDT.avgOver]
    refine Finset.sum_congr rfl fun xy _ => ?_
    rcases lt_or_eq_of_le ((_root_.MIPStarRE.QPBT.pauliQuestionDistribution P).nonnegative xy) with hpos | hzero
    · rw [hone xy.1 xy.2 hpos]
    · rw [← hzero, zero_mul, zero_mul]
  rw [hcongr]
  exact _root_.LIDT.MIPStarRE.LDT.avgOver_const_of_isProbability _ (_root_.MIPStarRE.QPBT.pauliBasisTestSymm P).μ_prob 1
