-- Prove2me | solution 1 for MIPStarRE.QPBT.msStrategyMeasurement_incident_commute
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T01:01:05.684892+00:00
-- url     : https://prove2.me/submissions/18e84683-0a68-44bd-9326-9b2d97804b27

-- Generated proof for MIPStarRE.QPBT.msStrategyMeasurement_incident_commute.
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
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Test_MagicSquare
import Definitions.Def_QPBT_QPBT_Test_MagicSquareTheorems_PerfectStrategy_Measurements

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/- Source helpers from QPBT/Test/MagicSquareTheorems/PerfectStrategy/Measurements.lean. -/
/-!
# Measurements of the perfect Magic Square strategy

This module turns the operator table of `thm:ms-from-ac` into a measurement
family.  It forms the joint measurement of two commuting binary projective
measurements, records the post-processing identities for injective
relabellings, encodes a constraint answer as the parity triple determined by
two freely chosen bits, and assembles the nine cell measurements into the
Magic Square measurement family, closing with the multiplication rule relating
a constraint outcome to the outcomes of its incident variables.

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
`thm:ms-from-ac`): on a variable question the global measurement
family reproduces the corresponding cell measurement: its effect at the answer
`bit b` is the effect of `P j` at `b`. -/
theorem msStrategyMeasurement_var_bit
    {V : Type*} [Fintype V] [DecidableEq V]
    (P : Fin 9 → _root_.LIDT.MIPStarRE.Quantum.Measurement (ZMod 2) V)
    (hP : ∀ j, _root_.MIPStarRE.QPBT.Measurement.IsProjective (P j))
    (hcomm : ∀ i k l a b,
      Commute ((P (_root_.MIPStarRE.QPBT.msConstraintVars i k)).effect a)
        ((P (_root_.MIPStarRE.QPBT.msConstraintVars i l)).effect b))
    (j : Fin 9) (b : ZMod 2) :
    (_root_.MIPStarRE.QPBT.msStrategyMeasurement P hP hcomm (.var j)).effect (.bit b) =
      (P j).effect b := by
  exact postprocess_effect_of_injective (P j) _root_.MIPStarRE.QPBT.MsAnswer.bit
    bit_embedding_injective b

/-- Formalization-only auxiliary lemma for
`exists_ms_perfect_strategy_of_anticommuting` (blueprint
`thm:ms-from-ac`): on a variable question the global measurement
family assigns the zero effect to every answer outside the range of
`MsAnswer.bit`. -/
theorem msStrategyMeasurement_var_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (P : Fin 9 → _root_.LIDT.MIPStarRE.Quantum.Measurement (ZMod 2) V)
    (hP : ∀ j, _root_.MIPStarRE.QPBT.Measurement.IsProjective (P j))
    (hcomm : ∀ i k l a b,
      Commute ((P (_root_.MIPStarRE.QPBT.msConstraintVars i k)).effect a)
        ((P (_root_.MIPStarRE.QPBT.msConstraintVars i l)).effect b))
    (j : Fin 9) {a : _root_.MIPStarRE.QPBT.MsAnswer}
    (ha : a ∉ Set.range (_root_.MIPStarRE.QPBT.MsAnswer.bit : ZMod 2 → _root_.MIPStarRE.QPBT.MsAnswer)) :
    (_root_.MIPStarRE.QPBT.msStrategyMeasurement P hP hcomm (.var j)).effect a = 0 := by
  exact _root_.MIPStarRE.QPBT.postprocess_effect_eq_zero_of_notMem (P j) _root_.MIPStarRE.QPBT.MsAnswer.bit ha

/-- Formalization-only auxiliary lemma for
`exists_ms_perfect_strategy_of_anticommuting` (blueprint
`thm:ms-from-ac`): on a constraint question the effect at the answer
triple encoding the bits `ab` equals the effect at `ab` of the joint measurement
of the first two cells of that constraint. -/
theorem msStrategyMeasurement_constraint_triple
    {V : Type*} [Fintype V] [DecidableEq V]
    (P : Fin 9 → _root_.LIDT.MIPStarRE.Quantum.Measurement (ZMod 2) V)
    (hP : ∀ j, _root_.MIPStarRE.QPBT.Measurement.IsProjective (P j))
    (hcomm : ∀ i k l a b,
      Commute ((P (_root_.MIPStarRE.QPBT.msConstraintVars i k)).effect a)
        ((P (_root_.MIPStarRE.QPBT.msConstraintVars i l)).effect b))
    (i : Fin 6) (ab : ZMod 2 × ZMod 2) :
    (_root_.MIPStarRE.QPBT.msStrategyMeasurement P hP hcomm (.constraint i)).effect
        (.triple (_root_.MIPStarRE.QPBT.parityTriple i ab)) =
      (_root_.MIPStarRE.QPBT.msConstraintJoint P hP hcomm i).effect ab := by
  exact postprocess_effect_of_injective (_root_.MIPStarRE.QPBT.msConstraintJoint P hP hcomm i)
    (fun cd => _root_.MIPStarRE.QPBT.MsAnswer.triple (_root_.MIPStarRE.QPBT.parityTriple i cd))
    (triple_embedding_injective i) ab

/-- Formalization-only auxiliary lemma for
`exists_ms_perfect_strategy_of_anticommuting` (blueprint
`thm:ms-from-ac`): on a constraint question the global measurement
family assigns the zero effect to every answer that is not a parity triple of
the constraint. -/
theorem msStrategyMeasurement_constraint_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (P : Fin 9 → _root_.LIDT.MIPStarRE.Quantum.Measurement (ZMod 2) V)
    (hP : ∀ j, _root_.MIPStarRE.QPBT.Measurement.IsProjective (P j))
    (hcomm : ∀ i k l a b,
      Commute ((P (_root_.MIPStarRE.QPBT.msConstraintVars i k)).effect a)
        ((P (_root_.MIPStarRE.QPBT.msConstraintVars i l)).effect b))
    (i : Fin 6) {a : _root_.MIPStarRE.QPBT.MsAnswer}
    (ha : a ∉ Set.range (fun ab => _root_.MIPStarRE.QPBT.MsAnswer.triple (_root_.MIPStarRE.QPBT.parityTriple i ab))) :
    (_root_.MIPStarRE.QPBT.msStrategyMeasurement P hP hcomm (.constraint i)).effect a = 0 := by
  exact _root_.MIPStarRE.QPBT.postprocess_effect_eq_zero_of_notMem (_root_.MIPStarRE.QPBT.msConstraintJoint P hP hcomm i)
    (fun ab => _root_.MIPStarRE.QPBT.MsAnswer.triple (_root_.MIPStarRE.QPBT.parityTriple i ab)) ha











end

end MIPStarRE.QPBT

/-!
# Perfect strategies for the Magic Square game

This file completes the construction of `thm:ms-from-ac`.  It identifies the
question pairs in the support of the Magic Square distribution, shows that the
measurement family commutes there and annihilates rejected answer pairs on the
EPR state, evaluates the Born weights of the accepted answers, and assembles a
symmetric SPCC strategy of value one from an anticommuting consistent pair of
binary measurements.

## References

The source statement is blueprint
`thm:ms-from-ac`, from
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:654-722`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

theorem solution
    {V : Type*} [Fintype V] [DecidableEq V]
    (P : Fin 9 → _root_.LIDT.MIPStarRE.Quantum.Measurement (ZMod 2) V)
    (hP : ∀ j, _root_.MIPStarRE.QPBT.Measurement.IsProjective (P j))
    (hcomm : ∀ i k l a b,
      Commute ((P (_root_.MIPStarRE.QPBT.msConstraintVars i k)).effect a)
        ((P (_root_.MIPStarRE.QPBT.msConstraintVars i l)).effect b))
    (i : Fin 6) (k : Fin 3) (a b : _root_.MIPStarRE.QPBT.MsAnswer) :
    Commute ((_root_.MIPStarRE.QPBT.msStrategyMeasurement P hP hcomm (.constraint i)).effect a)
      ((_root_.MIPStarRE.QPBT.msStrategyMeasurement P hP hcomm
        (.var (_root_.MIPStarRE.QPBT.msConstraintVars i k))).effect b) := by
  by_cases ha : a ∈ Set.range (fun ab => _root_.MIPStarRE.QPBT.MsAnswer.triple (_root_.MIPStarRE.QPBT.parityTriple i ab))
  · rcases ha with ⟨ab, rfl⟩
    rw [_root_.MIPStarRE.QPBT.msStrategyMeasurement_constraint_triple]
    by_cases hb : b ∈ Set.range (_root_.MIPStarRE.QPBT.MsAnswer.bit : ZMod 2 → _root_.MIPStarRE.QPBT.MsAnswer)
    · rcases hb with ⟨c, rfl⟩
      rw [_root_.MIPStarRE.QPBT.msStrategyMeasurement_var_bit]
      change Commute
        ((P (_root_.MIPStarRE.QPBT.msConstraintVars i 0)).effect ab.1 *
          (P (_root_.MIPStarRE.QPBT.msConstraintVars i 1)).effect ab.2)
        ((P (_root_.MIPStarRE.QPBT.msConstraintVars i k)).effect c)
      exact (hcomm i 0 k ab.1 c).mul_left (hcomm i 1 k ab.2 c)
    · rw [_root_.MIPStarRE.QPBT.msStrategyMeasurement_var_zero _ _ _ _ hb]
      exact Commute.zero_right _
  · rw [_root_.MIPStarRE.QPBT.msStrategyMeasurement_constraint_zero _ _ _ _ ha]
    exact Commute.zero_left _
