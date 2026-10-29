-- Prove2me | solution 1 for MIPStarRE.QPBT.completedPauliEffect_eq_raw_add_wrongForm
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T01:45:45.120477+00:00
-- url     : https://prove2.me/submissions/e96a9507-d248-4b85-ba3a-9afe19f28e98

-- Generated proof for MIPStarRE.QPBT.completedPauliEffect_eq_raw_add_wrongForm.
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
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus
namespace MIPStarRE.QPBT.WinImplications
end MIPStarRE.QPBT.WinImplications

/-!
# Transfer from completed to raw Pauli effects

The extraction proof uses the complete Pauli-register measurement obtained by
folding malformed answers into outcome zero. The source theorem instead
compares the raw effects attached to answers of the form `.pauliOutcome u`.
This module bounds the malformed-answer mass by rejection on the two oriented
point/Pauli edges and transfers the completed-family estimates to the raw
families without adding a hypothesis to the source theorem.

## References

Paper `thm:pauli`,
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1431-1445`,
and its proof at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1862-1876`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

theorem solution {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (M : _root_.LIDT.MIPStarRE.Quantum.Measurement (_root_.MIPStarRE.QPBT.PauliAnswer P) ι)
    (W : _root_.MIPStarRE.QPBT.PauliKind) (u : _root_.MIPStarRE.QPBT.PauliRegister P) :
    (M.postprocess _root_.MIPStarRE.QPBT.pauliAnswerOrZero).effect u =
      M.effect (.pauliOutcome u) +
        if u = 0 then _root_.MIPStarRE.QPBT.ProjectiveSetting.wrongFormEffect (.pauli W) M else 0 := by
  classical
  rw [_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect, _root_.MIPStarRE.QPBT.ProjectiveSetting.wrongFormEffect,
    Finset.sum_filter]
  by_cases hu : u = 0
  · subst u
    simp only [ite_true]
    calc
      (∑ answer, if _root_.MIPStarRE.QPBT.pauliAnswerOrZero answer = 0 then M.effect answer else 0) =
          ∑ answer, ((if answer = .pauliOutcome 0 then M.effect answer else 0) +
            (if _root_.MIPStarRE.QPBT.validPauliAnswer (.pauli W) answer = false then M.effect answer else 0)) := by
        apply Finset.sum_congr rfl
        intro answer _
        cases answer <;> simp [_root_.MIPStarRE.QPBT.pauliAnswerOrZero, _root_.MIPStarRE.QPBT.validPauliAnswer] <;> rfl
      _ = _ := by
        rw [Finset.sum_add_distrib]
        congr 1
        · simp
        · rw [← Finset.sum_filter]
  · simp only [hu, ite_false, add_zero]
    rw [Finset.sum_eq_single (.pauliOutcome u)]
    · simp [_root_.MIPStarRE.QPBT.pauliAnswerOrZero]
    · intro answer _ hanswer
      have hzero : (0 : _root_.MIPStarRE.QPBT.PauliRegister P) ≠ u := by
        simpa [eq_comm] using hu
      cases answer <;> simp_all [_root_.MIPStarRE.QPBT.pauliAnswerOrZero]
    · simp
