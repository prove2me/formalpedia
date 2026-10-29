-- Prove2me | solution 1 for MIPStarRE.QPBT.ProjectiveSetting.consistencyDefect_pairState_eq_AA_prime_BA_prime_prime
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T00:20:48.055385+00:00
-- url     : https://prove2.me/submissions/f4983d13-bd8e-47b7-94ab-02478aae2955

-- Generated proof for MIPStarRE.QPBT.ProjectiveSetting.consistencyDefect_pairState_eq_AA'_BA''.
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
import Definitions.Def_QPBT_QPBT_Combining_ExtendedLineGame
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_ExtendedLineGame_stateQForm_pairState_eq_AA_prime_BA_prime_prime

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.ProjectiveSetting
end MIPStarRE.QPBT.ProjectiveSetting

/-!
# Pair-state consistency transport

This module transports consistency defects on the two-player expanded state to
the corresponding opposite placements on the six-register expanded state.

## References

These formalization-only identities support the application of `lem:pasting`
in `lem:qld-xz-lines`, from
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:950-963` and
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:504-525`.
-/



open MIPStarRE.QPBT

open scoped MatrixOrder ComplexOrder

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum



open MIPStarRE.QPBT.ProjectiveSetting

theorem solution
    {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ} (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε)
    {Sample Outcome : Type*} [Fintype Sample] [DecidableEq Sample]
    [Fintype Outcome] [DecidableEq Outcome]
    (law : _root_.LIDT.MIPStarRE.LDT.Distribution Sample)
    (first : Sample → _root_.LIDT.MIPStarRE.Quantum.Measurement Outcome (S.ExpandedLocalSpace .alice))
    (second : Sample → _root_.LIDT.MIPStarRE.Quantum.Measurement Outcome (S.ExpandedLocalSpace .bob)) :
    _root_.MIPStarRE.QPBT.consistencyDefect law
        (fun sample answer => _root_.MIPStarRE.QPBT.heteroKron ((first sample).effect answer) 1)
        (fun sample answer => _root_.MIPStarRE.QPBT.heteroKron 1 ((second sample).effect answer))
        (_root_.MIPStarRE.QPBT.ExtendedLineGame.pairState S) =
      _root_.MIPStarRE.QPBT.consistencyDefect law
        (fun sample answer => S.place .AA' ((first sample).effect answer))
        (fun sample answer => S.place .BA'' ((second sample).effect answer))
        S.psiHat := by
  classical
  unfold _root_.MIPStarRE.QPBT.consistencyDefect
  apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
  intro sample
  apply Finset.sum_congr rfl
  intro firstAnswer _
  apply Finset.sum_congr rfl
  intro secondAnswer _
  by_cases hanswer : firstAnswer = secondAnswer
  · simp [hanswer]
  · simp only [if_neg hanswer]
    change _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm (_root_.MIPStarRE.QPBT.ExtendedLineGame.pairState S)
        (_root_.MIPStarRE.QPBT.heteroKron ((first sample).effect firstAnswer) 1 *
          _root_.MIPStarRE.QPBT.heteroKron 1 ((second sample).effect secondAnswer)) =
      _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm S.psiHat
        (S.place .AA' ((first sample).effect firstAnswer) *
          S.place .BA'' ((second sample).effect secondAnswer))
    rw [_root_.MIPStarRE.QPBT.heteroKron_mul, Matrix.mul_one, Matrix.one_mul]
    exact _root_.MIPStarRE.QPBT.ExtendedLineGame.stateQForm_pairState_eq_AA_prime_BA_prime_prime S _ _
      (Matrix.nonneg_iff_posSemidef.mp ((first sample).pos firstAnswer)).isHermitian
      (Matrix.nonneg_iff_posSemidef.mp ((second sample).pos secondAnswer)).isHermitian
