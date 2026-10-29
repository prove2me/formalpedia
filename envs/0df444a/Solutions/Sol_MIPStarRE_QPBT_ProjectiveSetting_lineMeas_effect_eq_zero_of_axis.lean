-- Prove2me | solution 1 for MIPStarRE.QPBT.ProjectiveSetting.lineMeas_effect_eq_zero_of_axis
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:59:25.372956+00:00
-- url     : https://prove2.me/submissions/1777568b-23b8-44a6-8d1e-0abbb5eb8858

-- Generated proof for MIPStarRE.QPBT.ProjectiveSetting.lineMeas_effect_eq_zero_of_axis.
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
import Definitions.Def_QPBT_QPBT_Algebra_Lines
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_LineDefs
import Definitions.Def_QPBT_QPBT_Observables_LineMeasurement_Restriction
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.ProjectiveSetting
end MIPStarRE.QPBT.ProjectiveSetting

/-!
# Expanded line measurements

This module constructs the expanded line measurements by convolving a strategy
line measurement with the Pauli-register line projectors, and records that the
result is a projective measurement whose effects vanish, on an axis-parallel
line, outside the embedded degree-`d` outcome space. It also introduces the
fine strategy--Pauli product measurement of which the expanded line
measurement is the addition postprocessing, and the evaluation-class and
point-effect families used by the consistency estimates.

## References

The declarations formalize `def:expanded-line-measurement`, whose paper
source is
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:552-556`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum









open MIPStarRE.QPBT.ProjectiveSetting

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}

theorem solution (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε)
    (side : _root_.MIPStarRE.QPBT.PlayerSide) (W : _root_.MIPStarRE.QPBT.PauliKind) (line : _root_.MIPStarRE.QPBT.LineDesc P.toLdParams)
    (haxis : line.kind = .axis) (f : _root_.MIPStarRE.QPBT.DegPoly P.toLdParams (P.m * P.d))
    (hf : ¬ f.FitsDegree P.d) :
    (S.lineMeas side W line).effect f = 0 := by
  cases line with
  | diagonal base seed direction baseFixed prefixZero =>
      simp [_root_.MIPStarRE.QPBT.LineDesc.kind] at haxis
  | axis base seed baseFixed =>
      unfold _root_.MIPStarRE.QPBT.ProjectiveSetting.lineMeas
      rw [_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect]
      apply Finset.sum_eq_zero
      intro a ha
      exfalso
      apply hf
      rw [← (Finset.mem_filter.mp ha).2]
      intro i hi
      have hi' : ¬ i.val < P.d + 1 := by omega
      cases a <;> simp [_root_.MIPStarRE.QPBT.ProjectiveSetting.lineAnswerOrZero, _root_.MIPStarRE.QPBT.DegPoly.padTo, hi']
