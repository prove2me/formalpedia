-- Prove2me | solution 1 for MIPStarRE.QPBT.exists_placedBasis_of_basisType
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T02:57:53.936033+00:00
-- url     : https://prove2.me/submissions/7da668d5-b207-42c4-a7a0-585ca56839cd

-- Generated proof for MIPStarRE.QPBT.exists_placedBasis_of_basisType.
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
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCode
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Observables_LineDefs
import Definitions.Def_QPBT_QPBT_Observables_LineMeasurement_Restriction
import Definitions.Def_QPBT_QPBT_Test_Completeness_HonestStrategy
import Definitions.Def_QPBT_QPBT_Test_Completeness_HonestStrategy_MeasurementFamily
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Theorems.Thm_MIPStarRE_QPBT_placedPauliMeasurement_postprocess_eq

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/-!
# Commutation of the honest Pauli measurements

This module proves that the honest measurement family of
`MIPStarRE.QPBT.Test.Completeness.HonestStrategy.MeasurementFamily` has commuting effects
on every question pair of positive weight for the Pauli question sampler.  The
argument first characterises the supported question pairs as the typed
conditionally linear images of a single ambient coefficient vector along an edge
of the Pauli type graph, and then treats the five edge families of that graph.

## References

This is the commutation obligation in the proof of `lem:pauli-completeness`,
blueprint `lem:pauli-completeness`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1364-1382`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum



set_option maxRecDepth 8000

/-! ### The supported question pairs -/







/-! ### Coarse-graining and tensor placement -/













/-! ### Honest measurements sharing a Pauli basis -/

theorem solution (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (t : _root_.MIPStarRE.QPBT.PauliType)
    (W : _root_.MIPStarRE.QPBT.PauliKind) (z : _root_.MIPStarRE.QPBT.PauliSpace P)
    (ht : t = .point W ∨ t = .aline W ∨ t = .dline W ∨ t = .pauli W ∨
      t = .pairW W) :
    ∃ f : _root_.MIPStarRE.QPBT.PauliRegister P → _root_.MIPStarRE.QPBT.PauliAnswer P,
      _root_.MIPStarRE.QPBT.honestMeasurement P t z = _root_.MIPStarRE.QPBT.placedPauliMeasurement (_root_.MIPStarRE.QPBT.pauliBasisMeasurement W) f := by
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, _root_.MIPStarRE.QPBT.placedPauliMeasurement_postprocess_eq (_root_.MIPStarRE.QPBT.pauliBasisMeasurement W)
      (fun h => _root_.MIPStarRE.QPBT.lowDegreeEnc h (_root_.MIPStarRE.QPBT.pauliPointBlock W z)) (fun a => _root_.MIPStarRE.QPBT.PauliAnswer.value a)⟩
  · exact ⟨_, _root_.MIPStarRE.QPBT.placedPauliMeasurement_postprocess_eq (_root_.MIPStarRE.QPBT.pauliBasisMeasurement W)
      (fun h => _root_.MIPStarRE.QPBT.restrictToAxisLine P.toLdParams
        (_root_.MIPStarRE.QPBT.aLineDescOf P.toLdParams (_root_.MIPStarRE.QPBT.ldALineCL P.toLdParams (_root_.MIPStarRE.QPBT.pauliToLd P W z)))
        (_root_.MIPStarRE.QPBT.lowDegreeEncoding h)) (fun a => _root_.MIPStarRE.QPBT.PauliAnswer.alinePoly a)⟩
  · exact ⟨_, _root_.MIPStarRE.QPBT.placedPauliMeasurement_postprocess_eq (_root_.MIPStarRE.QPBT.pauliBasisMeasurement W)
      (fun h => _root_.MIPStarRE.QPBT.restrictToLine P.toLdParams
        (_root_.MIPStarRE.QPBT.dLineDescOf P.toLdParams (_root_.MIPStarRE.QPBT.ldDLineCL P.toLdParams (_root_.MIPStarRE.QPBT.pauliToLd P W z)))
        (_root_.MIPStarRE.QPBT.lowDegreeEncoding h)) (fun a => _root_.MIPStarRE.QPBT.PauliAnswer.dlinePoly a)⟩
  · exact ⟨fun a => _root_.MIPStarRE.QPBT.PauliAnswer.pauliOutcome a, rfl⟩
  · exact ⟨_, _root_.MIPStarRE.QPBT.placedPauliMeasurement_postprocess_eq (_root_.MIPStarRE.QPBT.pauliBasisMeasurement W)
      (_root_.MIPStarRE.QPBT.pauliTraceBit P (_root_.MIPStarRE.QPBT.pauliPointBlock W z)
        (match W with | .X => _root_.MIPStarRE.QPBT.pauliRXBlock z | .Z => _root_.MIPStarRE.QPBT.pauliRZBlock z))
      (fun a => _root_.MIPStarRE.QPBT.PauliAnswer.bit a)⟩
