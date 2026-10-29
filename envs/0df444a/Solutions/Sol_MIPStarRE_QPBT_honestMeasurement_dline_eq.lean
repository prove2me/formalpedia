-- Prove2me | solution 1 for MIPStarRE.QPBT.honestMeasurement_dline_eq
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T02:57:54.13757+00:00
-- url     : https://prove2.me/submissions/383e04d3-cf9b-4ac9-bf41-72e0bb25a452

-- Generated proof for MIPStarRE.QPBT.honestMeasurement_dline_eq.
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
import Theorems.Thm_MIPStarRE_QPBT_ldDLineCL_idempotent
import Theorems.Thm_MIPStarRE_QPBT_placedPauliMeasurement_postprocess_eq

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/- Source helpers from QPBT/Test/Completeness/Rejection.lean. -/
/-!
# Rejection of wrong answers by the honest Pauli measurements

This module shows that the honest measurement family of
`MIPStarRE.QPBT.Test.Completeness.HonestStrategy.MeasurementFamily` assigns the zero
operator product to every answer pair rejected by the Pauli win predicate on a
question pair of positive weight for the Pauli question sampler.  Together with
the normalisation of the Born weights this yields the value-one assertion of
`lem:pauli-completeness`.

## References

Blueprint `lem:pauli-completeness`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1383-1421`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

set_option maxRecDepth 8000

/-! ### Answers of an inadmissible form -/

















/-! ### Coordinate invariants of the typed Pauli conditionally linear maps -/

/-- Reading the low-degree register back from its embedding in the
basis-selected Pauli blocks returns the original vector; this is the coordinate
bookkeeping of `def:pauli-question-distribution`. -/
theorem pauliToLd_embedLd (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (W : _root_.MIPStarRE.QPBT.PauliKind)
    (u : _root_.MIPStarRE.QPBT.LdSpace P.toLdParams) : _root_.MIPStarRE.QPBT.pauliToLd P W (_root_.MIPStarRE.QPBT.embedLd P W u) = u := by
  funext i
  cases W <;> rcases i with (j | ⟨⟩) | j <;> rfl











/-- The low-degree register carried by a Diagonal-line/W question is already
fixed by the diagonal-line conditionally linear map;
`def:pauli-question-distribution`. -/
theorem ldDLineCL_pauliToLd_pauliCL_dline (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (W : _root_.MIPStarRE.QPBT.PauliKind)
    (z : _root_.MIPStarRE.QPBT.PauliSpace P) :
    _root_.MIPStarRE.QPBT.ldDLineCL P.toLdParams (_root_.MIPStarRE.QPBT.pauliToLd P W (_root_.MIPStarRE.QPBT.pauliCL P (.dline W) z)) =
      _root_.MIPStarRE.QPBT.ldDLineCL P.toLdParams (_root_.MIPStarRE.QPBT.pauliToLd P W z) := by
  rw [show _root_.MIPStarRE.QPBT.pauliToLd P W (_root_.MIPStarRE.QPBT.pauliCL P (.dline W) z) =
      _root_.MIPStarRE.QPBT.ldDLineCL P.toLdParams (_root_.MIPStarRE.QPBT.pauliToLd P W z) from _root_.MIPStarRE.QPBT.pauliToLd_embedLd P W _,
    _root_.MIPStarRE.QPBT.ldDLineCL_idempotent]











/-! ### The honest measurements as coarse-grainings of one Pauli basis -/















/-! ### The consistency clauses along the incidence forms -/





/-! ### Zero products along the incidence forms of the Pauli type graph -/















/-! ### The Pair/W versus Pair incidence form -/





/-! ### The Magic Square incidence forms -/



/-! ### Zero products along the oriented incidence forms -/



end

end MIPStarRE.QPBT

/-!
# Rejection of wrong answers by the honest Pauli measurements

This module shows that the honest measurement family of
`MIPStarRE.QPBT.Test.Completeness.HonestStrategy.MeasurementFamily` assigns the zero
operator product to every answer pair rejected by the Pauli win predicate on a
question pair of positive weight for the Pauli question sampler.  Together with
the normalisation of the Born weights this yields the value-one assertion of
`lem:pauli-completeness`.

## References

Blueprint `lem:pauli-completeness`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1383-1421`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum



set_option maxRecDepth 8000

/-! ### Answers of an inadmissible form -/

















/-! ### Coordinate invariants of the typed Pauli conditionally linear maps -/

























/-! ### The honest measurements as coarse-grainings of one Pauli basis -/

theorem solution (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (W : _root_.MIPStarRE.QPBT.PauliKind)
    (z : _root_.MIPStarRE.QPBT.PauliSpace P) :
    _root_.MIPStarRE.QPBT.honestMeasurement P (.dline W) (_root_.MIPStarRE.QPBT.pauliCL P (.dline W) z) =
      _root_.MIPStarRE.QPBT.placedPauliMeasurement (_root_.MIPStarRE.QPBT.pauliBasisMeasurement W)
        (fun h => _root_.MIPStarRE.QPBT.PauliAnswer.dlinePoly (_root_.MIPStarRE.QPBT.restrictToLine P.toLdParams
          (_root_.MIPStarRE.QPBT.dLineDescOf P.toLdParams (_root_.MIPStarRE.QPBT.ldDLineCL P.toLdParams (_root_.MIPStarRE.QPBT.pauliToLd P W z)))
          (_root_.MIPStarRE.QPBT.lowDegreeEncoding h))) := by
  have h1 : _root_.MIPStarRE.QPBT.honestMeasurement P (.dline W) (_root_.MIPStarRE.QPBT.pauliCL P (.dline W) z) =
      _root_.MIPStarRE.QPBT.placedPauliMeasurement (_root_.MIPStarRE.QPBT.pauliBasisMeasurement W)
        (fun h => _root_.MIPStarRE.QPBT.PauliAnswer.dlinePoly (_root_.MIPStarRE.QPBT.restrictToLine P.toLdParams
          (_root_.MIPStarRE.QPBT.dLineDescOf P.toLdParams (_root_.MIPStarRE.QPBT.ldDLineCL P.toLdParams
            (_root_.MIPStarRE.QPBT.pauliToLd P W (_root_.MIPStarRE.QPBT.pauliCL P (.dline W) z))))
          (_root_.MIPStarRE.QPBT.lowDegreeEncoding h))) :=
    _root_.MIPStarRE.QPBT.placedPauliMeasurement_postprocess_eq (_root_.MIPStarRE.QPBT.pauliBasisMeasurement W)
      (fun h => _root_.MIPStarRE.QPBT.restrictToLine P.toLdParams
        (_root_.MIPStarRE.QPBT.dLineDescOf P.toLdParams (_root_.MIPStarRE.QPBT.ldDLineCL P.toLdParams
          (_root_.MIPStarRE.QPBT.pauliToLd P W (_root_.MIPStarRE.QPBT.pauliCL P (.dline W) z)))) (_root_.MIPStarRE.QPBT.lowDegreeEncoding h))
      (fun a => _root_.MIPStarRE.QPBT.PauliAnswer.dlinePoly a)
  rw [h1, _root_.MIPStarRE.QPBT.ldDLineCL_pauliToLd_pauliCL_dline]
