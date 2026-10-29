-- Prove2me | solution 1 for MIPStarRE.QPBT.ldDLineCL_idempotent
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T01:01:05.575996+00:00
-- url     : https://prove2.me/submissions/1537b43b-c1b0-48db-b12b-a71eace0e9ce

-- Generated proof for MIPStarRE.QPBT.ldDLineCL_idempotent.
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
import Definitions.Def_QPBT_QPBT_Algebra_Lines
import Definitions.Def_QPBT_QPBT_Observables_LineDefs
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Mathlib

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/- Source helpers from QPBT/Test/LowDegreeGame.lean. -/
/-!
# The low-degree game

The low-degree component of the Pauli basis test has finite question and answer
alphabets.  Its question maps act explicitly on the point, coordinate, and
direction registers of the ambient coefficient space and have recursive
conditionally linear representations of levels one, two, and three.

## References

The source-facing nodes are blueprint `def:ld-game`,
`def:ld-question-distribution`, and `def:ld-win-predicate`; their paper origin is
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`.
The exact decomposition of a scalar seed into its coordinate index and its
residue records the balance assertion for the map `chi` in the same source
definition.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT

noncomputable section























/-! ### Formalization-only coordinate-index fibers

The following decomposition supplies the equal-fiber calculation used in the
uniform coordinate-index law.
-/



















/-- Zeroing the coordinates preceding a fixed index is idempotent.  This is a
formalization-only consequence of the prefix restriction in
`def:ld-question-distribution`, recorded as `lem:prefix-projection-idempotent`
in blueprint chapter 13. -/
theorem prefixProjection_idempotent {P : _root_.MIPStarRE.QPBT.LdParams} (i : Fin P.m)
    (v : Fin P.m → _root_.MIPStarRE.QPBT.ScalarQ P) :
    _root_.MIPStarRE.QPBT.prefixProjection i (_root_.MIPStarRE.QPBT.prefixProjection i v) = _root_.MIPStarRE.QPBT.prefixProjection i v := by
  funext j
  by_cases h : j.val < i.val
  · simp only [_root_.MIPStarRE.QPBT.prefixProjection, if_pos h]
  · simp only [_root_.MIPStarRE.QPBT.prefixProjection, if_neg h]









































































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

theorem solution (L : _root_.MIPStarRE.QPBT.LdParams) (w : _root_.MIPStarRE.QPBT.LdSpace L) :
    _root_.MIPStarRE.QPBT.ldDLineCL L (_root_.MIPStarRE.QPBT.ldDLineCL L w) = _root_.MIPStarRE.QPBT.ldDLineCL L w := by
  funext i
  rcases i with (j | ⟨⟩) | j
  · change (_root_.MIPStarRE.QPBT.lineRepMap (_root_.MIPStarRE.QPBT.prefixProjection (_root_.MIPStarRE.QPBT.chiIndex L w.seed)
        (_root_.MIPStarRE.QPBT.prefixProjection (_root_.MIPStarRE.QPBT.chiIndex L w.seed) w.direction))
          (_root_.MIPStarRE.QPBT.lineRepMap (_root_.MIPStarRE.QPBT.prefixProjection (_root_.MIPStarRE.QPBT.chiIndex L w.seed) w.direction) w.point)) j =
      (_root_.MIPStarRE.QPBT.lineRepMap (_root_.MIPStarRE.QPBT.prefixProjection (_root_.MIPStarRE.QPBT.chiIndex L w.seed) w.direction) w.point) j
    rw [_root_.MIPStarRE.QPBT.prefixProjection_idempotent]
    exact congrFun (_root_.MIPStarRE.QPBT.lineRepMap_apply_self _ _) j
  · rfl
  · change _root_.MIPStarRE.QPBT.prefixProjection (_root_.MIPStarRE.QPBT.chiIndex L w.seed)
        (_root_.MIPStarRE.QPBT.prefixProjection (_root_.MIPStarRE.QPBT.chiIndex L w.seed) w.direction) j =
      _root_.MIPStarRE.QPBT.prefixProjection (_root_.MIPStarRE.QPBT.chiIndex L w.seed) w.direction j
    rw [_root_.MIPStarRE.QPBT.prefixProjection_idempotent]
