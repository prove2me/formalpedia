-- Prove2me | solution 1 for MIPStarRE.QPBT.parseLdQuestion_ldCL_ofDirectResidue
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T21:25:06.310658+00:00
-- url     : https://prove2.me/submissions/7315e510-9c38-444b-a2d3-fb5f8919e202

-- Generated proof for MIPStarRE.QPBT.parseLdQuestion_ldCL_ofDirectResidue.
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
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Game
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Correspondence
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Mathlib

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/-!
# Question correspondence for the directly indexed low-degree game

The finite-field coordinates, polynomial answers, and question law of the
directly indexed game are equivalent to their seed-indexed and low individual
degree counterparts.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-458`
- `references/ldt-paper/test_definition.tex:98-151`
- `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`
-/



open scoped BigOperators MatrixOrder Matrix ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.Quantum



/-! ## Parameters and finite-field coordinates -/













/-! ## Bounded coefficient vectors -/

















/-! ## Parameters and answers of the two QPBT game presentations -/







/-! ## Parsing seed-indexed questions -/

theorem solution (L : _root_.MIPStarRE.QPBT.LdParams)
    (t : _root_.MIPStarRE.QPBT.LdType) (sample : _root_.MIPStarRE.QPBT.DirectLdSpace L.toDirectLdParams)
    (residue : Fin (L.q / L.m)) :
    _root_.MIPStarRE.QPBT.parseLdQuestion L
        (t, _root_.MIPStarRE.QPBT.ldCL L t (_root_.MIPStarRE.QPBT.ldSpaceOfDirectResidue L sample residue)) =
      (t, _root_.MIPStarRE.QPBT.directLdMap L.toDirectLdParams t sample) := by
  cases t with
  | point =>
    rfl
  | aline =>
      ext <;>
        simp only [_root_.MIPStarRE.QPBT.parseLdQuestion, _root_.MIPStarRE.QPBT.ldCL, _root_.MIPStarRE.QPBT.ldALineCL, _root_.MIPStarRE.QPBT.directLdMap,
          _root_.MIPStarRE.QPBT.ldSpaceOfDirectResidue, _root_.MIPStarRE.QPBT.ldSpaceOfDirectResidue_point, _root_.MIPStarRE.QPBT.LdSpace.seed,
          _root_.MIPStarRE.QPBT.chiIndex_seedOfIndexResidue]
      congr 1
  | dline =>
      ext <;>
        simp only [_root_.MIPStarRE.QPBT.parseLdQuestion, _root_.MIPStarRE.QPBT.ldCL, _root_.MIPStarRE.QPBT.ldDLineCL, _root_.MIPStarRE.QPBT.directLdMap,
          _root_.MIPStarRE.QPBT.ldSpaceOfDirectResidue, _root_.MIPStarRE.QPBT.ldSpaceOfDirectResidue_point,
          _root_.MIPStarRE.QPBT.ldSpaceOfDirectResidue_direction, _root_.MIPStarRE.QPBT.LdSpace.seed,
          _root_.MIPStarRE.QPBT.LdSpace.direction, _root_.MIPStarRE.QPBT.chiIndex_seedOfIndexResidue,
          _root_.MIPStarRE.QPBT.prefixProjection]
      rfl
