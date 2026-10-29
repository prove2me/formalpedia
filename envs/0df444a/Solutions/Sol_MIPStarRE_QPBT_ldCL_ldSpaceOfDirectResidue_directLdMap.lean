-- Prove2me | solution 1 for MIPStarRE.QPBT.ldCL_ldSpaceOfDirectResidue_directLdMap
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T21:28:22.851462+00:00
-- url     : https://prove2.me/submissions/d94e1203-e429-40fe-9197-6212321a6a60

-- Generated proof for MIPStarRE.QPBT.ldCL_ldSpaceOfDirectResidue_directLdMap.
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
import Definitions.Def_QPBT_QPBT_Observables_LineDefs
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Mathlib

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/DirectLowDegree/Geometry.lean. -/
/-!
# Geometry for the directly indexed low-degree game

This module defines the parameters, line carrier, and line-point distributions
for the directly indexed low-degree game.

## References

The line-point distributions originate in
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:243-272`.
The directly indexed repair is documented in
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.LDT.Preliminaries
open LIDT.MIPStarRE.Quantum

noncomputable section

























/-- Zeroing the coordinates preceding a prefix index is idempotent: the
coordinates it leaves unchanged are exactly those it does not zero. -/
theorem directPrefixProjection_idem (D : _root_.MIPStarRE.QPBT.DirectLdParams) (i : Fin D.m)
    (v : Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D) :
    _root_.MIPStarRE.QPBT.directPrefixProjection i (_root_.MIPStarRE.QPBT.directPrefixProjection i v) =
      _root_.MIPStarRE.QPBT.directPrefixProjection i v := by
  funext j
  unfold _root_.MIPStarRE.QPBT.directPrefixProjection
  split_ifs <;> rfl



/-! ## Finite direct-line carrier -/

















































end

end MIPStarRE.QPBT

/-!
# Value of the seed-fiber dilation

The correlated seed-fiber dilation `ldStrategyToDirect` reads a strategy for
the seed-indexed low-degree game as a strategy for the directly indexed game.
This module shows that the dilation preserves the value exactly.

The direct game asks the canonical questions of a common direct sample.  In
each residue block the dilated strategy asks the original strategy the seeded
canonical questions of that sample; since canonicalizing a canonical sample
changes nothing, these are the seed-indexed questions of the common sample
carrying that residue.  The Born weight of the dilation is the uniform average
of the original Born weights over the residue, the predicates agree after
parsing, and the seed-indexed sample is a direct sample together with a
uniform residue, so the two averages coincide branch by branch, including the
point/point, line/line, and wrong-form clauses and the zero-direction
convention.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:214-458`
- Blueprint `def:ld-question-distribution`, `lem:ld-aline-level`,
  `lem:ld-dline-level`, `lem:ld-question-typed-cl`, `lem:alnf`, and `lem:dlnf`
- `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`
-/



open scoped BigOperators MatrixOrder Matrix ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.Quantum

theorem solution (L : _root_.MIPStarRE.QPBT.LdParams) (t : _root_.MIPStarRE.QPBT.LdType)
    (sample : _root_.MIPStarRE.QPBT.DirectLdSpace L.toDirectLdParams) (residue : Fin (L.q / L.m)) :
    _root_.MIPStarRE.QPBT.ldCL L t (_root_.MIPStarRE.QPBT.ldSpaceOfDirectResidue L
        (_root_.MIPStarRE.QPBT.directLdMap L.toDirectLdParams t sample) residue) =
      _root_.MIPStarRE.QPBT.ldCL L t (_root_.MIPStarRE.QPBT.ldSpaceOfDirectResidue L sample residue) := by
  cases t with
  | point =>
      funext idx
      rcases idx with (j | ⟨⟩) | j <;> rfl
  | aline =>
      funext idx
      rcases idx with (j | ⟨⟩) | j
      · simp only [_root_.MIPStarRE.QPBT.ldCL, _root_.MIPStarRE.QPBT.ldALineCL, _root_.MIPStarRE.QPBT.ldSpaceOfDirectResidue_point,
          _root_.MIPStarRE.QPBT.ldSpaceOfDirectResidue_seed, _root_.MIPStarRE.QPBT.directLdMap, _root_.MIPStarRE.QPBT.chiIndex_seedOfIndexResidue]
        exact congrFun (_root_.MIPStarRE.QPBT.lineRepMap_apply_self _ _) j
      · rfl
      · rfl
  | dline =>
      funext idx
      rcases idx with (j | ⟨⟩) | j
      · simp only [_root_.MIPStarRE.QPBT.ldCL, _root_.MIPStarRE.QPBT.ldDLineCL, _root_.MIPStarRE.QPBT.ldSpaceOfDirectResidue_point,
          _root_.MIPStarRE.QPBT.ldSpaceOfDirectResidue_seed, _root_.MIPStarRE.QPBT.ldSpaceOfDirectResidue_direction, _root_.MIPStarRE.QPBT.directLdMap,
          _root_.MIPStarRE.QPBT.chiIndex_seedOfIndexResidue]
        change _root_.MIPStarRE.QPBT.lineRepMap
            (_root_.MIPStarRE.QPBT.directPrefixProjection sample.index
              (_root_.MIPStarRE.QPBT.directPrefixProjection sample.index sample.direction))
            (_root_.MIPStarRE.QPBT.lineRepMap (_root_.MIPStarRE.QPBT.directPrefixProjection sample.index sample.direction)
              sample.point) j =
          _root_.MIPStarRE.QPBT.lineRepMap (_root_.MIPStarRE.QPBT.directPrefixProjection sample.index sample.direction) sample.point j
        rw [_root_.MIPStarRE.QPBT.directPrefixProjection_idem]
        exact congrFun (_root_.MIPStarRE.QPBT.lineRepMap_apply_self _ _) j
      · rfl
      · simp only [_root_.MIPStarRE.QPBT.ldCL, _root_.MIPStarRE.QPBT.ldDLineCL, _root_.MIPStarRE.QPBT.ldSpaceOfDirectResidue_seed,
          _root_.MIPStarRE.QPBT.ldSpaceOfDirectResidue_direction, _root_.MIPStarRE.QPBT.directLdMap, _root_.MIPStarRE.QPBT.chiIndex_seedOfIndexResidue]
        change _root_.MIPStarRE.QPBT.directPrefixProjection sample.index
            (_root_.MIPStarRE.QPBT.directPrefixProjection sample.index sample.direction) j =
          _root_.MIPStarRE.QPBT.directPrefixProjection sample.index sample.direction j
        rw [_root_.MIPStarRE.QPBT.directPrefixProjection_idem]
