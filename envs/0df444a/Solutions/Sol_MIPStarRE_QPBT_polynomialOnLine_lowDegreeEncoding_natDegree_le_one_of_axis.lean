-- Prove2me | solution 1 for MIPStarRE.QPBT.polynomialOnLine_lowDegreeEncoding_natDegree_le_one_of_axis
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T00:04:37.833129+00:00
-- url     : https://prove2.me/submissions/0763621a-a30b-434b-810b-0d5bb1227545

-- Generated proof for MIPStarRE.QPBT.polynomialOnLine_lowDegreeEncoding_natDegree_le_one_of_axis.
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
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCode
import Definitions.Def_QPBT_QPBT_Observables_LineDefs
import Definitions.Def_QPBT_QPBT_Observables_LineMeasurement_Restriction
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Mathlib
import Theorems.Thm_MIPStarRE_QPBT_polynomialOnLine_lowDegreeEncoding_natDegree_le_sum

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/- Source helpers from QPBT/Observables/LineMeasurement/Restriction.lean. -/
/-!
# Restriction of low-degree encodings to canonical lines

This module substitutes a canonical line into a multivariate polynomial and
records the resulting univariate polynomial as a coefficient list. The
multilinear low-degree encoding has degree at most `m ≤ m*d` on any line and
degree at most `1 ≤ d` on an axis-parallel line. Its coefficient list evaluates
to the original encoding at every point on the line, including a line with
zero direction.

## References

The encoding is equation `eq:ld-encoding` in
`references/qpbt-paper/04_preliminaries.tex:869-896`. Restriction supplies the
line answers in `lem:pauli-completeness`, paper
`08_classical_and_quantum_low_degree_tests.tex:1244-1273`, and the ancillary
line projector in the proof of `lem:qld-comm-line-cons`, paper
`14_analysis_of_the_pauli_basis_test.tex:552-556`. The restriction bounds and
evaluation identities are recorded in blueprint
`lem:low-degree-encoding-line-restriction`.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT

noncomputable section





/-- Each coordinate of the affine parameterization has degree at most one.
This is a formalization-only auxiliary for the multilinearity argument in
blueprint `lem:low-degree-encoding-line-restriction`. -/
private theorem natDegree_lineCoordinate_le (L : _root_.MIPStarRE.QPBT.LdParams) (line : _root_.MIPStarRE.QPBT.LineDesc L)
    (i : Fin L.m) :
    (_root_.Polynomial.C (line.base i) +
        _root_.Polynomial.X * _root_.Polynomial.C (line.direction i) :
        Polynomial (_root_.MIPStarRE.QPBT.ScalarQ L)).natDegree ≤ 1 := by
  refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
  · simp
  · refine Polynomial.natDegree_mul_le.trans ?_
    simp

/-- A coordinate with zero direction is constant along the line.
This is a formalization-only auxiliary for the axis case of blueprint
`lem:low-degree-encoding-line-restriction`. -/
private theorem natDegree_lineCoordinate_eq_zero (L : _root_.MIPStarRE.QPBT.LdParams)
    (line : _root_.MIPStarRE.QPBT.LineDesc L) (i : Fin L.m) (hi : line.direction i = 0) :
    (_root_.Polynomial.C (line.base i) +
        _root_.Polynomial.X * _root_.Polynomial.C (line.direction i) :
        Polynomial (_root_.MIPStarRE.QPBT.ScalarQ L)).natDegree = 0 := by
  rw [hi, map_zero, mul_zero, add_zero, Polynomial.natDegree_C]











/-! ## Evaluation of the restriction along the line -/











end

end MIPStarRE.QPBT

/-!
# Restriction of low-degree encodings to canonical lines

This module substitutes a canonical line into a multivariate polynomial and
records the resulting univariate polynomial as a coefficient list. The
multilinear low-degree encoding has degree at most `m ≤ m*d` on any line and
degree at most `1 ≤ d` on an axis-parallel line. Its coefficient list evaluates
to the original encoding at every point on the line, including a line with
zero direction.

## References

The encoding is equation `eq:ld-encoding` in
`references/qpbt-paper/04_preliminaries.tex:869-896`. Restriction supplies the
line answers in `lem:pauli-completeness`, paper
`08_classical_and_quantum_low_degree_tests.tex:1244-1273`, and the ancillary
line projector in the proof of `lem:qld-comm-line-cons`, paper
`14_analysis_of_the_pauli_basis_test.tex:552-556`. The restriction bounds and
evaluation identities are recorded in blueprint
`lem:low-degree-encoding-line-restriction`.
-/



open scoped BigOperators

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT

theorem solution
    (L : _root_.MIPStarRE.QPBT.LdParams) (line : _root_.MIPStarRE.QPBT.LineDesc L) (haxis : line.kind = .axis)
    (h : _root_.MIPStarRE.QPBT.Cube L.m → _root_.MIPStarRE.QPBT.ScalarQ L) :
    (_root_.MIPStarRE.QPBT.polynomialOnLine L line (_root_.MIPStarRE.QPBT.lowDegreeEncoding h)).natDegree ≤ 1 := by
  classical
  cases line with
  | diagonal base seed direction baseFixed prefixZero =>
      simp [_root_.MIPStarRE.QPBT.LineDesc.kind] at haxis
  | axis base seed baseFixed =>
      refine (_root_.MIPStarRE.QPBT.polynomialOnLine_lowDegreeEncoding_natDegree_le_sum L _ h
        (fun i => if i = _root_.MIPStarRE.QPBT.chiIndex L seed then 1 else 0) ?_).trans ?_
      · intro i
        by_cases hij : i = _root_.MIPStarRE.QPBT.chiIndex L seed
        · rw [if_pos hij]
          exact natDegree_lineCoordinate_le L _ i
        · rw [if_neg hij]
          refine le_of_eq (natDegree_lineCoordinate_eq_zero L _ i ?_)
          change _root_.MIPStarRE.QPBT.coordinateDirection (_root_.MIPStarRE.QPBT.chiIndex L seed) i = 0
          simp [_root_.MIPStarRE.QPBT.coordinateDirection, hij]
      · simp
