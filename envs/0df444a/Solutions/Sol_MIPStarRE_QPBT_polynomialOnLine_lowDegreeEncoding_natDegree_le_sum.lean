-- Prove2me | solution 1 for MIPStarRE.QPBT.polynomialOnLine_lowDegreeEncoding_natDegree_le_sum
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:59:25.824767+00:00
-- url     : https://prove2.me/submissions/010c5f38-4c47-4399-9ee3-941ef53aa2ed

-- Generated proof for MIPStarRE.QPBT.polynomialOnLine_lowDegreeEncoding_natDegree_le_sum.
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
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCode
import Definitions.Def_QPBT_QPBT_Observables_LineDefs
import Definitions.Def_QPBT_QPBT_Observables_LineMeasurement_Restriction
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Mathlib

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace MIPStarRE.QPBT
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

theorem solution (L : _root_.MIPStarRE.QPBT.LdParams)
    (line : _root_.MIPStarRE.QPBT.LineDesc L) (h : _root_.MIPStarRE.QPBT.Cube L.m → _root_.MIPStarRE.QPBT.ScalarQ L) (bound : Fin L.m → ℕ)
    (hbound : ∀ i : Fin L.m,
      (_root_.Polynomial.C (line.base i) +
          _root_.Polynomial.X * _root_.Polynomial.C (line.direction i) :
          Polynomial (_root_.MIPStarRE.QPBT.ScalarQ L)).natDegree ≤ bound i) :
    (_root_.MIPStarRE.QPBT.polynomialOnLine L line (_root_.MIPStarRE.QPBT.lowDegreeEncoding h)).natDegree ≤
      ∑ i : Fin L.m, bound i := by
  classical
  unfold _root_.MIPStarRE.QPBT.polynomialOnLine _root_.MIPStarRE.QPBT.lowDegreeEncoding
  rw [map_sum]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ ?_
  intro y _
  rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval₂Hom_C]
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  unfold _root_.MIPStarRE.QPBT.indicatorPoly
  rw [map_prod]
  refine (Polynomial.natDegree_prod_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  by_cases hy : y i = true
  · rw [if_pos hy, MvPolynomial.eval₂Hom_X']
    exact hbound i
  · rw [if_neg hy, map_sub, map_one, MvPolynomial.eval₂Hom_X']
    refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ (hbound i))
    simp
