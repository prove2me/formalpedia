-- Prove2me | solution 1 for MIPStarRE.QPBT.evalCoefficient_restrictToAxisLine_lowDegreeEncoding
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-28T00:56:54.282087+00:00
-- url     : https://prove2.me/submissions/f6c96d9c-64d5-4365-8e46-34a6c4fc4afd

-- Generated proof for MIPStarRE.QPBT.evalCoefficient_restrictToAxisLine_lowDegreeEncoding.
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
import Definitions.Def_QPBT_QPBT_Algebra_Coefficients
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCode
import Definitions.Def_QPBT_QPBT_Observables_LineDefs
import Definitions.Def_QPBT_QPBT_Observables_LineMeasurement_Restriction
import Definitions.Def_QPBT_QPBT_Test_Completeness_HonestStrategy
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Mathlib
import Theorems.Thm_MIPStarRE_QPBT_eval_polynomialOnLine
import Theorems.Thm_MIPStarRE_QPBT_polynomialOnLine_lowDegreeEncoding_natDegree_le_one_of_axis

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/-!
# The honest Pauli basis measurements of the completeness proof

This module builds the measurements used by the honest strategy of
`lem:pauli-completeness`: the generalized Pauli basis measurement in a fixed
basis `W`, and its coarse-graining by the binary trace
`h ↦ tr(g_h(u_W) r_W)` which the source calls `A` (for `W = X`) and `B`
(for `W = Z`).  The main results are the observable identity

  `A_0 - A_1 = τ^W(ind_m(u_W) r_W)`

of `eq:finally-got-an-observable`, and the resulting commutation law

  `𝒪_A 𝒪_B = (-1)^γ 𝒪_B 𝒪_A`

with `γ` the phase bit `eq:gamma-value`.  When `γ ≠ 0` the two observables
anticommute, so `thm:ms-from-ac` produces the Magic Square part of the honest
strategy.

## References

The construction is the strategy displayed in the proof of
`lem:pauli-completeness`,
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1237-1360`;
blueprint `lem:pauli-completeness`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum



variable {K ι : Type*} [Field K] [Fintype K] [DecidableEq K] [Algebra (ZMod 2) K]
  [Fintype ι] [DecidableEq ι]

/-! ### The generalized Pauli basis measurement -/









/-! ### Symmetry and Hermiticity of the generalized Pauli observables -/



/-! ### Orthogonality of the generalized Pauli projectors

The generalized Pauli projectors in a fixed basis are pairwise orthogonal, so
every coarse-graining of a Pauli basis measurement is again projective.  This is
the projectivity used throughout the honest strategy of `lem:pauli-completeness`,
paper `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1364-1370`.
-/








/-! ### The honest Pair/W measurements

For an ambient question `ω = (u_X, u_Z, r_X, r_Z)` the honest player measures
the Pauli register in basis `W` and reports the binary trace
`tr(g_h(u_W) r_W)` of the resulting label.  These are the measurements `A` and
`B` of the proof of `lem:pauli-completeness`,
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1277-1286`.
-/

















/-! ### The honest Point/W measurements -/







/-! ### Honest line measurements -/

theorem solution
    (L : _root_.MIPStarRE.QPBT.LdParams) (line : _root_.MIPStarRE.QPBT.LineDesc L) (hline : line.kind = .axis)
    (h : _root_.MIPStarRE.QPBT.Cube L.m → _root_.MIPStarRE.QPBT.ScalarQ L) (t : _root_.MIPStarRE.QPBT.ScalarQ L) :
    _root_.MIPStarRE.QPBT.evalCoefficient (_root_.MIPStarRE.QPBT.restrictToAxisLine L line (_root_.MIPStarRE.QPBT.lowDegreeEncoding h)) t =
      MvPolynomial.eval (line.base + t • line.direction) (_root_.MIPStarRE.QPBT.lowDegreeEncoding h) := by
  calc
    _root_.MIPStarRE.QPBT.evalCoefficient (_root_.MIPStarRE.QPBT.restrictToAxisLine L line (_root_.MIPStarRE.QPBT.lowDegreeEncoding h)) t =
        Polynomial.eval t (_root_.MIPStarRE.QPBT.polynomialOnLine L line (_root_.MIPStarRE.QPBT.lowDegreeEncoding h)) := by
      unfold _root_.MIPStarRE.QPBT.evalCoefficient _root_.MIPStarRE.QPBT.restrictToAxisLine
      rw [Polynomial.eval_eq_sum_range'
        (Nat.lt_succ_of_le
          ((_root_.MIPStarRE.QPBT.polynomialOnLine_lowDegreeEncoding_natDegree_le_one_of_axis
            L line hline h).trans L.hd)) t]
      exact Fin.sum_univ_eq_sum_range
        (fun i => (_root_.MIPStarRE.QPBT.polynomialOnLine L line (_root_.MIPStarRE.QPBT.lowDegreeEncoding h)).coeff i * t ^ i)
        (L.d + 1)
    _ = _ := _root_.MIPStarRE.QPBT.eval_polynomialOnLine L line (_root_.MIPStarRE.QPBT.lowDegreeEncoding h) t
