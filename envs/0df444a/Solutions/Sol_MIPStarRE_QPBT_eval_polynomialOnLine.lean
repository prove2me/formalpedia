-- Prove2me | solution 1 for MIPStarRE.QPBT.eval_polynomialOnLine
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:59:25.505187+00:00
-- url     : https://prove2.me/submissions/c8285a63-fb33-4f32-91db-c8187df3ac1f

-- Generated proof for MIPStarRE.QPBT.eval_polynomialOnLine.
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





















/-! ## Evaluation of the restriction along the line -/

theorem solution (L : _root_.MIPStarRE.QPBT.LdParams) (line : _root_.MIPStarRE.QPBT.LineDesc L)
    (g : MvPolynomial (Fin L.m) (_root_.MIPStarRE.QPBT.ScalarQ L)) (t : _root_.MIPStarRE.QPBT.ScalarQ L) :
    Polynomial.eval t (_root_.MIPStarRE.QPBT.polynomialOnLine L line g) =
      MvPolynomial.eval (line.base + t • line.direction) g := by
  unfold _root_.MIPStarRE.QPBT.polynomialOnLine
  rw [← Polynomial.coe_evalRingHom, MvPolynomial.coe_eval₂Hom,
    MvPolynomial.eval₂_comp_left]
  have h1 : (Polynomial.evalRingHom t).comp
      (Polynomial.C : _root_.MIPStarRE.QPBT.ScalarQ L →+* Polynomial (_root_.MIPStarRE.QPBT.ScalarQ L)) =
        RingHom.id (_root_.MIPStarRE.QPBT.ScalarQ L) := by
    ext a
    simp
  have h2 : ((Polynomial.evalRingHom t) ∘ fun i : Fin L.m =>
      (_root_.Polynomial.C (line.base i) +
        _root_.Polynomial.X * _root_.Polynomial.C (line.direction i) :
        Polynomial (_root_.MIPStarRE.QPBT.ScalarQ L))) = line.base + t • line.direction := by
    funext i
    simp only [Function.comp_apply, Polynomial.coe_evalRingHom,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_C, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [h1, h2]
  rfl
