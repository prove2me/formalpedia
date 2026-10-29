-- Prove2me | solution 1 for MIPStarRE.QPBT.combineLinePoly_spec
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T21:01:20.036989+00:00
-- url     : https://prove2.me/submissions/fd429d88-99ed-4e23-8d2d-5efa8efe0c02

-- Generated proof for MIPStarRE.QPBT.combineLinePoly_spec.
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
import Definitions.Def_QPBT_QPBT_Combining_Defs
import Mathlib
import Theorems.Thm_MIPStarRE_QPBT_combineLinePolynomial_natDegree_le

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/- Source helpers from QPBT/Algebra/Coefficients.lean. -/
/-!
# Coefficient polynomials and finite-field collision bounds

This module supplies the coefficient evaluation and polynomial representation
shared by the low-degree games and the combining argument. Distinct bounded
coefficient vectors agree at no more parameters than their degree bound.

## References

- Blueprint `def:ld-win-predicate` and `lem:coefficient-polynomial-agreement`.
- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:331-344`.
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:950-955`.

Note: this module contributes declarations to the comparator statement closure
of the QPBT headline theorems, which must elaborate in the same environment as
the Mathlib-only `ChallengeQPBT.lean`.  Keep the full `import Mathlib`; do not
narrow it.  See `docs/comparator.md`, "Environment alignment".
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT







/-- Evaluating the polynomial represented by a coefficient list agrees with
`evalCoefficient`. -/
theorem linePolynomialOfCoefficients_eval {K : Type*} [Semiring K]
    {c : ℕ} (f : Fin (c + 1) → K) (t : K) :
    (_root_.MIPStarRE.QPBT.linePolynomialOfCoefficients f).eval t = _root_.MIPStarRE.QPBT.evalCoefficient f t := by
  change Polynomial.eval t
      (∑ i ∈ Finset.univ, Polynomial.C (f i) * Polynomial.X ^ i.val) =
    ∑ i ∈ Finset.univ, f i * t ^ i.val
  rw [Polynomial.eval_finsetSum]
  simp









end MIPStarRE.QPBT

/-!
# Polynomial combination and restricted line distributions

This file contains the concrete definitions at the foundation of the
Chapter 15 combining argument.  A pair of bounded individual-degree
polynomials is embedded into the two coordinate blocks of an extended
polynomial.  On lines, explicit affine reparameterizations are composed with
coefficient-list polynomials.  The original-dimensional restricted line laws
are formed before decoding, while their field seed is still present.

## References

The combining map is blueprint
`def:combine-map`, with paper origin
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:970-989`.
The restricted laws are blueprint `def:ith-restricted-line`,
with paper origin in the same source at lines 1038--1048.
-/



open scoped BigOperators

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.LDT.Preliminaries

theorem solution {K : Type*} [Field K] {m c : ℕ}
    (u v : Fin (2 * m + 2) → K) (uX vX uZ vZ : Fin m → K)
    (aX bX aZ bZ uα vα uβ vβ : K) (f g : Fin (c + 1) → K)
    (hcompat : _root_.MIPStarRE.QPBT.IsCombineLineCompatible u v uX vX uZ vZ
      aX bX aZ bZ uα vα uβ vβ) :
    ∀ t : K,
      _root_.MIPStarRE.QPBT.projX (u + t • v) = uX + (aX + bX * t) • vX ∧
      _root_.MIPStarRE.QPBT.projZ (u + t • v) = uZ + (aZ + bZ * t) • vZ ∧
      _root_.MIPStarRE.QPBT.evalCoefficient
          (_root_.MIPStarRE.QPBT.combineLinePoly aX bX aZ bZ uα vα uβ vβ f g) t =
        (uα + t * vα) * _root_.MIPStarRE.QPBT.evalCoefficient f (aX + bX * t) +
          (uβ + t * vβ) * _root_.MIPStarRE.QPBT.evalCoefficient g (aZ + bZ * t) := by
  intro t
  obtain ⟨-, -, -, -, hlines⟩ := hcompat
  refine ⟨(hlines t).1, (hlines t).2, ?_⟩
  have hdeg := _root_.MIPStarRE.QPBT.combineLinePolynomial_natDegree_le aX bX aZ bZ uα vα uβ vβ f g
  have heval :
      _root_.MIPStarRE.QPBT.evalCoefficient (_root_.MIPStarRE.QPBT.combineLinePoly aX bX aZ bZ uα vα uβ vβ f g) t =
        (_root_.MIPStarRE.QPBT.combineLinePolynomial aX bX aZ bZ uα vα uβ vβ f g).eval t := by
    rw [Polynomial.eval_eq_sum_range' (n := c + 1 + 1) (by omega) t]
    simp only [_root_.MIPStarRE.QPBT.evalCoefficient, _root_.MIPStarRE.QPBT.combineLinePoly]
    exact Fin.sum_univ_eq_sum_range
      (fun k =>
        (_root_.MIPStarRE.QPBT.combineLinePolynomial aX bX aZ bZ uα vα uβ vβ f g).coeff k * t ^ k)
      (c + 1 + 1)
  rw [heval, _root_.MIPStarRE.QPBT.combineLinePolynomial]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_comp, _root_.MIPStarRE.QPBT.linePolynomialOfCoefficients_eval]
  ring
