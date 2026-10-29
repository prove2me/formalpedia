-- Prove2me | solution 1 for MIPStarRE.QPBT.combineLinePolynomial_natDegree_le
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T20:57:53.979556+00:00
-- url     : https://prove2.me/submissions/4b2fc18c-0735-4e50-9b32-465cf683e747

-- Generated proof for MIPStarRE.QPBT.combineLinePolynomial_natDegree_le.
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









/-- The coefficient sum is the polynomial with coefficient `f i` in degree
`i.val` for `i : Fin (c + 1)` and zero coefficients in degrees greater than `c`. -/
theorem linePolynomialOfCoefficients_eq_ofFn {K : Type*} [Semiring K]
    [DecidableEq K] {c : ℕ} (f : Fin (c + 1) → K) :
    _root_.MIPStarRE.QPBT.linePolynomialOfCoefficients f = Polynomial.ofFn (c + 1) f := by
  simp only [_root_.MIPStarRE.QPBT.linePolynomialOfCoefficients, Polynomial.ofFn_eq_sum_monomial,
    Polynomial.C_mul_X_pow_eq_monomial]



/-- The polynomial of a bounded coefficient vector has degree at most `n`. -/
theorem linePolynomialOfCoefficients_natDegree_le {K : Type*} [Semiring K] {n : ℕ}
    (f : Fin (n + 1) → K) :
    (_root_.MIPStarRE.QPBT.linePolynomialOfCoefficients f).natDegree ≤ n := by
  classical
  rw [_root_.MIPStarRE.QPBT.linePolynomialOfCoefficients_eq_ofFn]
  exact Nat.lt_succ_iff.mp (Polynomial.ofFn_natDegree_lt (Nat.succ_pos n) f)



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

theorem solution {K : Type*} [CommSemiring K] {c : ℕ}
    (aX bX aZ bZ uα vα uβ vβ : K) (f g : Fin (c + 1) → K) :
    (_root_.MIPStarRE.QPBT.combineLinePolynomial aX bX aZ bZ uα vα uβ vβ f g).natDegree ≤ c + 1 := by
  have affineDegree : ∀ u v : K,
      (Polynomial.C u + Polynomial.C v * Polynomial.X).natDegree ≤ 1 := by
    intro u v
    refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
    · simp [Polynomial.natDegree_C]
    · refine Polynomial.natDegree_mul_le.trans ?_
      rw [Polynomial.natDegree_C]
      simpa using Polynomial.natDegree_X_le (R := K)
  have summandDegree : ∀ (a b u v : K) (h : Fin (c + 1) → K),
      ((Polynomial.C u + Polynomial.C v * Polynomial.X) *
        (_root_.MIPStarRE.QPBT.linePolynomialOfCoefficients h).comp
          (Polynomial.C a + Polynomial.C b * Polynomial.X)).natDegree ≤ c + 1 := by
    intro a b u v h
    refine Polynomial.natDegree_mul_le.trans ?_
    have hfactor := affineDegree u v
    have hcomp : ((_root_.MIPStarRE.QPBT.linePolynomialOfCoefficients h).comp
        (Polynomial.C a + Polynomial.C b * Polynomial.X)).natDegree ≤ c := by
      refine Polynomial.natDegree_comp_le.trans ?_
      calc
        (_root_.MIPStarRE.QPBT.linePolynomialOfCoefficients h).natDegree *
              (Polynomial.C a + Polynomial.C b * Polynomial.X).natDegree ≤ c * 1 :=
          Nat.mul_le_mul (_root_.MIPStarRE.QPBT.linePolynomialOfCoefficients_natDegree_le h) (affineDegree a b)
        _ = c := by ring
    omega
  exact (Polynomial.natDegree_add_le _ _).trans
    (max_le (summandDegree aX bX uα vα f) (summandDegree aZ bZ uβ vβ g))
