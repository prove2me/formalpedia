-- Prove2me | solution 1 for MIPStarRE.QPBT.evalCoefficient_collision_card_le
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T20:54:55.152842+00:00
-- url     : https://prove2.me/submissions/3f144bb6-0103-4d8d-9ffd-6d4a4924f8c7

-- Generated proof for MIPStarRE.QPBT.evalCoefficient_collision_card_le.
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
import Mathlib

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

/-- The coefficient sum is the polynomial with coefficient `f i` in degree
`i.val` for `i : Fin (c + 1)` and zero coefficients in degrees greater than `c`. -/
theorem linePolynomialOfCoefficients_eq_ofFn {K : Type*} [Semiring K]
    [DecidableEq K] {c : ℕ} (f : Fin (c + 1) → K) :
    _root_.MIPStarRE.QPBT.linePolynomialOfCoefficients f = Polynomial.ofFn (c + 1) f := by
  simp only [_root_.MIPStarRE.QPBT.linePolynomialOfCoefficients, Polynomial.ofFn_eq_sum_monomial,
    Polynomial.C_mul_X_pow_eq_monomial]

/-- Distinct bounded coefficient vectors represent distinct polynomials. -/
theorem linePolynomialOfCoefficients_injective {K : Type*} [Semiring K] (c : ℕ) :
    Function.Injective (_root_.MIPStarRE.QPBT.linePolynomialOfCoefficients (K := K) (c := c)) := by
  classical
  intro first second heq
  exact Polynomial.injective_ofFn (c + 1)
    (by simpa only [_root_.MIPStarRE.QPBT.linePolynomialOfCoefficients_eq_ofFn] using heq)

/-- The polynomial of a bounded coefficient vector has degree at most `n`. -/
theorem linePolynomialOfCoefficients_natDegree_le {K : Type*} [Semiring K] {n : ℕ}
    (f : Fin (n + 1) → K) :
    (_root_.MIPStarRE.QPBT.linePolynomialOfCoefficients f).natDegree ≤ n := by
  classical
  rw [_root_.MIPStarRE.QPBT.linePolynomialOfCoefficients_eq_ofFn]
  exact Nat.lt_succ_iff.mp (Polynomial.ofFn_natDegree_lt (Nat.succ_pos n) f)



end MIPStarRE.QPBT

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



open scoped BigOperators

open MIPStarRE.QPBT

theorem solution {K : Type*} [CommRing K] [IsDomain K]
    [Fintype K] [DecidableEq K] {bound : ℕ}
    (first second : Fin (bound + 1) → K) (hne : first ≠ second) :
    (Finset.univ.filter fun param => _root_.MIPStarRE.QPBT.evalCoefficient first param =
      _root_.MIPStarRE.QPBT.evalCoefficient second param).card ≤ bound := by
  classical
  by_contra hcard
  have heq := Polynomial.eq_of_natDegree_lt_card_of_eval_eq'
    (_root_.MIPStarRE.QPBT.linePolynomialOfCoefficients first) (_root_.MIPStarRE.QPBT.linePolynomialOfCoefficients second)
    (Finset.univ.filter fun param => _root_.MIPStarRE.QPBT.evalCoefficient first param =
      _root_.MIPStarRE.QPBT.evalCoefficient second param)
    (fun param hparam => by
      simpa only [_root_.MIPStarRE.QPBT.linePolynomialOfCoefficients_eval] using (Finset.mem_filter.mp hparam).2)
    (lt_of_le_of_lt (max_le (_root_.MIPStarRE.QPBT.linePolynomialOfCoefficients_natDegree_le first)
      (_root_.MIPStarRE.QPBT.linePolynomialOfCoefficients_natDegree_le second)) (Nat.lt_of_not_ge hcard))
  exact hne (_root_.MIPStarRE.QPBT.linePolynomialOfCoefficients_injective bound heq)
