-- Prove2me | solution 1 for MIPStarRE.QPBT.degreeOf_combinedCoef_le
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T21:06:23.936233+00:00
-- url     : https://prove2.me/submissions/45f12c69-bedc-408e-be1f-4e5af3665619

-- Generated proof for MIPStarRE.QPBT.degreeOf_combinedCoef_le.
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
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Combining_Coefficients
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Combining_Polynomial
import Mathlib
import Theorems.Thm_MIPStarRE_QPBT_combinedCoefAlgHom_monomial

namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/DirectLowDegree/Transport/Combining/Coefficients.lean. -/
/-!
# The coefficients of a polynomial in the combining variables

The recovery step of the combining reduction reads a polynomial `p` in the
`m + k` combined variables as a polynomial in the `k` combining variables whose
coefficients `c_μ` are polynomials in the `m` point variables, and characterises
the two properties it needs in terms of those coefficients: `p` is the combined
polynomial of a tuple exactly when `c_μ` vanishes for every exponent vector `μ`
outside the `k` standard basis vectors, and the restriction `p(u, ·)` is a
linear form exactly when `c_μ(u)` vanishes for every such `μ`.  The
individual degrees of the coefficients are bounded by those of `p`, so each
`c_μ` has total degree at most `m d` and the Schwartz--Zippel lemma applies to
it.

The rereading is the algebra homomorphism sending the point variables to
constants and keeping the combining variables; it is injective, its left
inverse being the substitution which renames the point variables back and sends
the combining variables to the combining coordinates.

## Main definitions

* `combinedPointExp`, `combinedCoefExp` — the two blocks of an exponent vector
  of the combined dimension.
* `combinedCoefAlgHom` — the rereading of a polynomial in the combined
  variables as a polynomial in the combining variables with polynomial
  coefficients.
* `combinedCoef` — the coefficient of the combining monomial `μ`.

## Main statements

* `combinedCoefAlgHom_monomial` — the rereading of a monomial.
* `combinedCoefAlgHom_injective` — the rereading is injective.
* `eval_combinedCoef` — the value at `u` of `c_μ` is the coefficient of `μ` in
  the restriction `p(u, ·)`.
* `combinePolyTuple_combinedCoef_iff` — `p` is combined exactly when `c_μ`
  vanishes off the standard basis vectors.
* `degreeOf_combinedCoef_le`, `totalDegree_combinedCoef_le` — the degree bounds.

## References

* `references/neexp-paper/05_quantum_preliminaries.tex:1440-1470`
* `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`
* `blueprint/src/chapter/ch13_qpbt_test.tex:575-600`
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT.Preliminaries

noncomputable section

/-! ## The two blocks of an exponent vector -/











/-! ## Rereading a polynomial in the combining variables -/















/-! ## Injectivity of the rereading -/







/-! ## The coefficients -/





/-! ## Combined polynomials in terms of the coefficients -/











/-! ## The degree bound on the coefficients -/

/-- The coefficient of `μ` as a sum over the support of `p`. -/
theorem combinedCoef_eq_sum {K : Type*} [CommSemiring K] {m k : ℕ}
    (p : MvPolynomial (Fin (m + k)) K) (μ : Fin k →₀ ℕ) :
    _root_.MIPStarRE.QPBT.combinedCoef p μ = ∑ s ∈ p.support,
      (if _root_.MIPStarRE.QPBT.combinedCoefExp s = μ then
        MvPolynomial.monomial (_root_.MIPStarRE.QPBT.combinedPointExp s) (p.coeff s) else 0) := by
  classical
  rw [_root_.MIPStarRE.QPBT.combinedCoef]
  conv_lhs => rw [p.as_sum]
  rw [map_sum, MvPolynomial.coeff_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [_root_.MIPStarRE.QPBT.combinedCoefAlgHom_monomial, MvPolynomial.coeff_monomial]









end

end MIPStarRE.QPBT

/-!
# The coefficients of a polynomial in the combining variables

The recovery step of the combining reduction reads a polynomial `p` in the
`m + k` combined variables as a polynomial in the `k` combining variables whose
coefficients `c_μ` are polynomials in the `m` point variables, and characterises
the two properties it needs in terms of those coefficients: `p` is the combined
polynomial of a tuple exactly when `c_μ` vanishes for every exponent vector `μ`
outside the `k` standard basis vectors, and the restriction `p(u, ·)` is a
linear form exactly when `c_μ(u)` vanishes for every such `μ`.  The
individual degrees of the coefficients are bounded by those of `p`, so each
`c_μ` has total degree at most `m d` and the Schwartz--Zippel lemma applies to
it.

The rereading is the algebra homomorphism sending the point variables to
constants and keeping the combining variables; it is injective, its left
inverse being the substitution which renames the point variables back and sends
the combining variables to the combining coordinates.

## Main definitions

* `combinedPointExp`, `combinedCoefExp` — the two blocks of an exponent vector
  of the combined dimension.
* `combinedCoefAlgHom` — the rereading of a polynomial in the combined
  variables as a polynomial in the combining variables with polynomial
  coefficients.
* `combinedCoef` — the coefficient of the combining monomial `μ`.

## Main statements

* `combinedCoefAlgHom_monomial` — the rereading of a monomial.
* `combinedCoefAlgHom_injective` — the rereading is injective.
* `eval_combinedCoef` — the value at `u` of `c_μ` is the coefficient of `μ` in
  the restriction `p(u, ·)`.
* `combinePolyTuple_combinedCoef_iff` — `p` is combined exactly when `c_μ`
  vanishes off the standard basis vectors.
* `degreeOf_combinedCoef_le`, `totalDegree_combinedCoef_le` — the degree bounds.

## References

* `references/neexp-paper/05_quantum_preliminaries.tex:1440-1470`
* `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`
* `blueprint/src/chapter/ch13_qpbt_test.tex:575-600`
-/



open scoped BigOperators

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT.Preliminaries



/-! ## The two blocks of an exponent vector -/











/-! ## Rereading a polynomial in the combining variables -/















/-! ## Injectivity of the rereading -/







/-! ## The coefficients -/





/-! ## Combined polynomials in terms of the coefficients -/











/-! ## The degree bound on the coefficients -/

theorem solution {K : Type*} [CommSemiring K] {m k d : ℕ}
    {p : MvPolynomial (Fin (m + k)) K} (hp : ∀ i, p.degreeOf i ≤ d)
    (μ : Fin k →₀ ℕ) (j : Fin m) : (_root_.MIPStarRE.QPBT.combinedCoef p μ).degreeOf j ≤ d := by
  classical
  rw [MvPolynomial.degreeOf_le_iff]
  intro ν hν
  rw [_root_.MIPStarRE.QPBT.combinedCoef_eq_sum] at hν
  obtain ⟨s, hs, hνs⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hν)
  by_cases hc : _root_.MIPStarRE.QPBT.combinedCoefExp s = μ
  · rw [if_pos hc] at hνs
    have hνeq : ν = _root_.MIPStarRE.QPBT.combinedPointExp s := by
      have := MvPolynomial.support_monomial_subset hνs
      simpa using this
    subst hνeq
    exact MvPolynomial.degreeOf_le_iff.mp (hp (_root_.MIPStarRE.QPBT.combinedPointVar m k j)) s hs
  · rw [if_neg hc] at hνs
    simp at hνs
