-- Prove2me | solution 1 for MIPStarRE.QPBT.combinedCoefAlgHom_monomial
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T21:01:20.558411+00:00
-- url     : https://prove2.me/submissions/5b1d0273-48ec-4de4-984a-8d3c574884bc

-- Generated proof for MIPStarRE.QPBT.combinedCoefAlgHom_monomial.
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









/-- A product over the combined dimension splits into the product over the point
coordinates and the product over the combining coordinates. -/
private theorem prod_combinedVar_split {M : Type*} [CommMonoid M] {m k : ℕ}
    (f : Fin (m + k) → M) :
    ∏ i : Fin (m + k), f i =
      (∏ j : Fin m, f (_root_.MIPStarRE.QPBT.combinedPointVar m k j)) *
        ∏ r : Fin k, f (_root_.MIPStarRE.QPBT.combinedCoefficientVar m k r) := by
  rw [← Fintype.prod_equiv finSumFinEquiv (fun x => f (finSumFinEquiv x)) f fun _ => rfl,
    Fintype.prod_sum_type]
  rfl

/-! ## Rereading a polynomial in the combining variables -/











theorem combinedCoefAlgHom_C (K : Type*) [CommSemiring K] (m k : ℕ) (a : K) :
    _root_.MIPStarRE.QPBT.combinedCoefAlgHom K m k (MvPolynomial.C a) =
      MvPolynomial.C (MvPolynomial.C a) := by
  rw [_root_.MIPStarRE.QPBT.combinedCoefAlgHom, MvPolynomial.aeval_C]
  simp [MvPolynomial.algebraMap_eq]



/-! ## Injectivity of the rereading -/







/-! ## The coefficients -/





/-! ## Combined polynomials in terms of the coefficients -/











/-! ## The degree bound on the coefficients -/











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

theorem solution {K : Type*} [CommSemiring K] {m k : ℕ}
    (s : Fin (m + k) →₀ ℕ) (a : K) :
    _root_.MIPStarRE.QPBT.combinedCoefAlgHom K m k (MvPolynomial.monomial s a) =
      MvPolynomial.monomial (_root_.MIPStarRE.QPBT.combinedCoefExp s)
        (MvPolynomial.monomial (_root_.MIPStarRE.QPBT.combinedPointExp s) a) := by
  classical
  set A := MvPolynomial (Fin k) (MvPolynomial (Fin m) K)
  have hL : _root_.MIPStarRE.QPBT.combinedCoefAlgHom K m k (MvPolynomial.monomial s a) =
      MvPolynomial.C (MvPolynomial.C a) *
        ((∏ j : Fin m, (MvPolynomial.C (MvPolynomial.X j) : A) ^ s (_root_.MIPStarRE.QPBT.combinedPointVar m k j)) *
          ∏ r : Fin k, (MvPolynomial.X r : A) ^ s (_root_.MIPStarRE.QPBT.combinedCoefficientVar m k r)) := by
    rw [MvPolynomial.monomial_eq,
      Finsupp.prod_fintype _ _ fun _ => pow_zero _, map_mul, map_prod,
      _root_.MIPStarRE.QPBT.combinedCoefAlgHom_C]
    simp only [map_pow, _root_.MIPStarRE.QPBT.combinedCoefAlgHom_X]
    rw [prod_combinedVar_split (fun i => (_root_.MIPStarRE.QPBT.combinedCoefSubstitution K m k i) ^ s i)]
    simp
  have hR : MvPolynomial.monomial (_root_.MIPStarRE.QPBT.combinedCoefExp s)
        (MvPolynomial.monomial (_root_.MIPStarRE.QPBT.combinedPointExp s) a) =
      MvPolynomial.C (MvPolynomial.C a) *
        ((∏ j : Fin m, (MvPolynomial.C (MvPolynomial.X j) : A) ^ s (_root_.MIPStarRE.QPBT.combinedPointVar m k j)) *
          ∏ r : Fin k, (MvPolynomial.X r : A) ^ s (_root_.MIPStarRE.QPBT.combinedCoefficientVar m k r)) := by
    rw [MvPolynomial.monomial_eq (s := _root_.MIPStarRE.QPBT.combinedCoefExp s),
      Finsupp.prod_fintype _ _ fun _ => pow_zero _,
      MvPolynomial.monomial_eq (s := _root_.MIPStarRE.QPBT.combinedPointExp s),
      Finsupp.prod_fintype _ _ fun _ => pow_zero _, map_mul, map_prod]
    simp only [map_pow, _root_.MIPStarRE.QPBT.combinedPointExp_apply, _root_.MIPStarRE.QPBT.combinedCoefExp_apply]
    ring
  rw [hL, hR]
