-- Prove2me | solution 1 for MIPStarRE.QPBT.eq_sum_monomial_single
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T21:01:20.524053+00:00
-- url     : https://prove2.me/submissions/1c52a747-0b78-472d-9e2a-fc78e83b6e58

-- Generated proof for MIPStarRE.QPBT.eq_sum_monomial_single.
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
import Mathlib

namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries
namespace MIPStarRE.QPBT
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

theorem solution {B : Type*} [CommSemiring B] {k : ℕ}
    (q : MvPolynomial (Fin k) B)
    (h : ∀ μ : Fin k →₀ ℕ, (∀ r : Fin k, μ ≠ Finsupp.single r 1) →
      q.coeff μ = 0) :
    q = ∑ r : Fin k, MvPolynomial.monomial (Finsupp.single r 1)
      (q.coeff (Finsupp.single r 1)) := by
  classical
  have hsub : q.support ⊆ Finset.image (fun r : Fin k => Finsupp.single r 1) Finset.univ := by
    intro μ hμ
    by_contra hcon
    refine MvPolynomial.mem_support_iff.mp hμ (h μ fun r hr => hcon ?_)
    exact Finset.mem_image.mpr ⟨r, Finset.mem_univ r, hr.symm⟩
  conv_lhs => rw [q.as_sum]
  rw [Finset.sum_subset hsub, Finset.sum_image]
  · intro r _ r' _ hrr'
    exact Finsupp.single_left_injective one_ne_zero hrr'
  · intro μ _ hμ
    rw [MvPolynomial.notMem_support_iff.mp hμ, map_zero]
