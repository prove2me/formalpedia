-- Prove2me | solution 1 for MIPStarRE.QPBT.directCombinedExactLinearity_avg_le
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T21:15:21.779063+00:00
-- url     : https://prove2.me/submissions/3f0a87b8-ab30-451a-bbb8-b275bf7306ec

-- Generated proof for MIPStarRE.QPBT.directCombinedExactLinearity_avg_le.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Polynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_AvgCongr
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Game
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Combining_Coefficients
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Combining_Linearity
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Combining_Parameters
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Combining_Polynomial
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Combining_Restriction
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGameMeasurements
import Mathlib
import Theorems.Thm_MIPStarRE_QPBT_combinedCoefAlgHom_combinePolyTuple
import Theorems.Thm_MIPStarRE_QPBT_combinedRestrict_combiningLinearForm_avg_le
import Theorems.Thm_MIPStarRE_QPBT_degreeOf_combinedCoef_le

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
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





theorem combinedCoef_combinePolyTuple {K : Type*} [CommSemiring K] {m k : ℕ}
    (g : Fin k → MvPolynomial (Fin m) K) (r : Fin k) :
    _root_.MIPStarRE.QPBT.combinedCoef (_root_.MIPStarRE.QPBT.combinePolyTuple g) (Finsupp.single r 1) = g r := by
  classical
  rw [_root_.MIPStarRE.QPBT.combinedCoef, _root_.MIPStarRE.QPBT.combinedCoefAlgHom_combinePolyTuple, MvPolynomial.coeff_sum,
    Finset.sum_eq_single r]
  · simp
  · intro s _ hs
    rw [MvPolynomial.coeff_monomial, if_neg]
    exact fun hEq => hs (Finsupp.single_left_injective one_ne_zero hEq)
  · intro h
    exact absurd (Finset.mem_univ r) h





/-! ## The degree bound on the coefficients -/





/-- The coefficients of a polynomial of individual degree at most `d` lie in the
low individual degree class in the point variables. -/
theorem combinedCoef_mem_polyFunc {K : Type*} [CommSemiring K] {m k d : ℕ}
    {p : MvPolynomial (Fin (m + k)) K} (hp : p ∈ _root_.LIDT.MIPStarRE.LDT.Preliminaries.polyFunc (m + k) K d) (μ : Fin k →₀ ℕ) :
    _root_.MIPStarRE.QPBT.combinedCoef p μ ∈ _root_.LIDT.MIPStarRE.LDT.Preliminaries.polyFunc m K d :=
  _root_.MIPStarRE.QPBT.mem_polyFunc_of_degreeOf_le
    (_root_.MIPStarRE.QPBT.degreeOf_combinedCoef_le (_root_.LIDT.MIPStarRE.LDT.Preliminaries.degreeOf_le_of_mem_polyFunc hp) μ)

/-- The components of a combined polynomial of individual degree at most `d`
have individual degree at most `d`: they are among its coefficients. -/
theorem mem_polyFunc_of_combinePolyTuple {K : Type*} [CommSemiring K] {m k d : ℕ}
    {p : MvPolynomial (Fin (m + k)) K} (hp : p ∈ _root_.LIDT.MIPStarRE.LDT.Preliminaries.polyFunc (m + k) K d)
    {g : Fin k → MvPolynomial (Fin m) K} (hg : p = _root_.MIPStarRE.QPBT.combinePolyTuple g) (r : Fin k) :
    g r ∈ _root_.LIDT.MIPStarRE.LDT.Preliminaries.polyFunc m K d := by
  have h := _root_.MIPStarRE.QPBT.combinedCoef_mem_polyFunc hp (Finsupp.single r 1)
  rwa [hg, _root_.MIPStarRE.QPBT.combinedCoef_combinePolyTuple] at h



end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/DirectLowDegree/Transport/Combining/Parameters.lean. -/
/-!
# The combined parameters of the simultaneity reduction

The extension of the quantum soundness of the low individual degree test from
simultaneity parameter `1` to a general simultaneity parameter `k` applies the
case `k = 1` once, to a directly indexed low-degree game whose dimension is
`m + k` and whose simultaneity parameter is `1`.  This module records that
parameter map, the polynomial-tuple outcomes it carries, and the two maps
relating outcomes of the two games: the combining map, which sends a tuple of
`k` polynomials in `m` variables to the one-component tuple consisting of the
combined polynomial in `m + k` variables, and its total left inverse, which
returns the components of a combined polynomial and an arbitrary tuple
otherwise.

The field, the degree, and the admissibility of the field size are inherited
unchanged; only the dimension and the simultaneity parameter change.  The
degree is inherited because the combining map is linear in the fresh
coordinates, so it raises no individual degree above `d` when `1 ≤ d`; this is
where the individual-degree formulation differs from the total-degree
formulation of the source, which passes from degree `d` to degree `d + 1`.

## References

* `references/neexp-paper/05_quantum_preliminaries.tex:1409-1503`
* `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`
* `blueprint/src/chapter/ch13_qpbt_test.tex:240-250`
* `docs/paper-gaps/qpbt_ld-simultaneous-sandwich.tex`
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.LDT.Preliminaries

noncomputable section

/-! ## The combined parameter tuple -/













/-- The scalar field of a directly indexed low-degree game has `q` elements. -/
theorem card_directScalarQ (D : _root_.MIPStarRE.QPBT.DirectLdParams) :
    Fintype.card (_root_.MIPStarRE.QPBT.DirectScalarQ D) = D.q := by
  rw [Fintype.card_congr (_root_.MIPStarRE.QPBT.binaryRepresentation D.model), Fintype.card_fin]



/-! ## The combining map on game outcomes -/













/-! ## Recovering the polynomial tuple -/













end

end MIPStarRE.QPBT

/-!
# Exact linearity in the combining variables

The recovery step of the combining reduction needs to know that a polynomial in
the combined variables which is not the combined polynomial of any tuple only
rarely restricts to a linear form in the combining variables: writing
`p = ∑_μ c_μ α^μ` with coefficients `c_μ` in the point variables, the
polynomial `p` is combined exactly when `c_μ` vanishes for every exponent vector
`μ` outside the `k` standard basis vectors, and the restriction `p(u, ·)` is a
linear form exactly when `c_μ(u)` vanishes for every such `μ`.  Fixing one such
`μ` with `c_μ ≠ 0`, whose total degree is at most `m d`, the Schwartz--Zippel
lemma bounds the probability of `c_μ(u) = 0` by `m d / q`.

## Main statements

* `exists_eq_combiningLinearForm_iff` — a polynomial in the combining variables
  is a linear form exactly when its coefficients vanish off the standard basis
  vectors.
* `combinedRestrict_combiningLinearForm_avg_le` — `lem:ld-combining-exact-linearity`.
* `directCombinedExactLinearity_avg_le` — the same bound in the parameters of
  the directly indexed low-degree game.

## References

* `references/neexp-paper/05_quantum_preliminaries.tex:1440-1477`
* `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`
* `blueprint/src/chapter/ch13_qpbt_test.tex:575-600`
-/



open scoped BigOperators

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.LDT.Preliminaries



/-! ## Linear forms in terms of their coefficients -/









/-! ## The exact-linearity estimate -/

open scoped Classical in

theorem solution (D : _root_.MIPStarRE.QPBT.DirectLdParams)
    (p : _root_.MIPStarRE.QPBT.PolyIndex D.combined.m (_root_.MIPStarRE.QPBT.DirectScalarQ D) D.d) (hnc : ¬ _root_.MIPStarRE.QPBT.IsDirectCombined D p) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D))
        (fun u => if ∃ c : Fin D.k → _root_.MIPStarRE.QPBT.DirectScalarQ D,
          _root_.MIPStarRE.QPBT.combinedRestrict p.1 u = _root_.MIPStarRE.QPBT.combiningLinearForm c then (1 : _root_.LIDT.MIPStarRE.LDT.Error) else 0) ≤
      ((D.m * D.d : ℕ) : _root_.LIDT.MIPStarRE.LDT.Error) / D.q := by
  classical
  have hnc' : ∀ g : Fin D.k → MvPolynomial (Fin D.m) (_root_.MIPStarRE.QPBT.DirectScalarQ D),
      p.1 ≠ _root_.MIPStarRE.QPBT.combinePolyTuple g := by
    intro g hg
    refine hnc ⟨fun r => ⟨g r, _root_.MIPStarRE.QPBT.mem_polyFunc_of_combinePolyTuple p.2 hg r⟩, ?_⟩
    exact Subtype.ext hg.symm
  have hbound := _root_.MIPStarRE.QPBT.combinedRestrict_combiningLinearForm_avg_le (d := D.d) p.2 hnc'
  calc
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D))
        (fun u => if ∃ c : Fin D.k → _root_.MIPStarRE.QPBT.DirectScalarQ D,
          _root_.MIPStarRE.QPBT.combinedRestrict p.1 u = _root_.MIPStarRE.QPBT.combiningLinearForm c then (1 : _root_.LIDT.MIPStarRE.LDT.Error) else 0)
      ≤ ((((D.m * D.d : ℕ) : ℚ≥0) /
          Fintype.card (_root_.MIPStarRE.QPBT.DirectScalarQ D) : ℚ≥0) : _root_.LIDT.MIPStarRE.LDT.Error) := hbound
    _ = ((D.m * D.d : ℕ) : _root_.LIDT.MIPStarRE.LDT.Error) / D.q := by
        rw [_root_.MIPStarRE.QPBT.card_directScalarQ]
        push_cast
        ring
