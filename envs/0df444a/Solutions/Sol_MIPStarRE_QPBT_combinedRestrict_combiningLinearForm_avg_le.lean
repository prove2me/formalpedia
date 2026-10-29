-- Prove2me | solution 1 for MIPStarRE.QPBT.combinedRestrict_combiningLinearForm_avg_le
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T21:11:08.656726+00:00
-- url     : https://prove2.me/submissions/e5c06f9f-86e8-40c5-901c-33da4e63e7ce

-- Generated proof for MIPStarRE.QPBT.combinedRestrict_combiningLinearForm_avg_le.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
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
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Combining_Coefficients
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Combining_Linearity
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Combining_Polynomial
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Combining_Restriction
import Mathlib
import Theorems.Thm_MIPStarRE_QPBT_combinedCoefAlgHom_combinePolyTuple
import Theorems.Thm_MIPStarRE_QPBT_degreeOf_combinedCoef_le
import Theorems.Thm_MIPStarRE_QPBT_eq_sum_monomial_single
import Theorems.Thm_MIPStarRE_QPBT_polynomialAgreement_avg_eq_agreementProbability

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/DirectLowDegree/Transport/Combining/Restriction.lean. -/
/-!
# Restricting a polynomial in the combined variables to a point

The recovery step of the combining reduction reads a polynomial `p` in the
`m + k` combined variables as a polynomial in the `k` combining variables whose
coefficients are polynomials in the `m` point variables, and asks whether the
restriction `p(u, ·)` obtained by substituting a point `u` for the point
variables is a linear form in the combining variables.  This module introduces
that restriction and records its elementary properties: it computes the
combined polynomial of a tuple to the linear form of the tuple of values of the
tuple at the point, and, when it is a linear form, its coefficients are forced
to be the values at the point of the components recovered by the substitution
of `lem:ld-combining-split`.  Consequently a restriction which is a linear form
agrees with the restriction of the combined polynomial of those components,
which is the first half of `lem:ld-combining-exact-linearity`.

## Main statements

* `eval_combinedRestrict` — evaluating `p(u, ·)` at `α` evaluates `p` at the
  combined point with parts `u` and `α`.
* `combinedRestrict_combinePolyTuple` — the restriction of a combined
  polynomial is the linear form of the tuple of values of its components.
* `combinedRestrict_eq_of_eq_combiningLinearForm` — a restriction which is a
  linear form agrees with the restriction of the combined polynomial of the
  components of `p`.

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

/-! ## The two coordinate blocks -/

/-- Every coordinate of the combined dimension is either a point coordinate or
a combining coordinate. -/
theorem combinedVar_cases {m k : ℕ} (i : Fin (m + k)) :
    (∃ j : Fin m, i = _root_.MIPStarRE.QPBT.combinedPointVar m k j) ∨
      ∃ r : Fin k, i = _root_.MIPStarRE.QPBT.combinedCoefficientVar m k r := by
  rcases h : finSumFinEquiv.symm i with j | r
  · exact Or.inl ⟨j, by rw [_root_.MIPStarRE.QPBT.combinedPointVar, ← h, Equiv.apply_symm_apply]⟩
  · exact Or.inr ⟨r, by rw [_root_.MIPStarRE.QPBT.combinedCoefficientVar, ← h, Equiv.apply_symm_apply]⟩





/-! ## The restriction to a point -/



















end

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



theorem combinedCoefInv_combinedCoefAlgHom {K : Type*} [CommSemiring K] {m k : ℕ}
    (p : MvPolynomial (Fin (m + k)) K) :
    _root_.MIPStarRE.QPBT.combinedCoefInv K m k (_root_.MIPStarRE.QPBT.combinedCoefAlgHom K m k p) = p := by
  have h : (_root_.MIPStarRE.QPBT.combinedCoefInv K m k).comp
      ((_root_.MIPStarRE.QPBT.combinedCoefAlgHom K m k : MvPolynomial (Fin (m + k)) K →ₐ[K] _) :
        MvPolynomial (Fin (m + k)) K →+* _) = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [_root_.MIPStarRE.QPBT.combinedCoefInv]
    · intro i
      rcases _root_.MIPStarRE.QPBT.combinedVar_cases i with ⟨j, rfl⟩ | ⟨r, rfl⟩ <;>
        simp [_root_.MIPStarRE.QPBT.combinedCoefInv]
  exact RingHom.congr_fun h p

/-- The rereading is injective: a polynomial in the combined variables is
determined by its coefficients in the combining variables. -/
theorem combinedCoefAlgHom_injective {K : Type*} [CommSemiring K] {m k : ℕ} :
    Function.Injective (_root_.MIPStarRE.QPBT.combinedCoefAlgHom K m k) :=
  Function.LeftInverse.injective _root_.MIPStarRE.QPBT.combinedCoefInv_combinedCoefAlgHom

/-! ## The coefficients -/



/-- The value at `u` of the coefficient of `μ` is the coefficient of `μ` in the
restriction of `p` at `u`. -/
theorem eval_combinedCoef {K : Type*} [CommSemiring K] {m k : ℕ}
    (p : MvPolynomial (Fin (m + k)) K) (u : Fin m → K) (μ : Fin k →₀ ℕ) :
    MvPolynomial.eval u (_root_.MIPStarRE.QPBT.combinedCoef p μ) =
      (_root_.MIPStarRE.QPBT.combinedRestrict p u).coeff μ := by
  have h : (MvPolynomial.mapAlgHom (MvPolynomial.aeval u)).comp (_root_.MIPStarRE.QPBT.combinedCoefAlgHom K m k) =
      MvPolynomial.aeval (_root_.MIPStarRE.QPBT.combinedRestrictSubstitution k u) := by
    apply MvPolynomial.algHom_ext
    intro i
    rcases _root_.MIPStarRE.QPBT.combinedVar_cases i with ⟨j, rfl⟩ | ⟨r, rfl⟩ <;> simp
  have hp := AlgHom.congr_fun h p
  simp only [AlgHom.coe_comp, Function.comp_apply, MvPolynomial.mapAlgHom_apply] at hp
  rw [_root_.MIPStarRE.QPBT.combinedRestrict, ← hp, _root_.MIPStarRE.QPBT.combinedCoef, MvPolynomial.coeff_map]
  rfl

/-! ## Combined polynomials in terms of the coefficients -/







theorem combinedCoef_combinePolyTuple_eq_zero {K : Type*} [CommSemiring K] {m k : ℕ}
    (g : Fin k → MvPolynomial (Fin m) K) {μ : Fin k →₀ ℕ}
    (hμ : ∀ r : Fin k, μ ≠ Finsupp.single r 1) :
    _root_.MIPStarRE.QPBT.combinedCoef (_root_.MIPStarRE.QPBT.combinePolyTuple g) μ = 0 := by
  classical
  rw [_root_.MIPStarRE.QPBT.combinedCoef, _root_.MIPStarRE.QPBT.combinedCoefAlgHom_combinePolyTuple, MvPolynomial.coeff_sum]
  refine Finset.sum_eq_zero fun r _ => ?_
  rw [MvPolynomial.coeff_monomial, if_neg]
  exact fun hEq => hμ r hEq.symm

/-- A polynomial in the combined variables is combined exactly when its
coefficients vanish outside the `k` standard basis vectors.  This is the
first half of the characterisation used in `lem:ld-combining-exact-linearity`. -/
theorem combinePolyTuple_combinedCoef_iff {K : Type*} [CommSemiring K] {m k : ℕ}
    (p : MvPolynomial (Fin (m + k)) K) :
    (∃ g : Fin k → MvPolynomial (Fin m) K, p = _root_.MIPStarRE.QPBT.combinePolyTuple g) ↔
      ∀ μ : Fin k →₀ ℕ, (∀ r : Fin k, μ ≠ Finsupp.single r 1) → _root_.MIPStarRE.QPBT.combinedCoef p μ = 0 := by
  classical
  constructor
  · rintro ⟨g, rfl⟩ μ hμ
    exact _root_.MIPStarRE.QPBT.combinedCoef_combinePolyTuple_eq_zero g hμ
  · intro h
    refine ⟨fun r => _root_.MIPStarRE.QPBT.combinedCoef p (Finsupp.single r 1), _root_.MIPStarRE.QPBT.combinedCoefAlgHom_injective ?_⟩
    rw [_root_.MIPStarRE.QPBT.combinedCoefAlgHom_combinePolyTuple]
    exact _root_.MIPStarRE.QPBT.eq_sum_monomial_single (_root_.MIPStarRE.QPBT.combinedCoefAlgHom K m k p) h

/-! ## The degree bound on the coefficients -/









/-- The coefficients of a polynomial of individual degree at most `d` have total
degree at most `m d`, which is the bound the Schwartz--Zippel lemma is applied
to in `lem:ld-combining-exact-linearity`. -/
theorem totalDegree_combinedCoef_le {K : Type*} [CommSemiring K] {m k d : ℕ}
    {p : MvPolynomial (Fin (m + k)) K} (hp : p ∈ _root_.LIDT.MIPStarRE.LDT.Preliminaries.polyFunc (m + k) K d) (μ : Fin k →₀ ℕ) :
    (_root_.MIPStarRE.QPBT.combinedCoef p μ).totalDegree ≤ m * d :=
  _root_.LIDT.MIPStarRE.LDT.Preliminaries.totalDegree_le_mul_of_degreeOf_le
    (_root_.MIPStarRE.QPBT.degreeOf_combinedCoef_le (_root_.LIDT.MIPStarRE.LDT.Preliminaries.degreeOf_le_of_mem_polyFunc hp) μ)

end

end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/DirectLowDegree/Transport/Combining/ExactLinearity.lean. -/
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

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.LDT.Preliminaries

noncomputable section

/-! ## Linear forms in terms of their coefficients -/

/-- A linear form is the sum of its monomials at the standard basis vectors. -/
theorem combiningLinearForm_eq_sum_monomial {K : Type*} [CommSemiring K] {k : ℕ}
    (c : Fin k → K) :
    _root_.MIPStarRE.QPBT.combiningLinearForm c =
      ∑ r : Fin k, MvPolynomial.monomial (Finsupp.single r 1) (c r) := by
  simp only [_root_.MIPStarRE.QPBT.combiningLinearForm]
  exact Finset.sum_congr rfl fun r _ => MvPolynomial.C_mul_X_eq_monomial

/-- The coefficients of a linear form vanish outside the standard basis
vectors. -/
theorem coeff_combiningLinearForm_eq_zero {K : Type*} [CommSemiring K] {k : ℕ}
    (c : Fin k → K) {μ : Fin k →₀ ℕ} (hμ : ∀ r : Fin k, μ ≠ Finsupp.single r 1) :
    (_root_.MIPStarRE.QPBT.combiningLinearForm c).coeff μ = 0 := by
  classical
  rw [_root_.MIPStarRE.QPBT.combiningLinearForm_eq_sum_monomial, MvPolynomial.coeff_sum]
  refine Finset.sum_eq_zero fun r _ => ?_
  rw [MvPolynomial.coeff_monomial, if_neg]
  exact fun hEq => hμ r hEq.symm

/-- A polynomial in the combining variables is a linear form exactly when its
coefficients vanish outside the `k` standard basis vectors. -/
theorem exists_eq_combiningLinearForm_iff {K : Type*} [CommSemiring K] {k : ℕ}
    (P : MvPolynomial (Fin k) K) :
    (∃ c : Fin k → K, P = _root_.MIPStarRE.QPBT.combiningLinearForm c) ↔
      ∀ μ : Fin k →₀ ℕ, (∀ r : Fin k, μ ≠ Finsupp.single r 1) →
        P.coeff μ = 0 := by
  classical
  constructor
  · rintro ⟨c, rfl⟩ μ hμ
    exact _root_.MIPStarRE.QPBT.coeff_combiningLinearForm_eq_zero c hμ
  · intro h
    refine ⟨fun r => P.coeff (Finsupp.single r 1), ?_⟩
    rw [_root_.MIPStarRE.QPBT.combiningLinearForm_eq_sum_monomial]
    exact _root_.MIPStarRE.QPBT.eq_sum_monomial_single P h

/-- The restriction of `p` at `u` is a linear form exactly when the values at
`u` of the coefficients off the standard basis vectors all vanish. -/
theorem exists_eq_combiningLinearForm_combinedRestrict_iff {K : Type*} [CommSemiring K]
    {m k : ℕ} (p : MvPolynomial (Fin (m + k)) K) (u : Fin m → K) :
    (∃ c : Fin k → K, _root_.MIPStarRE.QPBT.combinedRestrict p u = _root_.MIPStarRE.QPBT.combiningLinearForm c) ↔
      ∀ μ : Fin k →₀ ℕ, (∀ r : Fin k, μ ≠ Finsupp.single r 1) →
        MvPolynomial.eval u (_root_.MIPStarRE.QPBT.combinedCoef p μ) = 0 := by
  rw [_root_.MIPStarRE.QPBT.exists_eq_combiningLinearForm_iff]
  simp only [_root_.MIPStarRE.QPBT.eval_combinedCoef]

/-! ## The exact-linearity estimate -/





/-! ## The collision estimate at a fixed point -/









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

theorem solution {K : Type*} [Field K] [Fintype K]
    [DecidableEq K] {m k d : ℕ} {p : MvPolynomial (Fin (m + k)) K}
    (hp : p ∈ _root_.LIDT.MIPStarRE.LDT.Preliminaries.polyFunc (m + k) K d)
    (hnc : ∀ g : Fin k → MvPolynomial (Fin m) K, p ≠ _root_.MIPStarRE.QPBT.combinePolyTuple g) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin m → K))
        (fun u => if ∃ c : Fin k → K, _root_.MIPStarRE.QPBT.combinedRestrict p u = _root_.MIPStarRE.QPBT.combiningLinearForm c then
          (1 : _root_.LIDT.MIPStarRE.LDT.Error) else 0) ≤
      ((((m * d : ℕ) : ℚ≥0) / Fintype.card K : ℚ≥0) : _root_.LIDT.MIPStarRE.LDT.Error) := by
  classical
  obtain ⟨μ, hμ, hne⟩ : ∃ μ : Fin k →₀ ℕ, (∀ r : Fin k, μ ≠ Finsupp.single r 1) ∧
      _root_.MIPStarRE.QPBT.combinedCoef p μ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨g, hg⟩ := (_root_.MIPStarRE.QPBT.combinePolyTuple_combinedCoef_iff p).mpr hcon
    exact hnc g hg
  calc
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin m → K))
        (fun u => if ∃ c : Fin k → K, _root_.MIPStarRE.QPBT.combinedRestrict p u = _root_.MIPStarRE.QPBT.combiningLinearForm c then
          (1 : _root_.LIDT.MIPStarRE.LDT.Error) else 0)
      ≤ _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin m → K))
          (fun u => if MvPolynomial.eval u (_root_.MIPStarRE.QPBT.combinedCoef p μ) =
            MvPolynomial.eval u (0 : MvPolynomial (Fin m) K) then (1 : _root_.LIDT.MIPStarRE.LDT.Error) else 0) := by
        refine _root_.LIDT.MIPStarRE.LDT.avgOver_mono _ _ _ fun u => ?_
        by_cases hu : ∃ c : Fin k → K, _root_.MIPStarRE.QPBT.combinedRestrict p u = _root_.MIPStarRE.QPBT.combiningLinearForm c
        · have h0 : MvPolynomial.eval u (_root_.MIPStarRE.QPBT.combinedCoef p μ) =
              MvPolynomial.eval u (0 : MvPolynomial (Fin m) K) := by
            rw [map_zero]
            exact (_root_.MIPStarRE.QPBT.exists_eq_combiningLinearForm_combinedRestrict_iff p u).mp hu μ hμ
          rw [if_pos hu, if_pos h0]
        · rw [if_neg hu]
          split_ifs <;> norm_num
    _ = (_root_.LIDT.MIPStarRE.LDT.Preliminaries.polynomialAgreementProbability m K (_root_.MIPStarRE.QPBT.combinedCoef p μ) 0 : _root_.LIDT.MIPStarRE.LDT.Error) :=
        _root_.MIPStarRE.QPBT.polynomialAgreement_avg_eq_agreementProbability _ _
    _ ≤ ((((m * d : ℕ) : ℚ≥0) / Fintype.card K : ℚ≥0) : _root_.LIDT.MIPStarRE.LDT.Error) := by
        have hdeg : (_root_.MIPStarRE.QPBT.combinedCoef p μ).totalDegree ≤ m * d :=
          _root_.MIPStarRE.QPBT.totalDegree_combinedCoef_le hp μ
        have hzero : (0 : MvPolynomial (Fin m) K).totalDegree ≤ m * d := by
          simp
        exact_mod_cast _root_.LIDT.MIPStarRE.LDT.Preliminaries.schwartzZippel_totalDegree hne hdeg hzero
