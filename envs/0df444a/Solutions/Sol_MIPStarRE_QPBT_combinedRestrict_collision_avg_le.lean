-- Prove2me | solution 1 for MIPStarRE.QPBT.combinedRestrict_collision_avg_le
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T21:11:08.400084+00:00
-- url     : https://prove2.me/submissions/155651a8-7860-4a34-b669-e7d54e725945

-- Generated proof for MIPStarRE.QPBT.combinedRestrict_collision_avg_le.
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
import Theorems.Thm_MIPStarRE_QPBT_combinedCoefAlgHom_monomial
import Theorems.Thm_MIPStarRE_QPBT_polynomialAgreement_avg_eq_agreementProbability

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/DirectLowDegree/Transport/Combining/Linearity.lean. -/
/-!
# The linear form in the combining variables and its collision estimate

At a fixed point `u` of the original space, the combined polynomial of a tuple
`g` restricts, as a function of the combining variables `α`, to the linear form
`α ↦ ∑_{r < k} g_r(u) α_r`.  The recovery step of the reduction compares two
such linear forms: if the tuple of values `(g_0(u), …, g_{k-1}(u))` differs from
a tuple `b` of answers, then the two linear forms are distinct polynomials of
total degree at most one, so by the Schwartz--Zippel lemma they agree at a
uniformly sampled `α` with probability at most `1/q`.

This module proves that estimate.  It is the quantitative content of the last
paragraph of the source proof, where the same bound is obtained for the
combining map of the surface game.

## Main statements

* `combiningLinearForm_injective` — a linear form determines its coefficients.
* `combiningLinearForm_agreementProbability_le` — the Schwartz--Zippel bound.
* `directCombiningCollision_avg_le` — the bound in the averaged form used by the
  consistency calculus of the directly indexed game.

## References

* `references/neexp-paper/05_quantum_preliminaries.tex:1484-1503`
* `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`
* `blueprint/src/chapter/ch13_qpbt_test.tex:240-250`
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.LDT.Preliminaries

noncomputable section

/-! ## The linear form of a tuple of scalars -/





/-- A linear form has total degree at most one. -/
theorem combiningLinearForm_totalDegree_le_one {K : Type*} [CommSemiring K]
    [Nontrivial K] {k : ℕ} (c : Fin k → K) :
    (_root_.MIPStarRE.QPBT.combiningLinearForm c).totalDegree ≤ 1 := by
  refine le_trans (MvPolynomial.totalDegree_finsetSum _ _) (Finset.sup_le fun r _ => ?_)
  refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
  simp [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X]







/-! ## The averaged form -/





end

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









/-- Evaluating the restriction of `p` at `u` at a combining vector `α`
evaluates `p` at the combined point with parts `u` and `α`. -/
theorem eval_combinedRestrict {K : Type*} [CommSemiring K] {m k : ℕ}
    (p : MvPolynomial (Fin (m + k)) K) (u : Fin m → K) (α : Fin k → K) :
    MvPolynomial.eval α (_root_.MIPStarRE.QPBT.combinedRestrict p u) =
      MvPolynomial.eval (_root_.MIPStarRE.QPBT.combinedPoint u α) p := by
  have hcomp : (MvPolynomial.aeval (R := K) α).comp
        (MvPolynomial.aeval (_root_.MIPStarRE.QPBT.combinedRestrictSubstitution k u)) =
      MvPolynomial.aeval (_root_.MIPStarRE.QPBT.combinedPoint u α) := by
    apply MvPolynomial.algHom_ext
    intro i
    rcases _root_.MIPStarRE.QPBT.combinedVar_cases i with ⟨j, rfl⟩ | ⟨r, rfl⟩ <;> simp
  show MvPolynomial.aeval α (MvPolynomial.aeval (_root_.MIPStarRE.QPBT.combinedRestrictSubstitution k u) p) = _
  rw [← AlgHom.comp_apply, hcomp]
  rfl









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









/-! ## The exact-linearity estimate -/





/-! ## The collision estimate at a fixed point -/

/-- A nonzero coefficient of `μ` comes from a monomial of `p` whose combining
block is `μ`. -/
theorem exists_mem_support_of_combinedCoef_ne_zero {K : Type*} [CommSemiring K] {m k : ℕ}
    {p : MvPolynomial (Fin (m + k)) K} {μ : Fin k →₀ ℕ} (h : _root_.MIPStarRE.QPBT.combinedCoef p μ ≠ 0) :
    ∃ s ∈ p.support, _root_.MIPStarRE.QPBT.combinedCoefExp s = μ := by
  classical
  by_contra hcon
  push Not at hcon
  refine h ?_
  rw [_root_.MIPStarRE.QPBT.combinedCoef_eq_sum]
  exact Finset.sum_eq_zero fun s hs => if_neg (hcon s hs)

/-- The restriction of `p` to a point inherits the individual-degree bound of
`p` in the combining variables. -/
theorem degreeOf_combinedRestrict_le {K : Type*} [CommSemiring K] {m k d : ℕ}
    {p : MvPolynomial (Fin (m + k)) K} (hp : ∀ i, p.degreeOf i ≤ d) (u : Fin m → K)
    (r : Fin k) : (_root_.MIPStarRE.QPBT.combinedRestrict p u).degreeOf r ≤ d := by
  classical
  rw [MvPolynomial.degreeOf_le_iff]
  intro μ hμ
  have hne : _root_.MIPStarRE.QPBT.combinedCoef p μ ≠ 0 := by
    intro h0
    refine MvPolynomial.mem_support_iff.mp hμ ?_
    rw [← _root_.MIPStarRE.QPBT.eval_combinedCoef, h0, map_zero]
  obtain ⟨s, hs, rfl⟩ := _root_.MIPStarRE.QPBT.exists_mem_support_of_combinedCoef_ne_zero hne
  exact MvPolynomial.degreeOf_le_iff.mp (hp (_root_.MIPStarRE.QPBT.combinedCoefficientVar m k r)) s hs

/-- The restriction of a polynomial of individual degree at most `d` to a point
has total degree at most `k d` in the combining variables. -/
theorem totalDegree_combinedRestrict_le {K : Type*} [CommSemiring K] {m k d : ℕ}
    {p : MvPolynomial (Fin (m + k)) K} (hp : p ∈ _root_.LIDT.MIPStarRE.LDT.Preliminaries.polyFunc (m + k) K d) (u : Fin m → K) :
    (_root_.MIPStarRE.QPBT.combinedRestrict p u).totalDegree ≤ k * d :=
  _root_.LIDT.MIPStarRE.LDT.Preliminaries.totalDegree_le_mul_of_degreeOf_le
    (_root_.MIPStarRE.QPBT.degreeOf_combinedRestrict_le (_root_.LIDT.MIPStarRE.LDT.Preliminaries.degreeOf_le_of_mem_polyFunc hp) u)



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





/-! ## The collision estimate at a fixed point -/

open scoped Classical in

theorem solution {K : Type*} [Field K] [Fintype K]
    [DecidableEq K] {m k d : ℕ} {p : MvPolynomial (Fin (m + k)) K}
    (hp : p ∈ _root_.LIDT.MIPStarRE.LDT.Preliminaries.polyFunc (m + k) K d) (hkd : 1 ≤ k * d) (u : Fin m → K) (b : Fin k → K)
    (hu : ∀ c : Fin k → K, _root_.MIPStarRE.QPBT.combinedRestrict p u ≠ _root_.MIPStarRE.QPBT.combiningLinearForm c) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin k → K))
        (fun α => if MvPolynomial.eval (_root_.MIPStarRE.QPBT.combinedPoint u α) p =
          ∑ r : Fin k, b r * α r then (1 : _root_.LIDT.MIPStarRE.LDT.Error) else 0) ≤
      ((((k * d : ℕ) : ℚ≥0) / Fintype.card K : ℚ≥0) : _root_.LIDT.MIPStarRE.LDT.Error) := by
  classical
  have hdeg : (_root_.MIPStarRE.QPBT.combinedRestrict p u).totalDegree ≤ k * d :=
    _root_.MIPStarRE.QPBT.totalDegree_combinedRestrict_le hp u
  have hlin : (_root_.MIPStarRE.QPBT.combiningLinearForm b).totalDegree ≤ k * d :=
    le_trans (_root_.MIPStarRE.QPBT.combiningLinearForm_totalDegree_le_one b) hkd
  calc
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin k → K))
        (fun α => if MvPolynomial.eval (_root_.MIPStarRE.QPBT.combinedPoint u α) p =
          ∑ r : Fin k, b r * α r then (1 : _root_.LIDT.MIPStarRE.LDT.Error) else 0)
      = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin k → K))
          (fun α => if MvPolynomial.eval α (_root_.MIPStarRE.QPBT.combinedRestrict p u) =
            MvPolynomial.eval α (_root_.MIPStarRE.QPBT.combiningLinearForm b) then (1 : _root_.LIDT.MIPStarRE.LDT.Error) else 0) := by
        apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
        intro α
        rw [_root_.MIPStarRE.QPBT.eval_combinedRestrict, _root_.MIPStarRE.QPBT.combiningLinearForm_eval]
    _ = (_root_.LIDT.MIPStarRE.LDT.Preliminaries.polynomialAgreementProbability k K (_root_.MIPStarRE.QPBT.combinedRestrict p u)
          (_root_.MIPStarRE.QPBT.combiningLinearForm b) : _root_.LIDT.MIPStarRE.LDT.Error) :=
        _root_.MIPStarRE.QPBT.polynomialAgreement_avg_eq_agreementProbability _ _
    _ ≤ ((((k * d : ℕ) : ℚ≥0) / Fintype.card K : ℚ≥0) : _root_.LIDT.MIPStarRE.LDT.Error) := by
        exact_mod_cast _root_.LIDT.MIPStarRE.LDT.Preliminaries.schwartzZippel_totalDegree (hu b) hdeg hlin
