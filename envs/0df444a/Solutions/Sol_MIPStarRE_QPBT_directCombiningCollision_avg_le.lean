-- Prove2me | solution 1 for MIPStarRE.QPBT.directCombiningCollision_avg_le
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T21:11:08.651973+00:00
-- url     : https://prove2.me/submissions/a146a856-bfa1-437e-ab1e-ab3693c2a91c

-- Generated proof for MIPStarRE.QPBT.directCombiningCollision_avg_le.
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
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Combining_Linearity
import Mathlib
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

/-- The coefficient of the variable `α_r` in a linear form is `c r`. -/
theorem combiningLinearForm_coeff {K : Type*} [CommSemiring K] {k : ℕ}
    (c : Fin k → K) (r : Fin k) :
    (_root_.MIPStarRE.QPBT.combiningLinearForm c).coeff (Finsupp.single r 1) = c r := by
  classical
  rw [_root_.MIPStarRE.QPBT.combiningLinearForm, MvPolynomial.coeff_sum, Finset.sum_eq_single r]
  · simp [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X]
  · intro s _ hs
    rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X, if_neg, mul_zero]
    intro hEq
    exact hs (Finsupp.single_left_injective one_ne_zero hEq)
  · intro h
    exact absurd (Finset.mem_univ r) h

/-- A linear form determines its coefficients. -/
theorem combiningLinearForm_injective {K : Type*} [CommSemiring K] {k : ℕ} :
    Function.Injective (_root_.MIPStarRE.QPBT.combiningLinearForm (K := K) (k := k)) := by
  intro c c' h
  funext r
  rw [← _root_.MIPStarRE.QPBT.combiningLinearForm_coeff c r, h, _root_.MIPStarRE.QPBT.combiningLinearForm_coeff]

/-- Two linear forms with distinct coefficient tuples agree at a uniformly
sampled point with probability at most `1/q`.  This is the Schwartz--Zippel
bound at total degree one. -/
theorem combiningLinearForm_agreementProbability_le {K : Type*} [Field K] [Fintype K]
    [DecidableEq K] {k : ℕ} (c b : Fin k → K) (hne : c ≠ b) :
    _root_.LIDT.MIPStarRE.LDT.Preliminaries.polynomialAgreementProbability k K (_root_.MIPStarRE.QPBT.combiningLinearForm c) (_root_.MIPStarRE.QPBT.combiningLinearForm b) ≤
      1 / Fintype.card K := by
  have hpoly : _root_.MIPStarRE.QPBT.combiningLinearForm c ≠ _root_.MIPStarRE.QPBT.combiningLinearForm b := fun h =>
    hne (_root_.MIPStarRE.QPBT.combiningLinearForm_injective h)
  simpa using _root_.LIDT.MIPStarRE.LDT.Preliminaries.schwartzZippel_totalDegree (d := 1) hpoly
    (_root_.MIPStarRE.QPBT.combiningLinearForm_totalDegree_le_one c) (_root_.MIPStarRE.QPBT.combiningLinearForm_totalDegree_le_one b)

/-! ## The averaged form -/





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



open scoped BigOperators

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.LDT.Preliminaries



/-! ## The linear form of a tuple of scalars -/













/-! ## The averaged form -/

theorem solution (D : _root_.MIPStarRE.QPBT.DirectLdParams)
    (c b : Fin D.k → _root_.MIPStarRE.QPBT.DirectScalarQ D) (hne : c ≠ b) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin D.k → _root_.MIPStarRE.QPBT.DirectScalarQ D))
        (fun α => if ∑ r : Fin D.k, c r * α r = ∑ r : Fin D.k, b r * α r then
          (1 : _root_.LIDT.MIPStarRE.LDT.Error) else 0) ≤
      (1 : _root_.LIDT.MIPStarRE.LDT.Error) / D.q := by
  classical
  have hagree := _root_.MIPStarRE.QPBT.combiningLinearForm_agreementProbability_le c b hne
  calc
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin D.k → _root_.MIPStarRE.QPBT.DirectScalarQ D))
        (fun α => if ∑ r : Fin D.k, c r * α r = ∑ r : Fin D.k, b r * α r then
          (1 : _root_.LIDT.MIPStarRE.LDT.Error) else 0)
      = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin D.k → _root_.MIPStarRE.QPBT.DirectScalarQ D))
          (fun α => if MvPolynomial.eval α (_root_.MIPStarRE.QPBT.combiningLinearForm c) =
            MvPolynomial.eval α (_root_.MIPStarRE.QPBT.combiningLinearForm b) then (1 : _root_.LIDT.MIPStarRE.LDT.Error) else 0) := by
        apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
        intro α
        rw [_root_.MIPStarRE.QPBT.combiningLinearForm_eval, _root_.MIPStarRE.QPBT.combiningLinearForm_eval]
    _ = (_root_.LIDT.MIPStarRE.LDT.Preliminaries.polynomialAgreementProbability D.k (_root_.MIPStarRE.QPBT.DirectScalarQ D)
          (_root_.MIPStarRE.QPBT.combiningLinearForm c) (_root_.MIPStarRE.QPBT.combiningLinearForm b) : _root_.LIDT.MIPStarRE.LDT.Error) :=
        _root_.MIPStarRE.QPBT.polynomialAgreement_avg_eq_agreementProbability _ _
    _ ≤ ((1 / Fintype.card (_root_.MIPStarRE.QPBT.DirectScalarQ D) : ℚ≥0) : _root_.LIDT.MIPStarRE.LDT.Error) := by
        exact_mod_cast hagree
    _ = (1 : _root_.LIDT.MIPStarRE.LDT.Error) / D.q := by
        rw [_root_.MIPStarRE.QPBT.card_directScalarQ]
        simp
