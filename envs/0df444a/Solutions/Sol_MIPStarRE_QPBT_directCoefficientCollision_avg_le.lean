-- Prove2me | solution 1 for MIPStarRE.QPBT.directCoefficientCollision_avg_le
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T20:57:53.637925+00:00
-- url     : https://prove2.me/submissions/a8105836-aee5-4394-8602-535b2c4eaea0

-- Generated proof for MIPStarRE.QPBT.directCoefficientCollision_avg_le.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_AvgCongr
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_QPBT_QPBT_Algebra_Coefficients
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Game
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Mathlib
import Theorems.Thm_MIPStarRE_QPBT_evalCoefficient_collision_card_le

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries
namespace MIPStarRE.QPBT
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
# Collision bounds for direct line coefficients

This module bounds the probability that two distinct coefficient vectors give
the same value at a uniformly sampled affine parameter.  It uses the existing
coefficient-polynomial representation and Mathlib's univariate root count.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:331-344`
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1595-1603`
-/



open scoped BigOperators

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.LDT.Preliminaries

theorem solution (D : _root_.MIPStarRE.QPBT.DirectLdParams) (degree : ℕ)
    (a b : _root_.MIPStarRE.QPBT.DirectDegPoly D degree) (hne : a ≠ b) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectScalarQ D))
        (fun t => if _root_.MIPStarRE.QPBT.evalCoefficient a t = _root_.MIPStarRE.QPBT.evalCoefficient b t then
          (1 : ℝ) else 0) ≤
      (degree : ℝ) / (D.q : ℝ) := by
  classical
  let collisionSet : Finset (_root_.MIPStarRE.QPBT.DirectScalarQ D) :=
    Finset.univ.filter fun t => _root_.MIPStarRE.QPBT.evalCoefficient a t = _root_.MIPStarRE.QPBT.evalCoefficient b t
  have hcollision_card : collisionSet.card ≤ degree :=
    _root_.MIPStarRE.QPBT.evalCoefficient_collision_card_le a b hne
  calc
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectScalarQ D))
        (fun t => if _root_.MIPStarRE.QPBT.evalCoefficient a t = _root_.MIPStarRE.QPBT.evalCoefficient b t then
          (1 : ℝ) else 0) =
        (collisionSet.card : ℝ) /
          Fintype.card (_root_.MIPStarRE.QPBT.DirectScalarQ D) := by
      calc
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.DirectScalarQ D))
            (fun t => if _root_.MIPStarRE.QPBT.evalCoefficient a t = _root_.MIPStarRE.QPBT.evalCoefficient b t then
              (1 : ℝ) else 0) =
            ∑ t : _root_.MIPStarRE.QPBT.DirectScalarQ D,
              if _root_.MIPStarRE.QPBT.evalCoefficient a t = _root_.MIPStarRE.QPBT.evalCoefficient b t then
                (1 / Fintype.card (_root_.MIPStarRE.QPBT.DirectScalarQ D) : ℝ) else 0 := by
          simp [_root_.LIDT.MIPStarRE.LDT.avgOver, _root_.LIDT.MIPStarRE.LDT.uniformDistribution]
        _ = ∑ _t ∈ collisionSet,
              (1 / Fintype.card (_root_.MIPStarRE.QPBT.DirectScalarQ D) : ℝ) := by
          rw [← Finset.sum_filter]
        _ = (collisionSet.card : ℝ) /
              Fintype.card (_root_.MIPStarRE.QPBT.DirectScalarQ D) := by
          simp [div_eq_mul_inv]
    _ ≤ (degree : ℝ) / Fintype.card (_root_.MIPStarRE.QPBT.DirectScalarQ D) := by
      exact div_le_div_of_nonneg_right (by exact_mod_cast hcollision_card) (by positivity)
    _ = (degree : ℝ) / (D.q : ℝ) := by
      rw [_root_.MIPStarRE.QPBT.card_directScalarQ]
