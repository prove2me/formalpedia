-- Prove2me | solution 1 for MIPStarRE.QPBT.directCombinedRecoveryLocalBound_avg_le
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T21:25:06.255333+00:00
-- url     : https://prove2.me/submissions/159b79ff-326f-4eb8-b765-86012d13ef45

-- Generated proof for MIPStarRE.QPBT.directCombinedRecoveryLocalBound_avg_le.
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
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Combining_Parameters
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Combining_Recovery
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Combining_Restriction
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGameMeasurements
import Mathlib
import Theorems.Thm_MIPStarRE_QPBT_directCombinedExactLinearity_avg_le

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

/- Source helpers from QPBT/Combining/DirectLowDegree/Transport/Combining/Recovery.lean. -/
/-!
# The joint recovery estimate in the point and combining variables

`lem:ld-combining-recovery` compares the tuple of values at a point of the
components recovered from an outcome of the combined game with the tuple of
answers of the point measurement of the original game.  The comparison rests on
a joint estimate over the sampled point `u` and the sampled combining vector
`α`: for every outcome `p` of the combined game and every tuple `b` of scalars,
the event that the recovered tuple of values at `u` differs from `b` while the
value of `p` at the combined point agrees with the combination `∑_r α_r b_r`
has probability at most `(m + k) d / q`.

Two cases occur.  If `p` is the combined polynomial of a tuple `g`, its value at
the combined point is the combination `∑_r α_r g_r(u)`, and two combinations
with distinct coefficient tuples agree at a uniformly sampled `α` with
probability at most `1 / q`.  If `p` is not combined, then by
`lem:ld-combining-exact-linearity` its restriction `p(u, ·)` fails to be a
linear form except with probability `m d / q` over `u`, and off that event the
restriction and the linear form of `b` are distinct polynomials of total degree
at most `k d`, so they agree at a uniformly sampled `α` with probability at
most `k d / q`.

The estimate is recorded in two stages, because the consistency calculus
averages it against Born weights which depend on the sampled point but not on
the sampled combining vector: a bound at a fixed point which does not depend on
the tuple `b`, and the average of that bound over the point.

## Main statements

* `directCombinedRecoveryLocalBound` — the bound at a fixed point.
* `directCombinedRecoveryEvent_avg_le` — the estimate at a fixed point.
* `directCombinedRecoveryLocalBound_avg_le` — the average of the bound at a
  fixed point over a uniformly sampled point.
* `directCombinedRecoveryBadEvent_avg_le` — the joint estimate of
  `lem:ld-combining-recovery`.

## References

* `references/neexp-paper/05_quantum_preliminaries.tex:1440-1503`
* `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`
* `blueprint/src/chapter/ch13_qpbt_test.tex:617-680`
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.LDT.Preliminaries

noncomputable section

/-! ## Elementary facts about the parameters -/

/-- The field size of a directly indexed low-degree game is positive. -/
theorem directLdFieldSize_pos (D : _root_.MIPStarRE.QPBT.DirectLdParams) : (0 : ℝ) < (D.q : ℝ) := by
  have h : 0 < Fintype.card (_root_.MIPStarRE.QPBT.DirectScalarQ D) := Fintype.card_pos
  rw [_root_.MIPStarRE.QPBT.card_directScalarQ] at h
  exact_mod_cast h





/-! ## The collision estimates in the combining variables -/





/-! ## The estimate at a fixed point -/







/-! ## The averaged estimate -/





end

end MIPStarRE.QPBT

/-!
# The joint recovery estimate in the point and combining variables

`lem:ld-combining-recovery` compares the tuple of values at a point of the
components recovered from an outcome of the combined game with the tuple of
answers of the point measurement of the original game.  The comparison rests on
a joint estimate over the sampled point `u` and the sampled combining vector
`α`: for every outcome `p` of the combined game and every tuple `b` of scalars,
the event that the recovered tuple of values at `u` differs from `b` while the
value of `p` at the combined point agrees with the combination `∑_r α_r b_r`
has probability at most `(m + k) d / q`.

Two cases occur.  If `p` is the combined polynomial of a tuple `g`, its value at
the combined point is the combination `∑_r α_r g_r(u)`, and two combinations
with distinct coefficient tuples agree at a uniformly sampled `α` with
probability at most `1 / q`.  If `p` is not combined, then by
`lem:ld-combining-exact-linearity` its restriction `p(u, ·)` fails to be a
linear form except with probability `m d / q` over `u`, and off that event the
restriction and the linear form of `b` are distinct polynomials of total degree
at most `k d`, so they agree at a uniformly sampled `α` with probability at
most `k d / q`.

The estimate is recorded in two stages, because the consistency calculus
averages it against Born weights which depend on the sampled point but not on
the sampled combining vector: a bound at a fixed point which does not depend on
the tuple `b`, and the average of that bound over the point.

## Main statements

* `directCombinedRecoveryLocalBound` — the bound at a fixed point.
* `directCombinedRecoveryEvent_avg_le` — the estimate at a fixed point.
* `directCombinedRecoveryLocalBound_avg_le` — the average of the bound at a
  fixed point over a uniformly sampled point.
* `directCombinedRecoveryBadEvent_avg_le` — the joint estimate of
  `lem:ld-combining-recovery`.

## References

* `references/neexp-paper/05_quantum_preliminaries.tex:1440-1503`
* `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`
* `blueprint/src/chapter/ch13_qpbt_test.tex:617-680`
-/



open scoped BigOperators

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.LDT.Preliminaries



/-! ## Elementary facts about the parameters -/







/-! ## The collision estimates in the combining variables -/





/-! ## The estimate at a fixed point -/







/-! ## The averaged estimate -/

set_option maxHeartbeats 800000 in
open scoped Classical in

theorem solution (D : _root_.MIPStarRE.QPBT.DirectLdParams)
    (p : _root_.MIPStarRE.QPBT.PolyIndex D.combined.m (_root_.MIPStarRE.QPBT.DirectScalarQ D) D.d) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D))
        (_root_.MIPStarRE.QPBT.directCombinedRecoveryLocalBound D p) ≤
      ((D.combined.m * D.d : ℕ) : _root_.LIDT.MIPStarRE.LDT.Error) / D.q := by
  classical
  have hq := _root_.MIPStarRE.QPBT.directLdFieldSize_pos D
  have hsplit : ((D.combined.m * D.d : ℕ) : _root_.LIDT.MIPStarRE.LDT.Error) / D.q =
      ((D.m * D.d : ℕ) : _root_.LIDT.MIPStarRE.LDT.Error) / D.q + ((D.k * D.d : ℕ) : _root_.LIDT.MIPStarRE.LDT.Error) / D.q := by
    have hn : (D.combined.m * D.d : ℕ) = D.m * D.d + D.k * D.d := by
      simp [_root_.MIPStarRE.QPBT.DirectLdParams.combined_m, Nat.add_mul]
    rw [hn]
    push_cast
    ring
  by_cases hc : _root_.MIPStarRE.QPBT.IsDirectCombined D p
  · have hconst : ∀ u : Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D,
        _root_.MIPStarRE.QPBT.directCombinedRecoveryLocalBound D p u = (1 : _root_.LIDT.MIPStarRE.LDT.Error) / D.q := by
      intro u
      rw [_root_.MIPStarRE.QPBT.directCombinedRecoveryLocalBound, if_pos hc]
    rw [_root_.LIDT.MIPStarRE.LDT.avgOver_congr _ _ _ hconst, _root_.LIDT.MIPStarRE.LDT.avgOver_uniform_const]
    have h1 : (1 : _root_.LIDT.MIPStarRE.LDT.Error) ≤ ((D.combined.m * D.d : ℕ) : _root_.LIDT.MIPStarRE.LDT.Error) := by
      have hle : 1 ≤ D.combined.m * D.d := by
        simpa using Nat.mul_le_mul D.combined.hm D.combined.hd
      exact_mod_cast hle
    exact div_le_div_of_nonneg_right h1 hq.le
  · have hlin := _root_.MIPStarRE.QPBT.directCombinedExactLinearity_avg_le D p hc
    have heq : ∀ u : Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D,
        _root_.MIPStarRE.QPBT.directCombinedRecoveryLocalBound D p u =
          (if ∃ c : Fin D.k → _root_.MIPStarRE.QPBT.DirectScalarQ D,
              _root_.MIPStarRE.QPBT.combinedRestrict p.1 u = _root_.MIPStarRE.QPBT.combiningLinearForm c then (1 : _root_.LIDT.MIPStarRE.LDT.Error)
            else 0) + ((D.k * D.d : ℕ) : _root_.LIDT.MIPStarRE.LDT.Error) / D.q := by
      intro u
      rw [_root_.MIPStarRE.QPBT.directCombinedRecoveryLocalBound, if_neg hc]
    rw [_root_.LIDT.MIPStarRE.LDT.avgOver_congr _ _ _ heq, _root_.LIDT.MIPStarRE.LDT.avgOver_add, _root_.LIDT.MIPStarRE.LDT.avgOver_uniform_const, hsplit]
    linarith [hlin]
