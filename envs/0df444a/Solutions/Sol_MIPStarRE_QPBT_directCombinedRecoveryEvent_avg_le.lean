-- Prove2me | solution 1 for MIPStarRE.QPBT.directCombinedRecoveryEvent_avg_le
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T21:15:21.964957+00:00
-- url     : https://prove2.me/submissions/810ecdc2-66f4-4057-a0e4-5c90a1fe0c32

-- Generated proof for MIPStarRE.QPBT.directCombinedRecoveryEvent_avg_le.
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
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Game
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Combining_Linearity
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Combining_Parameters
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Combining_Polynomial
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Combining_Recovery
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Combining_Restriction
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGameMeasurements
import Mathlib
import Theorems.Thm_MIPStarRE_QPBT_combinedRestrict_collision_avg_le
import Theorems.Thm_MIPStarRE_QPBT_directCombiningCollision_avg_le

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/DirectLowDegree/Transport/Combining/Polynomial.lean. -/
/-!
# The combining map on tuples of low individual degree polynomials

The extension of the quantum soundness of the low individual degree test from
simultaneity parameter `1` to a general simultaneity parameter `k` is obtained
in the source by a reduction, not coordinatewise: the `k` answer polynomials
`g_0, …, g_{k-1}` in `m` variables are combined into the single polynomial

`comb(g)(u, α) = ∑_{r < k} α_r g_r(u)`

in `m + k` variables, the case `k = 1` is applied once in dimension `m + k`,
and the `k` polynomials are recovered from the resulting outcome by exact
linearity in the combining variables `α` together with the Schwartz--Zippel
lemma.  This module develops the polynomial algebra of that combining map: the
coordinate split of `Fin (m + k)`, the map itself, its evaluation identity, its
individual-degree bound, and the substitution recovering the `r`-th component,
which exhibits the map as injective.

The combining map of `def:combine-map` (`MIPStarRE/QPBT/Combining/Defs.lean`)
is the special case of two components used by the Chapter 15 combining
argument, written there in the fixed coordinate layout of that chapter; the
present map is the general `k`-component form required by the reduction, in the
coordinate layout of the directly indexed low-degree game, where the `m` point
coordinates precede the `k` combining coordinates.

## Main definitions

* `combinedPointVar`, `combinedCoefficientVar` — the two coordinate blocks of
  the combined dimension `m + k`.
* `combinePolyTuple` — the combining map on tuples of polynomials.
* `splitCombinedPoly` — the substitution `α ↦ e_r` recovering the `r`-th
  component of a combined polynomial.

## References

* `references/neexp-paper/05_quantum_preliminaries.tex:1409-1503`
  (the derivation of Theorem 4.43 from Theorem 4.40)
* `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`
* `blueprint/src/chapter/ch13_qpbt_test.tex:240-250`
* `docs/paper-gaps/qpbt_ld-simultaneous-sandwich.tex`
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT.Preliminaries

noncomputable section

/-! ## The coordinates of the combined dimension -/























/-! ## The combining map -/



/-- Evaluation of a combined polynomial is the displayed combining formula. -/
theorem combinePolyTuple_eval {K : Type*} [CommSemiring K] {m k : ℕ}
    (g : Fin k → MvPolynomial (Fin m) K) (z : Fin (m + k) → K) :
    MvPolynomial.eval z (_root_.MIPStarRE.QPBT.combinePolyTuple g) =
      ∑ r : Fin k, _root_.MIPStarRE.QPBT.combinedCoefficientPart z r *
        MvPolynomial.eval (_root_.MIPStarRE.QPBT.combinedPointPart z) (g r) := by
  simp only [_root_.MIPStarRE.QPBT.combinePolyTuple, map_sum, map_mul, MvPolynomial.eval_X,
    MvPolynomial.eval_rename, _root_.MIPStarRE.QPBT.combinedCoefficientPart]
  rfl

/-- Evaluation of a combined polynomial at a point given by its two blocks. -/
theorem combinePolyTuple_eval_combinedPoint {K : Type*} [CommSemiring K] {m k : ℕ}
    (g : Fin k → MvPolynomial (Fin m) K) (u : Fin m → K) (α : Fin k → K) :
    MvPolynomial.eval (_root_.MIPStarRE.QPBT.combinedPoint u α) (_root_.MIPStarRE.QPBT.combinePolyTuple g) =
      ∑ r : Fin k, α r * MvPolynomial.eval u (g r) := by
  rw [_root_.MIPStarRE.QPBT.combinePolyTuple_eval, _root_.MIPStarRE.QPBT.combinedPointPart_combinedPoint,
    _root_.MIPStarRE.QPBT.combinedCoefficientPart_combinedPoint]

/-! ## Recovering the components -/













/-! ## The individual-degree bound -/











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





/-- Evaluating the combined polynomial at a point of the combined space with
point part `u` and combining part `α` gives `∑_{r < k} α_r g_r(u)`. -/
theorem directCombinedPolynomial_eval (D : _root_.MIPStarRE.QPBT.DirectLdParams) (g : _root_.MIPStarRE.QPBT.DirectPolyTuple D)
    (u : Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D) (α : Fin D.k → _root_.MIPStarRE.QPBT.DirectScalarQ D) :
    MvPolynomial.eval (_root_.MIPStarRE.QPBT.combinedPoint u α) (_root_.MIPStarRE.QPBT.directCombinedPolynomial D g).1 =
      ∑ r : Fin D.k, α r * _root_.MIPStarRE.QPBT.evalDirectPolyTupleAt u g r := by
  rw [_root_.MIPStarRE.QPBT.directCombinedPolynomial_val, _root_.MIPStarRE.QPBT.combinePolyTuple_eval_combinedPoint]
  rfl







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

/-- Commuting the two factors of a combination of a tuple of scalars. -/
private theorem directCombiningSum_comm {K : Type*} [CommSemiring K] {k : ℕ}
    (c α : Fin k → K) : ∑ r : Fin k, α r * c r = ∑ r : Fin k, c r * α r :=
  Finset.sum_congr rfl fun _ _ => mul_comm _ _

/-- The rational bound produced by the Schwartz--Zippel estimates, read in the
field size of the directly indexed game. -/
private theorem directCombiningRatio_eq (D : _root_.MIPStarRE.QPBT.DirectLdParams) (n : ℕ) :
    ((((n : ℕ) : ℚ≥0) / Fintype.card (_root_.MIPStarRE.QPBT.DirectScalarQ D) : ℚ≥0) : _root_.LIDT.MIPStarRE.LDT.Error) =
      ((n : ℕ) : _root_.LIDT.MIPStarRE.LDT.Error) / D.q := by
  rw [_root_.MIPStarRE.QPBT.card_directScalarQ]
  push_cast
  ring

/-! ## The collision estimates in the combining variables -/

open scoped Classical in
/-- Collision of two combinations with distinct coefficient tuples, written with
the combining vector as the left factor. -/
private theorem directCombiningCollision_avg_le_comm (D : _root_.MIPStarRE.QPBT.DirectLdParams)
    (c b : Fin D.k → _root_.MIPStarRE.QPBT.DirectScalarQ D) (hne : c ≠ b) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin D.k → _root_.MIPStarRE.QPBT.DirectScalarQ D))
        (fun α => if ∑ r : Fin D.k, α r * c r = ∑ r : Fin D.k, α r * b r then
          (1 : _root_.LIDT.MIPStarRE.LDT.Error) else 0) ≤ (1 : _root_.LIDT.MIPStarRE.LDT.Error) / D.q := by
  refine le_trans (le_of_eq (_root_.LIDT.MIPStarRE.LDT.avgOver_congr _ _ _ fun α => ?_))
    (_root_.MIPStarRE.QPBT.directCombiningCollision_avg_le D c b hne)
  rw [directCombiningSum_comm c α, directCombiningSum_comm b α]

set_option maxHeartbeats 1000000 in
open scoped Classical in
/-- Collision of a restriction which is not a linear form with the linear form
of a tuple of scalars, written with the combining vector as the left factor. -/
private theorem directCombinedRestrictCollision_avg_le (D : _root_.MIPStarRE.QPBT.DirectLdParams)
    (p : _root_.MIPStarRE.QPBT.PolyIndex D.combined.m (_root_.MIPStarRE.QPBT.DirectScalarQ D) D.d)
    (u : Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D) (b : Fin D.k → _root_.MIPStarRE.QPBT.DirectScalarQ D)
    (hu : ∀ c : Fin D.k → _root_.MIPStarRE.QPBT.DirectScalarQ D,
      _root_.MIPStarRE.QPBT.combinedRestrict p.1 u ≠ _root_.MIPStarRE.QPBT.combiningLinearForm c) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin D.k → _root_.MIPStarRE.QPBT.DirectScalarQ D))
        (fun α => if MvPolynomial.eval (_root_.MIPStarRE.QPBT.combinedPoint u α) p.1 =
          ∑ r : Fin D.k, α r * b r then (1 : _root_.LIDT.MIPStarRE.LDT.Error) else 0) ≤
      ((D.k * D.d : ℕ) : _root_.LIDT.MIPStarRE.LDT.Error) / D.q := by
  have hkd : 1 ≤ D.k * D.d := by simpa using Nat.mul_le_mul D.hk D.hd
  have hbound := _root_.MIPStarRE.QPBT.combinedRestrict_collision_avg_le (d := D.d) p.2 hkd u b hu
  refine le_trans (le_of_eq (_root_.LIDT.MIPStarRE.LDT.avgOver_congr _ _ _ fun α => ?_))
    (le_trans hbound (le_of_eq (directCombiningRatio_eq D (D.k * D.d))))
  rw [directCombiningSum_comm b α]

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

set_option maxHeartbeats 1600000 in
open scoped Classical in

theorem solution (D : _root_.MIPStarRE.QPBT.DirectLdParams)
    (p : _root_.MIPStarRE.QPBT.PolyIndex D.combined.m (_root_.MIPStarRE.QPBT.DirectScalarQ D) D.d)
    (u : Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D) (b : Fin D.k → _root_.MIPStarRE.QPBT.DirectScalarQ D) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin D.k → _root_.MIPStarRE.QPBT.DirectScalarQ D)) (fun α =>
        if _root_.MIPStarRE.QPBT.evalDirectPolyTupleAt u (_root_.MIPStarRE.QPBT.directTupleOfCombined D p) ≠ b ∧
            MvPolynomial.eval (_root_.MIPStarRE.QPBT.combinedPoint u α) p.1 =
              ∑ r : Fin D.k, α r * b r then (1 : _root_.LIDT.MIPStarRE.LDT.Error) else 0) ≤
      _root_.MIPStarRE.QPBT.directCombinedRecoveryLocalBound D p u := by
  classical
  have hq := _root_.MIPStarRE.QPBT.directLdFieldSize_pos D
  rw [_root_.MIPStarRE.QPBT.directCombinedRecoveryLocalBound]
  by_cases hc : _root_.MIPStarRE.QPBT.IsDirectCombined D p
  · rw [if_pos hc]
    obtain ⟨g, hg⟩ := hc
    subst hg
    rw [_root_.MIPStarRE.QPBT.directTupleOfCombined_directCombinedPolynomial]
    by_cases hub : _root_.MIPStarRE.QPBT.evalDirectPolyTupleAt u g = b
    · have hzero : ∀ α : Fin D.k → _root_.MIPStarRE.QPBT.DirectScalarQ D,
          (if _root_.MIPStarRE.QPBT.evalDirectPolyTupleAt u g ≠ b ∧
              MvPolynomial.eval (_root_.MIPStarRE.QPBT.combinedPoint u α)
                  (_root_.MIPStarRE.QPBT.directCombinedPolynomial D g).1 =
                ∑ r : Fin D.k, α r * b r then (1 : _root_.LIDT.MIPStarRE.LDT.Error) else 0) = 0 := by
        intro α
        refine if_neg ?_
        rintro ⟨hne, -⟩
        exact hne hub
      rw [_root_.LIDT.MIPStarRE.LDT.avgOver_congr _ _ _ hzero, _root_.LIDT.MIPStarRE.LDT.avgOver_zero]
      positivity
    · refine le_trans (_root_.LIDT.MIPStarRE.LDT.avgOver_mono _ _
        (fun α => if ∑ r : Fin D.k, α r * _root_.MIPStarRE.QPBT.evalDirectPolyTupleAt u g r =
          ∑ r : Fin D.k, α r * b r then (1 : _root_.LIDT.MIPStarRE.LDT.Error) else 0) fun α => ?_)
        (directCombiningCollision_avg_le_comm D _ b hub)
      by_cases hev : _root_.MIPStarRE.QPBT.evalDirectPolyTupleAt u g ≠ b ∧
          MvPolynomial.eval (_root_.MIPStarRE.QPBT.combinedPoint u α)
              (_root_.MIPStarRE.QPBT.directCombinedPolynomial D g).1 =
            ∑ r : Fin D.k, α r * b r
      · have h2 := hev.2
        rw [_root_.MIPStarRE.QPBT.directCombinedPolynomial_eval] at h2
        rw [if_pos hev, if_pos h2]
      · rw [if_neg hev]
        split_ifs
        · exact zero_le_one
        · exact le_rfl
  · rw [if_neg hc]
    by_cases hu : ∃ c : Fin D.k → _root_.MIPStarRE.QPBT.DirectScalarQ D,
        _root_.MIPStarRE.QPBT.combinedRestrict p.1 u = _root_.MIPStarRE.QPBT.combiningLinearForm c
    · rw [if_pos hu]
      have hkd : (0 : _root_.LIDT.MIPStarRE.LDT.Error) ≤ ((D.k * D.d : ℕ) : _root_.LIDT.MIPStarRE.LDT.Error) / D.q := by positivity
      refine le_trans (_root_.LIDT.MIPStarRE.LDT.avgOver_mono _ _ (fun _ => (1 : _root_.LIDT.MIPStarRE.LDT.Error)) fun α => ?_) ?_
      · split_ifs
        · exact le_rfl
        · exact zero_le_one
      · rw [_root_.LIDT.MIPStarRE.LDT.avgOver_uniform_const]
        linarith
    · rw [if_neg hu, zero_add]
      push Not at hu
      refine le_trans (_root_.LIDT.MIPStarRE.LDT.avgOver_mono _ _
        (fun α => if MvPolynomial.eval (_root_.MIPStarRE.QPBT.combinedPoint u α) p.1 =
          ∑ r : Fin D.k, α r * b r then (1 : _root_.LIDT.MIPStarRE.LDT.Error) else 0) fun α => ?_)
        (directCombinedRestrictCollision_avg_le D p u b hu)
      split_ifs with h1 h2
      · exact le_rfl
      · exact absurd h1.2 h2
      · exact zero_le_one
      · exact le_rfl
