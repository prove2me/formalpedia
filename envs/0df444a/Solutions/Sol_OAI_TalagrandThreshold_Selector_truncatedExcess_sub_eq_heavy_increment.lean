-- Prove2me | solution 1 for OAI.TalagrandThreshold.Selector.truncatedExcess_sub_eq_heavy_increment
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T13:52:24.270351+00:00
-- url     : https://prove2.me/submissions/852a9b82-0f33-4bac-a312-f123e2af6646

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ExpectationThreshold/SelectorTruncationSlope.lean:L48-L76
-- (upload_full_project.md Phase 4): solution for node OAI.TalagrandThreshold.Selector.truncatedExcess_sub_eq_heavy_increment. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Find
import Mathlib.Data.Real.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Order.Compact
import Definitions.Def_TalagrandExpectationThreshold
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_Model
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_Basic
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_RoundingMasses
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_ProbabilityFinite
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_ProbabilityProduct
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_RoundingExpectation
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_ProbabilityColors
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_ScaleBounds
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorTruncationDefinitions
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorDefinitions
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorFeasibility
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorCountingEncoding
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorCountingWords
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorCountingWordsTransport
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorCountingEncodingRows
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorProfile
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorCountingEncodingBound
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorDelay

-- ---- from OAI.Combinatorics.ExpectationThreshold.SelectorTruncationSlope ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

/-!
# The right-hand slope at a maximal admissible cutoff

A finite minimum provides an actual larger cutoff below every currently
heavy weight.  Between these cutoffs the truncated excess has the exact
affine increment contributed by the heavy coordinates.  Weights equal to
the original cutoff remain saturated, including when the cutoff is zero.
-/

namespace TalagrandThreshold.Selector

open scoped BigOperators

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- On the first interval to the right of a cutoff, precisely the strictly
heavy coordinates vary.  The inclusion in `A` makes their coefficient `d`. -/
theorem truncatedExcess_sub_eq_heavy_increment (w : α → ℝ) (A : Finset α)
    (d ε u : ℝ) (hεu : ε ≤ u)
    (hupper : ∀ x, ε < w x → u ≤ w x)
    (hheavy : ∀ x, ε < w x → x ∈ A) :
    truncatedExcess w A d u - truncatedExcess w A d ε =
      (u - ε) * d * ((heavySet w ε).card : ℝ) := by
  classical
  calc
    truncatedExcess w A d u - truncatedExcess w A d ε =
        ∑ x, if ε < w x then (u - ε) * d else 0 := by
      unfold truncatedExcess
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : ε < w x
      · simp only [min_eq_right (hupper x hx), min_eq_right hx.le,
          ite_eq_left hx, ite_eq_left (hheavy x hx)]
        ring
      · have hxε : w x ≤ ε := le_of_not_gt hx
        simp only [min_eq_left (hxε.trans hεu), min_eq_left hxε,
          ite_eq_right hx, sub_self]
    _ = ∑ x ∈ heavySet w ε, (u - ε) * d := by
      rw [← Finset.sum_filter]
      rfl
    _ = (u - ε) * d * ((heavySet w ε).card : ℝ) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring

end TalagrandThreshold.Selector

end OAI

-- ---- platform node ----
open OAI OAI.TalagrandThreshold OAI.TalagrandThreshold.Selector
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TalagrandThreshold.Selector.truncatedExcess_sub_eq_heavy_increment := @_root_.OAI.TalagrandThreshold.Selector.truncatedExcess_sub_eq_heavy_increment
