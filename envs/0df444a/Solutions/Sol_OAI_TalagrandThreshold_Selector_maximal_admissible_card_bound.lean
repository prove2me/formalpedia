-- Prove2me | solution 1 for OAI.TalagrandThreshold.Selector.maximal_admissible_card_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T13:55:24.172231+00:00
-- url     : https://prove2.me/submissions/c0d84d44-cdb0-4d8b-bc29-a47e1f1c8289

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ExpectationThreshold/SelectorTruncationSlope.lean:L78-L114
-- (upload_full_project.md Phase 4): solution for node OAI.TalagrandThreshold.Selector.maximal_admissible_card_bound. The node keeps its source
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
import Theorems.Thm_OAI_TalagrandThreshold_Selector_exists_short_right_cutoff
import Theorems.Thm_OAI_TalagrandThreshold_Selector_truncatedExcess_sub_eq_heavy_increment

-- ---- from OAI.Combinatorics.ExpectationThreshold.SelectorTruncationSlope ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
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

/-- The cardinality conclusion of maximal truncation.  Existence of a
maximal admissible cutoff is supplied separately by compactness. -/
theorem maximal_admissible_card_bound (w : α → ℝ) (A : Finset α) (m d ε : ℝ)
    (hwnonneg : ∀ x, 0 ≤ w x) (hwsum : ∑ x, w x = 1)
    (hm0 : 0 ≤ m) (_hd0 : 0 < d) (_hd1 : d < 1)
    (hε : Admissible w A m d ε)
    (hmax : ∀ u : ℝ, Admissible w A m d u → u ≤ ε) :
    d * ((heavySet w ε).card : ℝ) ≤ m := by
  classical
  have hwle (x : α) : w x ≤ 1 := by
    calc
      w x ≤ ∑ y, w y :=
        Finset.single_le_sum (fun y _ => hwnonneg y) (Finset.mem_univ x)
      _ = 1 := hwsum
  by_cases hεone : ε = 1
  · have hempty : heavySet w ε = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hlt := mem_heavySet.mp hx
      rw [hεone] at hlt
      exact (not_lt_of_ge (hwle x)) hlt
    simpa only [hempty, Finset.card_empty, Nat.cast_zero, mul_zero] using hm0
  · have hεlt : ε < 1 := lt_of_le_of_ne hε.2.1 hεone
    obtain ⟨u, hεu, hu1, hupper⟩ := exists_short_right_cutoff w hεlt
    by_contra hbound
    have hgap : m < d * ((heavySet w ε).card : ℝ) := lt_of_not_ge hbound
    have haffine := truncatedExcess_sub_eq_heavy_increment w A d ε u
      hεu.le hupper hε.2.2.1
    have hslope : 0 ≤ (u - ε) * (d * ((heavySet w ε).card : ℝ) - m) :=
      mul_nonneg (sub_nonneg.mpr hεu.le) (sub_nonneg.mpr hgap.le)
    have htest : m * u ≤ truncatedExcess w A d u := by
      have htestε := hε.2.2.2
      nlinarith
    have hu : Admissible w A m d u :=
      ⟨hε.1.trans hεu.le, hu1,
        fun x hx => hε.2.2.1 x (hεu.trans hx), htest⟩
    exact (not_lt_of_ge (hmax u hu)) hεu

end TalagrandThreshold.Selector

end OAI

-- ---- platform node ----
open OAI OAI.TalagrandThreshold OAI.TalagrandThreshold.Selector
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TalagrandThreshold.Selector.maximal_admissible_card_bound := @_root_.OAI.TalagrandThreshold.Selector.maximal_admissible_card_bound
