-- Prove2me | solution 1 for OAI.TalagrandThreshold.Selector.truncatedExcess_le_original
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T13:35:37.510463+00:00
-- url     : https://prove2.me/submissions/0a84cb82-7d1b-47d8-b0d7-dbb20952f7f1

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ExpectationThreshold/SelectorFeasibility.lean:L133-L150
-- (upload_full_project.md Phase 4): solution for node OAI.TalagrandThreshold.Selector.truncatedExcess_le_original. The node keeps its source
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

-- ---- from OAI.Combinatorics.ExpectationThreshold.SelectorFeasibility ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e

namespace OAI

/-!
# Feasible minima and the actual containment cover

Resetting an original family member to the first color proves existence of
a bounded feasible move. Minimization itself retains the unrestricted
feasibility witness from `Feasible`; the witness need not be that member.
All retained minima contribute their actual changed sets to a cover.
-/

noncomputable section

open scoped BigOperators

namespace TalagrandThreshold.Selector

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {F : Family α} {s : ℕ}

/-- Restoring weights increases the excess: only heavy points change, and
their coefficient is the nonnegative value `d`. -/
theorem truncatedExcess_le_original (w : α → ℝ) (A : Finset α) (d u : ℝ)
    (hd : 0 ≤ d) (hheavy : ∀ x, u < w x → x ∈ A) :
    truncatedExcess w A d u ≤
      ∑ x, w x * ((if x ∈ A then 1 else 0) - (1 - d)) := by
  classical
  unfold truncatedExcess
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : x ∈ A
  · have hcoef : ((if x ∈ A then (1 : ℝ) else 0) - (1 - d)) = d := by
      rw [ite_eq_left hx]
      ring
    rw [hcoef]
    exact mul_le_mul_of_nonneg_right (min_le_left (w x) u) hd
  · have hxu : w x ≤ u := le_of_not_gt (fun h => hx (hheavy x h))
    rw [min_eq_left hxu]

end TalagrandThreshold.Selector

end

end OAI

-- ---- platform node ----
open OAI OAI.TalagrandThreshold OAI.TalagrandThreshold.Selector
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TalagrandThreshold.Selector.truncatedExcess_le_original := @_root_.OAI.TalagrandThreshold.Selector.truncatedExcess_le_original
