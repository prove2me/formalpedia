-- Prove2me | solution 1 for OAI.TalagrandThreshold.Selector.selected_cost_group_by_endpoint
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T14:10:52.997646+00:00
-- url     : https://prove2.me/submissions/2e200e0c-fd96-426f-b80f-636ea5fb09f4

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ExpectationThreshold/SelectorGlobalCost.lean:L78-L96
-- (upload_full_project.md Phase 4): solution for node OAI.TalagrandThreshold.Selector.selected_cost_group_by_endpoint. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorCommonWitness
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_TupleCoefficients
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorGlobalCost

-- ---- from OAI.Combinatorics.ExpectationThreshold.SelectorGlobalCost ----
namespace OAI

/-!
# The global cost of actual selected moves

Partition selected pairs first by their final coloring and then by their
full profile. The profile estimate removes the profile-dependent heavy
sets before summation. Word-count normalization and the finite geometric
bound then give the strict budget under the actual coloring law.
-/

noncomputable section

open scoped BigOperators Classical

namespace TalagrandThreshold.Selector

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {F : Family α} {s : ℕ}

/-- Swapping the two finite sums groups all actual selected pairs by endpoint. -/
theorem selected_cost_group_by_endpoint (mu : MassFamily F)
    (f : Coloring α s → Coloring α s → ℝ) :
    (∑ a ∈ (Finset.univ : Finset (Coloring α s)).filter (Bad mu),
      ∑ z ∈ selectedMoves mu a, f a z) =
      ∑ z : Coloring α s, ∑ a ∈ selectedOriginals mu z, f a z := by
  classical
  calc
    (∑ a ∈ (Finset.univ : Finset (Coloring α s)).filter (Bad mu),
        ∑ z ∈ selectedMoves mu a, f a z) =
        ∑ a : Coloring α s, ∑ z : Coloring α s,
          if Bad mu a ∧ Selected mu a z then f a z else 0 := by
      simp only [selectedMoves, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : Bad mu a <;> simp [ha]
    _ = ∑ z : Coloring α s, ∑ a ∈ selectedOriginals mu z, f a z := by
      rw [Finset.sum_comm]
      simp only [selectedOriginals, Finset.sum_filter]

end TalagrandThreshold.Selector

end

end OAI

-- ---- platform node ----
open OAI OAI.TalagrandThreshold OAI.TalagrandThreshold.Selector
open scoped BigOperators Classical


theorem solution : type_of% @_root_.OAI.TalagrandThreshold.Selector.selected_cost_group_by_endpoint := @_root_.OAI.TalagrandThreshold.Selector.selected_cost_group_by_endpoint
