-- Prove2me | solution 1 for OAI.TalagrandThreshold.Selector.selected_endpoint_cost_grouped
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T14:09:12.583676+00:00
-- url     : https://prove2.me/submissions/12b75f65-b31b-4a8e-991e-4c5ebd1c1d89

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ExpectationThreshold/SelectorGlobalCost.lean:L57-L76
-- (upload_full_project.md Phase 4): solution for node OAI.TalagrandThreshold.Selector.selected_endpoint_cost_grouped. The node keeps its source
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

/-- Grouping by the actual full profile loses no original coloring. -/
theorem selected_endpoint_cost_grouped (mu : MassFamily F)
    (z : Coloring α s) (f : Coloring α s → ℝ) :
    (∑ a ∈ selectedOriginals mu z, f a) =
      ∑ n ∈ selectedProfiles mu z, ∑ a ∈ groupOriginals mu z n, f a := by
  classical
  have hgroup (n : Profile s) :
      (selectedOriginals mu z).filter (fun a => profile a z = n) =
        groupOriginals mu z n := by
    ext a
    simp [selectedOriginals, groupOriginals, and_assoc]
  symm
  calc
    (∑ n ∈ selectedProfiles mu z, ∑ a ∈ groupOriginals mu z n, f a) =
        ∑ n ∈ selectedProfiles mu z,
          ∑ a ∈ (selectedOriginals mu z).filter (fun a => profile a z = n), f a := by
      simp only [hgroup]
    _ = ∑ a ∈ selectedOriginals mu z, f a :=
      Finset.sum_fiberwise_of_maps_to
        (fun a ha => Finset.mem_image.mpr ⟨a, ha, rfl⟩) f

end TalagrandThreshold.Selector

end

end OAI

-- ---- platform node ----
open OAI OAI.TalagrandThreshold OAI.TalagrandThreshold.Selector
open scoped BigOperators Classical


theorem solution : type_of% @_root_.OAI.TalagrandThreshold.Selector.selected_endpoint_cost_grouped := @_root_.OAI.TalagrandThreshold.Selector.selected_endpoint_cost_grouped
