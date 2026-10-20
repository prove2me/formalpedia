-- Prove2me | solution 1 for OAI.TalagrandThreshold.Selector.selected_total_cost_lt_one_twentieth
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T14:13:28.340255+00:00
-- url     : https://prove2.me/submissions/185d76fd-de5c-4d23-bec8-8beebb7c26db

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ExpectationThreshold/SelectorGlobalCost.lean:L131-L148
-- (upload_full_project.md Phase 4): solution for node OAI.TalagrandThreshold.Selector.selected_total_cost_lt_one_twentieth. The node keeps its source
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
import Theorems.Thm_OAI_TalagrandThreshold_Selector_selected_cost_group_by_endpoint
import Theorems.Thm_OAI_TalagrandThreshold_Selector_selected_endpoint_cost_lt

-- ---- from OAI.Combinatorics.ExpectationThreshold.ProbabilityColors ----
namespace OAI

/-!
# The actual independent color law

Colors are indexed from zero; their numerical levels are one larger. The
first `s` colors have masses `256^(i+1) * p`, and the final color carries the
remaining mass. All laws below use these literal weights.
-/

open scoped BigOperators
noncomputable section

namespace TalagrandThreshold

variable {α : Type*} [Fintype α]

variable [DecidableEq α]

/-- Summing over actual colorings gives total mass one. -/
theorem sum_colorMass (p : ℝ) (s : ℕ) :
    ∑ a : Coloring α s, colorMass p s a = 1 := by
  classical
  unfold colorMass
  rw [← Fintype.prod_sum (fun (_ : α) (c : Color s) => colorProb p s c)]
  simp only [sum_colorProb, Finset.prod_const_one]

end TalagrandThreshold

end

end OAI

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

/-- The complete selected cost is strictly below one twentieth. All grouping,
counting, reconstruction, entropy, and probability facts are proved above. -/
theorem selected_total_cost_lt_one_twentieth (mu : MassFamily F)
    (p : ℝ) (s : ℕ) (hp : 0 < p) (hs : p * scaleSum s ≤ 1 / 2) :
    (∑ a ∈ (Finset.univ : Finset (Coloring α s)).filter (Bad mu),
      ∑ z ∈ selectedMoves mu a, colorMass p s a * p ^ (changes a z).card) < 1 / 20 := by
  classical
  rw [selected_cost_group_by_endpoint]
  calc
    (∑ z : Coloring α s,
        ∑ a ∈ selectedOriginals mu z, colorMass p s a * p ^ (changes a z).card) <
        ∑ z : Coloring α s, colorMass p s z * (1 / 20) := by
      apply Finset.sum_lt_sum_of_nonempty
        ⟨(fun _ => Fin.last s), Finset.mem_univ _⟩
      intro z _
      exact selected_endpoint_cost_lt mu p s hp hs z
    _ = 1 / 20 := by
      rw [← Finset.sum_mul, sum_colorMass, one_mul]

end TalagrandThreshold.Selector

end

end OAI

-- ---- platform node ----
open OAI OAI.TalagrandThreshold OAI.TalagrandThreshold.Selector
open scoped BigOperators Classical


theorem solution : type_of% @_root_.OAI.TalagrandThreshold.Selector.selected_total_cost_lt_one_twentieth := @_root_.OAI.TalagrandThreshold.Selector.selected_total_cost_lt_one_twentieth
