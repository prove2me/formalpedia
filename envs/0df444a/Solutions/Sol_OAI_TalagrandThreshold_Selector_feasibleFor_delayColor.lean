-- Prove2me | solution 1 for OAI.TalagrandThreshold.Selector.feasibleFor_delayColor
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T13:46:49.611303+00:00
-- url     : https://prove2.me/submissions/81ceb0e2-a4a4-4af9-8687-eaa06e409bb2

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ExpectationThreshold/SelectorDelayFeasibility.lean:L64-L91
-- (upload_full_project.md Phase 4): solution for node OAI.TalagrandThreshold.Selector.feasibleFor_delayColor. The node keeps its source
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
import Theorems.Thm_OAI_TalagrandThreshold_Selector_Admissible_erase_one
import Theorems.Thm_OAI_TalagrandThreshold_Selector_prefix_delayColor_self

-- ---- from OAI.Combinatorics.ExpectationThreshold.SelectorDelay ----
namespace OAI

/-!
# Delaying one moved coordinate by one color

When a moved coordinate has final color `i`, replacing it by `i.succ` removes
exactly that coordinate from the prefixSet at cut `i`. Every other cut stays
unchanged, and total movement decreases by one.
-/

noncomputable section

open scoped BigOperators

namespace TalagrandThreshold.Selector

variable {α : Type*} [Fintype α] [DecidableEq α] {s : ℕ}

omit [Fintype α] in
theorem delayColor_apply_of_ne (z : Coloring α s) (x : α) (i : Fin s)
    (y : α) (hy : y ≠ x) : delayColor z x i y = z y := by
  simp [delayColor, hy]

theorem prefix_delayColor_of_ne (z : Coloring α s) (x : α) (i j : Fin s)
    (hx : (z x).val = i.val) (hji : j ≠ i) :
    prefixSet (delayColor z x i) j = prefixSet z j := by
  ext y
  by_cases hy : y = x
  · subst y
    have hvals : j.val ≠ i.val := fun h => hji (Fin.ext h)
    simp only [prefixSet, Finset.mem_filter, Finset.mem_univ, true_and,
      delayColor_apply_self]
    change i.val + 1 ≤ j.val ↔ (z x).val ≤ j.val
    omega
  · simp only [prefixSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [delayColor_apply_of_ne z x i y hy]

/-- Exactly one crossing disappears at the affected cut. -/
theorem crossings_delayColor_self (a z : Coloring α s) (x : α) (i : Fin s)
    (hx : (z x).val = i.val) (hmove : (z x).val < (a x).val) :
    crossings a (delayColor z x i) i + 1 = crossings a z i := by
  unfold crossings
  rw [prefix_delayColor_self z x i hx, Finset.erase_sdiff_comm]
  apply Finset.card_erase_add_one
  simp only [Finset.mem_sdiff, prefixSet, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor <;> omega

theorem crossings_delayColor_of_ne (a z : Coloring α s) (x : α) (i j : Fin s)
    (hx : (z x).val = i.val) (hji : j ≠ i) :
    crossings a (delayColor z x i) j = crossings a z j := by
  unfold crossings
  rw [prefix_delayColor_of_ne z x i j hx hji]

end TalagrandThreshold.Selector

end

end OAI

-- ---- from OAI.Combinatorics.ExpectationThreshold.SelectorDelayFeasibility ----
namespace OAI

/-!
# Feasibility after delaying one color

Removing a point from a tested prefixSet subtracts exactly its truncated weight
from the excess. If that point is not heavy, the heavy-set condition survives;
the crossing count decreases by one, so the same cutoff remains admissible.
The other tests and their cutoffs are unchanged.
-/

noncomputable section

open scoped BigOperators

namespace TalagrandThreshold.Selector

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- An actual one-step delay preserves all tests for the same family member.
At the affected scale it uses the supplied cutoff; all other cutoffs are the
ones already supplied by `hfeasible`. -/
theorem feasibleFor_delayColor {F : Family α} (mu : MassFamily F) {s : ℕ}
    (a z : Coloring α s) (H : ↥F) (hfeasible : FeasibleFor mu a z H)
    (x : α) (i : Fin s) (hx : (z x).val = i.val)
    (hmove : (z x).val < (a x).val) (ε : ℝ)
    (hε : Admissible (mu.weight H) (prefixSet z i)
      (crossings a z i : ℝ) (dscale i) ε)
    (hweight : mu.weight H x ≤ ε) :
    FeasibleFor mu a (delayColor z x i) H := by
  intro j
  by_cases hji : j = i
  · subst j
    refine ⟨ε, ?_⟩
    rw [prefix_delayColor_self z x i hx]
    have hmem : x ∈ prefixSet z i := by simp [prefixSet, hx]
    have hcount : (crossings a (delayColor z x i) i : ℝ) + 1 =
        (crossings a z i : ℝ) := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        congrArg (fun k : ℕ => (k : ℝ))
          (crossings_delayColor_self a z x i hx hmove)
    exact hε.erase_one hmem hweight hcount
  · obtain ⟨u, hu⟩ := hfeasible j
    refine ⟨u, ?_⟩
    rw [prefix_delayColor_of_ne z x i j hx hji,
      crossings_delayColor_of_ne a z x i j hx hji]
    exact hu

end TalagrandThreshold.Selector

end

end OAI

-- ---- platform node ----
open OAI OAI.TalagrandThreshold OAI.TalagrandThreshold.Selector
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TalagrandThreshold.Selector.feasibleFor_delayColor := @_root_.OAI.TalagrandThreshold.Selector.feasibleFor_delayColor
