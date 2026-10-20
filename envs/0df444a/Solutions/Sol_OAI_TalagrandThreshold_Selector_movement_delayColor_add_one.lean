-- Prove2me | solution 1 for OAI.TalagrandThreshold.Selector.movement_delayColor_add_one
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T13:45:20.913358+00:00
-- url     : https://prove2.me/submissions/67186173-2785-4475-bcb7-c62c75fba76d

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ExpectationThreshold/SelectorDelay.lean:L119-L140
-- (upload_full_project.md Phase 4): solution for node OAI.TalagrandThreshold.Selector.movement_delayColor_add_one. The node keeps its source
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

/-- The delay removes precisely one unit of total movement. -/
theorem movement_delayColor_add_one (a z : Coloring α s) (x : α) (i : Fin s)
    (hx : (z x).val = i.val) (hmove : (z x).val < (a x).val) :
    movement a (delayColor z x i) + 1 = movement a z := by
  let f : α → ℕ := fun y => (a y).val - (z y).val
  let g : α → ℕ := fun y => (a y).val - (delayColor z x i y).val
  have hrest : (∑ y ∈ Finset.univ.erase x, g y) =
      ∑ y ∈ Finset.univ.erase x, f y := by
    apply Finset.sum_congr rfl
    intro y hy
    have hne : y ≠ x := (Finset.mem_erase.mp hy).1
    dsimp only [g, f]
    rw [delayColor_apply_of_ne z x i y hne]
  have hpoint : g x + 1 = f x := by
    dsimp only [g, f]
    rw [delayColor_apply_self]
    change (a x).val - (i.val + 1) + 1 = (a x).val - (z x).val
    omega
  change (∑ y, g y) + 1 = ∑ y, f y
  rw [← Finset.sum_erase_add Finset.univ g (Finset.mem_univ x),
    ← Finset.sum_erase_add Finset.univ f (Finset.mem_univ x), hrest]
  omega

end TalagrandThreshold.Selector

end

end OAI

-- ---- platform node ----
open OAI OAI.TalagrandThreshold OAI.TalagrandThreshold.Selector
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TalagrandThreshold.Selector.movement_delayColor_add_one := @_root_.OAI.TalagrandThreshold.Selector.movement_delayColor_add_one
