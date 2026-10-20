-- Prove2me | solution 1 for OAI.TalagrandThreshold.Selector.prefix_delayColor_self
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T13:44:31.704855+00:00
-- url     : https://prove2.me/submissions/9fc3e243-fd48-46e5-8711-00f6a2a576bf

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ExpectationThreshold/SelectorDelay.lean:L65-L87
-- (upload_full_project.md Phase 4): solution for node OAI.TalagrandThreshold.Selector.prefix_delayColor_self. The node keeps its source
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

theorem prefix_delayColor_self (z : Coloring α s) (x : α) (i : Fin s)
    (_hx : (z x).val = i.val) :
    prefixSet (delayColor z x i) i = (prefixSet z i).erase x := by
  ext y
  by_cases hy : y = x
  · subst y
    simp only [prefixSet, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_erase, delayColor_apply_self]
    simp
  · constructor
    · intro hnew
      have hle : (delayColor z x i y).val ≤ i.val :=
        (Finset.mem_filter.mp hnew).2
      rw [delayColor_apply_of_ne z x i y hy] at hle
      exact Finset.mem_erase.mpr
        ⟨hy, Finset.mem_filter.mpr ⟨Finset.mem_univ y, hle⟩⟩
    · intro hold
      have hmem : y ∈ prefixSet z i := (Finset.mem_erase.mp hold).2
      have hle : (z y).val ≤ i.val := (Finset.mem_filter.mp hmem).2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ y, ?_⟩
      rw [delayColor_apply_of_ne z x i y hy]
      exact hle

end TalagrandThreshold.Selector

end

end OAI

-- ---- platform node ----
open OAI OAI.TalagrandThreshold OAI.TalagrandThreshold.Selector
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TalagrandThreshold.Selector.prefix_delayColor_self := @_root_.OAI.TalagrandThreshold.Selector.prefix_delayColor_self
