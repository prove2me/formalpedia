-- Prove2me | solution 1 for OAI.TalagrandThreshold.Selector.exists_short_right_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T13:50:29.649783+00:00
-- url     : https://prove2.me/submissions/6852754f-aa1e-4f63-b63f-4fbc1056d8f7

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ExpectationThreshold/SelectorTruncationSlope.lean:L28-L46
-- (upload_full_project.md Phase 4): solution for node OAI.TalagrandThreshold.Selector.exists_short_right_cutoff. The node keeps its source
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

omit [DecidableEq α] in
/-- There is a strictly larger cutoff, at most one, that does not pass any
weight strictly above the current cutoff. -/
theorem exists_short_right_cutoff (w : α → ℝ) {ε : ℝ} (hε : ε < 1) :
    ∃ u : ℝ, ε < u ∧ u ≤ 1 ∧ ∀ x, ε < w x → u ≤ w x := by
  classical
  let S : Finset ℝ := insert 1 ((heavySet w ε).image w)
  have hS : S.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
  refine ⟨S.min' hS, ?_, S.min'_le 1 (Finset.mem_insert_self _ _), ?_⟩
  · apply (Finset.lt_min'_iff S hS).2
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact hε
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      exact mem_heavySet.mp hx
  · intro x hx
    apply S.min'_le (w x)
    exact Finset.mem_insert_of_mem
      (Finset.mem_image.mpr ⟨x, mem_heavySet.mpr hx, rfl⟩)

end TalagrandThreshold.Selector

end OAI

-- ---- platform node ----
open OAI OAI.TalagrandThreshold OAI.TalagrandThreshold.Selector
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TalagrandThreshold.Selector.exists_short_right_cutoff := @_root_.OAI.TalagrandThreshold.Selector.exists_short_right_cutoff
