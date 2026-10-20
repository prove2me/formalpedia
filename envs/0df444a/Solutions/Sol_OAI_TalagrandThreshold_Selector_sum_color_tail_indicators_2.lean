-- Prove2me | solution 2 for OAI.TalagrandThreshold.Selector.sum_color_tail_indicators
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T14:14:22.535859+00:00
-- url     : https://prove2.me/submissions/c928b214-ec35-4c92-9d4f-ecbf1643022e

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ExpectationThreshold/SelectorAverageColor.lean:L21-L35
-- (upload_full_project.md Phase 4): solution for node OAI.TalagrandThreshold.Selector.sum_color_tail_indicators. The node keeps its source
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

-- ---- from OAI.Combinatorics.ExpectationThreshold.SelectorAverageColor ----
namespace OAI

/-!
# Average color from simultaneous capture

An integer color is one plus the number of preceding prefixes it misses.
Summing this finite identity against the actual probability mass gives the
mean-color identity. A captured coloring has the same family member at
every scale, so the geometric sum of its missed masses is at most one.
-/

namespace TalagrandThreshold.Selector

open scoped BigOperators

/-- Count the prefixes strictly below a color, including the final color. -/
theorem sum_color_tail_indicators {s : ℕ} (c : Color s) :
    (∑ i : Fin s, if i.val < c.val then (1 : ℝ) else 0) = (c.val : ℝ) := by
  have hcs : c.val ≤ s := Nat.le_of_lt_succ c.isLt
  have hfilter : (Finset.range s).filter (fun i => i < c.val) = Finset.range c.val := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨And.right, fun hi => ⟨hi.trans_le hcs, hi⟩⟩
  calc
    (∑ i : Fin s, if i.val < c.val then (1 : ℝ) else 0) =
        ∑ i ∈ Finset.range s, if i < c.val then (1 : ℝ) else 0 :=
      Fin.sum_univ_eq_sum_range (fun i => if i < c.val then (1 : ℝ) else 0) s
    _ = (((Finset.range s).filter (fun i => i < c.val)).card : ℝ) :=
      Finset.sum_boole _ _
    _ = (c.val : ℝ) := by rw [hfilter, Finset.card_range]

variable {α : Type*} [Fintype α] [DecidableEq α]

end TalagrandThreshold.Selector

end OAI

-- ---- platform node ----
open OAI OAI.TalagrandThreshold OAI.TalagrandThreshold.Selector
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TalagrandThreshold.Selector.sum_color_tail_indicators := @_root_.OAI.TalagrandThreshold.Selector.sum_color_tail_indicators
