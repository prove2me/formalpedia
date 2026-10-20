-- Prove2me | solution 1 for OAI.TalagrandThreshold.Selector.Admissible.erase_one
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T13:46:01.547623+00:00
-- url     : https://prove2.me/submissions/11e00411-b664-495f-ad45-5ff0fb6915ed

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ExpectationThreshold/SelectorDelayFeasibility.lean:L45-L62
-- (upload_full_project.md Phase 4): solution for node OAI.TalagrandThreshold.Selector.Admissible.erase_one. The node keeps its source
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

theorem truncatedExcess_erase (mu : α → ℝ) (A : Finset α) (d u : ℝ)
    (x : α) (hx : x ∈ A) :
    truncatedExcess mu (A.erase x) d u =
      truncatedExcess mu A d u - min (mu x) u := by
  classical
  unfold truncatedExcess
  calc
    (∑ y, min (mu y) u * ((if y ∈ A.erase x then 1 else 0) - (1 - d))) =
        ∑ y, (min (mu y) u * ((if y ∈ A then 1 else 0) - (1 - d)) -
          if y = x then min (mu x) u else 0) := by
      apply Finset.sum_congr rfl
      intro y hy
      by_cases hyx : y = x
      · subst y
        simp only [Finset.notMem_erase, ite_false, hx, ite_true]
        ring
      · simp [Finset.mem_erase, hyx]
    _ = (∑ y, min (mu y) u * ((if y ∈ A then 1 else 0) - (1 - d))) -
        min (mu x) u := by
      rw [Finset.sum_sub_distrib]
      simp

/-- The same cutoff works after deleting a non-heavy point and reducing the
crossing parameter by one. No maximality assumption on the cutoff is used. -/
theorem Admissible.erase_one {mu : α → ℝ} {A : Finset α} {m m' d u : ℝ}
    (hu : Admissible mu A m d u) {x : α} (hx : x ∈ A)
    (hxu : mu x ≤ u) (hm : m' + 1 = m) :
    Admissible mu (A.erase x) m' d u := by
  refine ⟨hu.1, hu.2.1, ?_, ?_⟩
  · intro y hy
    refine Finset.mem_erase.mpr ⟨?_, hu.2.2.1 y hy⟩
    intro hyx
    subst y
    exact (not_lt_of_ge hxu) hy
  · rw [truncatedExcess_erase mu A d u x hx]
    calc
      m' * u = m * u - u := by rw [← hm]; ring
      _ ≤ truncatedExcess mu A d u - u := sub_le_sub_right hu.2.2.2 u
      _ ≤ truncatedExcess mu A d u - min (mu x) u :=
        sub_le_sub_left (min_le_right (mu x) u) _

end TalagrandThreshold.Selector

end

end OAI

-- ---- platform node ----
open OAI OAI.TalagrandThreshold OAI.TalagrandThreshold.Selector
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TalagrandThreshold.Selector.Admissible.erase_one := @_root_.OAI.TalagrandThreshold.Selector.Admissible.erase_one
