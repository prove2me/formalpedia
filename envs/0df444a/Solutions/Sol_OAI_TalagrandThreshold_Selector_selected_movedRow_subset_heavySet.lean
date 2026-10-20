-- Prove2me | solution 1 for OAI.TalagrandThreshold.Selector.selected_movedRow_subset_heavySet
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T13:48:43.77878+00:00
-- url     : https://prove2.me/submissions/883b4487-6e8e-43fa-9cdd-285b3c7f88ab

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ExpectationThreshold/SelectorReconstruction.lean:L19-L44
-- (upload_full_project.md Phase 4): solution for node OAI.TalagrandThreshold.Selector.selected_movedRow_subset_heavySet. The node keeps its source
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
import Theorems.Thm_OAI_TalagrandThreshold_Selector_changes_delayColor_subset
import Theorems.Thm_OAI_TalagrandThreshold_Selector_feasibleFor_delayColor
import Theorems.Thm_OAI_TalagrandThreshold_Selector_movement_delayColor_add_one

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

omit [Fintype α] in
theorem earlier_delayColor (a z : Coloring α s) (x : α) (i : Fin s)
    (hx : (z x).val = i.val) (hmove : (z x).val < (a x).val)
    (hearlier : Earlier a z) : Earlier a (delayColor z x i) := by
  intro y
  by_cases hy : y = x
  · subst y
    rw [delayColor_apply_self]
    change i.val + 1 ≤ (a x).val
    omega
  · rw [delayColor_apply_of_ne z x i y hy]
    exact hearlier y

end TalagrandThreshold.Selector

end

end OAI

-- ---- from OAI.Combinatorics.ExpectationThreshold.SelectorReconstruction ----
namespace OAI

/-!
# Minimal moves reconstruct inside the heavy sets

The family member in this theorem is any member witnessing feasibility of the
selected endpoint. It need not be the member restricting the changed set in
the minimization. This permits one witness to be used for an entire profile.
-/

noncomputable section

namespace TalagrandThreshold.Selector

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Every point moved into row `i` is heavy for every admissible cutoff of any
common feasibility witness. Otherwise its actual color can be delayed by one,
preserving that witness and contradicting minimal total movement. -/
theorem selected_movedRow_subset_heavySet {F : Family α} (mu : MassFamily F)
    {s : ℕ} (a z : Coloring α s) (hselected : Selected mu a z)
    (H : ↥F) (hfeasible : FeasibleFor mu a z H) (i : Fin s) (ε : ℝ)
    (hε : Admissible (mu.weight H) (prefixSet z i)
      (crossings a z i : ℝ) (dscale i) ε) :
    movedRow a z i ⊆ heavySet (mu.weight H) ε := by
  classical
  intro x hxrow
  obtain ⟨hx, hmove⟩ := (Finset.mem_filter.mp hxrow).2
  apply mem_heavySet.mpr
  by_contra hheavy
  have hweight : mu.weight H x ≤ ε := le_of_not_gt hheavy
  obtain ⟨H₀, hbounded, hminimal⟩ := hselected
  have hbounded' : BoundedFeasible mu a H₀ (delayColor z x i) := by
    refine ⟨⟨earlier_delayColor a z x i hx hmove hbounded.1.1, ?_⟩, ?_⟩
    · exact ⟨H, feasibleFor_delayColor mu a z H hfeasible x i hx hmove ε hε hweight⟩
    · intro y hy
      exact hbounded.2 (changes_delayColor_subset a z x i hx hy)
  have hmin := hminimal (delayColor z x i) hbounded'
  have hdec := movement_delayColor_add_one a z x i hx hmove
  have hstrict : movement a (delayColor z x i) < movement a z :=
    lt_of_lt_of_eq (Nat.lt_succ_self _) hdec
  exact (not_lt_of_ge hmin) hstrict

end TalagrandThreshold.Selector

end

end OAI

-- ---- platform node ----
open OAI OAI.TalagrandThreshold OAI.TalagrandThreshold.Selector


theorem solution : type_of% @_root_.OAI.TalagrandThreshold.Selector.selected_movedRow_subset_heavySet := @_root_.OAI.TalagrandThreshold.Selector.selected_movedRow_subset_heavySet
