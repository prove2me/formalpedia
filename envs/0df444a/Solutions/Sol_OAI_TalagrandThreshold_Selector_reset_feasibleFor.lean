-- Prove2me | solution 1 for OAI.TalagrandThreshold.Selector.reset_feasibleFor
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T13:31:26.386115+00:00
-- url     : https://prove2.me/submissions/72b37b62-4b06-4a70-b16a-d31597e81ad3

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ExpectationThreshold/SelectorFeasibility.lean:L48-L66
-- (upload_full_project.md Phase 4): solution for node OAI.TalagrandThreshold.Selector.reset_feasibleFor. The node keeps its source
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

-- ---- from OAI.Combinatorics.ExpectationThreshold.SelectorFeasibility ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e

namespace OAI

/-!
# Feasible minima and the actual containment cover

Resetting an original family member to the first color proves existence of
a bounded feasible move. Minimization itself retains the unrestricted
feasibility witness from `Feasible`; the witness need not be that member.
All retained minima contribute their actual changed sets to a cover.
-/

noncomputable section

open scoped BigOperators

namespace TalagrandThreshold.Selector

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {F : Family α} {s : ℕ}

/-- The reset uses this one member as a witness, with every cutoff zero. -/
theorem reset_feasibleFor (mu : MassFamily F) (a : Coloring α s) (H₀ : ↥F) :
    FeasibleFor mu a (reset a H₀) H₀ := by
  classical
  intro i
  refine ⟨0, le_rfl, zero_le_one, ?_, ?_⟩
  · intro x hpos
    have hx : x ∈ H₀.val := by
      by_contra hnot
      rw [mu.supported H₀ x hnot] at hpos
      exact (lt_irrefl (0 : ℝ)) hpos
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ x, ?_⟩
    change (if x ∈ H₀.val then (0 : Color s) else a x).val ≤ i.val
    rw [ite_eq_left hx]
    exact Nat.zero_le i.val
  · have hmin : ∀ x, min (mu.weight H₀ x) (0 : ℝ) = 0 :=
      fun x => min_eq_right (mu.nonneg H₀ x)
    simp only [truncatedExcess, hmin, zero_mul, Finset.sum_const_zero, mul_zero, le_refl]

end TalagrandThreshold.Selector

end

end OAI

-- ---- platform node ----
open OAI OAI.TalagrandThreshold OAI.TalagrandThreshold.Selector
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TalagrandThreshold.Selector.reset_feasibleFor := @_root_.OAI.TalagrandThreshold.Selector.reset_feasibleFor
