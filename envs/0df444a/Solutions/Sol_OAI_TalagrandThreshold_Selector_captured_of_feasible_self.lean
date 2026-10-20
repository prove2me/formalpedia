-- Prove2me | solution 1 for OAI.TalagrandThreshold.Selector.captured_of_feasible_self
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T13:36:21.855993+00:00
-- url     : https://prove2.me/submissions/b10e3171-5f66-4968-b1a1-a29548ee2dba

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ExpectationThreshold/SelectorFeasibility.lean:L167-L186
-- (upload_full_project.md Phase 4): solution for node OAI.TalagrandThreshold.Selector.captured_of_feasible_self. The node keeps its source
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
import Theorems.Thm_OAI_TalagrandThreshold_Selector_truncatedExcess_le_original

-- ---- from OAI.Combinatorics.ExpectationThreshold.SelectorDefinitionsLemmas ----
namespace OAI

/-! Elementary bounds on the literal truncation scales. -/

namespace TalagrandThreshold.Selector

theorem dscale_pos {s : ℕ} (i : Fin s) : 0 < dscale i := by
  exact inv_pos.mpr (pow_pos (by norm_num : (0 : ℝ) < 2) _)

theorem dscale_nonneg {s : ℕ} (i : Fin s) : 0 ≤ dscale i :=
  (dscale_pos i).le

end TalagrandThreshold.Selector

end OAI

-- ---- from OAI.Combinatorics.ExpectationThreshold.SelectorFeasibility ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
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

theorem originalExcess_eq_mass_sub (w : α → ℝ) (A : Finset α) (d : ℝ)
    (htotal : ∑ x, w x = 1) :
    (∑ x, w x * ((if x ∈ A then 1 else 0) - (1 - d))) =
      (∑ x ∈ A, w x) - (1 - d) := by
  classical
  calc
    (∑ x, w x * ((if x ∈ A then 1 else 0) - (1 - d))) =
        (∑ x, if x ∈ A then w x else 0) - (∑ x, w x) * (1 - d) := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro x _
      split_ifs <;> ring
    _ = (∑ x ∈ A, w x) - (1 - d) := by
      rw [Finset.sum_ite_mem_eq, htotal, one_mul]

/-- The actual feasibility witness is chosen once, before the scale index. -/
theorem captured_of_feasible_self {mu : MassFamily F} {a : Coloring α s}
    (h : Feasible mu a a) : Captured mu a := by
  classical
  obtain ⟨H, hH⟩ := h.2
  refine ⟨H, ?_⟩
  intro i
  obtain ⟨u, hu⟩ := hH i
  have htest : 0 ≤ truncatedExcess (mu.weight H) (prefixSet a i) (dscale i) u := by
    simpa [crossings] using hu.2.2.2
  have hfull : 0 ≤ (∑ x ∈ prefixSet a i, mu.weight H x) - (1 - dscale i) := by
    calc
      0 ≤ truncatedExcess (mu.weight H) (prefixSet a i) (dscale i) u := htest
      _ ≤ ∑ x, mu.weight H x *
          ((if x ∈ prefixSet a i then 1 else 0) - (1 - dscale i)) :=
        truncatedExcess_le_original (mu.weight H) (prefixSet a i) (dscale i) u
          (dscale_nonneg i) hu.2.2.1
      _ = (∑ x ∈ prefixSet a i, mu.weight H x) - (1 - dscale i) :=
        originalExcess_eq_mass_sub (mu.weight H) (prefixSet a i) (dscale i) (mu.total H)
  exact sub_nonneg.mp hfull

end TalagrandThreshold.Selector

end

end OAI

-- ---- platform node ----
open OAI OAI.TalagrandThreshold OAI.TalagrandThreshold.Selector
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TalagrandThreshold.Selector.captured_of_feasible_self := @_root_.OAI.TalagrandThreshold.Selector.captured_of_feasible_self
