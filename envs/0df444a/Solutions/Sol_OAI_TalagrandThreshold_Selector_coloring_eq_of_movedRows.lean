-- Prove2me | solution 1 for OAI.TalagrandThreshold.Selector.coloring_eq_of_movedRows
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T13:37:06.906035+00:00
-- url     : https://prove2.me/submissions/ea27a106-560e-4140-8f1a-be3c9f231c4c

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ExpectationThreshold/SelectorCountingEncoding.lean:L22-L46
-- (upload_full_project.md Phase 4): solution for node OAI.TalagrandThreshold.Selector.coloring_eq_of_movedRows. The node keeps its source
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

-- ---- from OAI.Combinatorics.ExpectationThreshold.SelectorCountingEncoding ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
# Reconstruction from the actual changed rows

For an earlier coloring, every point outside the changed rows retains its final
color. Inside a changed row its original color is recorded. Thus the changed
subsets and their original labels determine the entire original coloring.
-/

noncomputable section

namespace TalagrandThreshold.Selector

variable {α : Type*} [Fintype α] [DecidableEq α] {s : ℕ}

omit [DecidableEq α] in
/-- An original coloring is reconstructed from its changed rows and the
original labels on those rows. No disjointness of ambient row supersets is used. -/
theorem coloring_eq_of_movedRows
    {a b z : Coloring α s} (ha : Earlier a z) (hb : Earlier b z)
    (hrows : ∀ i, movedRow a z i = movedRow b z i)
    (hlabels : ∀ i x, x ∈ movedRow a z i → a x = b x) : a = b := by
  funext x
  by_cases hxa : z x < a x
  · let i : Fin s := ⟨(z x).val,
      Nat.lt_of_lt_of_le hxa (Nat.le_of_lt_succ (a x).isLt)⟩
    apply hlabels i x
    simp only [movedRow, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨rfl, hxa⟩
  · have haeq : a x = z x := le_antisymm (le_of_not_gt hxa) (ha x)
    have hxb : ¬ z x < b x := by
      intro hxb
      let i : Fin s := ⟨(z x).val,
        Nat.lt_of_lt_of_le hxb (Nat.le_of_lt_succ (b x).isLt)⟩
      have hx : x ∈ movedRow b z i := by
        simp only [movedRow, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨rfl, hxb⟩
      rw [← hrows i] at hx
      exact hxa (Finset.mem_filter.mp hx).2.2
    exact haeq.trans (le_antisymm (le_of_not_gt hxb) (hb x)).symm

end TalagrandThreshold.Selector

end

end OAI

-- ---- platform node ----
open OAI OAI.TalagrandThreshold OAI.TalagrandThreshold.Selector


theorem solution : type_of% @_root_.OAI.TalagrandThreshold.Selector.coloring_eq_of_movedRows := @_root_.OAI.TalagrandThreshold.Selector.coloring_eq_of_movedRows
