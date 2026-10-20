-- Prove2me | solution 1 for OAI.TalagrandThreshold.half_mass_of_weighted_average_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T13:26:27.986981+00:00
-- url     : https://prove2.me/submissions/c4373ca2-6ed6-49a4-bee9-50ff61996aa9

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ExpectationThreshold/RoundingLowerBound.lean:L26-L52
-- (upload_full_project.md Phase 4): solution for node OAI.TalagrandThreshold.half_mass_of_weighted_average_le. The node keeps its source
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

-- ---- from OAI.Combinatorics.ExpectationThreshold.RoundingLowerBound ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

/-!
# The deterministic lower bound for rounding

A weighted average at most two places at least half the mass on subsets with
average at most four. On those subsets the quotient-of-powers product is at
least one, yielding the lower bound one quarter for the full product score.
This statement is pointwise in the coloring and needs no independence premise.
-/

open scoped BigOperators

namespace TalagrandThreshold

/-- Finite weighted Markov inequality in the form used by rounding. -/
theorem half_mass_of_weighted_average_le {β : Type*} (T : Finset β)
    (w v : β → ℝ) (hw : ∀ i ∈ T, 0 ≤ w i) (hv : ∀ i ∈ T, 0 ≤ v i)
    (hmean : (∑ i ∈ T, w i * v i) ≤ 2 * (∑ i ∈ T, w i)) :
    (∑ i ∈ T, w i) / 2 ≤ ∑ i ∈ T.filter (fun i => v i ≤ 4), w i := by
  classical
  have hpoint (i : β) (hi : i ∈ T) :
      4 * w i ≤ w i * v i + 4 * (if v i ≤ 4 then w i else 0) := by
    by_cases hgood : v i ≤ 4
    · simp only [ite_eq_left hgood]
      have hnonneg := mul_nonneg (hw i hi) (hv i hi)
      linarith
    · simp only [ite_eq_right hgood, mul_zero, add_zero]
      calc
        4 * w i = w i * 4 := mul_comm _ _
        _ ≤ w i * v i :=
          mul_le_mul_of_nonneg_left (le_of_lt (lt_of_not_ge hgood)) (hw i hi)
  have hsum : 4 * (∑ i ∈ T, w i) ≤
      (∑ i ∈ T, w i * v i) + 4 * (∑ i ∈ T.filter (fun i => v i ≤ 4), w i) := by
    calc
      _ = ∑ i ∈ T, 4 * w i := Finset.mul_sum _ _ _
      _ ≤ ∑ i ∈ T, (w i * v i + 4 * (if v i ≤ 4 then w i else 0)) :=
        Finset.sum_le_sum hpoint
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_filter,
          mul_ite, mul_zero]
  linarith

variable {α : Type*} [Fintype α] [DecidableEq α]

end TalagrandThreshold

end OAI

-- ---- platform node ----
open OAI OAI.TalagrandThreshold
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TalagrandThreshold.half_mass_of_weighted_average_le := @_root_.OAI.TalagrandThreshold.half_mass_of_weighted_average_le
