-- Prove2me | solution 1 for OAI.LeanBlast.SecondKahnKalai.bernoulliProbability_subset
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:17:52.184452+00:00
-- url     : https://prove2.me/submissions/9b83c38e-3b9d-4415-bd24-5131d292dee4

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GraphThreshold/FiniteProbability.lean:L242-L271
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.SecondKahnKalai.bernoulliProbability_subset. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.List.Pairwise
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.Monotone
import Definitions.Def_SecondKahnKalai
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphEncoding
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphProbability
import Definitions.Def_OAI_Combinatorics_GraphThreshold_EmbeddingExtension
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphSupport
import Definitions.Def_OAI_Combinatorics_GraphThreshold_Basic
import Definitions.Def_OAI_Combinatorics_GraphThreshold_FiniteProbability

-- ---- from OAI.Combinatorics.GraphThreshold.FiniteProbability ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace LeanBlast.SecondKahnKalai

namespace FiniteLaw

variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

end FiniteLaw

variable {X : Type*} [Fintype X] [DecidableEq X]

theorem subset_indicator_product (A W : Finset X) :
    (if A ⊆ W then (1 : ℝ) else 0) =
      ∏ x, (if x ∈ A then (if x ∈ W then (1 : ℝ) else 0) else 1) := by
  rw [Fintype.prod_ite_mem, Finset.prod_boole]
  rfl

theorem bernoulliProbability_subset (p : ℝ) (A : Finset X) :
    bernoulliProbability p (fun W => A ⊆ W) = p ^ A.card := by
  trans bernoulliExpectation p (fun W =>
    ∏ x, (if x ∈ A then (if x ∈ W then (1 : ℝ) else 0) else 1))
  · unfold bernoulliProbability bernoulliExpectation
    apply Finset.sum_congr rfl
    intro W _
    dsimp only
    by_cases hs : A ⊆ W
    · have hh := (subset_indicator_product A W).symm
      simp only [ite_eq_left hs] at hh
      rw [hh]
      simp [hs]
    · have hh := (subset_indicator_product A W).symm
      simp only [ite_eq_right hs] at hh
      rw [hh]
      simp [hs]
  calc
    bernoulliExpectation p (fun W =>
        ∏ x, (if x ∈ A then (if x ∈ W then (1 : ℝ) else 0) else 1)) =
        ∏ x, (p * (if x ∈ A then (1 : ℝ) else 1) +
          (1 - p) * (if x ∈ A then (0 : ℝ) else 1)) := by
      simpa only [decide_eq_true_eq, Bool.true_eq, ite_true, Bool.false_eq_true, ite_false] using
        bernoulliExpectation_product p
          (fun x b => if x ∈ A then (if b then (1 : ℝ) else 0) else 1)
    _ = ∏ x, (if x ∈ A then p else 1) := by
      apply Finset.prod_congr rfl
      intro x _
      by_cases hx : x ∈ A <;> simp [hx]
    _ = p ^ A.card := by rw [Fintype.prod_ite_mem]; simp

end LeanBlast.SecondKahnKalai

end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.SecondKahnKalai
open scoped BigOperators
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.LeanBlast.SecondKahnKalai.bernoulliProbability_subset := @_root_.OAI.LeanBlast.SecondKahnKalai.bernoulliProbability_subset
