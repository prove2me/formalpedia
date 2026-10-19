-- Prove2me | solution 2 for OAI.ReflexiveFixedPoints.WeightedTree.sum_pathWeight_parent
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T17:11:22.225393+00:00
-- url     : https://prove2.me/submissions/544f04d4-2694-4583-a356-25c0a6a552ab

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Nonexpansive/WeightedTree.lean:L96-L110
-- (upload_full_project.md Phase 4): solution for node OAI.ReflexiveFixedPoints.WeightedTree.sum_pathWeight_parent. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ReflexiveFixedPoints
import Definitions.Def_OAI_Analysis_Nonexpansive_Model
import Definitions.Def_OAI_Analysis_Nonexpansive_Basic
import Definitions.Def_OAI_Analysis_Nonexpansive_WeakCompactness
import Definitions.Def_OAI_Analysis_Nonexpansive_ScalarNormalization
import Definitions.Def_OAI_Analysis_Nonexpansive_WeakMetric
import Definitions.Def_OAI_Analysis_Nonexpansive_OrderedTree
import Definitions.Def_OAI_Analysis_Nonexpansive_WeightedTree

-- ---- from OAI.Analysis.Nonexpansive.WeightedTree ----
namespace OAI

/-!
# Positive edge weights and the actual path mass

Path mass is defined recursively from the parent maps and edge weights.
Its normalization and its mass on every descendant block are consequences
of the normalization at each parent.
-/

open scoped BigOperators

namespace ReflexiveFixedPoints

/-- Partition a finite sum by the fibers of a function. -/
theorem sum_fiber_partition {A B M : Type*} [Fintype A] [Fintype B]
    [DecidableEq B] [AddCommMonoid M] (f : A → B) (g : A → M) :
    (∑ b, ∑ a ∈ Finset.univ.filter (fun a => f a = b), g a) = ∑ a, g a := by
  classical
  exact Finset.sum_fiberwise Finset.univ f g

/-- Regroup a weighted finite sum by the fibers of a function. -/
theorem sum_fiber_mul {A B R : Type*} [Fintype A] [Fintype B]
    [DecidableEq B] [NonUnitalNonAssocSemiring R]
    (f : A → B) (r : B → R) (g : A → R) :
    (∑ b, r b * (∑ a ∈ Finset.univ.filter (fun a => f a = b), g a)) =
      ∑ a, r (f a) * g a := by
  classical
  calc
    _ = ∑ b, ∑ a ∈ Finset.univ.filter (fun a => f a = b), r (f a) * g a := by
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      rw [(Finset.mem_filter.mp ha).2]
    _ = _ := sum_fiber_partition f _

namespace WeightedTree

variable {T : OrderedTree} (W : WeightedTree T)

/-- The parent map pushes the child path masses to the parent path masses. -/
theorem sum_pathWeight_parent (k : ℕ) (f : T.Node k → ℝ) :
    (∑ c, W.pathWeight (k + 1) c * f (T.parent k c)) =
      ∑ p, W.pathWeight k p * f p := by
  calc
    _ = ∑ c, (W.pathWeight k (T.parent k c) * f (T.parent k c)) * W.weight k c := by
      apply Finset.sum_congr rfl
      intro c _
      rw [W.pathWeight_succ]
      exact mul_right_comm (W.pathWeight k (T.parent k c)) (W.weight k c)
        (f (T.parent k c))
    _ = ∑ p, (W.pathWeight k p * f p) *
        (∑ c ∈ Finset.univ.filter (fun c => T.parent k c = p), W.weight k c) :=
      (sum_fiber_mul (T.parent k) (fun p => W.pathWeight k p * f p) (W.weight k)).symm
    _ = _ := by simp only [W.weight_sum, mul_one]

end WeightedTree
end ReflexiveFixedPoints

end OAI

-- ---- platform node ----
open OAI OAI.ReflexiveFixedPoints OAI.ReflexiveFixedPoints.WeightedTree
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.ReflexiveFixedPoints.WeightedTree.sum_pathWeight_parent := @_root_.OAI.ReflexiveFixedPoints.WeightedTree.sum_pathWeight_parent
