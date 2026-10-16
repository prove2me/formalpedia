-- Prove2me | solution 1 for OAI.CliqueFreeIndependence.FiniteCoupling.shared_rejection
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:39:53.515612+00:00
-- url     : https://prove2.me/submissions/d6d0ed08-1e17-4e77-81c0-fa25102097fa

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/CliqueFree/FiniteCoupling.lean:L272-L334
-- (upload_full_project.md Phase 4): solution for node OAI.CliqueFreeIndependence.FiniteCoupling.shared_rejection. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CliqueFreeLog
import Definitions.Def_OAI_Combinatorics_CliqueFree_Numerical
import Definitions.Def_OAI_Combinatorics_CliqueFree_WeightedGraph
import Definitions.Def_OAI_Combinatorics_CliqueFree_Optimizer
import Definitions.Def_OAI_Combinatorics_CliqueFree_Lottery
import Definitions.Def_OAI_Combinatorics_CliqueFree_MultiplierLaw
import Definitions.Def_OAI_Combinatorics_CliqueFree_Deletion
import Definitions.Def_OAI_Combinatorics_CliqueFree_FiniteEntropy
import Definitions.Def_OAI_Combinatorics_CliqueFree_EdgeState
import Definitions.Def_OAI_Combinatorics_CliqueFree_SparseMultipliers
import Definitions.Def_OAI_Combinatorics_CliqueFree_TriangleState
import Definitions.Def_OAI_Combinatorics_CliqueFree_Projection
import Definitions.Def_OAI_Combinatorics_CliqueFree_Splitting
import Definitions.Def_OAI_Combinatorics_CliqueFree_Reach
import Definitions.Def_OAI_Combinatorics_CliqueFree_FiniteKernel
import Definitions.Def_OAI_Combinatorics_CliqueFree_LocalWalk
import Definitions.Def_OAI_Combinatorics_CliqueFree_WalkEntropy
import Definitions.Def_OAI_Combinatorics_CliqueFree_FiniteCoupling
import Theorems.Thm_OAI_CliqueFreeIndependence_FiniteCoupling_exists_threshold_law
import Theorems.Thm_OAI_CliqueFreeIndependence_FiniteCoupling_joint_of_trials

-- ---- from OAI.Combinatorics.CliqueFree.FiniteCoupling ----
namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence

universe u v

namespace FiniteCoupling
universe z
variable {I : Type u} {J : Type v} {E : Type z}
variable [Fintype I] [Fintype J] [Fintype E]
attribute [local instance] OAI.CliqueFreeIndependence.FiniteCoupling.instDecidableEq_oAI_2
lemma sum_abs_eq (a b : ℝ) : a + b - 2 * min a b = |a - b| := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.2 h)]; ring
  · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.2 h)]; ring

/-- The joint finite law in the shared rejection lemma, with its sharp bound. -/
lemma shared_rejection [Nonempty J] (p : I → J → ℝ) (hp : ∀ i, Law (p i)) :
    ∃ q : (I → J) → ℝ, Law q ∧
      (∀ i y, (∑ f, if f i = y then q f else 0) = p i y) ∧
      (∀ i j, (∑ f, if f i ≠ f j then q f else 0) ≤
        2 * dist (p i) (p j) / (1 + dist (p i) (p j))) := by
  have hbound (i : I) (y : J) : p i y ≤ 1 := by
    rw [← (hp i).2]
    exact single_le_sum (fun z _ ↦ (hp i).1 z) (mem_univ y)
  have hex (y : J) := exists_threshold_law (fun i ↦ p i y) (fun i ↦ (hp i).1 y) (fun i ↦ hbound i y)
  choose q hq hsingle hboth using hex
  let t : J × Finset I → ℝ := fun e ↦ q e.1 e.2
  have hmarg (i : I) (y : J) :
      (∑ e : J × Finset I, if i ∈ e.2 ∧ e.1 = y then t e else 0) = p i y := by
    rw [Fintype.sum_prod_type]
    calc
      _ = ∑ z, if z = y then (∑ A, if i ∈ A then q z A else 0) else 0 := by
        apply sum_congr rfl
        intro z _
        by_cases hz : z = y <;> simp [hz, t]
      _ = _ := by simp [hsingle]
  have hxor (i j : I) (y : J) :
      (∑ A, if Xor (i ∈ A) (j ∈ A) then q y A else 0) = |p i y - p j y| := by
    calc
      _ = ∑ A, ((if i ∈ A then q y A else 0) + (if j ∈ A then q y A else 0) -
          2 * (if i ∈ A ∧ j ∈ A then q y A else 0)) := by
        apply sum_congr rfl
        intro A _
        by_cases hi : i ∈ A <;> by_cases hj : j ∈ A <;> simp [hi, hj, Xor]
        ring
      _ = _ := by
        rw [sum_sub_distrib, sum_add_distrib, ← mul_sum, hsingle, hsingle, hboth]
        exact sum_abs_eq _ _
  have hor (i j : I) (y : J) :
      (∑ A, if i ∈ A ∨ j ∈ A then q y A else 0) =
        (p i y + p j y + |p i y - p j y|) / 2 := by
    calc
      _ = ∑ A, ((if i ∈ A then q y A else 0) + (if j ∈ A then q y A else 0) -
          (if i ∈ A ∧ j ∈ A then q y A else 0)) := by
        apply sum_congr rfl
        intro A _
        by_cases hi : i ∈ A <;> by_cases hj : j ∈ A <;> simp [hi, hj]
      _ = _ := by
        rw [sum_sub_distrib, sum_add_distrib, hsingle, hsingle, hboth]
        linarith [sum_abs_eq (p i y) (p j y)]
  have hdist0 (i j : I) : 0 ≤ dist (p i) (p j) :=
    div_nonneg (sum_nonneg fun _ _ ↦ abs_nonneg _) (by norm_num)
  apply joint_of_trials p hp t (fun e ↦ (hq e.1).1 e.2) Prod.snd Prod.fst hmarg
    (fun i j ↦ 2 * dist (p i) (p j) / (1 + dist (p i) (p j)))
  intro i j
  have hden : 1 + dist (p i) (p j) ≠ 0 := by linarith [hdist0 i j]
  have hX : (∑ e : J × Finset I, if Xor (i ∈ e.2) (j ∈ e.2) then t e else 0) =
      2 * dist (p i) (p j) := by
    rw [Fintype.sum_prod_type]
    simp only [t, hxor, dist]
    ring
  have hU : (∑ e : J × Finset I, if i ∈ e.2 ∨ j ∈ e.2 then t e else 0) =
      1 + dist (p i) (p j) := by
    rw [Fintype.sum_prod_type]
    simp only [t, hor, ← sum_div, sum_add_distrib, (hp i).2, (hp j).2, dist]
    ring
  change (∑ e : J × Finset I, if Xor (i ∈ e.2) (j ∈ e.2) then t e else 0) ≤ _
  rw [hX, hU, div_mul_cancel₀ _ hden]

end FiniteCoupling

end CliqueFreeIndependence

end

end OAI

-- ---- platform node ----
open OAI OAI.CliqueFreeIndependence OAI.CliqueFreeIndependence.FiniteCoupling
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
attribute [local instance] OAI.CliqueFreeIndependence.FiniteCoupling.instDecidableEq_oAI_2


theorem solution.{u,v} : type_of% @_root_.OAI.CliqueFreeIndependence.FiniteCoupling.shared_rejection.{u,v} := @_root_.OAI.CliqueFreeIndependence.FiniteCoupling.shared_rejection.{u,v}
