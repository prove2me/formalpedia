-- Prove2me | solution 1 for OAI.CliqueFreeIndependence.FiniteEntropy.entropy_mix_gap
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T23:44:18.617805+00:00
-- url     : https://prove2.me/submissions/81502bea-6626-4808-904b-a45bf22b4f87

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/CliqueFree/FiniteEntropy.lean:L192-L213
-- (upload_full_project.md Phase 4): solution for node OAI.CliqueFreeIndependence.FiniteEntropy.entropy_mix_gap. The node keeps its source
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

-- ---- from OAI.Combinatorics.CliqueFree.FiniteEntropy ----
namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence

universe u v

namespace FiniteEntropy

variable {I : Type u} [Fintype I]

lemma entropy_eq_sum {w p : I → ℝ} (hw : ∀ i, 0 < w i) (hp : ∀ i, 0 ≤ p i) :
    entropy w p = ∑ i, (p i * Real.log (w i) - p i * Real.log (p i)) := by
  apply sum_congr rfl
  intro i _
  rcases (hp i).eq_or_lt with hi | hi
  · simp [← hi]
  · rw [Real.log_div (hw i).ne' hi.ne', mul_sub]

lemma divergence_eq_sum {p q : I → ℝ} (hp : ∀ i, 0 ≤ p i)
    (hs : ∀ i, 0 < p i → 0 < q i) :
    divergence p q = ∑ i, (p i * Real.log (p i) - p i * Real.log (q i)) := by
  apply sum_congr rfl
  intro i _
  rcases (hp i).eq_or_lt with hi | hi
  · simp [← hi]
  · rw [Real.log_div hi.ne' (hs i hi).ne', mul_sub]

variable {J : Type v} [Fintype J]

/-- Mixing finitely many probability vectors. -/
lemma mix_isProb {a : J → ℝ} {p : J → I → ℝ} (ha : IsProb a)
    (hp : ∀ j, IsProb (p j)) : IsProb (fun i ↦ ∑ j, a j * p j i) := by
  refine ⟨fun i ↦ sum_nonneg fun j _ ↦ mul_nonneg (ha.1 j) ((hp j).1 i), ?_⟩
  rw [sum_comm]
  simp_rw [← mul_sum, fun j ↦ (hp j).2, mul_one]
  exact ha.2

omit [Fintype I] in
lemma mix_support {a : J → ℝ} {p : J → I → ℝ} (ha : ∀ j, 0 ≤ a j)
    (hp : ∀ j i, 0 ≤ p j i) {j : J} (hj : 0 < a j) {i : I} (hi : 0 < p j i) :
    0 < ∑ k, a k * p k i := by
  classical
  exact (mul_pos hj hi).trans_le (single_le_sum
    (fun k _ ↦ mul_nonneg (ha k) (hp k i)) (mem_univ j))

/-- The finite entropy-mixture identity for the averaged increment. -/
lemma entropy_mix_gap {w : I → ℝ} (hw : ∀ i, 0 < w i)
    {a : J → ℝ} {p : J → I → ℝ} (ha : IsProb a) (hp : ∀ j, IsProb (p j)) :
    entropy w (fun i ↦ ∑ j, a j * p j i) - ∑ j, a j * entropy w (p j) =
      ∑ j, a j * divergence (p j) (fun i ↦ ∑ k, a k * p k i) := by
  let b := fun i ↦ ∑ j, a j * p j i
  have hb := mix_isProb ha hp
  have hd (j : J) : a j * divergence (p j) b =
      a j * (∑ i, (p j i * Real.log (p j i) - p j i * Real.log (b i))) := by
    rcases (ha.1 j).eq_or_lt with hj | hj
    · simp [← hj]
    · rw [divergence_eq_sum (hp j).1
        (fun i hi ↦ mix_support ha.1 (fun k ↦ (hp k).1) hj hi)]
  change entropy w b - ∑ j, a j * entropy w (p j) = ∑ j, a j * divergence (p j) b
  rw [entropy_eq_sum hw hb.1]
  simp_rw [entropy_eq_sum hw (hp _).1, hd, mul_sum, mul_sub, sum_sub_distrib]
  have he (f : I → ℝ) : (∑ i, b i * f i) = ∑ j, ∑ i, a j * (p j i * f i) := by
    dsimp [b]
    simp_rw [sum_mul, mul_assoc]
    rw [sum_comm]
  rw [he, he]
  ring

end FiniteEntropy

end CliqueFreeIndependence

end

end OAI

-- ---- platform node ----
open OAI OAI.CliqueFreeIndependence OAI.CliqueFreeIndependence.FiniteEntropy
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable


theorem solution.{u,v} : type_of% @_root_.OAI.CliqueFreeIndependence.FiniteEntropy.entropy_mix_gap.{u,v} := @_root_.OAI.CliqueFreeIndependence.FiniteEntropy.entropy_mix_gap.{u,v}
