-- Prove2me | solution 1 for OAI.Release075.grid_line_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T08:54:41.243709+00:00
-- url     : https://prove2.me/submissions/2d3e7a19-c608-4ca3-927f-4f860182fce0

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/MatrixRank.lean:L733-L758
-- (upload_full_project.md Phase 4): solution for node OAI.Release075.grid_line_certificate. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank

-- ---- from OAI.GroupTheory.Hyperbolic.MatrixRank ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

namespace Release075

universe u v

open scoped BigOperators

/-- A polynomial below the finite-field power-sum threshold has zero total sum. -/
theorem polynomial_sum_eq_zero {K : Type*} [Field K] [Fintype K]
    (p : Polynomial K) (hdeg : p.natDegree < Fintype.card K - 1) :
    ∑ x, p.eval x = 0 := by
  simp only [Polynomial.eval_eq_sum_range]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro i hi
  rw [← Finset.mul_sum, FiniteField.sum_pow_lt_card_sub_one K i
    (lt_of_le_of_lt (Nat.le_of_lt_succ (Finset.mem_range.mp hi)) hdeg), mul_zero]

theorem gridLagrange_other {T K : Type*} [Fintype T] [Field K]
    [DecidableEq K] (S : Finset K) (a x : T → K) (hx : ∀ t, x t ∈ S)
    (hax : a ≠ x) : gridLagrange S a x = 0 := by
  classical
  obtain ⟨t, ht⟩ := Function.ne_iff.mp hax
  apply Finset.prod_eq_zero (Finset.mem_univ t)
  apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨ht.symm, hx t⟩)
  simp

theorem gridLagrangeLine_natDegree_le {T K : Type*} [Fintype T] [Field K]
    [DecidableEq K] (S : Finset K) (a b v : T → K) (ha : ∀ t, a t ∈ S) :
    (gridLagrangeLine S a b v).natDegree ≤ Fintype.card T * (S.card - 1) := by
  apply (Polynomial.natDegree_prod_le _ _).trans
  calc
    _ ≤ ∑ t : T, (S.card - 1) := by
      apply Finset.sum_le_sum
      intro t _
      apply (Polynomial.natDegree_prod_le _ _).trans
      calc
        _ ≤ ∑ _w ∈ S.erase (a t), 1 := by
          apply Finset.sum_le_sum
          intro w _
          apply Polynomial.natDegree_mul_le.trans
          simp only [Polynomial.natDegree_C, add_zero]
          apply (Polynomial.natDegree_add_le _ _).trans
          apply max_le
          · simp
          · exact Polynomial.natDegree_mul_le.trans (by simp)
        _ = S.card - 1 := by simp [Finset.card_erase_of_mem (ha t)]
    _ = _ := by simp

/-- Every entry of the rank-one weight matrix has zero sum over a full line. -/
theorem polygon_weight_line_sum {T K : Type*} [Fintype T] [Field K] [Fintype K]
    [DecidableEq K] (S : Finset K) (a a' b v : T → K)
    (ha : ∀ t, a t ∈ S) (ha' : ∀ t, a' t ∈ S)
    (hdeg : 2 * (Fintype.card T * (S.card - 1)) < Fintype.card K - 1) :
    (∑ x : K, gridLagrange S a (fun t => b t + x * v t) *
      gridLagrange S a' (fun t => b t + x * v t)) = 0 := by
  have h := polynomial_sum_eq_zero (gridLagrangeLine S a b v * gridLagrangeLine S a' b v)
    (lt_of_le_of_lt (Polynomial.natDegree_mul_le.trans (Nat.add_le_add
      (gridLagrangeLine_natDegree_le S a b v ha)
      (gridLagrangeLine_natDegree_le S a' b v ha'))) (by omega))
  simpa only [Polynomial.eval_mul, gridLagrangeLine_eval] using h

/-- Summation on a punctured line subtracts exactly the value at its own mark. -/
theorem puncturedLine_sum {T K R : Type*} [Fintype T] [Field K] [Fintype K]
    [AddCommGroup R] (a v : T → K) (hv : v ≠ 0) (w : (T → K) → R) :
    (∑ z ∈ puncturedLine a v, w z) = (∑ x, w (affineLineMap a v x)) - w a := by
  classical
  have hzero : affineLineMap a v 0 = a := by ext t; simp [affineLineMap]
  rw [puncturedLine, Finset.sum_image (affineLineMap_injective a v hv).injOn,
    Finset.sum_erase_eq_sub (Finset.mem_univ 0), hzero]

/-- The exact finite-field punctured-line matrix certificate, with no asymptotic
or characteristic assumption beyond its explicit degree threshold. -/
theorem grid_line_certificate {T I K : Type*} [Fintype T] [Fintype I]
    [DecidableEq T] [DecidableEq I] [Field K] [Fintype K] [DecidableEq K]
    (S : Finset K) (a v : I → T → K) (ha : ∀ i t, a i t ∈ S)
    (hinj : Function.Injective a) (hv : ∀ i, v i ≠ 0)
    (hdeg : 2 * (Fintype.card T * (S.card - 1)) < Fintype.card K - 1) :
    ∀ i j k, (∑ z, if i ∈ lineIncidence a v z then
      gridLagrange S (a j) z * gridLagrange S (a k) z else 0) =
      -(if j = i ∧ k = i then 1 else 0) := by
  classical
  intro i j k
  have heval (j : I) : gridLagrange S (a j) (a i) = if j = i then 1 else 0 := by
    by_cases hji : j = i
    · subst j; simp
    · rw [ite_eq_right hji]
      exact gridLagrange_other S (a j) (a i) (ha i) (fun h => hji (hinj h))
  have hs : (∑ z, if i ∈ lineIncidence a v z then
      gridLagrange S (a j) z * gridLagrange S (a k) z else 0) =
      ∑ z ∈ puncturedLine (a i) (v i), gridLagrange S (a j) z * gridLagrange S (a k) z := by
    simp [lineIncidence]
  rw [hs, puncturedLine_sum (a i) (v i) (hv i)]
  rw [show (∑ x, gridLagrange S (a j) (affineLineMap (a i) (v i) x) *
    gridLagrange S (a k) (affineLineMap (a i) (v i) x)) = 0 from
      polygon_weight_line_sum S (a j) (a k) (a i) (v i) (ha j) (ha k) hdeg]
  by_cases hj : j = i <;> by_cases hk : k = i <;> simp_all

end Release075

end OAI

-- ---- platform node ----
open OAI OAI.Release075
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.Release075.grid_line_certificate := @_root_.OAI.Release075.grid_line_certificate
