-- Prove2me | solution 1 for GlobalTheory.DirichletTail.norm_sum_range_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:34:21.466877+00:00
-- url     : https://prove2.me/submissions/935d3d5e-36c2-4d2f-88f1-db6f054f9ef3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LFunctionEqTsumOfOneLt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory GlobalTheory.DirichletTail
open Filter Topology
namespace GlobalTheory.DirichletTail
theorem _root_.solution {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (m : ℕ) :
    ‖∑ n ∈ Finset.range m, χ ((n + 1 : ℕ) : ZMod q)‖ ≤ q := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hper : ∑ a : ZMod q, χ a = ∑ n ∈ Finset.range q, χ (n : ZMod q) := by
    refine Finset.sum_bij' (fun a _ ↦ a.val) (fun n _ ↦ (n : ZMod q)) ?_ ?_ ?_ ?_ ?_
    · intro a _
      exact Finset.mem_range.mpr (ZMod.val_lt a)
    · intro n _
      exact Finset.mem_univ _
    · intro a _
      exact ZMod.natCast_zmod_val a
    · intro n hn
      exact ZMod.val_cast_of_lt (Finset.mem_range.mp hn)
    · intro a _
      rw [ZMod.natCast_zmod_val]
  have hshift : ∀ k : ℕ, ∑ n ∈ Finset.range q, χ ((k + n : ℕ) : ZMod q) = 0 := by
    intro k
    induction k with
    | zero =>
      simp only [zero_add]
      rw [← hper]
      exact MulChar.sum_eq_zero_of_ne_one hχ
    | succ k ih =>
      have h1 := Finset.sum_range_succ (fun n ↦ χ ((k + n : ℕ) : ZMod q)) q
      have h2 := Finset.sum_range_succ' (fun n ↦ χ ((k + n : ℕ) : ZMod q)) q
      beta_reduce at h1 h2
      have hkq : χ ((k + q : ℕ) : ZMod q) = χ ((k + 0 : ℕ) : ZMod q) := by
        simp [Nat.cast_add]
      have hc : ∑ n ∈ Finset.range q, χ ((k + 1 + n : ℕ) : ZMod q) =
          ∑ n ∈ Finset.range q, χ ((k + (n + 1) : ℕ) : ZMod q) :=
        Finset.sum_congr rfl fun n _ ↦ by rw [show k + 1 + n = k + (n + 1) by omega]
      rw [hc]
      linear_combination ih + hkq - h1.symm.trans h2
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    by_cases hm : m ≤ q
    · calc ‖∑ n ∈ Finset.range m, χ ((n + 1 : ℕ) : ZMod q)‖
          ≤ ∑ n ∈ Finset.range m, ‖χ ((n + 1 : ℕ) : ZMod q)‖ := norm_sum_le _ _
        _ ≤ ∑ n ∈ Finset.range m, (1 : ℝ) := Finset.sum_le_sum fun n _ ↦ χ.norm_le_one _
        _ = m := by simp
        _ ≤ q := by exact_mod_cast hm
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + q := ⟨m - q, by omega⟩
      rw [Finset.sum_range_add]
      have hb : ∑ x ∈ Finset.range q, χ ((k + x + 1 : ℕ) : ZMod q) = 0 := by
        rw [← hshift (k + 1)]
        exact Finset.sum_congr rfl fun x _ ↦ by rw [show k + x + 1 = k + 1 + x by omega]
      rw [hb, add_zero]
      exact ih k (by omega)
end GlobalTheory.DirichletTail
