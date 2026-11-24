-- Prove2me | solution 1 for MomentComparison.cubeAverage_walsh
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:05:51.366797+00:00
-- url     : https://prove2.me/submissions/dda4dc22-82f1-48f2-87e2-46a2ce67ff25

module
public import Definitions.Def_MomentComparison_Basic
public import Mathlib.Data.Finset.SymmDiff
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Ring
public import Definitions.Def_MomentComparison_Basic
import all Definitions.Def_MomentComparison_Basic
public import Definitions.Def_MomentComparison_Walsh
public import Theorems.Thm_MomentComparison_walsh_empty
public import Theorems.Thm_MomentComparison_cubeSign_mul_self
public import Theorems.Thm_MomentComparison_cubeAverage_const
attribute [local simp] MomentComparison.walsh_empty
attribute [local simp] MomentComparison.cubeSign_mul_self
attribute [local simp] MomentComparison.cubeAverage_const
section
public section
open scoped BigOperators symmDiff
namespace MomentComparison
open Finset
private theorem flip_involutive {n : ℕ} (i : Fin n) : Function.Involutive (flip i) := by
  intro x
  ext j
  by_cases h : j = i
  · subst j
    simp [flip]
  · simp [flip, Function.update_of_ne h]
private theorem walsh_flip {n : ℕ} (s : Finset (Fin n)) (x : Cube n) {i : Fin n}
    (hi : i ∈ s) : walsh s (flip i x) = -walsh s x := by
  unfold walsh
  rw [← prod_erase_mul s _ hi, ← prod_erase_mul s _ hi]
  have he : (∏ j ∈ s.erase i, cubeSign (flip i x) j) =
      ∏ j ∈ s.erase i, cubeSign x j := by
    apply prod_congr rfl
    intro j hj
    simp [cubeSign, flip, Function.update_of_ne (ne_of_mem_erase hj)]
  rw [he]
  cases h : x i <;> simp [cubeSign, flip, h]
end MomentComparison
end
end

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators symmDiff
open MomentComparison
open Finset
namespace MomentComparison
theorem _root_.solution {n : ℕ} (s : Finset (Fin n)) :
    cubeAverage (walsh s) = if s = ∅ then 1 else 0 := by
  split_ifs with h
  · subst s
    simpa only [show walsh (∅ : Finset (Fin n)) = fun _ => 1 from funext walsh_empty] using
      (cubeAverage_const (n := n) 1)
  · obtain ⟨i, hi⟩ := nonempty_iff_ne_empty.mpr h
    let e := (flip_involutive i).toPerm (flip i)
    have he := Equiv.sum_comp e (walsh s)
    change (∑ x, walsh s (flip i x)) = ∑ x, walsh s x at he
    simp_rw [walsh_flip s _ hi, sum_neg_distrib] at he
    have hz : (∑ x, walsh s x) = 0 := by linarith
    simp [cubeAverage, hz]
end MomentComparison
