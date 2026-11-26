-- Prove2me | solution 1 for MellinDuality.sum_univ_eq_sum_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:54:43.65922+00:00
-- url     : https://prove2.me/submissions/e13224c1-3d38-4f1a-aaff-d6137bd54113

module
public import Definitions.Def_MellinDuality_Defs
public import Definitions.Def_MellinDuality_Half
public import Theorems.Thm_MellinDuality_zero_mem_half
public import Theorems.Thm_MellinDuality_neg_mem_half_iff
public import Theorems.Thm_MellinDuality_gi_im
public import Theorems.Thm_MellinDuality_gi_re
attribute [local simp] MellinDuality.gi_im
attribute [local simp] MellinDuality.gi_re



set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace MellinDuality
theorem _root_.solution (hp2 : p ≠ 2) {M : Type*} [AddCommMonoid M] (f : ZMod p → M)
    (h0 : f 0 = 0) : ∑ x, f x = ∑ n ∈ half p, (f n + f (-n)) := by
  rw [sum_add_distrib, ← sum_filter_add_sum_filter_not univ (· ∈ half p)]
  congr 1
  · congr 1; ext x; simp
  · rw [← sum_erase (half p) (a := 0) (f := fun n => f (-n)) (by simp [h0])]
    refine sum_nbij' (fun x => -x) (fun x => -x) ?_ ?_ ?_ ?_ ?_
    · intro x hx
      simp only [mem_filter, mem_univ, true_and] at hx
      have hx0 : x ≠ 0 := by rintro rfl; exact hx zero_mem_half
      simp only [mem_erase, ne_eq, neg_eq_zero]
      exact ⟨hx0, (neg_mem_half_iff hp2 hx0).2 hx⟩
    · intro x hx
      simp only [mem_erase, ne_eq] at hx
      simp only [mem_filter, mem_univ, true_and]
      exact fun h => ((neg_mem_half_iff hp2 hx.1).1 h) hx.2
    · intro x _; simp
    · intro x _; simp
    · intro x _; simp
end MellinDuality
