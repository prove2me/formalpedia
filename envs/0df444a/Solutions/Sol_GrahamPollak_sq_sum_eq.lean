-- Prove2me | solution 1 for GrahamPollak.sq_sum_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:19:26.363109+00:00
-- url     : https://prove2.me/submissions/bbf9c473-ad5e-42c0-a272-ea497db9e519

module
public import Mathlib
public import Definitions.Def_GrahamPollakLib_GrahamPollak
public import Theorems.Thm_GrahamPollak_pair_count_add
public import Theorems.Thm_GrahamPollak_sum_prod_eq

set_option autoImplicit true
@[expose] public section
public section
open GrahamPollak
variable {V : Type*}
variable [DecidableEq V]
namespace GrahamPollak
theorem _root_.solution [Fintype V] {m : ℕ} {A B : Fin m → Finset V}
    (h : IsBicliqueDecomposition A B) (x : V → ℝ) :
    (∑ v, x v) ^ 2 = ∑ v, x v ^ 2 + 2 * ∑ i, (∑ u ∈ A i, x u) * (∑ v ∈ B i, x v) := by
  set e : V → V → ℝ := fun u v => ∑ i, ((if u ∈ A i ∧ v ∈ B i then 1 else 0 : ℝ)) with he
  have hS := sum_prod_eq A B x
  have hS' : ∑ i, (∑ u ∈ A i, x u) * (∑ v ∈ B i, x v) = ∑ u, ∑ v, x u * x v * e v u := by
    rw [hS, Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    simp only [he]; ring
  have h2 : 2 * ∑ i, (∑ u ∈ A i, x u) * (∑ v ∈ B i, x v) =
      ∑ u, ∑ v, x u * x v * (if u = v then 0 else 1) := by
    rw [two_mul]
    nth_rewrite 1 [hS]
    rw [hS', ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [← pair_count_add h u v]; ring
  have h3 : ∑ v, x v ^ 2 = ∑ u, ∑ v, x u * x v * (if u = v then 1 else 0) := by
    refine Finset.sum_congr rfl fun u _ => ?_
    simp [sq]
  rw [h2, h3, ← Finset.sum_add_distrib, sq, Finset.sum_mul]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  split_ifs <;> ring
end GrahamPollak
