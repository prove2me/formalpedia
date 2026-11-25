-- Prove2me | solution 1 for GrahamPollak.pair_count_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:15:50.816125+00:00
-- url     : https://prove2.me/submissions/6e665c91-3b13-49b7-b8a1-d23b5d643f41

module
public import Mathlib
public import Definitions.Def_GrahamPollakLib_GrahamPollak

set_option autoImplicit true
@[expose] public section
public section
open GrahamPollak
variable {V : Type*}
variable [DecidableEq V]
namespace GrahamPollak
theorem _root_.solution {m : ℕ} {A B : Fin m → Finset V}
    (h : IsBicliqueDecomposition A B) (u v : V) :
    (∑ i, ((if u ∈ A i ∧ v ∈ B i then 1 else 0 : ℝ))) +
      (∑ i, ((if v ∈ A i ∧ u ∈ B i then 1 else 0 : ℝ))) = if u = v then 0 else 1 := by
  rw [← Finset.sum_add_distrib]
  split_ifs with huv
  · subst huv
    refine Finset.sum_eq_zero fun i _ => ?_
    have hd := Finset.disjoint_left.mp (h.1 i)
    by_cases hu : u ∈ A i
    · simp [hu, hd hu]
    · simp [hu]
  · have h1 := h.2 u v huv
    rw [Finset.card_eq_sum_ones, Finset.sum_filter] at h1
    have h2 : ((∑ i, ((if (u ∈ A i ∧ v ∈ B i) ∨ (v ∈ A i ∧ u ∈ B i) then 1 else 0 : ℕ)) : ℕ)
        : ℝ) = 1 := by
      rw [h1]; simp
    rw [Nat.cast_sum] at h2
    refine (Finset.sum_congr rfl fun i _ => ?_).trans h2
    have hd := Finset.disjoint_left.mp (h.1 i)
    by_cases h3 : u ∈ A i ∧ v ∈ B i
    · have h4 : ¬ (v ∈ A i ∧ u ∈ B i) := fun h4 => hd h4.1 h3.2
      simp [h3, h4]
    · by_cases h4 : v ∈ A i ∧ u ∈ B i
      · simp [h3, h4]
      · simp [h3, h4]
end GrahamPollak
