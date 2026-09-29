-- Prove2me | solution 1 for Grunbaum2003.caratheodory_convex_representation
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-27T02:50:17.120486+00:00
-- url     : https://prove2.me/submissions/69531a6d-d494-42dc-a2bb-ed6b004f4fc5

import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Constructions

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

theorem car_main (d : ℕ)
    (A : Set (Fin d → ℝ)) (x : Fin d → ℝ) (hx : x ∈ convexHull ℝ A) :
    ∃ (v : Fin (d + 1) → Fin d → ℝ) (w : Fin (d + 1) → ℝ),
      (∀ i, v i ∈ A) ∧ (∀ i, 0 ≤ w i) ∧
        (∑ i, w i) = 1 ∧ x = ∑ i, w i • v i := by
  classical
  obtain ⟨ι, hι, z, w, hzA, hind, hwpos, hw1, hxz⟩ := eq_pos_convex_span_of_mem_convexHull hx
  have hcard : Fintype.card ι ≤ d + 1 := by
    have h1 := hind.card_le_finrank_succ
    have h2 := Submodule.finrank_le (vectorSpan ℝ (Set.range z))
    rw [Module.finrank_fin_fun] at h2
    omega
  have hne : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp at hw1
  obtain ⟨i0⟩ := hne
  set k := Fintype.card ι with hk
  let e : ι ≃ Fin k := Fintype.equivFin ι
  have key : ∀ (M : Type) [AddCommMonoid M] (g : ι → M) (F : Fin (d + 1) → M),
      (∀ i : Fin (d + 1), F i = if h : (i : ℕ) < k then g (e.symm ⟨i, h⟩) else 0) →
      ∑ i, F i = ∑ j, g j := by
    intro M _ g F hF
    rw [Finset.sum_congr rfl (fun i _ => hF i)]
    set G : ℕ → M := fun n => if h : n < k then g (e.symm ⟨n, h⟩) else 0 with hG
    have h1 : ∑ i : Fin (d + 1), (if h : (i : ℕ) < k then g (e.symm ⟨i, h⟩) else 0) =
        ∑ n ∈ Finset.range (d + 1), G n := Fin.sum_univ_eq_sum_range G (d + 1)
    have h2 : ∑ n ∈ Finset.range (d + 1), G n = ∑ n ∈ Finset.range k, G n := by
      symm
      apply Finset.sum_subset (Finset.range_subset_range.mpr hcard)
      intro n _ hnk
      simp only [Finset.mem_range] at hnk
      simp [hG, hnk]
    have h3 : ∑ n ∈ Finset.range k, G n = ∑ j : Fin k, g (e.symm j) := by
      rw [← Fin.sum_univ_eq_sum_range]
      exact Finset.sum_congr rfl fun j _ => by simp [hG, j.isLt]
    have h4 : ∑ j : Fin k, g (e.symm j) = ∑ i, g i := Equiv.sum_comp e.symm g
    rw [h1, h2, h3, h4]
  let v : Fin (d + 1) → Fin d → ℝ := fun i =>
    if h : (i : ℕ) < k then z (e.symm ⟨i, h⟩) else z i0
  let w' : Fin (d + 1) → ℝ := fun i =>
    if h : (i : ℕ) < k then w (e.symm ⟨i, h⟩) else 0
  refine ⟨v, w', fun i => ?_, fun i => ?_, ?_, ?_⟩
  · simp only [v]
    split_ifs
    · exact hzA (Set.mem_range_self _)
    · exact hzA (Set.mem_range_self _)
  · simp only [w']
    split_ifs
    · exact (hwpos _).le
    · exact le_rfl
  · rw [key ℝ w w' (fun i => rfl), hw1]
  · rw [key (Fin d → ℝ) (fun i => w i • z i) (fun i => w' i • v i) (fun i => by
      by_cases h : (i : ℕ) < k
      · simp [w', v, h]
      · simp [w', v, h]), hxz]

end Grunbaum2003

open Grunbaum2003

theorem solution (d : ℕ)
    (A : Set (Fin d → ℝ)) (x : Fin d → ℝ) (hx : x ∈ convexHull ℝ A) :
    ∃ (v : Fin (d + 1) → Fin d → ℝ) (w : Fin (d + 1) → ℝ),
      (∀ i, v i ∈ A) ∧ (∀ i, 0 ≤ w i) ∧
        (∑ i, w i) = 1 ∧ x = ∑ i, w i • v i := by
  exact car_main d A x hx
