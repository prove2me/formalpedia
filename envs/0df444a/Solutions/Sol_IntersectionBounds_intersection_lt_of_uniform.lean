-- Prove2me | solution 1 for IntersectionBounds.intersection_lt_of_uniform
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:49:55.481182+00:00
-- url     : https://prove2.me/submissions/86d53f01-9d46-4260-b523-23fe0a7ccd4f

module
public import Definitions.Def_IntersectionBounds_UniformSpace
public import Definitions.Def_IntersectionBounds_Separation
public import Mathlib.Data.Rat.Cast.CharZero
public import Definitions.Def_IntersectionBounds_RayChaudhuriWilson

set_option autoImplicit true
@[expose] public section
public section
open IntersectionBounds
open Finset Submodule
universe u v
variable {V : Type u} [Fintype V]
open Classical
omit [Fintype V]
namespace IntersectionBounds
theorem _root_.solution (F : Finset (Finset V)) (k : ℕ)
    (huni : Uniform F k) (A B : Finset V) (hA : A ∈ F) (hB : B ∈ F) (hne : A ≠ B) :
    (A ∩ B).card < k := by
  have hle : (A ∩ B).card ≤ k := (Finset.card_le_card inter_subset_left).trans_eq (huni A hA)
  by_contra hnot
  have heq : A ∩ B = A := Finset.eq_of_subset_of_card_le inter_subset_left (by
    rw [huni A hA]
    omega)
  have hsub : A ⊆ B := by rw [← heq]; exact inter_subset_right
  exact hne (Finset.eq_of_subset_of_card_le hsub (by rw [huni A hA, huni B hB]))
end IntersectionBounds
