-- Prove2me | solution 1 for IntersectionBounds.uniform_separation_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T13:02:06.062864+00:00
-- url     : https://prove2.me/submissions/4484a22f-3c97-4cef-a3ea-8be69461263a

module
public import Definitions.Def_IntersectionBounds_UniformSpace
public import Definitions.Def_IntersectionBounds_Separation
public import Mathlib.Data.Rat.Cast.CharZero
public import Definitions.Def_IntersectionBounds_RayChaudhuriWilson
public import Theorems.Thm_IntersectionBounds_card_le_finrank_degree
public import Theorems.Thm_IntersectionBounds_degreeSpace_le_exact_of_uniform
public import Theorems.Thm_IntersectionBounds_finrank_exactSpace_le


set_option autoImplicit true
@[expose] public section
public section
open IntersectionBounds
open Finset Submodule
universe u v
variable {V : Type u} [Fintype V]
open Classical
namespace IntersectionBounds
theorem _root_.solution {K : Type v} [Field K] [CharZero K]
    (F : Finset (Finset V)) (L : Finset K) (k : ℕ)
    (huni : Uniform F k) (hs : L.card ≤ k)
    (hself : ∀ A ∈ F, (A.card : K) ∉ L)
    (hinter : ∀ A ∈ F, ∀ B ∈ F, A ≠ B → ((A ∩ B).card : K) ∈ L) :
    F.card ≤ (Fintype.card V).choose L.card := by
  calc
    _ ≤ Module.finrank K (degreeSpace (K := K) F L.card) := card_le_finrank_degree F L hself hinter
    _ ≤ Module.finrank K (exactSpace (K := K) F L.card) :=
      Submodule.finrank_mono (degreeSpace_le_exact_of_uniform F k L.card huni hs)
    _ ≤ _ := finrank_exactSpace_le F L.card
end IntersectionBounds
