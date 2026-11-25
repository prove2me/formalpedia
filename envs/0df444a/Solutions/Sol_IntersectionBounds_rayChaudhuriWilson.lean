-- Prove2me | solution 1 for IntersectionBounds.rayChaudhuriWilson
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T13:06:05.651311+00:00
-- url     : https://prove2.me/submissions/a97c272f-8c9e-437c-b3a3-e45bdde193e9

module
public import Definitions.Def_IntersectionBounds_UniformSpace
public import Definitions.Def_IntersectionBounds_Separation
public import Mathlib.Data.Rat.Cast.CharZero
public import Definitions.Def_IntersectionBounds_RayChaudhuriWilson
public import Theorems.Thm_IntersectionBounds_uniform_separation_bound
public import Theorems.Thm_IntersectionBounds_indicator_empty
attribute [local simp] IntersectionBounds.indicator_empty



set_option autoImplicit true
@[expose] public section
public section
open IntersectionBounds
open Finset Submodule
universe u v
variable {V : Type u} [Fintype V]
open Classical
namespace IntersectionBounds
theorem _root_.solution (F : Finset (Finset V)) (L : Finset ℕ) (k : ℕ)
    (huni : Uniform F k) (hL : ∀ l ∈ L, l < k) (hinter : IntersectionsIn F L) :
    F.card ≤ (Fintype.card V).choose L.card := by
  classical
  let LR : Finset ℚ := L.image (fun l : ℕ => (l : ℚ))
  have hcard : LR.card = L.card := Finset.card_image_of_injective _ Nat.cast_injective
  have hs : LR.card ≤ k := by
    rw [hcard]
    calc
      _ ≤ (Finset.range k).card := Finset.card_le_card (by
        intro l hl
        exact Finset.mem_range.mpr (hL l hl))
      _ = k := Finset.card_range k
  have hself : ∀ A ∈ F, (A.card : ℚ) ∉ LR := by
    intro A hA ha
    obtain ⟨l, hl, heq⟩ := Finset.mem_image.mp ha
    have heq' : l = A.card := Nat.cast_injective heq
    have := hL l hl
    rw [heq', huni A hA] at this
    omega
  have hcross : ∀ A ∈ F, ∀ B ∈ F, A ≠ B → ((A ∩ B).card : ℚ) ∈ LR := by
    intro A hA B hB hne
    exact Finset.mem_image.mpr ⟨_, hinter A hA B hB hne, rfl⟩
  simpa only [hcard] using uniform_separation_bound F LR k huni hs hself hcross
end IntersectionBounds
