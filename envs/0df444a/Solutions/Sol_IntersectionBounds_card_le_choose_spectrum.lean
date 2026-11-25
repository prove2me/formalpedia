-- Prove2me | solution 1 for IntersectionBounds.card_le_choose_spectrum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T13:09:29.291586+00:00
-- url     : https://prove2.me/submissions/cc0b6f30-afde-4b0f-b9ce-739ade5ce70e

module
public import Definitions.Def_IntersectionBounds_UniformSpace
public import Definitions.Def_IntersectionBounds_Separation
public import Mathlib.Data.Rat.Cast.CharZero
public import Definitions.Def_IntersectionBounds_RayChaudhuriWilson
public import Theorems.Thm_IntersectionBounds_rayChaudhuriWilson
public import Theorems.Thm_IntersectionBounds_intersection_lt_of_uniform

set_option autoImplicit true
@[expose] public section
public section
open IntersectionBounds
open Finset Submodule
universe u v
variable {V : Type u} [Fintype V]
namespace IntersectionBounds
theorem _root_.solution (F : Finset (Finset V)) (k : ℕ) (huni : Uniform F k) :
    F.card ≤ (Fintype.card V).choose (intersectionSpectrum F).card := by
  classical
  apply rayChaudhuriWilson F (intersectionSpectrum F) k huni
  · intro l hl
    obtain ⟨⟨A, B⟩, hAB, rfl⟩ := Finset.mem_image.mp hl
    obtain ⟨hA, hB, hne⟩ := Finset.mem_offDiag.mp hAB
    exact intersection_lt_of_uniform F k huni A B hA hB hne
  · intro A hA B hB hne
    exact Finset.mem_image.mpr ⟨(A, B), Finset.mem_offDiag.mpr ⟨hA, hB, hne⟩, rfl⟩
end IntersectionBounds
