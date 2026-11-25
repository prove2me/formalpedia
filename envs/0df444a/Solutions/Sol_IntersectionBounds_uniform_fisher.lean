-- Prove2me | solution 1 for IntersectionBounds.uniform_fisher
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T13:14:34.673954+00:00
-- url     : https://prove2.me/submissions/a3e14dcc-9261-4a55-8462-975511ca852a

module
public import Definitions.Def_IntersectionBounds_UniformSpace
public import Definitions.Def_IntersectionBounds_Separation
public import Mathlib.Data.Rat.Cast.CharZero
public import Definitions.Def_IntersectionBounds_RayChaudhuriWilson
public import Theorems.Thm_IntersectionBounds_rayChaudhuriWilson
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
theorem _root_.solution (F : Finset (Finset V)) (k l : ℕ)
    (huni : Uniform F k) (hl : l < k)
    (hinter : ∀ A ∈ F, ∀ B ∈ F, A ≠ B → (A ∩ B).card = l) :
    F.card ≤ Fintype.card V := by
  have h := rayChaudhuriWilson F {l} k huni (by simpa)
    (by intro A hA B hB hne; simpa using hinter A hA B hB hne)
  simpa using h
end IntersectionBounds
