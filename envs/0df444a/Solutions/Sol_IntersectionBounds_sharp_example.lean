-- Prove2me | solution 1 for IntersectionBounds.sharp_example
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T13:26:26.001331+00:00
-- url     : https://prove2.me/submissions/5955187b-48a7-462d-9d82-b879ec964b1a

module
public import Definitions.Def_IntersectionBounds_UniformSpace
public import Definitions.Def_IntersectionBounds_Separation
public import Mathlib.Data.Rat.Cast.CharZero
public import Definitions.Def_IntersectionBounds_RayChaudhuriWilson
public import Theorems.Thm_IntersectionBounds_intersection_lt_of_uniform
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
theorem _root_.solution (s : ℕ) :
    let F := (univ : Finset V).powersetCard s
    Uniform F s ∧ IntersectionsIn F (range s) ∧ F.card = (Fintype.card V).choose s := by
  classical
  dsimp
  have huni : Uniform ((univ : Finset V).powersetCard s) s := by
    intro A hA
    exact (Finset.mem_powersetCard.mp hA).2
  refine ⟨huni, ?_, by simp⟩
  intro A hA B hB hne
  exact Finset.mem_range.mpr (intersection_lt_of_uniform _ s huni A B hA hB hne)
end IntersectionBounds
