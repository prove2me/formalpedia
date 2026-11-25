-- Prove2me | solution 1 for IntersectionBounds.degreeSpace_le_exact_of_uniform
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:58:30.063925+00:00
-- url     : https://prove2.me/submissions/3d233773-fdbf-49aa-a83a-50c22ae2a890

module
public import Definitions.Def_IntersectionBounds_EvaluationSpace
public import Definitions.Def_IntersectionBounds_Definitions
public import Definitions.Def_IntersectionBounds_UniformSpace
public import Theorems.Thm_IntersectionBounds_indicator_mem_exact_of_uniform

set_option autoImplicit true
@[expose] public section
public section
open IntersectionBounds
open Finset Submodule
universe u v
variable {V : Type u} [Fintype V] {K : Type v} [Field K]
variable (F : Finset (Finset V))
namespace IntersectionBounds
theorem _root_.solution [CharZero K] (k s : ℕ)
    (huni : Uniform F k) (hs : s ≤ k) :
    degreeSpace F s ≤ (exactSpace F s : Submodule K (F → K)) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨T, hT, rfl⟩
  exact indicator_mem_exact_of_uniform F k s huni hs T hT
end IntersectionBounds
