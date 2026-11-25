-- Prove2me | solution 1 for IntersectionBounds.separator_off_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:49:47.407294+00:00
-- url     : https://prove2.me/submissions/dc7c1673-01ca-4a2d-be19-3d687c257d14

module
public import Definitions.Def_IntersectionBounds_EvaluationSpace
public import Definitions.Def_IntersectionBounds_Separation
public import Theorems.Thm_IntersectionBounds_indicator_empty
attribute [local simp] IntersectionBounds.indicator_empty



set_option autoImplicit true
@[expose] public section
public section
open IntersectionBounds
open Finset Submodule
universe u v
variable {V : Type u} {K : Type v} [Field K]
variable (F : Finset (Finset V)) (L : Finset K)
open Classical
namespace IntersectionBounds
theorem _root_.solution (A B : F) (h : ((A.val ∩ B.val).card : K) ∈ L) :
    separator F L A.val B = 0 := by
  classical
  simp only [separator, Finset.prod_apply]
  apply Finset.prod_eq_zero h
  simp
end IntersectionBounds
