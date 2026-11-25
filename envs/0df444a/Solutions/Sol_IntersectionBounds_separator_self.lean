-- Prove2me | solution 1 for IntersectionBounds.separator_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:46:53.841218+00:00
-- url     : https://prove2.me/submissions/d51c8a9b-d597-45f6-a14e-1713d92acb9e

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
namespace IntersectionBounds
theorem _root_.solution (A : F) :
    separator F L A.val A = ∏ l ∈ L, ((A.val.card : K) - l) := by
  classical
  simp [separator]
end IntersectionBounds
