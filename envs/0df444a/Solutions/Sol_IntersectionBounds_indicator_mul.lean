-- Prove2me | solution 1 for IntersectionBounds.indicator_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:46:33.944012+00:00
-- url     : https://prove2.me/submissions/f26ed12b-652b-4f47-b601-cc2bdc17d880

module
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.NormNum
public import Definitions.Def_IntersectionBounds_EvaluationSpace

set_option autoImplicit true
@[expose] public section
public section
open IntersectionBounds
open Finset Submodule
universe u v
variable {V : Type u} {K : Type v} [Field K]
variable (F : Finset (Finset V))
open Classical
namespace IntersectionBounds
theorem _root_.solution (S T : Finset V) :
    indicator F S * indicator F T = (indicator F (S ∪ T) : F → K) := by
  classical
  funext B
  by_cases hs : S ⊆ B.val <;> by_cases ht : T ⊆ B.val <;> simp [indicator, Finset.union_subset_iff, hs, ht]
end IntersectionBounds
