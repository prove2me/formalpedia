-- Prove2me | solution 1 for IntersectionBounds.separator_mem_degree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:54:50.918095+00:00
-- url     : https://prove2.me/submissions/d1e17ec9-ca7e-4d65-9340-1547b163b6e6

module
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.NormNum
public import Definitions.Def_IntersectionBounds_EvaluationSpace
public import Theorems.Thm_IntersectionBounds_degreeSpace_mul
public import Theorems.Thm_IntersectionBounds_indicator_empty
public import Theorems.Thm_IntersectionBounds_one_mem_degree
public import Theorems.Thm_IntersectionBounds_factor_mem_degree
attribute [local simp] IntersectionBounds.indicator_empty

set_option autoImplicit true
@[expose] public section
public section
open IntersectionBounds
open Finset Submodule
universe u v
variable {V : Type u} {K : Type v} [Field K]
variable (F : Finset (Finset V))
namespace IntersectionBounds
theorem _root_.solution (L : Finset K) (A : Finset V) :
    separator F L A ∈ degreeSpace F L.card := by
  classical
  induction L using Finset.induction with
  | empty => simpa [separator] using (one_mem_degree (K := K) F)
  | @insert l L hl ih =>
    have h := degreeSpace_mul F (factor_mem_degree F A l) ih
    simpa [separator, Finset.prod_insert hl, Finset.card_insert_of_notMem hl, Nat.add_comm] using h
end IntersectionBounds
