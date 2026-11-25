-- Prove2me | solution 1 for IntersectionBounds.indicator_mem_degree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:41:59.364667+00:00
-- url     : https://prove2.me/submissions/bc221379-1cb4-43dc-8016-bf004cfb7b52

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
namespace IntersectionBounds
theorem _root_.solution (T : Finset V) (d : ℕ) (h : T.card ≤ d) :
    (indicator F T : F → K) ∈ degreeSpace F d := subset_span ⟨T, h, rfl⟩
end IntersectionBounds
