-- Prove2me | solution 1 for IntersectionBounds.factor_mem_degree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:50:56.168996+00:00
-- url     : https://prove2.me/submissions/bfc7825b-3bdb-4162-913f-e2593eceb012

module
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.NormNum
public import Definitions.Def_IntersectionBounds_EvaluationSpace
public import Theorems.Thm_IntersectionBounds_indicator_mem_degree
public import Theorems.Thm_IntersectionBounds_indicator_empty
public import Theorems.Thm_IntersectionBounds_intersection_as_sum
attribute [local simp] IntersectionBounds.indicator_empty

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
theorem _root_.solution (A : Finset V) (l : K) :
    (fun B : F => ((A ∩ B.val).card : K) - l) ∈ degreeSpace F 1 := by
  classical
  have hi : (fun B : F => ((A ∩ B.val).card : K)) ∈ degreeSpace F 1 := by
    rw [intersection_as_sum]
    apply Submodule.sum_mem
    intro a _
    exact indicator_mem_degree F {a} 1 (by simp)
  have hl : (fun _ : F => l) ∈ degreeSpace F 1 := by
    have h := (degreeSpace F 1).smul_mem l (indicator_mem_degree F ∅ 1 (by simp))
    simpa only [indicator_empty, Pi.smul_def, Pi.one_apply, smul_eq_mul, mul_one] using h
  exact (degreeSpace (K := K) F 1).sub_mem hi hl
end IntersectionBounds
