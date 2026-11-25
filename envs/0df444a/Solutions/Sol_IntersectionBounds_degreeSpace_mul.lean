-- Prove2me | solution 1 for IntersectionBounds.degreeSpace_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:50:31.67662+00:00
-- url     : https://prove2.me/submissions/18e3e492-5bd6-4fbb-aa3c-4c558b88513e

module
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.NormNum
public import Definitions.Def_IntersectionBounds_EvaluationSpace
public import Theorems.Thm_IntersectionBounds_indicator_mem_degree
public import Theorems.Thm_IntersectionBounds_indicator_mul

set_option autoImplicit true
@[expose] public section
public section
open IntersectionBounds
open Finset Submodule
universe u v
variable {V : Type u} {K : Type v} [Field K]
variable (F : Finset (Finset V))
namespace IntersectionBounds
theorem _root_.solution {a b : ℕ} {f g : F → K}
    (hf : f ∈ degreeSpace F a) (hg : g ∈ degreeSpace F b) :
    f * g ∈ degreeSpace F (a + b) := by
  classical
  change f ∈ span K _ at hf
  change g ∈ span K _ at hg
  induction hf, hg using Submodule.span_induction₂ with
  | mem_mem f g hf hg =>
    obtain ⟨S, hS, rfl⟩ := hf
    obtain ⟨T, hT, rfl⟩ := hg
    rw [indicator_mul]
    exact indicator_mem_degree F _ _ ((Finset.card_union_le _ _).trans (add_le_add hS hT))
  | zero_left g _ => simp
  | zero_right f _ => simp
  | add_left f₁ f₂ g _ _ _ h₁ h₂ =>
    simpa [add_mul] using (degreeSpace F (a + b)).add_mem h₁ h₂
  | add_right f g₁ g₂ _ _ _ h₁ h₂ =>
    simpa [mul_add] using (degreeSpace F (a + b)).add_mem h₁ h₂
  | smul_left c f g _ _ h =>
    simpa [smul_mul_assoc] using (degreeSpace F (a + b)).smul_mem c h
  | smul_right c f g _ _ h =>
    simpa [mul_smul_comm] using (degreeSpace F (a + b)).smul_mem c h
end IntersectionBounds
