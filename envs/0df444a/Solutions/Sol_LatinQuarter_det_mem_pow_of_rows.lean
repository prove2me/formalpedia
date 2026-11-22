-- Prove2me | solution 1 for LatinQuarter.det_mem_pow_of_rows
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:21:37.279558+00:00
-- url     : https://prove2.me/submissions/a8b2e409-f34f-4f9e-9da3-9444b0653c50

module
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.RingTheory.Ideal.Operations
public import Definitions.Def_LeanPool_LatinQuarter_Minors

set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter
open scoped BigOperators Matrix
variable {R : Type*} [CommRing R]
namespace LatinQuarter
theorem _root_.solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι R) (J : Ideal R) (s : Finset ι)
    (h : ∀ i ∈ s, ∀ j, M i j ∈ J) : M.det ∈ J ^ s.card := by
  classical
  rw [← Matrix.det_transpose, Matrix.det_apply']
  apply Submodule.sum_mem
  intro σ _
  apply Ideal.mul_mem_left
  change (∏ i, M i (σ i)) ∈ J ^ s.card
  rw [← Finset.prod_mul_prod_compl s]
  apply Ideal.mul_mem_right
  have hp := Ideal.prod_mem_prod (I := fun _ : ι => J) (x := fun i => M i (σ i))
    (s := s) (fun i hi => h i hi (σ i))
  simpa using hp
end LatinQuarter
