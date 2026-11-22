-- Prove2me | solution 1 for LatinQuarter.marked_blocks_product_vanishes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:23:26.172736+00:00
-- url     : https://prove2.me/submissions/62c16cf3-933e-44b3-a47b-04173609eee2

module
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.Algebra.CharP.Frobenius
public import Definitions.Def_LeanPool_LatinQuarter_Minors
public import Definitions.Def_LeanPool_LatinQuarter_SquareZero
public import Definitions.Def_LeanPool_LatinQuarter_Vanishing
public import Theorems.Thm_LatinQuarter_marked_blocks_minor_ideal
public import Theorems.Thm_LatinQuarter_span_square_zero_pow_eq_bot


set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter
open scoped BigOperators Matrix
variable {R : Type*} [CommRing R] [CharP R 2]
namespace LatinQuarter
theorem _root_.solution {k h : ℕ} {ι : Type*} [Fintype ι]
    (A : Matrix (Fin k) (Fin k) R)
    (B : Matrix (Fin k) (Fin h) R)
    (C : Matrix (Fin h) (Fin k) R)
    (D : Matrix (Fin h) (Fin h) R)
    (hA : squareHom.mapMatrix A = 1)
    (hC : C.map squareHom = 0)
    (hD : D.map squareHom = 0)
    (t : ι → ℕ)
    (r c : (i : ι) → Fin (t i) → Fin k ⊕ Fin h)
    (hbudget : h * h < ∑ i, (t i - k)) :
    (∏ i, ((Matrix.fromBlocks A B C D).submatrix (r i) (c i)).det) = 0 := by
  classical
  obtain ⟨z, hz, hm⟩ := marked_blocks_minor_ideal A B C D hA hC hD
  have hp := Ideal.prod_mem_prod (s := Finset.univ)
    (I := fun i => Ideal.span (Set.range z) ^ (t i - k))
    (x := fun i => ((Matrix.fromBlocks A B C D).submatrix (r i) (c i)).det)
    (fun i _ => hm (t i) (r i) (c i))
  rw [Finset.prod_pow_eq_pow_sum] at hp
  rw [span_square_zero_pow_eq_bot z hz (by simpa using hbudget)] at hp
  exact hp
end LatinQuarter
