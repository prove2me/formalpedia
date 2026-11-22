-- Prove2me | solution 1 for LatinQuarter.product_eq_zero_of_repeated_square_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:20:47.709395+00:00
-- url     : https://prove2.me/submissions/b1afc53e-a37d-404c-93bd-3ff8823d434d

module
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.Algebra.Algebra.Operations
public import Definitions.Def_LeanPool_LatinQuarter_SquareZero

set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter
open scoped BigOperators Pointwise
variable {R : Type*} [CommRing R]
namespace LatinQuarter
theorem _root_.solution
    {ι : Type*} [Fintype ι] (f : ι → R)
    {a b : ι} (hab : a ≠ b) (heq : f a = f b)
    (hsq : f a * f a = 0) : ∏ i, f i = 0 := by
  classical
  rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ a)]
  rw [← Finset.mul_prod_erase (Finset.univ.erase a) f
    (Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ b⟩)]
  rw [← mul_assoc, ← heq, hsq, zero_mul]
end LatinQuarter
