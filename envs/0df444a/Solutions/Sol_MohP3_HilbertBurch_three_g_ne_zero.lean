-- Prove2me | solution 1 for MohP3.HilbertBurch.three_g_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:40:26.531007+00:00
-- url     : https://prove2.me/submissions/cdad139d-7a1f-48e1-817a-4c9ef90d3042

module
public import Definitions.Def_MohP3_Generic
public import Mathlib
public import Definitions.Def_MohP3_HilbertBurch
public import Theorems.Thm_MohP3_HilbertBurch_rowMap_apply
attribute [local simp] MohP3.HilbertBurch.rowMap_apply

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open MohP3 MohP3.HilbertBurch
open Matrix
open MvPolynomial
variable {A : Type*} [CommRing A]
variable (k : Type*) [Field k] [CharZero k]
namespace MohP3.HilbertBurch
theorem _root_.solution : (3 * ((X 1) ^ 5 - (X 2) ^ 4) : MvPolynomial (Fin 3) k) ≠ 0 := by
  intro h
  have := congrArg (MvPolynomial.eval (![0, 1, 0] : Fin 3 → k)) h
  simp at this
end MohP3.HilbertBurch
