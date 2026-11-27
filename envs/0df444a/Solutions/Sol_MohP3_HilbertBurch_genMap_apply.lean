-- Prove2me | solution 1 for MohP3.HilbertBurch.genMap_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:47:34.776262+00:00
-- url     : https://prove2.me/submissions/0ab10873-0024-4c3c-a145-7a21fc5308a2

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
omit [CharZero k]
namespace MohP3.HilbertBurch
theorem _root_.solution (a : Fin 4 → S k) :
    genMap k a = a 0 * Gen.f1 (X 0) (X 1) (X 2) + a 1 * Gen.f2 (X 0) (X 1) (X 2) +
      a 2 * Gen.f3 (X 0) (X 1) (X 2) + a 3 * Gen.f4 (X 0) (X 1) (X 2) := by
  simp [genMap, fvec, dotProduct, Fin.sum_univ_succ, add_assoc]
end MohP3.HilbertBurch
