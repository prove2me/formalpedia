-- Prove2me | solution 1 for MohP3.HilbertBurch.range_fvec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:38:05.071172+00:00
-- url     : https://prove2.me/submissions/5442508b-ca08-4ee6-81a6-ef9a7ec16d06

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
namespace MohP3.HilbertBurch
theorem _root_.solution (x y z : A) :
    Set.range (fvec x y z) = {Gen.f1 x y z, Gen.f2 x y z, Gen.f3 x y z, Gen.f4 x y z} := by
  ext w
  simp only [Set.mem_range, Fin.exists_fin_succ, Fin.exists_fin_zero, fvec, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  simp [eq_comm]
end MohP3.HilbertBurch
