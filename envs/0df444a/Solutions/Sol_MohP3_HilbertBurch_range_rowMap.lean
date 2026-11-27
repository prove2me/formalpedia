-- Prove2me | solution 1 for MohP3.HilbertBurch.range_rowMap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:40:44.191972+00:00
-- url     : https://prove2.me/submissions/1dc6f252-a010-4d77-9cd7-85cf8bfb1e93

module
public import Definitions.Def_MohP3_Generic
public import Mathlib
public import Definitions.Def_MohP3_HilbertBurch
public import Theorems.Thm_MohP3_HilbertBurch_rowMap_apply
public import Theorems.Thm_MohP3_HilbertBurch_span_fvec
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
theorem _root_.solution (x y z : A) :
    LinearMap.range (rowMap (fvec x y z)) = (Gen.P x y z : Submodule A A) := by
  rw [← span_fvec]
  ext w
  change _ ↔ w ∈ Submodule.span A (Set.range (fvec x y z))
  rw [LinearMap.mem_range, Submodule.mem_span_range_iff_exists_fun]
  simp only [rowMap_apply, dotProduct, smul_eq_mul]
end MohP3.HilbertBurch
