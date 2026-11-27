-- Prove2me | solution 1 for MohP3.HilbertBurch.f4_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:39:51.226209+00:00
-- url     : https://prove2.me/submissions/1582e4e8-f11a-40a4-abac-8494e5f1b96c

module
public import Definitions.Def_MohP3_Generic
public import Mathlib
public import Definitions.Def_MohP3_HilbertBurch

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
theorem _root_.solution (x y z : A) : Gen.f4 x y z ∈ Ideal.span (Set.range (fvec x y z)) :=
  Ideal.subset_span ⟨3, rfl⟩
end MohP3.HilbertBurch
