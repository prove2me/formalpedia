-- Prove2me | solution 1 for MohP3.HilbertBurch.f1_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:12:20.822965+00:00
-- url     : https://prove2.me/submissions/3d96f82e-fd9e-41bc-96ae-71ee9651057a

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
theorem _root_.solution (x y z : A) : Gen.f1 x y z ∈ Ideal.span (Set.range (fvec x y z)) :=
  Ideal.subset_span ⟨0, rfl⟩
end MohP3.HilbertBurch
