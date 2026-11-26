-- Prove2me | solution 1 for MohP3.Gen.f3_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:52:32.234706+00:00
-- url     : https://prove2.me/submissions/7909ebd1-5692-4552-9194-7ffc1165f495

module
public import Mathlib
public import Definitions.Def_MohP3_Generic

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MohP3 MohP3.Gen
variable {A : Type*} [CommRing A]
variable (x y z : A)
namespace MohP3.Gen
theorem _root_.solution : f3 x y z ∈ P x y z := Ideal.subset_span (by simp)
end MohP3.Gen
