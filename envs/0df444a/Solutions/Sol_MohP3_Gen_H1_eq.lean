-- Prove2me | solution 1 for MohP3.Gen.H1_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:48:38.806637+00:00
-- url     : https://prove2.me/submissions/46c3b787-c8ba-4e5d-87a9-54e7190209bf

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
theorem _root_.solution : H1 x y z = (-24*x)*f1 x y z + ell x y z*f3 x y z + 81*f4 x y z := by
  simp only [H1]; ring
end MohP3.Gen
