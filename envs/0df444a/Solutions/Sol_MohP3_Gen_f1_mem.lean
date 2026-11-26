-- Prove2me | solution 1 for MohP3.Gen.f1_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:51:57.392587+00:00
-- url     : https://prove2.me/submissions/5fb474c1-4ee6-4239-94dc-1a676cb199eb

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
theorem _root_.solution : f1 x y z ∈ P x y z := Ideal.subset_span (by simp)
end MohP3.Gen
