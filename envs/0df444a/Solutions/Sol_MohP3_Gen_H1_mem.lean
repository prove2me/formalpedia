-- Prove2me | solution 1 for MohP3.Gen.H1_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:47:21.224465+00:00
-- url     : https://prove2.me/submissions/916f1215-57e3-43bd-8939-8b74e37b14f0

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
theorem _root_.solution : H1 x y z ∈ Q x y z := Ideal.subset_span (by simp)
end MohP3.Gen
