-- Prove2me | solution 1 for MohP3.Gen.f4_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:52:35.119202+00:00
-- url     : https://prove2.me/submissions/920232dd-ef8a-4773-9790-e25241eed8ac

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
theorem _root_.solution : f4 x y z ∈ P x y z := Ideal.subset_span (by simp)
end MohP3.Gen
