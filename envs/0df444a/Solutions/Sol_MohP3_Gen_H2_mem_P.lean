-- Prove2me | solution 1 for MohP3.Gen.H2_mem_P
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:55:07.544166+00:00
-- url     : https://prove2.me/submissions/9d0f9659-469c-4091-9c6d-156bd4c67eeb

module
public import Mathlib
public import Definitions.Def_MohP3_Generic
public import Theorems.Thm_MohP3_Gen_mem_P_of_eq

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MohP3 MohP3.Gen
variable {A : Type*} [CommRing A]
variable (x y z : A)
namespace MohP3.Gen
theorem _root_.solution : H2 x y z ∈ P x y z :=
  mem_P_of_eq (c1 := -12*y) (c2 := 27*x) (c3 := kappa x y z) (c4 := 0) (by simp only [H2]; ring)
end MohP3.Gen
