-- Prove2me | solution 1 for MohP3.Gen.H1_mem_P
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:55:03.322078+00:00
-- url     : https://prove2.me/submissions/91bc5fa7-1e81-40e0-bddf-53d19a7597b4

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
theorem _root_.solution : H1 x y z ∈ P x y z :=
  mem_P_of_eq (c1 := -24*x) (c2 := 0) (c3 := ell x y z) (c4 := 81) (by simp only [H1]; ring)
end MohP3.Gen
