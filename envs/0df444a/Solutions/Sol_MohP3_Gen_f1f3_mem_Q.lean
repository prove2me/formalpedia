-- Prove2me | solution 1 for MohP3.Gen.f1f3_mem_Q
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:08:27.262693+00:00
-- url     : https://prove2.me/submissions/d964b023-1a01-4dd2-be89-a15b6e536cf2

module
public import Mathlib
public import Definitions.Def_MohP3_Generic
public import Theorems.Thm_MohP3_Gen_H1_mem
public import Theorems.Thm_MohP3_Gen_H2_mem
public import Theorems.Thm_MohP3_Gen_mem_of_nsmul_mem
public import Theorems.Thm_MohP3_Gen_cert_13

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MohP3 MohP3.Gen
variable {A : Type*} [CommRing A]
variable (x y z : A)
variable [Algebra ℚ A]
namespace MohP3.Gen
theorem _root_.solution : f1 x y z * f3 x y z ∈ Q x y z := by
  refine mem_of_nsmul_mem (n := 972) (by norm_num) ?_
  rw [show (((972 : ℕ)) : A) = (972 : A) by norm_num, cert_13]
  exact (Q x y z).add_mem (Ideal.mul_mem_left _ _ (H1_mem x y z))
    (Ideal.mul_mem_left _ _ (H2_mem x y z))
end MohP3.Gen
