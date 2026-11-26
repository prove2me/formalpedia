-- Prove2me | solution 1 for MohP3.Gen.f2f4_mem_Q
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:09:02.109606+00:00
-- url     : https://prove2.me/submissions/1720acb0-486b-4ba1-a312-81534de49705

module
public import Mathlib
public import Definitions.Def_MohP3_Generic
public import Theorems.Thm_MohP3_Gen_H1_mem
public import Theorems.Thm_MohP3_Gen_H2_mem
public import Theorems.Thm_MohP3_Gen_mem_of_nsmul_mem
public import Theorems.Thm_MohP3_Gen_cert_24

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MohP3 MohP3.Gen
variable {A : Type*} [CommRing A]
variable (x y z : A)
variable [Algebra ℚ A]
namespace MohP3.Gen
theorem _root_.solution : f2 x y z * f4 x y z ∈ Q x y z := by
  refine mem_of_nsmul_mem (n := 4374) (by norm_num) ?_
  rw [show (((4374 : ℕ)) : A) = (4374 : A) by norm_num, cert_24]
  exact (Q x y z).add_mem (Ideal.mul_mem_left _ _ (H1_mem x y z))
    (Ideal.mul_mem_left _ _ (H2_mem x y z))
end MohP3.Gen
