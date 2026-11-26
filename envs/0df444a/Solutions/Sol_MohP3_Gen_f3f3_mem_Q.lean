-- Prove2me | solution 1 for MohP3.Gen.f3f3_mem_Q
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:09:24.657798+00:00
-- url     : https://prove2.me/submissions/385d4f28-ec9d-4b7d-bc1c-74ba50518dda

module
public import Mathlib
public import Definitions.Def_MohP3_Generic
public import Theorems.Thm_MohP3_Gen_H1_mem
public import Theorems.Thm_MohP3_Gen_H2_mem
public import Theorems.Thm_MohP3_Gen_mem_of_nsmul_mem
public import Theorems.Thm_MohP3_Gen_cert_33

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MohP3 MohP3.Gen
variable {A : Type*} [CommRing A]
variable (x y z : A)
variable [Algebra ℚ A]
namespace MohP3.Gen
theorem _root_.solution : f3 x y z * f3 x y z ∈ Q x y z := by
  refine mem_of_nsmul_mem (n := 162) (by norm_num) ?_
  rw [show (((162 : ℕ)) : A) = (162 : A) by norm_num, cert_33]
  exact (Q x y z).add_mem (Ideal.mul_mem_left _ _ (H1_mem x y z))
    (Ideal.mul_mem_left _ _ (H2_mem x y z))
end MohP3.Gen
