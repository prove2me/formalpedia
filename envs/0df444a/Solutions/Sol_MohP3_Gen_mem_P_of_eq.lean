-- Prove2me | solution 1 for MohP3.Gen.mem_P_of_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:53:48.298827+00:00
-- url     : https://prove2.me/submissions/6592e834-6d98-4142-8f5d-c586c10cfc5a

module
public import Mathlib
public import Definitions.Def_MohP3_Generic
public import Theorems.Thm_MohP3_Gen_f1_mem
public import Theorems.Thm_MohP3_Gen_f2_mem
public import Theorems.Thm_MohP3_Gen_f3_mem
public import Theorems.Thm_MohP3_Gen_f4_mem

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MohP3 MohP3.Gen
variable {A : Type*} [CommRing A]
variable (x y z : A)
namespace MohP3.Gen
theorem _root_.solution {x y z : A} {g c1 c2 c3 c4 : A}
    (h : g = c1 * f1 x y z + c2 * f2 x y z + c3 * f3 x y z + c4 * f4 x y z) : g ∈ P x y z := by
  rw [h]
  exact (P x y z).add_mem ((P x y z).add_mem ((P x y z).add_mem
    (Ideal.mul_mem_left _ _ (f1_mem x y z)) (Ideal.mul_mem_left _ _ (f2_mem x y z)))
    (Ideal.mul_mem_left _ _ (f3_mem x y z))) (Ideal.mul_mem_left _ _ (f4_mem x y z))
end MohP3.Gen
