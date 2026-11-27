-- Prove2me | solution 1 for MohP3.Gen.mem_Q_of_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:45:10.048566+00:00
-- url     : https://prove2.me/submissions/e8fc2b49-c16f-45c7-bf30-a3a563db2f83

module
public import Mathlib
public import Definitions.Def_MohP3_Generic
public import Theorems.Thm_MohP3_Gen_H1_mem
public import Theorems.Thm_MohP3_Gen_H2_mem

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MohP3 MohP3.Gen
variable {A : Type*} [CommRing A]
variable (x y z : A)
namespace MohP3.Gen
theorem _root_.solution {x y z : A} {g a b : A} (h : g = a * H1 x y z + b * H2 x y z) : g ∈ Q x y z := by
  rw [h]
  exact (Q x y z).add_mem (Ideal.mul_mem_left _ _ (H1_mem x y z))
    (Ideal.mul_mem_left _ _ (H2_mem x y z))
end MohP3.Gen
