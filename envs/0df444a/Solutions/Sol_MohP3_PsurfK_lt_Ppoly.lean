-- Prove2me | solution 1 for MohP3.PsurfK_lt_Ppoly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:37:00.122928+00:00
-- url     : https://prove2.me/submissions/b3bf8db9-258d-4887-ba69-3c51ad673ae7

module
public import Definitions.Def_MohP3_GlobalK
public import Definitions.Def_MohP3_Ara
public import Definitions.Def_MohP3_HeightK
public import Theorems.Thm_MohP3_PsurfK_le_Ppoly
public import Theorems.Thm_MohP3_f4K_notMem_PsurfK
public import Theorems.Thm_MohP3_Gen_f4_mem


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3
variable (k : Type*) [Field k] [CharZero k]
namespace MohP3
theorem _root_.solution : PsurfK k < Ppoly k :=
  lt_of_le_of_ne (PsurfK_le_Ppoly k)
    (fun h => f4K_notMem_PsurfK k (h ▸ Gen.f4_mem (xk k) (yk k) (zk k)))
end MohP3
