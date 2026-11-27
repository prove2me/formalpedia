-- Prove2me | solution 1 for MohP3.key_z_divK
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:27:13.408941+00:00
-- url     : https://prove2.me/submissions/d45ab5e2-3329-4117-945f-98cb27f86330

module
public import Definitions.Def_MohP3_GenClosure
public import Definitions.Def_MohP3_IndependenceK
public import Definitions.Def_MohP3_GlobalK
public import Theorems.Thm_MohP3_C18_mul_18K
public import Theorems.Thm_MohP3_Gen_key_zA


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3
variable (k : Type*) [Field k] [CharZero k]
namespace MohP3
theorem _root_.solution (i : Fin 8) :
    zk k * hhK k i = MvPolynomial.C ((18 : k)⁻¹) *
      ((∑ j, Gen.qzA (yk k) i j * hhK k j) +
        ∑ j, Gen.wzA (xk k) (yk k) (zk k) i j * ffK k j) := by
  have h : (18 : Rk k) * (zk k * hhK k i) =
      (∑ j, Gen.qzA (yk k) i j * hhK k j) +
        ∑ j, Gen.wzA (xk k) (yk k) (zk k) i j * ffK k j :=
    Gen.key_zA (xk k) (yk k) (zk k) i
  rw [← h, ← mul_assoc, C18_mul_18K, one_mul]
end MohP3
