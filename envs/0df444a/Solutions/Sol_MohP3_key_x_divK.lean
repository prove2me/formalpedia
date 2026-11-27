-- Prove2me | solution 1 for MohP3.key_x_divK
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:26:57.408037+00:00
-- url     : https://prove2.me/submissions/9803849d-e872-45ee-b5b4-f9e135c08306

module
public import Definitions.Def_MohP3_GenClosure
public import Definitions.Def_MohP3_IndependenceK
public import Definitions.Def_MohP3_GlobalK
public import Theorems.Thm_MohP3_C18_mul_18K
public import Theorems.Thm_MohP3_Gen_key_xA


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3
variable (k : Type*) [Field k] [CharZero k]
namespace MohP3
theorem _root_.solution (i : Fin 8) :
    xk k * hhK k i = MvPolynomial.C ((18 : k)⁻¹) *
      ((∑ j, Gen.qxA (yk k) i j * hhK k j) +
        ∑ j, Gen.wxA (xk k) (yk k) (zk k) i j * ffK k j) := by
  have h : (18 : Rk k) * (xk k * hhK k i) =
      (∑ j, Gen.qxA (yk k) i j * hhK k j) +
        ∑ j, Gen.wxA (xk k) (yk k) (zk k) i j * ffK k j :=
    Gen.key_xA (xk k) (yk k) (zk k) i
  rw [← h, ← mul_assoc, C18_mul_18K, one_mul]
end MohP3
