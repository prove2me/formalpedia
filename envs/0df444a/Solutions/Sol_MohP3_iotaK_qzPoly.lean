-- Prove2me | solution 1 for MohP3.iotaK_qzPoly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:27:19.950195+00:00
-- url     : https://prove2.me/submissions/b9d25131-00fc-4536-95f8-9bee621ea3fe

module
public import Definitions.Def_MohP3_GenClosure
public import Definitions.Def_MohP3_IndependenceK
public import Definitions.Def_MohP3_GlobalK
public import Theorems.Thm_MohP3_iotaK_X
public import Theorems.Thm_MohP3_iotaK_C
attribute [local simp] MohP3.iotaK_X
attribute [local simp] MohP3.iotaK_C

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3
variable (k : Type*) [Field k] [CharZero k]
omit [CharZero k]
namespace MohP3
theorem _root_.solution (i j : Fin 8) : iotaK k (qzPoly k i j) = Gen.qzA (yk k) i j := by
  rw [qzPoly, Gen.qzA, map_mul, map_pow, iotaK_C, iotaK_X]
  congr 1
end MohP3
