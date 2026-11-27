-- Prove2me | solution 1 for MohP3.iotaK_qxPoly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:27:19.504742+00:00
-- url     : https://prove2.me/submissions/b13a9643-b6f2-4c2f-abd9-63c309385d6a

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
theorem _root_.solution (i j : Fin 8) : iotaK k (qxPoly k i j) = Gen.qxA (yk k) i j := by
  rw [qxPoly, Gen.qxA, map_mul, map_pow, iotaK_C, iotaK_X]
  congr 1
end MohP3
