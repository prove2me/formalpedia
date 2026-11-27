-- Prove2me | solution 1 for MohP3.RepP_all
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:34:18.877736+00:00
-- url     : https://prove2.me/submissions/18151d7f-e7a5-4573-a67d-619bef1ef6f9

module
public import Definitions.Def_MohP3_GenClosure
public import Definitions.Def_MohP3_IndependenceK
public import Definitions.Def_MohP3_GlobalK
public import Theorems.Thm_MohP3_RepP_C
public import Theorems.Thm_MohP3_RepP_add
public import Theorems.Thm_MohP3_RepP_mul_yk
public import Theorems.Thm_MohP3_RepP_mul_xk
public import Theorems.Thm_MohP3_RepP_mul_zk

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3
variable (k : Type*) [Field k] [CharZero k]
namespace MohP3
theorem _root_.solution (g : Rk k) : RepP k g := by
  induction g using MvPolynomial.induction_on with
  | C a => exact RepP_C k a
  | add p q hp hq => exact RepP_add k hp hq
  | mul_X p i hp =>
      fin_cases i
      · rw [mul_comm]; exact RepP_mul_xk k hp
      · rw [mul_comm]; exact RepP_mul_yk k hp
      · rw [mul_comm]; exact RepP_mul_zk k hp
end MohP3
