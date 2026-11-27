-- Prove2me | solution 1 for MohP3.good_all
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:20:03.403843+00:00
-- url     : https://prove2.me/submissions/a19680d5-669f-4023-aefe-7bd3a168271e

module
public import Definitions.Def_MohP3_Closure
public import Definitions.Def_MohP3_Independence
public import Definitions.Def_MohP3_Kernel
public import Theorems.Thm_MohP3_good_C
public import Theorems.Thm_MohP3_good_add
public import Theorems.Thm_MohP3_good_mul_y
public import Theorems.Thm_MohP3_good_mul_x
public import Theorems.Thm_MohP3_good_mul_z

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3
namespace MohP3
theorem _root_.solution (g : R) : Good g := by
  induction g using MvPolynomial.induction_on with
  | C a => exact good_C a
  | add p q hp hq => exact good_add hp hq
  | mul_X p i hp =>
      fin_cases i
      · rw [mul_comm]; exact good_mul_x hp
      · rw [mul_comm]; exact good_mul_y hp
      · rw [mul_comm]; exact good_mul_z hp
end MohP3
