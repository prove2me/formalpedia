-- Prove2me | solution 1 for MohP3.key_x
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:16:26.509975+00:00
-- url     : https://prove2.me/submissions/2e69684e-c5dc-4f01-8642-0e83184ce7e1

module
public import Definitions.Def_MohP3_Certificate
public import Definitions.Def_MohP3_Closure
public import Theorems.Thm_MohP3_key_x_0
public import Theorems.Thm_MohP3_key_x_1
public import Theorems.Thm_MohP3_key_x_2
public import Theorems.Thm_MohP3_key_x_3
public import Theorems.Thm_MohP3_key_x_4
public import Theorems.Thm_MohP3_key_x_5
public import Theorems.Thm_MohP3_key_x_6
public import Theorems.Thm_MohP3_key_x_7

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3
namespace MohP3
theorem _root_.solution (i : Fin 8) : (18 : R) * (x * hh i) - ∑ j, iota (QX i j) * hh j ∈ P := by
  fin_cases i
  exacts [key_x_0, key_x_1, key_x_2, key_x_3, key_x_4, key_x_5, key_x_6, key_x_7]
end MohP3
