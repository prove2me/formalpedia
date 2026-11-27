-- Prove2me | solution 1 for MohP3.key_z
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:17:39.892319+00:00
-- url     : https://prove2.me/submissions/1d099f90-3032-4113-800d-6af950538c15

module
public import Definitions.Def_MohP3_Certificate
public import Definitions.Def_MohP3_Closure
public import Theorems.Thm_MohP3_key_z_0
public import Theorems.Thm_MohP3_key_z_1
public import Theorems.Thm_MohP3_key_z_2
public import Theorems.Thm_MohP3_key_z_3
public import Theorems.Thm_MohP3_key_z_4
public import Theorems.Thm_MohP3_key_z_5
public import Theorems.Thm_MohP3_key_z_6
public import Theorems.Thm_MohP3_key_z_7

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3
namespace MohP3
theorem _root_.solution (i : Fin 8) : (18 : R) * (z * hh i) - ∑ j, iota (QZ i j) * hh j ∈ P := by
  fin_cases i
  exacts [key_z_0, key_z_1, key_z_2, key_z_3, key_z_4, key_z_5, key_z_6, key_z_7]
end MohP3
