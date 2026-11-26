-- Prove2me | solution 1 for MohP3.mem_P_of_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:53:05.562126+00:00
-- url     : https://prove2.me/submissions/3efbcaa2-ccd8-4581-9fdf-ab250552c5e0

module
public import Mathlib
public import Definitions.Def_MohP3_Defs
public import Theorems.Thm_MohP3_f1_mem
public import Theorems.Thm_MohP3_f2_mem
public import Theorems.Thm_MohP3_f3_mem
public import Theorems.Thm_MohP3_f4_mem

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3
namespace MohP3
theorem _root_.solution {g c1 c2 c3 c4 : R}
    (h : g = c1 * f1 + c2 * f2 + c3 * f3 + c4 * f4) : g ∈ P := by
  rw [h]
  exact P.add_mem (P.add_mem (P.add_mem
    (Ideal.mul_mem_left _ _ f1_mem) (Ideal.mul_mem_left _ _ f2_mem))
    (Ideal.mul_mem_left _ _ f3_mem)) (Ideal.mul_mem_left _ _ f4_mem)
end MohP3
