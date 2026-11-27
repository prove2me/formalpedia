-- Prove2me | solution 1 for MohP3.mem_Q_of_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:45:08.072596+00:00
-- url     : https://prove2.me/submissions/818549c9-6f70-49d6-b07b-6e641f837c51

module
public import Mathlib
public import Definitions.Def_MohP3_Defs
public import Theorems.Thm_MohP3_H1_mem
public import Theorems.Thm_MohP3_H2_mem

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3
namespace MohP3
theorem _root_.solution {g a b : R} (h : g = a * H1 + b * H2) : g ∈ Q := by
  rw [h]
  exact Q.add_mem (Ideal.mul_mem_left _ _ H1_mem) (Ideal.mul_mem_left _ _ H2_mem)
end MohP3
