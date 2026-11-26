-- Prove2me | solution 1 for MohP3.dvd8_ntd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:46:19.271465+00:00
-- url     : https://prove2.me/submissions/301c6c6a-566d-4c4b-a846-1b6189263697

module
public import Mathlib
public import Definitions.Def_MohP3_Independence
public import Theorems.Thm_MohP3_comp_X8_coeff
public import Theorems.Thm_MohP3_comp_X8_ne_zero

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Polynomial
open MohP3
namespace MohP3
theorem _root_.solution {p : ℚ[X]} (hp : p ≠ 0) : 8 ∣ (p.comp (X^8)).natTrailingDegree := by
  by_contra h
  exact (Polynomial.coeff_natTrailingDegree_ne_zero.mpr (comp_X8_ne_zero hp))
    (comp_X8_coeff p _ h)
end MohP3
