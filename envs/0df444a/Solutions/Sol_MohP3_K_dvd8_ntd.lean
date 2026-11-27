-- Prove2me | solution 1 for MohP3.K.dvd8_ntd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:26:37.53433+00:00
-- url     : https://prove2.me/submissions/419a273d-0ded-4fc5-a22d-0501f4d5898e

module
public import Mathlib
public import Definitions.Def_MohP3_IndependenceK
public import Theorems.Thm_MohP3_K_comp_X8_coeff
public import Theorems.Thm_MohP3_K_comp_X8_ne_zero

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Polynomial
open MohP3 MohP3.K
variable (k : Type*) [Field k]
variable {k}
namespace MohP3.K
theorem _root_.solution {p : Polynomial k} (hp : p ≠ 0) : 8 ∣ (p.comp (X ^ 8)).natTrailingDegree := by
  by_contra h
  exact (Polynomial.coeff_natTrailingDegree_ne_zero.mpr (comp_X8_ne_zero hp))
    (comp_X8_coeff p _ h)
end MohP3.K
