-- Prove2me | solution 1 for MohP3.vv_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:45:21.713804+00:00
-- url     : https://prove2.me/submissions/7bb53518-ff09-4c7a-b5c1-baefc14f6346

module
public import Mathlib
public import Definitions.Def_MohP3_Independence

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Polynomial
open MohP3
namespace MohP3
theorem _root_.solution (i : Fin 8) : vv i ≠ 0 := by
  fin_cases i <;> simp [vv] <;> intro h <;>
    · have := congrArg (fun r : ℚ[X] => r.coeff 0) h
      simp [coeff_X_pow] at this
end MohP3
