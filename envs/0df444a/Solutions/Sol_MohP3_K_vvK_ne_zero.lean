-- Prove2me | solution 1 for MohP3.K.vvK_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:26:01.106031+00:00
-- url     : https://prove2.me/submissions/ea2cd762-09aa-4251-9820-cc1f1df38e0d

module
public import Mathlib
public import Definitions.Def_MohP3_IndependenceK

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Polynomial
open MohP3 MohP3.K
variable (k : Type*) [Field k]
variable {k}
variable (k) [CharZero k]
namespace MohP3.K
theorem _root_.solution (i : Fin 8) : vvK k i ≠ 0 := by
  fin_cases i <;> simp [vvK] <;> intro h <;>
    · have := congrArg (fun r : Polynomial k => r.coeff 0) h
      simp [coeff_X_pow] at this
end MohP3.K
