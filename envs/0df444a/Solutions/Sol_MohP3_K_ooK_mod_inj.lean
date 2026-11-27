-- Prove2me | solution 1 for MohP3.K.ooK_mod_inj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:26:27.437626+00:00
-- url     : https://prove2.me/submissions/953e1417-aa04-4f98-a458-3827b111efdb

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
theorem _root_.solution {i j : Fin 8} (h : ooK i % 8 = ooK j % 8) : i = j := by
  fin_cases i <;> fin_cases j <;> simp_all [ooK]
end MohP3.K
