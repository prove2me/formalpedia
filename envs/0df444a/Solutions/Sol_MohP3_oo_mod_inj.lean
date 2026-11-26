-- Prove2me | solution 1 for MohP3.oo_mod_inj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:45:22.346693+00:00
-- url     : https://prove2.me/submissions/0c5908d0-b359-4b35-9e7b-a89dba780777

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
theorem _root_.solution {i j : Fin 8} (h : oo i % 8 = oo j % 8) : i = j := by
  fin_cases i <;> fin_cases j <;> simp_all [oo]
end MohP3
