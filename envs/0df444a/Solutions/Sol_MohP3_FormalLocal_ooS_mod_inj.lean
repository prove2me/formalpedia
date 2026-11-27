-- Prove2me | solution 1 for MohP3.FormalLocal.ooS_mod_inj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:18:43.815468+00:00
-- url     : https://prove2.me/submissions/e2cdbda0-79f9-4ad8-aa60-ea70643d41db

module
public import Definitions.Def_MohP3_Generic
public import Definitions.Def_MohP3_FormalLocal

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPowerSeries
open MohP3 MohP3.FormalLocal
variable (k : Type*) [Field k] [CharZero k]
namespace MohP3.FormalLocal
theorem _root_.solution {i j : Fin 8} (h : ooS i % 8 = ooS j % 8) : i = j := by
  fin_cases i <;> fin_cases j <;> simp_all [ooS]
end MohP3.FormalLocal
