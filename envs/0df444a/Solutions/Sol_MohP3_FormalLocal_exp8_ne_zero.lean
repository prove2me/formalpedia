-- Prove2me | solution 1 for MohP3.FormalLocal.exp8_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:19:15.906323+00:00
-- url     : https://prove2.me/submissions/2ba36132-1368-4a05-8703-2c6c44e1b327

module
public import Definitions.Def_MohP3_Generic
public import Definitions.Def_MohP3_FormalLocal
public import Theorems.Thm_MohP3_FormalLocal_order_exp8

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPowerSeries
open MohP3 MohP3.FormalLocal
variable (k : Type*) [Field k] [CharZero k]
omit [CharZero k]
namespace MohP3.FormalLocal
theorem _root_.solution {q : PowerSeries k} (hq : q ≠ 0) : exp8 k q ≠ 0 := by
  intro h
  have h2 := order_exp8 k hq
  rw [h, PowerSeries.order_eq_top.mpr rfl] at h2
  exact (ENat.coe_ne_top _) h2.symm
end MohP3.FormalLocal
