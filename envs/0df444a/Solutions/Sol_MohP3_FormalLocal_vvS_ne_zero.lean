-- Prove2me | solution 1 for MohP3.FormalLocal.vvS_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:20:41.054987+00:00
-- url     : https://prove2.me/submissions/b9fc3297-3fb5-41a9-9597-e1a32df46c0d

module
public import Definitions.Def_MohP3_Generic
public import Definitions.Def_MohP3_FormalLocal
public import Theorems.Thm_MohP3_FormalLocal_order_vvS

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPowerSeries
open MohP3 MohP3.FormalLocal
variable (k : Type*) [Field k] [CharZero k]
namespace MohP3.FormalLocal
theorem _root_.solution (i : Fin 8) : vvS k i ≠ 0 := by
  intro h
  have h2 := order_vvS k i
  rw [h, PowerSeries.order_eq_top.mpr rfl] at h2
  exact (ENat.coe_ne_top _) h2.symm
end MohP3.FormalLocal
