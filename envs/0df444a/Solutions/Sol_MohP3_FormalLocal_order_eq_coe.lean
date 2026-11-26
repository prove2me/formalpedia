-- Prove2me | solution 1 for MohP3.FormalLocal.order_eq_coe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:57:40.036393+00:00
-- url     : https://prove2.me/submissions/97659091-71e5-43b5-a215-c6a31970df02

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
omit [CharZero k]
namespace MohP3.FormalLocal
theorem _root_.solution {q : PowerSeries k} (hq : q ≠ 0) : q.order = (q.order.toNat : ℕ∞) := by
  rw [ENat.coe_toNat]
  exact (PowerSeries.order_finite_iff_ne_zero.mpr hq).ne
end MohP3.FormalLocal
