-- Prove2me | solution 1 for MohP3.FormalLocal.order_exp8
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:58:29.245261+00:00
-- url     : https://prove2.me/submissions/f0e5e9c9-ebe4-47ef-b012-2d6759eaa46b

module
public import Definitions.Def_MohP3_Generic
public import Definitions.Def_MohP3_FormalLocal
public import Theorems.Thm_MohP3_FormalLocal_order_eq_coe

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPowerSeries
open MohP3 MohP3.FormalLocal
variable (k : Type*) [Field k] [CharZero k]
omit [CharZero k]
namespace MohP3.FormalLocal
theorem _root_.solution {q : PowerSeries k} (hq : q ≠ 0) :
    (exp8 k q).order = ((8 * q.order.toNat : ℕ) : ℕ∞) := by
  rw [exp8, PowerSeries.order_expand, order_eq_coe k hq, ENat.toNat_coe]
  push_cast
  simp
end MohP3.FormalLocal
