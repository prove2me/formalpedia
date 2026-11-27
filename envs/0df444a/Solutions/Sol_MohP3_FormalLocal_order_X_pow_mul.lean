-- Prove2me | solution 1 for MohP3.FormalLocal.order_X_pow_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:18:44.343002+00:00
-- url     : https://prove2.me/submissions/0134426a-87e7-48ec-8f0f-cdbe560498e7

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
theorem _root_.solution (n : ℕ) (w : PowerSeries k) (hw : PowerSeries.coeff 0 w ≠ 0) :
    ((PowerSeries.X : PowerSeries k)^n * w).order = (n : ℕ∞) := by
  have h0 : w.order = 0 := le_antisymm (by simpa using PowerSeries.order_le 0 hw) zero_le
  rw [PowerSeries.order_mul, PowerSeries.order_X_pow, h0, add_zero]
end MohP3.FormalLocal
