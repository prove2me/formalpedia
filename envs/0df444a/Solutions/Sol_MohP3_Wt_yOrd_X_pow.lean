-- Prove2me | solution 1 for MohP3.Wt.yOrd_X_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:59:45.19885+00:00
-- url     : https://prove2.me/submissions/77aed53e-a703-44f7-b867-1f74becd5509

module
public import Mathlib
public import Definitions.Def_MohP3_Order

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPowerSeries
open MohP3 MohP3.Wt
variable {k : Type*} [CommRing k]
namespace MohP3.Wt
theorem _root_.solution (e : ℕ) : YOrd ((PowerSeries.X : PowerSeries k) ^ e) (8 * e) := by
  intro m hm
  rw [PowerSeries.coeff_X_pow]
  have : m ≠ e := by omega
  simp [this]
end MohP3.Wt
