-- Prove2me | solution 1 for MohP3.Wt.yOrd_of_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:59:43.929657+00:00
-- url     : https://prove2.me/submissions/3a3b7032-e0bb-4d34-8daa-3be7d6ac1f2d

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
theorem _root_.solution {n : ℕ} : YOrd (0 : PowerSeries k) n := by intro m _; simp
end MohP3.Wt
