-- Prove2me | solution 1 for MohP3.Wt.yOrd_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:59:39.339848+00:00
-- url     : https://prove2.me/submissions/17bf8cc4-005d-46cf-940c-9accdaf09514

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
theorem _root_.solution (p : PowerSeries k) : YOrd p 0 := by
  intro m hm; exact absurd hm (Nat.not_lt_zero _)
end MohP3.Wt
