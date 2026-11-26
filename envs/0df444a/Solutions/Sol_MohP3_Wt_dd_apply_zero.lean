-- Prove2me | solution 1 for MohP3.Wt.dd_apply_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:50:01.133888+00:00
-- url     : https://prove2.me/submissions/454d9200-f077-43c0-b29e-21d2a4ff82f4

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
theorem _root_.solution (a b c : ℕ) : dd a b c 0 = a := by
  simp [dd]
end MohP3.Wt
