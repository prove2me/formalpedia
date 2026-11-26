-- Prove2me | solution 1 for MohP3.Wt.wOrd_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:59:07.341834+00:00
-- url     : https://prove2.me/submissions/c6d1b633-b3fd-472c-9ae4-59cd841411bf

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
theorem _root_.solution (F : MvPowerSeries (Fin 3) k) : WOrd F 0 := by
  intro d hd; exact absurd hd (Nat.not_lt_zero _)
end MohP3.Wt
