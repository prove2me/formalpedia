-- Prove2me | solution 1 for MohP3.Wt.yOrd_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:51:07.576469+00:00
-- url     : https://prove2.me/submissions/f548dd75-90eb-4506-9ad9-bd5071d9be1b

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
theorem _root_.solution {p q : PowerSeries k} {n : ℕ} (hp : YOrd p n) (hq : YOrd q n) :
    YOrd (p + q) n := by intro m hm; simp [hp m hm, hq m hm]
end MohP3.Wt
