-- Prove2me | solution 1 for MohP3.Wt.yOrd_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:46:46.645456+00:00
-- url     : https://prove2.me/submissions/87497ac4-0e2e-4671-84a7-0f1d63e618f0

module
public import Mathlib
public import Definitions.Def_MohP3_Order
public import Theorems.Thm_MohP3_Wt_yOrd_add
public import Theorems.Thm_MohP3_Wt_yOrd_neg

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPowerSeries
open MohP3 MohP3.Wt
variable {k : Type*} [CommRing k]
namespace MohP3.Wt
theorem _root_.solution {p q : PowerSeries k} {n : ℕ} (hp : YOrd p n) (hq : YOrd q n) :
    YOrd (p - q) n := by rw [sub_eq_add_neg]; exact yOrd_add hp (yOrd_neg hq)
end MohP3.Wt
