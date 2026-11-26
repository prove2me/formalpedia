-- Prove2me | solution 1 for MohP3.Wt.yOrd_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:59:18.209079+00:00
-- url     : https://prove2.me/submissions/fe76d4e5-efc5-4119-a711-082dcd5794ac

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
theorem _root_.solution {p : PowerSeries k} {m n : ℕ} (h : n ≤ m) (hp : YOrd p m) : YOrd p n :=
  fun d hd => hp d (lt_of_lt_of_le hd h)
end MohP3.Wt
