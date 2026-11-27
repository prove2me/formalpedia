-- Prove2me | solution 1 for MohP3.Wt.yOrd_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:19:59.384784+00:00
-- url     : https://prove2.me/submissions/e681f167-e038-4925-8a38-fcf0a7dd4127

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
theorem _root_.solution {p : PowerSeries k} {n : ℕ} (hp : YOrd p n) : YOrd (-p) n := by
  intro m hm; simp [hp m hm]
end MohP3.Wt
