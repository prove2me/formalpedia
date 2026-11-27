-- Prove2me | solution 1 for MohP3.Wt.wt_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:19:30.335156+00:00
-- url     : https://prove2.me/submissions/49b10b9a-f6c3-476f-9968-e55161e1dfe3

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
theorem _root_.solution (d e : Fin 3 →₀ ℕ) : wt (d + e) = wt d + wt e := by
  simp only [wt, Finsupp.add_apply]; ring
end MohP3.Wt
