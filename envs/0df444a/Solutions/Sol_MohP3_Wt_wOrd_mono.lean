-- Prove2me | solution 1 for MohP3.Wt.wOrd_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:50:06.544997+00:00
-- url     : https://prove2.me/submissions/45c94fa6-5f21-41b0-b1c2-089453f12d89

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
theorem _root_.solution {F : MvPowerSeries (Fin 3) k} {m n : ℕ} (h : n ≤ m) (hF : WOrd F m) :
    WOrd F n := fun d hd => hF d (lt_of_lt_of_le hd h)
end MohP3.Wt
