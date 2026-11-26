-- Prove2me | solution 1 for MohP3.Wt.wOrd_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:50:15.412775+00:00
-- url     : https://prove2.me/submissions/48e92148-f1a3-4584-87a2-763914ff1d4b

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
theorem _root_.solution {F G : MvPowerSeries (Fin 3) k} {n : ℕ} (hF : WOrd F n) (hG : WOrd G n) :
    WOrd (F + G) n := by
  intro d hd; simp [hF d hd, hG d hd]
end MohP3.Wt
