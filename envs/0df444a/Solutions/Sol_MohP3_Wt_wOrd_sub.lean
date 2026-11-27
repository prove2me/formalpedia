-- Prove2me | solution 1 for MohP3.Wt.wOrd_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:20:29.472276+00:00
-- url     : https://prove2.me/submissions/f4acfd1f-bdea-41bc-970b-14c80412caa6

module
public import Mathlib
public import Definitions.Def_MohP3_Order
public import Theorems.Thm_MohP3_Wt_wOrd_add
public import Theorems.Thm_MohP3_Wt_wOrd_neg

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPowerSeries
open MohP3 MohP3.Wt
variable {k : Type*} [CommRing k]
namespace MohP3.Wt
theorem _root_.solution {F G : MvPowerSeries (Fin 3) k} {n : ℕ} (hF : WOrd F n) (hG : WOrd G n) :
    WOrd (F - G) n := by
  rw [sub_eq_add_neg]; exact wOrd_add hF (wOrd_neg hG)
end MohP3.Wt
