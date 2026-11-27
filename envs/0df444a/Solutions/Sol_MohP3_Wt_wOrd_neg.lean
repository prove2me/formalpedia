-- Prove2me | solution 1 for MohP3.Wt.wOrd_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:19:42.591439+00:00
-- url     : https://prove2.me/submissions/25a6dc17-f038-4da6-a7c5-bd35edc1e1e7

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
theorem _root_.solution {F : MvPowerSeries (Fin 3) k} {n : ℕ} (hF : WOrd F n) : WOrd (-F) n := by
  intro d hd; simp [hF d hd]
end MohP3.Wt
