-- Prove2me | solution 1 for MohP3.Wt.wOrd_X
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:19:47.669999+00:00
-- url     : https://prove2.me/submissions/b31a3d33-d9de-4179-af0f-280cb2b9879c

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
theorem _root_.solution (i : Fin 3) : WOrd (X i : MvPowerSeries (Fin 3) k) (wt (Finsupp.single i 1)) := by
  classical
  intro d hd
  rw [MvPowerSeries.coeff_X]
  split
  · next h => exact absurd (h ▸ hd) (lt_irrefl _)
  · rfl
end MohP3.Wt
