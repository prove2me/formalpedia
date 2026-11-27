-- Prove2me | solution 1 for MohP3.Wt.wOrd_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:19:50.702342+00:00
-- url     : https://prove2.me/submissions/57e4ec52-f951-464f-8b21-3ea23c8fe811

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
theorem _root_.solution {F : MvPowerSeries (Fin 3) k} (h : ∀ n, WOrd F n) : F = 0 := by
  ext d
  simpa using h (wt d + 1) d (by omega)
end MohP3.Wt
