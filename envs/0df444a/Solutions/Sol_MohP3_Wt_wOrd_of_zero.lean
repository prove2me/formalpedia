-- Prove2me | solution 1 for MohP3.Wt.wOrd_of_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:59:23.498799+00:00
-- url     : https://prove2.me/submissions/2d494411-6f14-4ab8-a575-cb4c17af87c3

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
theorem _root_.solution {n : ℕ} : WOrd (0 : MvPowerSeries (Fin 3) k) n := by
  intro d _; simp
end MohP3.Wt
