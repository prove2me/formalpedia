-- Prove2me | solution 1 for MohP3.FormalLocal.psi_f3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:18:20.084425+00:00
-- url     : https://prove2.me/submissions/680414b0-5dcc-4f14-b395-0e5d7b072091

module
public import Definitions.Def_MohP3_Generic
public import Definitions.Def_MohP3_FormalLocal

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPowerSeries
open MohP3 MohP3.FormalLocal
variable (k : Type*) [Field k] [CharZero k]
omit [CharZero k]
namespace MohP3.FormalLocal
theorem _root_.solution : psi k (Gen.f3 (xs k) (ys k) (zs k)) = 0 := by
  simp only [Gen.f3, map_add, map_sub, map_mul, map_pow, map_ofNat, psi_xs, psi_ys, psi_zs]
  ring
end MohP3.FormalLocal
