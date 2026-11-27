-- Prove2me | solution 1 for MohP3.FormalLocal.psi_f2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:18:16.712847+00:00
-- url     : https://prove2.me/submissions/bb61562b-f2e5-416c-8e10-bc70f8a2f9b0

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
theorem _root_.solution : psi k (Gen.f2 (xs k) (ys k) (zs k)) = 0 := by
  simp only [Gen.f2, map_add, map_sub, map_mul, map_pow, map_ofNat, psi_xs, psi_ys, psi_zs]
  ring
end MohP3.FormalLocal
