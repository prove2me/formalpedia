-- Prove2me | solution 1 for MohP3.FormalLocal.psi_f4
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:18:22.917388+00:00
-- url     : https://prove2.me/submissions/501f4301-ef5f-4e33-8d46-14bb79c24b38

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
theorem _root_.solution : psi k (Gen.f4 (xs k) (ys k) (zs k)) = 0 := by
  simp only [Gen.f4, map_add, map_sub, map_mul, map_pow, map_ofNat, psi_xs, psi_ys, psi_zs]
  ring
end MohP3.FormalLocal
