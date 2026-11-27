-- Prove2me | solution 1 for MohP3.FormalLocal.order_vvS
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:19:54.181589+00:00
-- url     : https://prove2.me/submissions/3f05c9c0-80e8-42b2-a0e8-721e8f22f823

module
public import Definitions.Def_MohP3_Generic
public import Definitions.Def_MohP3_FormalLocal
public import Theorems.Thm_MohP3_FormalLocal_order_X_pow_mul

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPowerSeries
open MohP3 MohP3.FormalLocal
variable (k : Type*) [Field k] [CharZero k]
namespace MohP3.FormalLocal
theorem _root_.solution (i : Fin 8) : (vvS k i).order = (ooS i : ℕ∞) := by
  fin_cases i
  · simp [vvS, ooS]
  · simpa [vvS, ooS] using
      order_X_pow_mul k 6 (1 + PowerSeries.X^25) (by simp)
  · simp [vvS, ooS]
  · simpa [vvS, ooS] using
      order_X_pow_mul k 12 (1 + 2*PowerSeries.X^25 + PowerSeries.X^50) (by simp)
  · simp [vvS, ooS]
  · simpa [vvS, ooS] using
      order_X_pow_mul k 43 (3 + 3*PowerSeries.X^25 + PowerSeries.X^50) (by simp [map_ofNat])
  · simpa [vvS, ooS] using
      order_X_pow_mul k 45 (-2 - PowerSeries.X^25) (by simp [map_ofNat])
  · simp [vvS, ooS]
end MohP3.FormalLocal
