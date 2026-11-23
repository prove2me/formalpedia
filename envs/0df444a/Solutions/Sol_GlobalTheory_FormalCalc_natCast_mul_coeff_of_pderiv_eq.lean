-- Prove2me | solution 1 for GlobalTheory.FormalCalc.natCast_mul_coeff_of_pderiv_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:29:19.151716+00:00
-- url     : https://prove2.me/submissions/676f9fdf-3d8d-4b38-a67b-8eb0012b11aa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.FormalCalc
open MvPowerSeries Finsupp
variable {σ ι A : Type*} [CommRing A]
namespace GlobalTheory.FormalCalc
theorem _root_.solution {f a : MvPowerSeries σ A} {s : σ}
    (h : pderiv A s f = a) {α : σ →₀ ℕ} (hα : α s ≠ 0) :
    (α s : A) * coeff α f = coeff (α - single s 1) a := by
  have hle : single s 1 ≤ α := single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hα)
  rw [← h, coeff_pderiv, tsub_add_cancel_of_le hle, coe_tsub, Pi.sub_apply, single_eq_same,
    Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hα), Nat.cast_one, sub_add_cancel, mul_comm]
end GlobalTheory.FormalCalc
