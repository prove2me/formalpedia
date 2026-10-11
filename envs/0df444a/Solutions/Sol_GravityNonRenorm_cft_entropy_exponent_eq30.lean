-- Prove2me | solution 1 for GravityNonRenorm.cft_entropy_exponent_eq30
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-10T12:03:57.603983+00:00
-- url     : https://prove2.me/submissions/e4cf8913-1817-45f6-9a7a-f8f5a05db679

import Definitions.Def_GravityNonRenorm_Defs
import Mathlib

open GravityNonRenorm Filter Asymptotics

namespace GravityNonRenorm

theorem cfte30_main (d : ℕ) (hd : 2 ≤ d) (a b R : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hR : 0 < R) :
    (fun E : ℝ => cftEntropyOfEnergy d a b R E) =Θ[atTop]
      (fun E : ℝ => E ^ (((d : ℝ) - 1) / d)) := by
  set c : ℝ := b * R ^ (d - 1) with hc_def
  have hc : 0 < c := by positivity
  set x : ℝ := ((d : ℝ) - 1) / d with hx_def
  set K : ℝ := a * R ^ (d - 1) / c ^ x with hK_def
  have hK : K ≠ 0 := by
    have : 0 < c ^ x := Real.rpow_pos_of_pos hc x
    positivity
  have hexp : (1 / (d : ℝ)) * ((d - 1 : ℕ) : ℝ) = x := by
    rw [hx_def, Nat.cast_sub (by omega : 1 ≤ d)]
    push_cast
    ring
  have heq : (fun E : ℝ => cftEntropyOfEnergy d a b R E) =ᶠ[atTop]
      (fun E : ℝ => K * E ^ x) := by
    filter_upwards [eventually_gt_atTop 0] with E hE
    unfold cftEntropyOfEnergy
    rw [← hc_def, mul_pow, ← Real.rpow_mul_natCast (div_nonneg hE.le hc.le), hexp,
      Real.div_rpow hE.le hc.le, hK_def]
    field_simp
  exact heq.trans_isTheta ((isTheta_const_mul_left hK).2 (isTheta_refl _ _))

end GravityNonRenorm

theorem solution (d : ℕ) (hd : 2 ≤ d) (a b R : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hR : 0 < R) :
    (fun E : ℝ => cftEntropyOfEnergy d a b R E) =Θ[atTop]
      (fun E : ℝ => E ^ (((d : ℝ) - 1) / d)) :=
  GravityNonRenorm.cfte30_main d hd a b R ha hb hR
