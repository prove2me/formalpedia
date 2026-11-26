-- Prove2me | solution 1 for Kyprianou.Ch04.geometricWorkloadResolventArithmetic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:46:26.014105+00:00
-- url     : https://prove2.me/submissions/c1994bfc-1565-4a94-b9ca-20bce5218a62

import Mathlib
open scoped ENNReal
set_option autoImplicit false

/-- The geometric resolvent with normalized tail transform equals the workload Laplace ratio. -/
theorem solution (r : ENNReal) (d a p : ℝ)
    (hr0 : 0 < r) (hr1 : r < 1) (hd : 0 < d) (ha : 0 < a)
    (hp : 0 < p) (hgap : p ≤ d*a) :
    ((1-r) * (1-r*((ENNReal.ofReal d*r)⁻¹ *
        ENNReal.ofReal ((d*a-p)/a)))⁻¹).toReal =
      (d-d*r.toReal)*a/p := by
  let K := ENNReal.ofReal d*r
  let gap := (d*a-p)/a
  let z := r*(K⁻¹*ENNReal.ofReal gap)
  have hrTop : r ≠ ⊤ := ne_of_lt (hr1.trans ENNReal.one_lt_top)
  have hrReal : 0 < r.toReal := ENNReal.toReal_pos hr0.ne' hrTop
  have hK0 : K ≠ 0 := (mul_ne_zero ((ENNReal.ofReal_pos.mpr hd).ne') hr0.ne')
  have hzTop : z ≠ ⊤ :=
    ENNReal.mul_ne_top hrTop (ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hK0) ENNReal.ofReal_ne_top)
  have hg : 0 ≤ gap := div_nonneg (sub_nonneg.mpr hgap) ha.le
  have hz : z.toReal = gap/d := by
    dsimp [z,K]
    rw [ENNReal.toReal_mul,ENNReal.toReal_mul,ENNReal.toReal_inv,ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hd.le,ENNReal.toReal_ofReal hg]
    field_simp [hd.ne',hrReal.ne']
    <;> ring
  have hz1 : z < 1 := by
    apply (ENNReal.toReal_lt_toReal hzTop ENNReal.one_ne_top).mp
    rw [ENNReal.toReal_one,hz]
    apply (div_lt_iff₀ hd).2
    dsimp [gap]
    apply (div_lt_iff₀ ha).2
    linarith
  change ((1-r)*(1-z)⁻¹).toReal = _
  rw [ENNReal.toReal_mul,ENNReal.toReal_inv,
    ENNReal.toReal_sub_of_le hr1.le ENNReal.one_ne_top,
    ENNReal.toReal_sub_of_le hz1.le ENNReal.one_ne_top,ENNReal.toReal_one,hz]
  dsimp [gap]
  field_simp [hd.ne',ha.ne',hp.ne']
  <;> ring
