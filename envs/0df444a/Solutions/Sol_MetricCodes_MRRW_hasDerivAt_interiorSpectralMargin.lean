-- Prove2me | solution 1 for MetricCodes.MRRW.hasDerivAt_interiorSpectralMargin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.949776+00:00
-- url     : https://prove2.me/submissions/c70ccdfb-5693-4b44-80f1-e5f5100acbab

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Johnson_sqrt_one_sub_centeredDegree_sq
import Theorems.Thm_MetricCodes_MRRW_interior_boundary_delta_relation
import Theorems.Thm_MetricCodes_MRRW_spectralLimit_interior_eq

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.MRRW
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped Topology
namespace MetricCodes.MRRW
theorem _root_.solution
    {δ a u : ℝ}
    (hu : 0 < u) (hua : u < a) (ha : a < (1 : ℝ) / 2)
    (hboundary :
      MetricCodes.Johnson.spectralLimit a 0 0 u =
        MetricCodes.Johnson.asymptoticThreshold δ a) :
    HasDerivAt (interiorSpectralMargin δ a u)
      ((1 - 2 * (a * (1 - a))) *
          (1 - 2 * Real.sqrt (u * (1 - u))) /
        (a * (1 - a) * Real.sqrt (u * (1 - u)) *
          (1 + 2 * Real.sqrt (u * (1 - u))))) 0 := by
  have ha0 : 0 < a := lt_trans hu hua
  have ha1 : 0 < 1 - a := by linarith
  have hu1 : 0 < 1 - u := by linarith
  have hz0 : 0 < 1 - 2 * u := by linarith
  have hm0 : 0 < 1 - 2 * a := by linarith
  have hrad : 0 < 1 - (1 - 2 * u) ^ 2 := by
    nlinarith [mul_pos hu hu1]
  have hmrad : 0 < 1 - (1 - 2 * a) ^ 2 := by
    nlinarith [mul_pos ha0 ha1]
  have hs : 0 < Real.sqrt (u * (1 - u)) :=
    Real.sqrt_pos.mpr (mul_pos hu hu1)
  have hsquare := Real.sq_sqrt (mul_pos hu hu1).le
  have hroot :
      Real.sqrt (1 - (1 - 2 * u) ^ 2) =
        2 * Real.sqrt (u * (1 - u)) := by
    simpa [MetricCodes.Johnson.centeredDegree] using
      MetricCodes.Johnson.sqrt_one_sub_centeredDegree_sq hu (lt_trans hua ha)
  have hdelta :=
    interior_boundary_delta_relation hu hua ha hboundary
  let c : ℝ := interiorSlope a u
  let A : ℝ → ℝ := fun e => a - c * e
  let m : ℝ → ℝ := fun e => 1 - 2 * A e
  let t : ℝ → ℝ := fun e => 1 - 2 * e
  let z : ℝ := 1 - 2 * u
  let q : ℝ := Real.sqrt (1 - z ^ 2)
  let p : ℝ → ℝ := fun e => t e ^ 2 - z ^ 2
  let Q : ℝ → ℝ := fun e => 1 - m e ^ 2
  have hA : HasDerivAt A (-c) 0 := by
    change
      HasDerivAt
        ((fun _ : ℝ => a) - (fun e : ℝ => c * e)) (-c) 0
    simpa using
      (hasDerivAt_const (x := (0 : ℝ)) a).sub
        ((hasDerivAt_id (0 : ℝ)).const_mul c)
  have hm : HasDerivAt m (2 * c) 0 := by
    change
      HasDerivAt
        ((fun _ : ℝ => 1) -
          (fun e : ℝ => 2 * (a - c * e)))
        (2 * c) 0
    simpa using
      (hasDerivAt_const (x := (0 : ℝ)) (1 : ℝ)).sub
        (hA.const_mul 2)
  have ht : HasDerivAt t (-2) 0 := by
    change
      HasDerivAt
        ((fun _ : ℝ => 1) - (fun e : ℝ => 2 * e))
        (-2) 0
    simpa using
      (hasDerivAt_const (x := (0 : ℝ)) (1 : ℝ)).sub
        ((hasDerivAt_id (0 : ℝ)).const_mul 2)
  have hp : HasDerivAt p (-4) 0 := by
    change
      HasDerivAt
        (((fun e : ℝ => 1 - 2 * e) ^ 2) -
          (fun _ : ℝ => z ^ 2))
        (-4) 0
    exact
      ((ht.pow 2).sub
        (hasDerivAt_const (x := (0 : ℝ)) (z ^ 2))).congr_deriv
        (by norm_num)
  have hQ : HasDerivAt Q (-4 * (1 - 2 * a) * c) 0 := by
    change
      HasDerivAt
        ((fun _ : ℝ => 1) -
          ((fun e : ℝ => 1 - 2 * (a - c * e)) ^ 2))
        (-4 * (1 - 2 * a) * c) 0
    exact
      ((hasDerivAt_const (x := (0 : ℝ)) (1 : ℝ)).sub
        (hm.pow 2)).congr_deriv (by dsimp [m, A]; ring)
  have hden1 : z ^ 2 * Q 0 * (1 - z ^ 2) ≠ 0 := by
    simpa [z, Q, m, A] using
      mul_ne_zero
        (mul_ne_zero (pow_ne_zero 2 hz0.ne') hmrad.ne')
        hrad.ne'
  have hden2 : z ^ 2 * Q 0 * q ≠ 0 := by
    have hroot_ne : Real.sqrt (1 - (1 - 2 * u) ^ 2) ≠ 0 :=
      (Real.sqrt_pos.mpr hrad).ne'
    simpa [z, Q, m, A, q] using
      mul_ne_zero
        (mul_ne_zero (pow_ne_zero 2 hz0.ne') hmrad.ne')
        hroot_ne
  have hden3 : 2 * A 0 * (1 - A 0) ≠ 0 := by
    simpa [A] using
      mul_ne_zero
        (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) ha0.ne')
        ha1.ne'
  have hterm1 :=
    ((hm.mul hp).pow 2).div
      (((hasDerivAt_const (x := (0 : ℝ)) (z ^ 2)).mul hQ).mul
        (hasDerivAt_const (x := (0 : ℝ)) (1 - z ^ 2))) hden1
  have hterm2 :=
    (((hasDerivAt_const (x := (0 : ℝ)) (z ^ 2)).sub
        ((hm.mul ht).pow 2)).mul hp).div
      (((hasDerivAt_const (x := (0 : ℝ)) (z ^ 2)).mul hQ).mul
        (hasDerivAt_const (x := (0 : ℝ)) q)) hden2
  have hthreshold :=
    (hasDerivAt_const (x := (0 : ℝ)) δ).div
      ((hA.const_mul 2).mul
        ((hasDerivAt_const (x := (0 : ℝ)) (1 : ℝ)).sub hA))
      hden3
  have hraw :=
    ((hterm1.add hterm2).sub
      (hasDerivAt_const (x := (0 : ℝ)) (1 : ℝ))).add hthreshold
  have hfun :
      (fun e : ℝ => interiorSpectralMargin δ a u e) =
        (fun e : ℝ =>
          (m e * p e) ^ 2 /
              (z ^ 2 * Q e * (1 - z ^ 2)) +
            ((z ^ 2 - (m e * t e) ^ 2) * p e) /
              (z ^ 2 * Q e * q) - 1 +
            δ / (2 * A e * (1 - A e))) := by
    funext e
    unfold interiorSpectralMargin
    rw [spectralLimit_interior_eq]
    dsimp [MetricCodes.Johnson.asymptoticThreshold,
      MetricCodes.Johnson.centeredDegree, MetricCodes.Johnson.centeredWeight,
      A, m, t, z, q, p, Q, c, interiorWeight]
    ring
  change HasDerivAt (fun e : ℝ => interiorSpectralMargin δ a u e) _ 0
  rw [hfun]
  refine hraw.congr_deriv ?_
  simp [p, Q, m, t, A, z, q, c, interiorSlope]
  rw [hroot]
  have hdelta_div :
      δ =
        2 * (a * (1 - a) - u * (1 - u)) /
          (1 + 2 * Real.sqrt (u * (1 - u))) := by
    apply (eq_div_iff (by positivity)).2
    exact hdelta
  rw [hdelta_div]
  field_simp [ha0.ne', ha1.ne', hu.ne', hu1.ne',
    hz0.ne', hm0.ne', hs.ne', hrad.ne', hmrad.ne']
  ring_nf at hsquare ⊢
  linear_combination
    ((-128 * a ^ 3 * (a - 1) ^ 3 * (2 * a - 1) ^ 3 *
        Real.sqrt (u - u ^ 2)) +
      (64 * a ^ 2 * u * (a - 1) ^ 2 * (2 * a - 1) * (u - 1))) *
      hsquare
end MetricCodes.MRRW
