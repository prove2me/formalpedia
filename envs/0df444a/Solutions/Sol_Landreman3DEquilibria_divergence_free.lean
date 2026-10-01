-- Prove2me | solution 1 for Landreman3DEquilibria.divergence_free
-- status  : ACCEPTED   (prove)
-- author  : @BrunoDCDO
-- created : 2026-09-23T22:25:14.422984+00:00
-- url     : https://prove2.me/submissions/d521262d-de5e-4808-9015-90e14e74b8f6

import Mathlib
import Definitions.Def_landreman_vector_calculus
import Definitions.Def_landreman_integer_iota_family

open Landreman3DEquilibria

theorem solution (e : ℝ) (he : 0 < e) (he1 : e < 1) (x : LVec)
    (hx : x ∈ domainU e) : divg (Bfield e) x = 0 := by
  have ha : aCoef e ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by linarith))
  have hb : bCoef e ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by linarith))
  have hr : 0 < radicand e x := hx
  have hs : sFun e x ≠ 0 := by
    intro hz
    unfold radicand at hr
    rw [hz] at hr
    nlinarith [sq_nonneg (x 2)]
  have hF : FFun e x ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hr)
  have h0 := hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 3) x
  have h1 := hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 3) x
  have h2 := hasFDerivAt_apply (𝕜 := ℝ) (2 : Fin 3) x
  have ds := ((h0.pow 2).mul_const (aCoef e ^ 2)⁻¹).add
    ((h1.pow 2).mul_const (bCoef e ^ 2)⁻¹)
  change HasFDerivAt (sFun e) _ x at ds
  have dr := (((hasFDerivAt_const (1 : ℝ) x).sub
    (((hasFDerivAt_const (1 : ℝ) x).sub ds).pow 2)).sub
    ((h2.pow 2).const_mul 4))
  change HasFDerivAt (radicand e) _ x at dr
  have dF := dr.sqrt (ne_of_gt hr)
  change HasFDerivAt (FFun e) _ x at dF
  have dinv := (hasDerivAt_inv hs).comp_hasFDerivAt x ds
  have dB0 := (((h2.const_mul 2).mul h0).sub
    ((dF.const_mul (aCoef e / bCoef e)).mul h1)).mul dinv
  have dB1 := (((h2.const_mul 2).mul h1).add
    ((dF.const_mul (bCoef e / aCoef e)).mul h0)).mul dinv
  have dB2 := (hasFDerivAt_const (1 : ℝ) x).sub ds
  change HasFDerivAt (fun y => Bfield e y 0) _ x at dB0
  change HasFDerivAt (fun y => Bfield e y 1) _ x at dB1
  change HasFDerivAt (fun y => Bfield e y 2) _ x at dB2
  unfold divg
  rw [Fin.sum_univ_three]
  unfold partialD
  rw [dB0.fderiv, dB1.fderiv, dB2.fderiv]
  simp
  field_simp [ha, hb, hs, hF]
  unfold sFun
  field_simp
  ring
