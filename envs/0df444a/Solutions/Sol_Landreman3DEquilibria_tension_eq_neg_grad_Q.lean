-- Prove2me | solution 1 for Landreman3DEquilibria.tension_eq_neg_grad_Q
-- status  : ACCEPTED   (prove)
-- author  : @BrunoDCDO
-- created : 2026-09-23T22:52:34.906408+00:00
-- url     : https://prove2.me/submissions/85e11ba9-0563-4440-951a-e05bdf70f00e

import Mathlib
import Definitions.Def_landreman_vector_calculus
import Definitions.Def_landreman_integer_iota_family

open Landreman3DEquilibria

theorem solution (e : ℝ) (he : 0 < e) (he1 : e < 1) (x : LVec)
    (hx : x ∈ domainU e) : tension (Bfield e) x = -grad Qfun x := by
  have ha : aCoef e ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by linarith))
  have hb : bCoef e ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by linarith))
  have hr : 0 < radicand e x := hx
  have hs : sFun e x ≠ 0 := by
    intro hz
    unfold radicand at hr
    rw [hz] at hr
    nlinarith [sq_nonneg (x 2)]
  have hFsq : FFun e x ^ 2 = 1 - (1 - sFun e x) ^ 2 - 4 * x 2 ^ 2 :=
    Real.sq_sqrt hr.le
  have h0 := hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 3) x
  have h1 := hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 3) x
  have h2 := hasFDerivAt_apply (𝕜 := ℝ) (2 : Fin 3) x
  have ds_aux := ((h0.pow 2).mul_const (aCoef e ^ 2)⁻¹).add
    ((h1.pow 2).mul_const (bCoef e ^ 2)⁻¹)
  change HasFDerivAt (sFun e) _ x at ds_aux
  have hsB : fderiv ℝ (sFun e) x (Bfield e x) = 4 * x 2 := by
    rw [ds_aux.fderiv]
    simp [Bfield]
    field_simp [ha, hb, hs]
    unfold sFun
    field_simp
    ring
  have ds := ds_aux.differentiableAt.hasFDerivAt
  have dr := (((hasFDerivAt_const (1 : ℝ) x).sub
    (((hasFDerivAt_const (1 : ℝ) x).sub ds).pow 2)).sub
    ((h2.pow 2).const_mul 4))
  change HasFDerivAt (radicand e) _ x at dr
  have dF_aux := dr.sqrt (ne_of_gt hr)
  change HasFDerivAt (FFun e) _ x at dF_aux
  have hFB : fderiv ℝ (FFun e) x (Bfield e x) = 0 := by
    rw [dF_aux.fderiv]
    simp only [smul_apply, sub_apply,
      zero_apply, ContinuousLinearMap.proj_apply, smul_eq_mul, hsB]
    simp [Bfield]
    right
    ring
  have dF := dF_aux.differentiableAt.hasFDerivAt
  have dinv := (hasDerivAt_inv hs).comp_hasFDerivAt x ds
  have dB0 := (((h2.const_mul 2).mul h0).sub
    ((dF.const_mul (aCoef e / bCoef e)).mul h1)).mul dinv
  have dB1 := (((h2.const_mul 2).mul h1).add
    ((dF.const_mul (bCoef e / aCoef e)).mul h0)).mul dinv
  have dB2 := (hasFDerivAt_const (1 : ℝ) x).sub ds
  change HasFDerivAt (fun y => Bfield e y 0) _ x at dB0
  change HasFDerivAt (fun y => Bfield e y 1) _ x at dB1
  change HasFDerivAt (fun y => Bfield e y 2) _ x at dB2
  have dQ := (((h0.pow 2).add (h1.pow 2)).add ((h2.pow 2).const_mul 4)).mul_const (2 : ℝ)⁻¹
  change HasFDerivAt Qfun _ x at dQ
  have hdirecao (f : LVec → ℝ) : advect (Bfield e) f x = fderiv ℝ f x (Bfield e x) := by
    unfold advect partialD
    calc
      _ = fderiv ℝ f x (∑ j : Fin 3, (Bfield e x j) • (Pi.single j (1 : ℝ) : LVec)) := by
        simp
      _ = _ := by
        congr 1
        ext j
        simp [Pi.single_apply]
  ext i
  fin_cases i
  · simp only [tension, grad, Pi.neg_apply, hdirecao, partialD]
    change fderiv ℝ (fun y => Bfield e y 0) x (Bfield e x) =
      -fderiv ℝ Qfun x (Pi.single 0 1)
    rw [dB0.fderiv, dQ.fderiv]
    simp only [add_apply, smul_apply,
      sub_apply, ContinuousLinearMap.proj_apply, smul_eq_mul, hsB, hFB]
    simp [Bfield]
    field_simp [ha, hb, hs]
    linear_combination -(x 0 * bCoef e) * hFsq
  · simp only [tension, grad, Pi.neg_apply, hdirecao, partialD]
    change fderiv ℝ (fun y => Bfield e y 1) x (Bfield e x) =
      -fderiv ℝ Qfun x (Pi.single 1 1)
    rw [dB1.fderiv, dQ.fderiv]
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.proj_apply, smul_eq_mul, hsB, hFB]
    simp [Bfield]
    field_simp [ha, hb, hs]
    linear_combination -(x 1 * aCoef e) * hFsq
  · simp only [tension, grad, Pi.neg_apply, hdirecao, partialD]
    change fderiv ℝ (fun y => Bfield e y 2) x (Bfield e x) =
      -fderiv ℝ Qfun x (Pi.single 2 1)
    rw [dB2.fderiv, dQ.fderiv]
    simp [hsB]
    ring
