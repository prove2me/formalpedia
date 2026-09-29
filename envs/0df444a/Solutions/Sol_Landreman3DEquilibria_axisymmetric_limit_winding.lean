-- Prove2me | solution 1 for Landreman3DEquilibria.axisymmetric_limit_winding
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T22:07:15.748895+00:00
-- url     : https://prove2.me/submissions/cb5a0291-6b68-4081-8f56-50d58fdc00a9

import Mathlib
import Definitions.Def_landreman_vector_calculus
import Definitions.Def_landreman_integer_iota_family

open Landreman3DEquilibria

theorem solution (u v z : ℝ)
    (huv : u ^ 2 + v ^ 2 < 1 / 4) :
    ((posMap 0 u v z 0 ^ 2 + posMap 0 u v z 1 ^ 2 - 1) / 2 : ℝ) -
        Complex.I * (posMap 0 u v z 2 : ℝ) =
      Complex.exp (2 * z * Complex.I) * (starRingEnd ℂ) (u + v * Complex.I) := by
  have hq : 0 ≤ 1 - 4 * (u ^ 2 + v ^ 2) := by nlinarith
  have hr2 : Real.sqrt (1 - 4 * (u ^ 2 + v ^ 2)) ^ 2 = 1 - 4 * (u ^ 2 + v ^ 2) :=
    Real.sq_sqrt hq
  have hr0 : 0 ≤ Real.sqrt (1 - 4 * (u ^ 2 + v ^ 2)) := Real.sqrt_nonneg _
  have hLpos : 0 < Lfun u v := by
    unfold Lfun
    exact Real.sqrt_pos.mpr (by positivity)
  have hL2 : Lfun u v ^ 2 = (1 + Real.sqrt (1 - 4 * (u ^ 2 + v ^ 2))) / 2 := by
    unfold Lfun
    exact Real.sq_sqrt (by positivity)
  have hrel : Lfun u v ^ 4 - Lfun u v ^ 2 + (u ^ 2 + v ^ 2) = 0 := by
    linear_combination (Lfun u v ^ 2 + (1 + Real.sqrt (1 - 4 * (u ^ 2 + v ^ 2))) / 2 - 1) * hL2
      + (1 / 4 : ℝ) * hr2
  have hX : posMap 0 u v z 0 =
      Lfun u v * Real.cos z + (u * Real.cos z + v * Real.sin z) / Lfun u v := by
    simp [posMap, aCoef]
  have hY : posMap 0 u v z 1 =
      Lfun u v * Real.sin z + (v * Real.cos z - u * Real.sin z) / Lfun u v := by
    simp [posMap, bCoef]
  have hZ : posMap 0 u v z 2 = v * Real.cos (2 * z) - u * Real.sin (2 * z) := by
    simp [posMap]
  have hLne : Lfun u v ≠ 0 := hLpos.ne'
  have hXL : posMap 0 u v z 0 * Lfun u v =
      Lfun u v ^ 2 * Real.cos z + u * Real.cos z + v * Real.sin z := by
    rw [hX]; field_simp <;> ring
  have hYL : posMap 0 u v z 1 * Lfun u v =
      Lfun u v ^ 2 * Real.sin z + v * Real.cos z - u * Real.sin z := by
    rw [hY]; field_simp <;> ring
  have htrig := Real.cos_sq_add_sin_sq z
  have hc2 := Real.cos_two_mul z
  have hs2 := Real.sin_two_mul z
  have hsum : (posMap 0 u v z 0 ^ 2 + posMap 0 u v z 1 ^ 2) * Lfun u v ^ 2 =
      (1 + 2 * (u * Real.cos (2 * z) + v * Real.sin (2 * z))) * Lfun u v ^ 2 := by
    linear_combination
      (posMap 0 u v z 0 * Lfun u v +
          (Lfun u v ^ 2 * Real.cos z + u * Real.cos z + v * Real.sin z)) * hXL
      + (posMap 0 u v z 1 * Lfun u v +
          (Lfun u v ^ 2 * Real.sin z + v * Real.cos z - u * Real.sin z)) * hYL
      + (Lfun u v ^ 4 + (u ^ 2 + v ^ 2) - 2 * Lfun u v ^ 2 * u) * htrig + hrel
      - 2 * Lfun u v ^ 2 * u * hc2 - 2 * Lfun u v ^ 2 * v * hs2
  have hP0 : posMap 0 u v z 0 ^ 2 + posMap 0 u v z 1 ^ 2 =
      1 + 2 * (u * Real.cos (2 * z) + v * Real.sin (2 * z)) :=
    mul_right_cancel₀ (pow_ne_zero 2 hLne) hsum
  apply Complex.ext
  · simp [Complex.exp_re, Complex.exp_im, sq]
    linear_combination (1 / 2 : ℝ) * hP0
  · simp [Complex.exp_re, Complex.exp_im, sq]
    linear_combination (-1 : ℝ) * hZ

theorem W4b_Landreman3DEquilibria_field_eq_stretched_axisymmetric (e : ℝ) (he : 0 < e)
    (he1 : e < 1) (x : LVec) (hx : x ∈ domainU e) :
    Bfield e x =
      ![aCoef e * Bfield 0 ![x 0 / aCoef e, x 1 / bCoef e, x 2] 0,
        bCoef e * Bfield 0 ![x 0 / aCoef e, x 1 / bCoef e, x 2] 1,
        Bfield 0 ![x 0 / aCoef e, x 1 / bCoef e, x 2] 2] := by
  have ha : aCoef e ≠ 0 := (Real.sqrt_pos.mpr (by linarith)).ne'
  have hb : bCoef e ≠ 0 := (Real.sqrt_pos.mpr (by linarith)).ne'
  have ha0 : aCoef 0 = 1 := by simp [aCoef]
  have hb0 : bCoef 0 = 1 := by simp [bCoef]
  have hs : sFun 0 ![x 0 / aCoef e, x 1 / bCoef e, x 2] = sFun e x := by
    simp [sFun, ha0, hb0, div_pow]
  have hF : FFun 0 ![x 0 / aCoef e, x 1 / bCoef e, x 2] = FFun e x := by
    unfold FFun radicand
    rw [hs]
    simp
  unfold Bfield
  rw [hs, hF]
  ext i
  fin_cases i <;> simp [ha0, hb0] <;> field_simp <;> ring
