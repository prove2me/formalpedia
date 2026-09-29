-- Prove2me | solution 1 for Landreman3DEquilibria.H_at_toroidal_zero
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T00:58:14.825753+00:00
-- url     : https://prove2.me/submissions/f11d9d4b-8177-44ad-a05c-4c4a219823b3

import Mathlib
import Definitions.Def_landreman_vector_calculus
import Definitions.Def_landreman_integer_iota_family

open Landreman3DEquilibria

theorem W5_Landreman3DEquilibria_aux (L u v : ℝ) (hL : L ≠ 0)
    (hrel : L ^ 4 - L ^ 2 + (u ^ 2 + v ^ 2) = 0) :
    (L + u / L) ^ 2 + (v / L) ^ 2 = 1 + 2 * u ∧
    (4 * u + 8 * (u ^ 2 + v ^ 2)) * ((L + u / L) ^ 2 - (v / L) ^ 2)
      - 8 * v * (2 * L ^ 2 - 1) * (L + u / L) * (v / L) = 4 * u * (1 + 2 * u) ^ 2 := by
  have hL2 : L ^ 2 ≠ 0 := pow_ne_zero 2 hL
  constructor
  · have h : L ^ 2 * ((L + u / L) ^ 2 + (v / L) ^ 2 - (1 + 2 * u)) =
        L ^ 4 - L ^ 2 + (u ^ 2 + v ^ 2) := by
      field_simp
      ring
    rw [hrel] at h
    have := (mul_eq_zero.mp h).resolve_left hL2
    linarith
  · have h : L ^ 2 * ((4 * u + 8 * (u ^ 2 + v ^ 2)) * ((L + u / L) ^ 2 - (v / L) ^ 2)
      - 8 * v * (2 * L ^ 2 - 1) * (L + u / L) * (v / L) - 4 * u * (1 + 2 * u) ^ 2) =
        (4 * u + 8 * u ^ 2 - 8 * v ^ 2) * (L ^ 4 - L ^ 2 + (u ^ 2 + v ^ 2)) := by
      field_simp
      ring
    rw [hrel, mul_zero] at h
    have := (mul_eq_zero.mp h).resolve_left hL2
    linarith

theorem solution (e u v : ℝ) (he : 0 < e) (he1 : e < 1)
    (huv : u ^ 2 + v ^ 2 < 1 / 4) :
    Hfun e (posMap e u v 0) = 1 + 2 * e * u + 2 * (u ^ 2 + v ^ 2) := by
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
  have hrL : Real.sqrt (1 - 4 * (u ^ 2 + v ^ 2)) = 2 * Lfun u v ^ 2 - 1 := by linarith
  obtain ⟨hT, hXY⟩ := W5_Landreman3DEquilibria_aux (Lfun u v) u v hLpos.ne' hrel
  have hapos : 0 < aCoef e := Real.sqrt_pos.mpr (by linarith)
  have hbpos : 0 < bCoef e := Real.sqrt_pos.mpr (by linarith)
  have ha : aCoef e ^ 2 = 1 + e := Real.sq_sqrt (by linarith)
  have hb : bCoef e ^ 2 = 1 - e := Real.sq_sqrt (by linarith)
  have h0 : posMap e u v 0 0 = aCoef e * (Lfun u v + u / Lfun u v) := by simp [posMap]
  have h1 : posMap e u v 0 1 = bCoef e * (v / Lfun u v) := by simp [posMap]
  have h2 : posMap e u v 0 2 = v := by simp [posMap]
  generalize hX : Lfun u v + u / Lfun u v = X at h0 hT hXY
  generalize hY : v / Lfun u v = Y at h1 hT hXY
  generalize hR : 2 * Lfun u v ^ 2 - 1 = R at hrL hXY
  have hR2 : R ^ 2 = 1 - 4 * (u ^ 2 + v ^ 2) := by rw [← hrL]; exact hr2
  have hs : sFun e (posMap e u v 0) = 1 + 2 * u := by
    rw [sFun, h0, h1, mul_pow, mul_pow, mul_div_cancel_left₀ _ (by positivity),
      mul_div_cancel_left₀ _ (by positivity)]
    exact hT
  have hsne : (1 + 2 * u) ≠ 0 := by nlinarith
  have hrad : radicand e (posMap e u v 0) = 1 - 4 * (u ^ 2 + v ^ 2) := by
    rw [radicand, hs, h2]; ring
  have hF : FFun e (posMap e u v 0) = R := by rw [FFun, hrad, hrL]
  have hB0 : Bfield e (posMap e u v 0) 0 = aCoef e * (2 * v * X - R * Y) / (1 + 2 * u) := by
    show (2 * posMap e u v 0 2 * posMap e u v 0 0
      - (aCoef e / bCoef e) * FFun e (posMap e u v 0) * posMap e u v 0 1)
        / sFun e (posMap e u v 0) = _
    rw [hs, hF, h0, h1, h2]
    congr 1
    field_simp
  have hB1 : Bfield e (posMap e u v 0) 1 = bCoef e * (2 * v * Y + R * X) / (1 + 2 * u) := by
    show (2 * posMap e u v 0 2 * posMap e u v 0 1
      + (bCoef e / aCoef e) * FFun e (posMap e u v 0) * posMap e u v 0 0)
        / sFun e (posMap e u v 0) = _
    rw [hs, hF, h0, h1, h2]
    congr 1
    field_simp
  have hB2 : Bfield e (posMap e u v 0) 2 = -(2 * u) := by
    show 1 - sFun e (posMap e u v 0) = _
    rw [hs]; ring
  have hH : Hfun e (posMap e u v 0) =
      ((aCoef e * X) ^ 2 + (bCoef e * Y) ^ 2 + 4 * v ^ 2) / 2 +
        ((aCoef e * (2 * v * X - R * Y) / (1 + 2 * u)) ^ 2 +
          (bCoef e * (2 * v * Y + R * X) / (1 + 2 * u)) ^ 2 + (-(2 * u)) ^ 2) / 2 := by
    rw [Hfun, Qfun, normSq, Fin.sum_univ_three, hB0, hB1, hB2, h0, h1, h2]
  have hE : ((aCoef e * X) ^ 2 + (bCoef e * Y) ^ 2 + 4 * v ^ 2) / 2 +
        ((aCoef e * (2 * v * X - R * Y) / (1 + 2 * u)) ^ 2 +
          (bCoef e * (2 * v * Y + R * X) / (1 + 2 * u)) ^ 2 + (-(2 * u)) ^ 2) / 2
        - (1 + 2 * e * u + 2 * (u ^ 2 + v ^ 2)) =
      ((1 + 2 * u) ^ 2 * (aCoef e ^ 2 * X ^ 2 + bCoef e ^ 2 * Y ^ 2 + 4 * v ^ 2)
        + aCoef e ^ 2 * (2 * v * X - R * Y) ^ 2 + bCoef e ^ 2 * (2 * v * Y + R * X) ^ 2
        + 4 * u ^ 2 * (1 + 2 * u) ^ 2
        - 2 * (1 + 2 * u) ^ 2 * (1 + 2 * e * u + 2 * (u ^ 2 + v ^ 2))) / (2 * (1 + 2 * u) ^ 2) := by
    field_simp
    ring
  have hN : (1 + 2 * u) ^ 2 * (aCoef e ^ 2 * X ^ 2 + bCoef e ^ 2 * Y ^ 2 + 4 * v ^ 2)
        + aCoef e ^ 2 * (2 * v * X - R * Y) ^ 2 + bCoef e ^ 2 * (2 * v * Y + R * X) ^ 2
        + 4 * u ^ 2 * (1 + 2 * u) ^ 2
        - 2 * (1 + 2 * u) ^ 2 * (1 + 2 * e * u + 2 * (u ^ 2 + v ^ 2)) = 0 := by
    linear_combination ((1 + 2 * u) ^ 2 + 4 * v ^ 2 + R ^ 2) * hT
      + ((1 + 2 * u) - e * (X ^ 2 - Y ^ 2)) * hR2 + e * hXY
      + ((1 + 2 * u) ^ 2 * X ^ 2 + (2 * v * X - R * Y) ^ 2) * ha
      + ((1 + 2 * u) ^ 2 * Y ^ 2 + (2 * v * Y + R * X) ^ 2) * hb
  rw [hN, zero_div] at hE
  rw [hH]
  linarith
