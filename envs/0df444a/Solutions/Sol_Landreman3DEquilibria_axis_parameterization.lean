-- Prove2me | solution 1 for Landreman3DEquilibria.axis_parameterization
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T08:24:28.26238+00:00
-- url     : https://prove2.me/submissions/2b210564-0818-4978-9d03-f6d6d808eeee

import Mathlib
import Definitions.Def_landreman_vector_calculus
import Definitions.Def_landreman_integer_iota_family

open Landreman3DEquilibria

theorem W7a_Landreman3DEquilibria_aux (L u v : ℝ) (hL : L ≠ 0)
    (hrel : L ^ 4 - L ^ 2 + (u ^ 2 + v ^ 2) = 0) :
    (L + u / L) ^ 2 + (v / L) ^ 2 = 1 + 2 * u ∧
    (4 * u + 8 * (u ^ 2 + v ^ 2)) * ((L + u / L) ^ 2 - (v / L) ^ 2)
      - 8 * v * (2 * L ^ 2 - 1) * (L + u / L) * (v / L) = 4 * u * (1 + 2 * u) ^ 2 ∧
    (4 * u + 8 * (u ^ 2 + v ^ 2)) * (2 * (L + u / L) * (v / L))
      + 4 * v * (2 * L ^ 2 - 1) * ((L + u / L) ^ 2 - (v / L) ^ 2) =
        4 * (1 + 2 * u) ^ 2 * v := by
  have hL2 : L ^ 2 ≠ 0 := pow_ne_zero 2 hL
  refine ⟨?_, ?_, ?_⟩
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
  · have h : L ^ 2 * ((4 * u + 8 * (u ^ 2 + v ^ 2)) * (2 * (L + u / L) * (v / L))
      + 4 * v * (2 * L ^ 2 - 1) * ((L + u / L) ^ 2 - (v / L) ^ 2) -
        4 * (1 + 2 * u) ^ 2 * v) =
        (8 * L ^ 2 * v + 16 * u * v + 4 * v) * (L ^ 4 - L ^ 2 + (u ^ 2 + v ^ 2)) := by
      field_simp
      ring
    rw [hrel, mul_zero] at h
    have := (mul_eq_zero.mp h).resolve_left hL2
    linarith

/-- Field-line coordinates in the rotated frame. -/
theorem W7a_Landreman3DEquilibria_setup (e u v z : ℝ) (he : 0 < e) (he1 : e < 1)
    (huv : u ^ 2 + v ^ 2 < 1 / 4) :
    ∃ L U V R : ℝ, 0 < L ∧ Lfun u v = L ∧ L ^ 4 - L ^ 2 + (U ^ 2 + V ^ 2) = 0 ∧
      U ^ 2 + V ^ 2 = u ^ 2 + v ^ 2 ∧
      u = U * (Real.cos z ^ 2 - Real.sin z ^ 2) - V * (2 * Real.sin z * Real.cos z) ∧
      v = U * (2 * Real.sin z * Real.cos z) + V * (Real.cos z ^ 2 - Real.sin z ^ 2) ∧
      U = u * (Real.cos z ^ 2 - Real.sin z ^ 2) + v * (2 * Real.sin z * Real.cos z) ∧
      R = 2 * L ^ 2 - 1 ∧ 0 ≤ R ∧
      posMap e u v z 0 = aCoef e * (Real.cos z * (L + U / L) - Real.sin z * (V / L)) ∧
      posMap e u v z 1 = bCoef e * (Real.sin z * (L + U / L) + Real.cos z * (V / L)) ∧
      posMap e u v z 2 = V ∧
      sFun e (posMap e u v z) = 1 + 2 * U ∧
      FFun e (posMap e u v z) = R := by
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
  have hcs : Real.cos z ^ 2 + Real.sin z ^ 2 = 1 := Real.cos_sq_add_sin_sq z
  have hc2 : Real.cos (2 * z) = Real.cos z ^ 2 - Real.sin z ^ 2 := by
    rw [Real.cos_two_mul]; linear_combination hcs
  have hs2 : Real.sin (2 * z) = 2 * Real.sin z * Real.cos z := Real.sin_two_mul z
  set c := Real.cos z with hc
  set s := Real.sin z with hs
  set L := Lfun u v with hLdef
  have hLne : L ≠ 0 := hLpos.ne'
  have hUV : (u * (c ^ 2 - s ^ 2) + v * (2 * s * c)) ^ 2 +
      (v * (c ^ 2 - s ^ 2) - u * (2 * s * c)) ^ 2 = u ^ 2 + v ^ 2 := by
    linear_combination (u ^ 2 + v ^ 2) * ((c ^ 2 + s ^ 2) + 1) * hcs
  have hrelUV : L ^ 4 - L ^ 2 + ((u * (c ^ 2 - s ^ 2) + v * (2 * s * c)) ^ 2 +
      (v * (c ^ 2 - s ^ 2) - u * (2 * s * c)) ^ 2) = 0 := by
    rw [hUV]; exact hrel
  have hT := (W7a_Landreman3DEquilibria_aux L _ _ hLne hrelUV).1
  have h0 : posMap e u v z 0 = aCoef e * (c * (L + (u * (c ^ 2 - s ^ 2) + v * (2 * s * c)) / L)
      - s * ((v * (c ^ 2 - s ^ 2) - u * (2 * s * c)) / L)) := by
    show aCoef e * (L * c + (u * c + v * s) / L) = _
    congr 1
    field_simp
    linear_combination (-(u * c) - v * s) * hcs
  have h1 : posMap e u v z 1 = bCoef e * (s * (L + (u * (c ^ 2 - s ^ 2) + v * (2 * s * c)) / L)
      + c * ((v * (c ^ 2 - s ^ 2) - u * (2 * s * c)) / L)) := by
    show bCoef e * (L * s + (v * c - u * s) / L) = _
    congr 1
    field_simp
    linear_combination (s * u - v * c) * hcs
  have h2 : posMap e u v z 2 = v * (c ^ 2 - s ^ 2) - u * (2 * s * c) := by
    show v * Real.cos (2 * z) - u * Real.sin (2 * z) = _
    rw [hc2, hs2]
  have hapos : 0 < aCoef e := Real.sqrt_pos.mpr (by linarith)
  have hbpos : 0 < bCoef e := Real.sqrt_pos.mpr (by linarith)
  have hs : sFun e (posMap e u v z) = 1 + 2 * (u * (c ^ 2 - s ^ 2) + v * (2 * s * c)) := by
    rw [sFun, h0, h1, mul_pow, mul_pow, mul_div_cancel_left₀ _ (by positivity),
      mul_div_cancel_left₀ _ (by positivity)]
    linear_combination hT + ((L + (u * (c ^ 2 - s ^ 2) + v * (2 * s * c)) / L) ^ 2 +
      ((v * (c ^ 2 - s ^ 2) - u * (2 * s * c)) / L) ^ 2) * hcs
  have hF : FFun e (posMap e u v z) = 2 * L ^ 2 - 1 := by
    rw [FFun, radicand, hs, h2, ← hrL]
    congr 1
    linear_combination (-4) * hUV
  exact ⟨L, u * (c ^ 2 - s ^ 2) + v * (2 * s * c), v * (c ^ 2 - s ^ 2) - u * (2 * s * c),
    2 * L ^ 2 - 1, hLpos, rfl, hrelUV, hUV,
    by linear_combination (-u) * ((c ^ 2 + s ^ 2) + 1) * hcs,
    by linear_combination (-v) * ((c ^ 2 + s ^ 2) + 1) * hcs, rfl, rfl,
    by rw [← hrL]; exact hr0, h0, h1, h2, hs, hF⟩

theorem W7a_Landreman3DEquilibria_s_pos (e : ℝ) (x : LVec) (hx : x ∈ domainU e) :
    0 < sFun e x := by
  have h0 : 0 ≤ sFun e x := by unfold sFun; positivity
  have h1 : 0 < radicand e x := hx
  unfold radicand at h1
  nlinarith [sq_nonneg (x 2)]

theorem W7a_Landreman3DEquilibria_sFun_contDiff (e : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (sFun e) := by
  unfold sFun
  fun_prop

theorem W7a_Landreman3DEquilibria_radicand_contDiff (e : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (radicand e) := by
  have := W7a_Landreman3DEquilibria_sFun_contDiff e
  unfold radicand
  fun_prop

theorem W7a_Landreman3DEquilibria_FFun_contDiffOn (e : ℝ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (FFun e) (domainU e) := by
  intro x hx
  have hr : radicand e x ≠ 0 := (show 0 < radicand e x from hx).ne'
  exact ((W7a_Landreman3DEquilibria_radicand_contDiff e).contDiffAt.sqrt hr).contDiffWithinAt

theorem W7a_Landreman3DEquilibria_field_smooth_on_domainU (e : ℝ) (he : 0 < e) (he1 : e < 1) :
    ContDiffOn ℝ (⊤ : ℕ∞) (Bfield e) (domainU e) := by
  have hs := W7a_Landreman3DEquilibria_sFun_contDiff e
  have hF := W7a_Landreman3DEquilibria_FFun_contDiffOn e
  have hsne : ∀ x ∈ domainU e, sFun e x ≠ 0 := fun x hx =>
    (W7a_Landreman3DEquilibria_s_pos e x hx).ne'
  have c0 : ContDiff ℝ (⊤ : ℕ∞) (fun x : LVec => x 0) := contDiff_apply ℝ ℝ 0
  have c1 : ContDiff ℝ (⊤ : ℕ∞) (fun x : LVec => x 1) := contDiff_apply ℝ ℝ 1
  have c2 : ContDiff ℝ (⊤ : ℕ∞) (fun x : LVec => x 2) := contDiff_apply ℝ ℝ 2
  rw [contDiffOn_pi]
  intro i
  fin_cases i
  · simp only [Bfield]
    simp
    refine ContDiffOn.div ?_ hs.contDiffOn hsne
    exact ((contDiffOn_const.mul c2.contDiffOn).mul c0.contDiffOn).sub
      ((contDiffOn_const.mul hF).mul c1.contDiffOn)
  · simp only [Bfield]
    simp
    refine ContDiffOn.div ?_ hs.contDiffOn hsne
    exact ((contDiffOn_const.mul c2.contDiffOn).mul c1.contDiffOn).add
      ((contDiffOn_const.mul hF).mul c0.contDiffOn)
  · simp only [Bfield]
    simp
    exact contDiffOn_const.sub hs.contDiffOn

theorem W7a_Landreman3DEquilibria_Hval (e u v z : ℝ) (he : 0 < e) (he1 : e < 1)
    (huv : u ^ 2 + v ^ 2 < 1 / 4) :
    Hfun e (posMap e u v z) = 1 + 2 * e * u + 2 * (u ^ 2 + v ^ 2) := by
  obtain ⟨L, U, V, R, hLpos, -, hrel, hUV, hu, -, -, hR, hR0, h0, h1, h2, hs, hF⟩ :=
    W7a_Landreman3DEquilibria_setup e u v z he he1 huv
  have hLne := hLpos.ne'
  obtain ⟨hT, hRe, hIm⟩ := W7a_Landreman3DEquilibria_aux L U V hLne hrel
  have hcs : Real.cos z ^ 2 + Real.sin z ^ 2 = 1 := Real.cos_sq_add_sin_sq z
  have hR2 : R ^ 2 = 1 - 4 * (U ^ 2 + V ^ 2) := by
    linear_combination (R + 2 * L ^ 2 - 1) * hR + 4 * hrel
  rw [← hR] at hRe hIm
  have hapos : 0 < aCoef e := Real.sqrt_pos.mpr (by linarith)
  have hbpos : 0 < bCoef e := Real.sqrt_pos.mpr (by linarith)
  have ha : aCoef e ^ 2 = 1 + e := Real.sq_sqrt (by linarith)
  have hb : bCoef e ^ 2 = 1 - e := Real.sq_sqrt (by linarith)
  generalize Real.cos z = c at *
  generalize Real.sin z = s at *
  generalize L + U / L = X at *
  generalize V / L = Y at *
  have hsne : (1 + 2 * U) ≠ 0 := by
    have : 0 < 1 + 2 * U := by nlinarith [sq_nonneg V, sq_nonneg (U + 1/2)]
    exact this.ne'
  have hT0 : (c * X - s * Y) ^ 2 + (s * X + c * Y) ^ 2 = 1 + 2 * U := by
    linear_combination hT + (X ^ 2 + Y ^ 2) * hcs
  have hXY0 : (4 * U + 8 * (U ^ 2 + V ^ 2)) * ((c * X - s * Y) ^ 2 - (s * X + c * Y) ^ 2)
      - 8 * V * R * (c * X - s * Y) * (s * X + c * Y) = 4 * u * (1 + 2 * U) ^ 2 := by
    linear_combination (c ^ 2 - s ^ 2) * hRe - 2 * s * c * hIm - 4 * (1 + 2 * U) ^ 2 * hu
  generalize hX0 : c * X - s * Y = X0 at *
  generalize hY0 : s * X + c * Y = Y0 at *
  have hB0 : Bfield e (posMap e u v z) 0 = aCoef e * (2 * V * X0 - R * Y0) / (1 + 2 * U) := by
    show (2 * posMap e u v z 2 * posMap e u v z 0
      - (aCoef e / bCoef e) * FFun e (posMap e u v z) * posMap e u v z 1)
        / sFun e (posMap e u v z) = _
    rw [hs, hF, h0, h1, h2]
    congr 1
    field_simp
  have hB1 : Bfield e (posMap e u v z) 1 = bCoef e * (2 * V * Y0 + R * X0) / (1 + 2 * U) := by
    show (2 * posMap e u v z 2 * posMap e u v z 1
      + (bCoef e / aCoef e) * FFun e (posMap e u v z) * posMap e u v z 0)
        / sFun e (posMap e u v z) = _
    rw [hs, hF, h0, h1, h2]
    congr 1
    field_simp
  have hB2 : Bfield e (posMap e u v z) 2 = -(2 * U) := by
    show 1 - sFun e (posMap e u v z) = _
    rw [hs]; ring
  have hH : Hfun e (posMap e u v z) =
      ((aCoef e * X0) ^ 2 + (bCoef e * Y0) ^ 2 + 4 * V ^ 2) / 2 +
        ((aCoef e * (2 * V * X0 - R * Y0) / (1 + 2 * U)) ^ 2 +
          (bCoef e * (2 * V * Y0 + R * X0) / (1 + 2 * U)) ^ 2 + (-(2 * U)) ^ 2) / 2 := by
    rw [Hfun, Qfun, normSq, Fin.sum_univ_three, hB0, hB1, hB2, h0, h1, h2]
  have hE : ((aCoef e * X0) ^ 2 + (bCoef e * Y0) ^ 2 + 4 * V ^ 2) / 2 +
        ((aCoef e * (2 * V * X0 - R * Y0) / (1 + 2 * U)) ^ 2 +
          (bCoef e * (2 * V * Y0 + R * X0) / (1 + 2 * U)) ^ 2 + (-(2 * U)) ^ 2) / 2
        - (1 + 2 * e * u + 2 * (u ^ 2 + v ^ 2)) =
      ((1 + 2 * U) ^ 2 * (aCoef e ^ 2 * X0 ^ 2 + bCoef e ^ 2 * Y0 ^ 2 + 4 * V ^ 2)
        + aCoef e ^ 2 * (2 * V * X0 - R * Y0) ^ 2 + bCoef e ^ 2 * (2 * V * Y0 + R * X0) ^ 2
        + 4 * U ^ 2 * (1 + 2 * U) ^ 2
        - 2 * (1 + 2 * U) ^ 2 * (1 + 2 * e * u + 2 * (u ^ 2 + v ^ 2))) /
          (2 * (1 + 2 * U) ^ 2) := by
    field_simp
    ring
  have hN : (1 + 2 * U) ^ 2 * (aCoef e ^ 2 * X0 ^ 2 + bCoef e ^ 2 * Y0 ^ 2 + 4 * V ^ 2)
        + aCoef e ^ 2 * (2 * V * X0 - R * Y0) ^ 2 + bCoef e ^ 2 * (2 * V * Y0 + R * X0) ^ 2
        + 4 * U ^ 2 * (1 + 2 * U) ^ 2
        - 2 * (1 + 2 * U) ^ 2 * (1 + 2 * e * u + 2 * (u ^ 2 + v ^ 2)) = 0 := by
    linear_combination ((1 + 2 * U) ^ 2 * X0 ^ 2 + (2 * V * X0 - R * Y0) ^ 2) * ha
      + ((1 + 2 * U) ^ 2 * Y0 ^ 2 + (2 * V * Y0 + R * X0) ^ 2) * hb
      + e * hXY0 + ((1 + 2 * U) - e * (X0 ^ 2 - Y0 ^ 2)) * hR2
      + ((1 + 2 * U) ^ 2 + 4 * V ^ 2 + R ^ 2) * hT0 + 4 * (1 + 2 * U) ^ 2 * hUV
  rw [hN, zero_div] at hE
  rw [hH]
  linarith

theorem W7a_Landreman3DEquilibria_H_field_line_constant (e u v z : ℝ) (he : 0 < e) (he1 : e < 1)
    (huv : u ^ 2 + v ^ 2 < 1 / 4) :
    Hfun e (posMap e u v z) = Hfun e (posMap e u v 0) := by
  rw [W7a_Landreman3DEquilibria_Hval e u v z he he1 huv,
    W7a_Landreman3DEquilibria_Hval e u v 0 he he1 huv]

theorem W7a_Landreman3DEquilibria_posMap_is_field_line (e u v z : ℝ) (he : 0 < e) (he1 : e < 1)
    (huv : u ^ 2 + v ^ 2 < 1 / 4) (i : Fin 3) :
    deriv (fun t => posMap e u v t i) z = Bfield e (posMap e u v z) i := by
  obtain ⟨L, U, V, R, hLpos, hLeq, hrel, hUV, hu, hv, hUdef, hR, hR0, h0, h1, h2, hs, hF⟩ :=
    W7a_Landreman3DEquilibria_setup e u v z he he1 huv
  have hLne := hLpos.ne'
  have hcs : Real.cos z ^ 2 + Real.sin z ^ 2 = 1 := Real.cos_sq_add_sin_sq z
  have hapos : 0 < aCoef e := Real.sqrt_pos.mpr (by linarith)
  have hbpos : 0 < bCoef e := Real.sqrt_pos.mpr (by linarith)
  have hsne : (1 + 2 * U) ≠ 0 := by
    have : 0 < 1 + 2 * U := by nlinarith [sq_nonneg V, sq_nonneg (U + 1/2)]
    exact this.ne'
  subst hR
  have hXp : (L + U / L) * L = L ^ 2 + U := by rw [add_mul, div_mul_cancel₀ _ hLne]; ring
  have hXm : (L - U / L) * L = L ^ 2 - U := by rw [sub_mul, div_mul_cancel₀ _ hLne]; ring
  have hY : V / L * L = V := div_mul_cancel₀ V hLne
  have hA : (1 + 2 * U) * (V / L) = 2 * V * (L + U / L) - (2 * L ^ 2 - 1) * (V / L) := by
    have hm : L * ((1 + 2 * U) * (V / L) - (2 * V * (L + U / L) - (2 * L ^ 2 - 1) * (V / L)))
        = 0 := by
      linear_combination (1 + 2 * U) * hY - 2 * V * hXp + (2 * L ^ 2 - 1) * hY
    have := (mul_eq_zero.mp hm).resolve_left hLne
    linarith
  have hB : (1 + 2 * U) * (L - U / L) = 2 * V * (V / L) + (2 * L ^ 2 - 1) * (L + U / L) := by
    have hm : L * ((1 + 2 * U) * (L - U / L) - (2 * V * (V / L) + (2 * L ^ 2 - 1) * (L + U / L)))
        = 0 := by
      linear_combination (1 + 2 * U) * hXm - 2 * V * hY - (2 * L ^ 2 - 1) * hXp - 2 * hrel
    have := (mul_eq_zero.mp hm).resolve_left hLne
    linarith
  have hane : aCoef e ≠ 0 := hapos.ne'
  have hbne : bCoef e ≠ 0 := hbpos.ne'
  have hab : ∀ w, aCoef e / bCoef e * (2 * L ^ 2 - 1) * (bCoef e * w) =
      aCoef e * (2 * L ^ 2 - 1) * w := fun w => by field_simp <;> ring
  have hba : ∀ w, bCoef e / aCoef e * (2 * L ^ 2 - 1) * (aCoef e * w) =
      bCoef e * (2 * L ^ 2 - 1) * w := fun w => by field_simp <;> ring
  fin_cases i
  · have hfun : (fun t => posMap e u v t 0) = fun t =>
        aCoef e * (L * Real.cos t + (u * Real.cos t + v * Real.sin t) / L) := by
      funext t; rw [← hLeq]; rfl
    have hd : HasDerivAt (fun t => aCoef e * (L * Real.cos t +
        (u * Real.cos t + v * Real.sin t) / L)) _ z := ((((Real.hasDerivAt_cos z).const_mul L).add
      ((((Real.hasDerivAt_cos z).const_mul u).add
        ((Real.hasDerivAt_sin z).const_mul v)).div_const L)).const_mul (aCoef e))
    simp only [Fin.zero_eta, Fin.isValue]
    rw [hfun, hd.deriv]
    have hnum : u * -Real.sin z + v * Real.cos z = U * Real.sin z + V * Real.cos z := by
      rw [hu, hv]; linear_combination (U * Real.sin z + V * Real.cos z) * hcs
    rw [hnum]
    show _ = (2 * posMap e u v z 2 * posMap e u v z 0
      - (aCoef e / bCoef e) * FFun e (posMap e u v z) * posMap e u v z 1)
        / sFun e (posMap e u v z)
    rw [hs, hF, h0, h1, h2, hab, eq_div_iff hsne]
    linear_combination (aCoef e) * ((-Real.sin z) * hB + Real.cos z * hA)
  · have hfun : (fun t => posMap e u v t 1) = fun t =>
        bCoef e * (L * Real.sin t + (v * Real.cos t - u * Real.sin t) / L) := by
      funext t; rw [← hLeq]; rfl
    have hd : HasDerivAt (fun t => bCoef e * (L * Real.sin t +
        (v * Real.cos t - u * Real.sin t) / L)) _ z := ((((Real.hasDerivAt_sin z).const_mul L).add
      ((((Real.hasDerivAt_cos z).const_mul v).sub
        ((Real.hasDerivAt_sin z).const_mul u)).div_const L)).const_mul (bCoef e))
    simp only [Fin.mk_one, Fin.isValue]
    rw [hfun, hd.deriv]
    have hnum : v * -Real.sin z - u * Real.cos z = -(U * Real.cos z) + V * Real.sin z := by
      rw [hu, hv]; linear_combination (-(U * Real.cos z) + V * Real.sin z) * hcs
    rw [hnum]
    show _ = (2 * posMap e u v z 2 * posMap e u v z 1
      + (bCoef e / aCoef e) * FFun e (posMap e u v z) * posMap e u v z 0)
        / sFun e (posMap e u v z)
    rw [hs, hF, h0, h1, h2, hba, eq_div_iff hsne]
    linear_combination (bCoef e) * (Real.cos z * hB + Real.sin z * hA)
  · have hfun : (fun t => posMap e u v t 2) = fun t =>
        v * Real.cos (2 * t) - u * Real.sin (2 * t) := by
      funext t; rfl
    have hd : HasDerivAt (fun t => v * Real.cos (2 * t) - u * Real.sin (2 * t)) _ z :=
      (((hasDerivAt_id' z).const_mul (2:ℝ)).cos.const_mul v).sub
      (((hasDerivAt_id' z).const_mul (2:ℝ)).sin.const_mul u)
    simp only [Fin.reduceFinMk, Fin.isValue]
    rw [hfun, hd.deriv]
    show _ = 1 - sFun e (posMap e u v z)
    rw [hs, hUdef, Real.cos_two_mul, Real.sin_two_mul]
    linear_combination (-2 * u) * hcs

theorem solution (e z : ℝ) (he : 0 < e) (he1 : e < 1) :
    posMap e (-(e / 2)) 0 z = axisCurve e z ∧ psiFun e (axisCurve e z) = 0 := by
  have hapos : 0 < aCoef e := Real.sqrt_pos.mpr (by linarith)
  have hbpos : 0 < bCoef e := Real.sqrt_pos.mpr (by linarith)
  have ha : aCoef e ^ 2 = 1 + e := Real.sq_sqrt (by linarith)
  have hb : bCoef e ^ 2 = 1 - e := Real.sq_sqrt (by linarith)
  have hab : Real.sqrt (1 - e ^ 2) = aCoef e * bCoef e := by
    rw [aCoef, bCoef, ← Real.sqrt_mul (by linarith)]
    congr 1
    ring
  have hL : Lfun (-(e / 2)) 0 = (aCoef e + bCoef e) / 2 := by
    unfold Lfun
    have h1 : 1 - 4 * ((-(e / 2)) ^ 2 + 0 ^ 2) = 1 - e ^ 2 := by ring
    rw [h1, hab]
    rw [show (1 + aCoef e * bCoef e) / 2 = ((aCoef e + bCoef e) / 2) ^ 2 by
      linear_combination (-1 / 4 : ℝ) * ha - (1 / 4 : ℝ) * hb]
    exact Real.sqrt_sq (by positivity)
  have hsum : aCoef e + bCoef e ≠ 0 := by positivity
  have hq : e / (aCoef e + bCoef e) = (aCoef e - bCoef e) / 2 := by
    rw [div_eq_iff hsum]
    linear_combination (-1 / 2 : ℝ) * ha + (1 / 2 : ℝ) * hb
  have hpos : posMap e (-(e / 2)) 0 z = axisCurve e z := by
    funext i
    fin_cases i
    · show aCoef e * (Lfun (-(e / 2)) 0 * Real.cos z +
          (-(e / 2) * Real.cos z + 0 * Real.sin z) / Lfun (-(e / 2)) 0) =
        Real.sqrt (1 - e ^ 2) * Real.cos z
      rw [hL, hab]
      have h2 : (-(e / 2) * Real.cos z + 0 * Real.sin z) / ((aCoef e + bCoef e) / 2) =
          -(Real.cos z * (e / (aCoef e + bCoef e))) := by
        field_simp
        try ring
      rw [h2, hq]
      ring
    · show bCoef e * (Lfun (-(e / 2)) 0 * Real.sin z +
          (0 * Real.cos z - -(e / 2) * Real.sin z) / Lfun (-(e / 2)) 0) =
        Real.sqrt (1 - e ^ 2) * Real.sin z
      rw [hL, hab]
      have h2 : (0 * Real.cos z - -(e / 2) * Real.sin z) / ((aCoef e + bCoef e) / 2) =
          Real.sin z * (e / (aCoef e + bCoef e)) := by
        field_simp
        try ring
      rw [h2, hq]
      ring
    · show 0 * Real.cos (2 * z) - -(e / 2) * Real.sin (2 * z) = e / 2 * Real.sin (2 * z)
      ring
  refine ⟨hpos, ?_⟩
  rw [← hpos]
  unfold psiFun
  rw [W7a_Landreman3DEquilibria_Hval e (-(e / 2)) 0 z he he1 (by nlinarith)]
  ring

theorem W7a_Landreman3DEquilibria_trig_integral (K α β γ δ : ℝ) :
    ∫ z in (0 : ℝ)..(2 * Real.pi), (K + α * Real.cos (2 * z) + β * Real.sin (2 * z) +
      γ * Real.cos (4 * z) + δ * Real.sin (4 * z)) = 2 * Real.pi * K := by
  have hF : ∀ x, HasDerivAt (fun z => K * z + α * Real.sin (2 * z) / 2 - β * Real.cos (2 * z) / 2
      + γ * Real.sin (4 * z) / 4 - δ * Real.cos (4 * z) / 4)
      (K + α * Real.cos (2 * x) + β * Real.sin (2 * x) +
        γ * Real.cos (4 * x) + δ * Real.sin (4 * x)) x := by
    intro x
    have h2 := (hasDerivAt_id' x).const_mul (2:ℝ)
    have h4 := (hasDerivAt_id' x).const_mul (4:ℝ)
    have := (((((hasDerivAt_id' x).const_mul K).add ((h2.sin.const_mul α).div_const 2)).sub
      ((h2.cos.const_mul β).div_const 2)).add ((h4.sin.const_mul γ).div_const 4)).sub
      ((h4.cos.const_mul δ).div_const 4)
    exact this.congr_deriv (by (try simp only [Pi.sub_apply, Pi.add_apply, Pi.mul_apply, Pi.neg_apply]); ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hF x)
    (by apply Continuous.intervalIntegrable; fun_prop)]
  have e1 : Real.sin (2 * (2 * Real.pi)) = 0 := by
    rw [show 2 * (2 * Real.pi) = ((4 : ℕ) : ℝ) * Real.pi by push_cast; ring]
    exact Real.sin_nat_mul_pi 4
  have e2 : Real.cos (2 * (2 * Real.pi)) = 1 := by
    rw [show 2 * (2 * Real.pi) = ((2 : ℕ) : ℝ) * (2 * Real.pi) by push_cast; ring]
    exact Real.cos_nat_mul_two_pi 2
  have e3 : Real.sin (4 * (2 * Real.pi)) = 0 := by
    rw [show 4 * (2 * Real.pi) = ((8 : ℕ) : ℝ) * Real.pi by push_cast; ring]
    exact Real.sin_nat_mul_pi 8
  have e4 : Real.cos (4 * (2 * Real.pi)) = 1 := by
    rw [show 4 * (2 * Real.pi) = ((4 : ℕ) : ℝ) * (2 * Real.pi) by push_cast; ring]
    exact Real.cos_nat_mul_two_pi 4
  simp only [e1, e2, e3, e4, mul_zero, Real.sin_zero, Real.cos_zero]
  ring

theorem W7a_Landreman3DEquilibria_normSq_pt (e u v : ℝ) (he : 0 < e) (he1 : e < 1)
    (huv : u ^ 2 + v ^ 2 < 1 / 4) :
    ∃ α β γ δ : ℝ, ∀ z : ℝ, normSq (Bfield e (posMap e u v z)) =
      (1 + 2 * e * u + 2 * (u ^ 2 + v ^ 2)) + α * Real.cos (2 * z) + β * Real.sin (2 * z) +
        γ * Real.cos (4 * z) + δ * Real.sin (4 * z) := by
  obtain ⟨L, U, V, R, hLpos, hLeq, hrel, hUV, -, -, -, -, -, -, -, -, -, -⟩ :=
    W7a_Landreman3DEquilibria_setup e u v 0 he he1 huv
  have hLne := hLpos.ne'
  have hrel' : L ^ 4 - L ^ 2 + (u ^ 2 + v ^ 2) = 0 := by rw [← hUV]; exact hrel
  have ha : aCoef e ^ 2 = 1 + e := Real.sq_sqrt (by linarith)
  have hb : bCoef e ^ 2 = 1 - e := Real.sq_sqrt (by linarith)
  set a := aCoef e
  set b := bCoef e
  set A := L + u / L with hA
  set A' := L - u / L with hA'
  set B := v / L with hB
  have hq : (u ^ 2 + v ^ 2) / L ^ 2 = 1 - L ^ 2 := by
    rw [div_eq_iff (pow_ne_zero 2 hLne)]
    linear_combination hrel'
  have hAB : A ^ 2 + B ^ 2 = L ^ 2 + 2 * u + (u ^ 2 + v ^ 2) / L ^ 2 := by
    rw [hA, hB]; field_simp; ring
  have hAB' : A' ^ 2 + B ^ 2 = L ^ 2 - 2 * u + (u ^ 2 + v ^ 2) / L ^ 2 := by
    rw [hA', hB]; field_simp; ring
  have hK1 : (a ^ 2 * A ^ 2 + b ^ 2 * B ^ 2 + a ^ 2 * B ^ 2 + b ^ 2 * A' ^ 2) / 2
      + 2 * u ^ 2 + 2 * v ^ 2 = 1 + 2 * e * u + 2 * (u ^ 2 + v ^ 2) := by
    have : (a ^ 2 * A ^ 2 + b ^ 2 * B ^ 2 + a ^ 2 * B ^ 2 + b ^ 2 * A' ^ 2) / 2 =
        (a ^ 2 * (A ^ 2 + B ^ 2) + b ^ 2 * (A' ^ 2 + B ^ 2)) / 2 := by ring
    rw [this, hAB, hAB', hq, ha, hb]
    ring
  refine ⟨-(a ^ 2 * A ^ 2 + b ^ 2 * B ^ 2 - a ^ 2 * B ^ 2 - b ^ 2 * A' ^ 2) / 2,
    -(a ^ 2 * A * B + b ^ 2 * A' * B), -(2 * v ^ 2 - 2 * u ^ 2), 4 * u * v, fun z => ?_⟩
  have hH := W7a_Landreman3DEquilibria_Hval e u v z he he1 huv
  have hns : normSq (Bfield e (posMap e u v z)) = 2 * (1 + 2 * e * u + 2 * (u ^ 2 + v ^ 2))
      - (posMap e u v z 0 ^ 2 + posMap e u v z 1 ^ 2 + 4 * posMap e u v z 2 ^ 2) := by
    rw [Hfun, Qfun] at hH
    linarith
  have h0 : posMap e u v z 0 = a * (A * Real.cos z + B * Real.sin z) := by
    show aCoef e * (Lfun u v * Real.cos z + (u * Real.cos z + v * Real.sin z) / Lfun u v) = _
    rw [hLeq, hA, hB]; ring
  have h1 : posMap e u v z 1 = b * (A' * Real.sin z + B * Real.cos z) := by
    show bCoef e * (Lfun u v * Real.sin z + (v * Real.cos z - u * Real.sin z) / Lfun u v) = _
    rw [hLeq, hA', hB]; ring
  have h2 : posMap e u v z 2 = v * Real.cos (2 * z) - u * Real.sin (2 * z) := rfl
  rw [hns, h0, h1, h2]
  have e1 : Real.cos z ^ 2 = 1 / 2 + Real.cos (2 * z) / 2 := Real.cos_sq z
  have e2 : Real.sin z ^ 2 = 1 / 2 - Real.cos (2 * z) / 2 := by rw [Real.sin_sq, e1]; ring
  have e3 : Real.sin z * Real.cos z = Real.sin (2 * z) / 2 := by rw [Real.sin_two_mul]; ring
  have h4 : 4 * z = 2 * (2 * z) := by ring
  have e4 : Real.cos (2 * z) ^ 2 = 1 / 2 + Real.cos (4 * z) / 2 := by
    rw [h4]; exact Real.cos_sq (2 * z)
  have e5 : Real.sin (2 * z) ^ 2 = 1 / 2 - Real.cos (4 * z) / 2 := by
    rw [Real.sin_sq, e4]; ring
  have e6 : Real.sin (2 * z) * Real.cos (2 * z) = Real.sin (4 * z) / 2 := by
    rw [h4, Real.sin_two_mul (2 * z)]; ring
  linear_combination (-(a ^ 2 * A ^ 2 + b ^ 2 * B ^ 2)) * e1
    + (-(a ^ 2 * B ^ 2 + b ^ 2 * A' ^ 2)) * e2
    + (-2 * (a ^ 2 * A * B + b ^ 2 * A' * B)) * e3
    + (-4 * v ^ 2) * e4 + (-4 * u ^ 2) * e5 + (8 * u * v) * e6 - hK1

theorem W7a_Landreman3DEquilibria_field_line_average_B_sq (e u v : ℝ) (he : 0 < e) (he1 : e < 1)
    (huv : u ^ 2 + v ^ 2 < 1 / 4) :
    (1 / (2 * Real.pi)) * ∫ z in (0 : ℝ)..(2 * Real.pi), normSq (Bfield e (posMap e u v z)) =
      1 - e ^ 2 / 2 + 2 * ((u + e / 2) ^ 2 + v ^ 2) := by
  obtain ⟨α, β, γ, δ, h⟩ := W7a_Landreman3DEquilibria_normSq_pt e u v he he1 huv
  simp only [h]
  rw [W7a_Landreman3DEquilibria_trig_integral]
  field_simp
  ring

theorem W7a_Landreman3DEquilibria_domainU_open (e : ℝ) : IsOpen (domainU e) := by
  have := (W7a_Landreman3DEquilibria_radicand_contDiff e).continuous
  exact isOpen_lt continuous_const this

theorem W7a_Landreman3DEquilibria_line_deriv (f : LVec → ℝ) (x v : LVec)
    (hf : DifferentiableAt ℝ f x) :
    HasDerivAt (fun t : ℝ => f (x + t • v)) (fderiv ℝ f x v) (0:ℝ) := by
  have hl : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    simpa using ((hasDerivAt_id' (0:ℝ)).smul_const v).const_add x
  have h2 : HasFDerivAt f (fderiv ℝ f x) (x + (0:ℝ) • v) := by simpa using hf.hasFDerivAt
  exact (h2.comp_hasDerivAt (0:ℝ) hl : _)

theorem W7a_Landreman3DEquilibria_dir (f : LVec → ℝ) (x v : LVec)
    (hf : DifferentiableAt ℝ f x) (f' : ℝ)
    (h : HasDerivAt (fun t : ℝ => f (x + t • v)) f' (0:ℝ)) : fderiv ℝ f x v = f' :=
  (W7a_Landreman3DEquilibria_line_deriv f x v hf).unique h

theorem W7a_Landreman3DEquilibria_line_comp (x v : LVec) :
    ∀ j, HasDerivAt (fun t : ℝ => (x + t • v) j) (v j) 0 := by
  have hl : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    simpa using ((hasDerivAt_id' (0:ℝ)).smul_const v).const_add x
  exact fun j => hasDerivAt_pi.1 hl j

theorem W7a_Landreman3DEquilibria_sum_fderiv (f : LVec → ℝ) (x v : LVec) :
    ∑ j : Fin 3, v j * fderiv ℝ f x (Pi.single j 1) = fderiv ℝ f x v := by
  rw [Fin.sum_univ_three]
  have hv : v = v 0 • (Pi.single 0 1 : LVec) + v 1 • (Pi.single 1 1 : LVec) +
      v 2 • (Pi.single 2 1 : LVec) := by
    ext i; fin_cases i <;> simp
  conv_rhs => rw [hv]
  simp only [map_add, map_smul, smul_eq_mul]

theorem W7a_Landreman3DEquilibria_advect_eq (V : LVec → LVec) (f : LVec → ℝ) (x : LVec) :
    advect V f x = fderiv ℝ f x (V x) :=
  W7a_Landreman3DEquilibria_sum_fderiv f x (V x)

/-- Derivatives of the ingredients along a curve. -/
theorem W7a_Landreman3DEquilibria_hasDerivAt_s (e : ℝ) (γ : ℝ → LVec) (d : LVec) (t0 : ℝ)
    (x : LVec) (hγ0 : γ t0 = x) (hγ : ∀ j, HasDerivAt (fun t => γ t j) (d j) t0) :
    HasDerivAt (fun t => sFun e (γ t))
      (2 * x 0 * d 0 / aCoef e ^ 2 + 2 * x 1 * d 1 / bCoef e ^ 2) t0 := by
  subst hγ0
  have h := (((hγ 0).mul (hγ 0)).div_const (aCoef e ^ 2)).add
    (((hγ 1).mul (hγ 1)).div_const (bCoef e ^ 2))
  have hfun : (fun t => sFun e (γ t)) =
      fun t => γ t 0 * γ t 0 / aCoef e ^ 2 + γ t 1 * γ t 1 / bCoef e ^ 2 := by
    funext t; simp only [sFun]; ring
  rw [hfun]
  exact h.congr_deriv (by (try simp only [Pi.sub_apply, Pi.add_apply, Pi.mul_apply, Pi.neg_apply]); ring)

theorem W7a_Landreman3DEquilibria_hasDerivAt_Q (γ : ℝ → LVec) (d : LVec) (t0 : ℝ)
    (x : LVec) (hγ0 : γ t0 = x) (hγ : ∀ j, HasDerivAt (fun t => γ t j) (d j) t0) :
    HasDerivAt (fun t => Qfun (γ t)) (x 0 * d 0 + x 1 * d 1 + 4 * x 2 * d 2) t0 := by
  subst hγ0
  have h := ((((hγ 0).mul (hγ 0)).add ((hγ 1).mul (hγ 1))).add
    (((hγ 2).mul (hγ 2)).const_mul 4)).div_const 2
  have hfun : (fun t => Qfun (γ t)) =
      fun t => (γ t 0 * γ t 0 + γ t 1 * γ t 1 + 4 * (γ t 2 * γ t 2)) / 2 := by
    funext t; simp only [Qfun]; ring
  rw [hfun]
  exact h.congr_deriv (by (try simp only [Pi.sub_apply, Pi.add_apply, Pi.mul_apply, Pi.neg_apply]); ring)

theorem W7a_Landreman3DEquilibria_hasDerivAt_F (e : ℝ) (γ : ℝ → LVec) (d : LVec) (t0 : ℝ)
    (x : LVec) (hγ0 : γ t0 = x)
    (hγ : ∀ j, HasDerivAt (fun t => γ t j) (d j) t0) (hx : x ∈ domainU e) :
    HasDerivAt (fun t => FFun e (γ t))
      ((2 * (1 - sFun e x) *
          (2 * x 0 * d 0 / aCoef e ^ 2 + 2 * x 1 * d 1 / bCoef e ^ 2)
          - 8 * x 2 * d 2) / (2 * FFun e x)) t0 := by
  have hs := W7a_Landreman3DEquilibria_hasDerivAt_s e γ d t0 x hγ0 hγ
  subst hγ0
  have hr := ((hasDerivAt_const t0 (1:ℝ)).sub (((hasDerivAt_const t0 (1:ℝ)).sub hs).mul
    ((hasDerivAt_const t0 (1:ℝ)).sub hs))).sub (((hγ 2).mul (hγ 2)).const_mul 4)
  have hfun : (fun t => radicand e (γ t)) = fun t =>
      1 - (1 - sFun e (γ t)) * (1 - sFun e (γ t)) - 4 * (γ t 2 * γ t 2) := by
    funext t; simp only [radicand]; ring
  have hr' : HasDerivAt (fun t => radicand e (γ t))
      (2 * (1 - sFun e (γ t0)) *
          (2 * γ t0 0 * d 0 / aCoef e ^ 2 + 2 * γ t0 1 * d 1 / bCoef e ^ 2)
          - 8 * γ t0 2 * d 2) t0 := by
    rw [hfun]
    exact hr.congr_deriv (by (try simp only [Pi.sub_apply, Pi.add_apply, Pi.mul_apply, Pi.neg_apply]); ring)
  have hne : radicand e (γ t0) ≠ 0 := (show 0 < radicand e (γ t0) from hx).ne'
  exact hr'.sqrt hne

theorem W7a_Landreman3DEquilibria_hasDerivAt_B0 (e : ℝ) (γ : ℝ → LVec) (d : LVec) (t0 : ℝ)
    (x : LVec) (hγ0 : γ t0 = x)
    (hγ : ∀ j, HasDerivAt (fun t => γ t j) (d j) t0) (hx : x ∈ domainU e) :
    HasDerivAt (fun t => Bfield e (γ t) 0)
      (((2 * d 2 * x 0 + 2 * x 2 * d 0 - aCoef e / bCoef e *
          ((2 * (1 - sFun e x) *
            (2 * x 0 * d 0 / aCoef e ^ 2 + 2 * x 1 * d 1 / bCoef e ^ 2)
            - 8 * x 2 * d 2) / (2 * FFun e x) * x 1 + FFun e x * d 1))
          * sFun e x -
        (2 * x 2 * x 0 - aCoef e / bCoef e * FFun e x * x 1) *
          (2 * x 0 * d 0 / aCoef e ^ 2 + 2 * x 1 * d 1 / bCoef e ^ 2))
        / sFun e x ^ 2) t0 := by
  have hs := W7a_Landreman3DEquilibria_hasDerivAt_s e γ d t0 x hγ0 hγ
  have hF := W7a_Landreman3DEquilibria_hasDerivAt_F e γ d t0 x hγ0 hγ hx
  have hsne := (W7a_Landreman3DEquilibria_s_pos e _ hx).ne'
  subst hγ0
  have h := ((((hγ 2).const_mul 2).mul (hγ 0)).sub ((hF.const_mul (aCoef e / bCoef e)).mul
    (hγ 1))).div hs hsne
  have hfun : (fun t => Bfield e (γ t) 0) = fun t =>
      (2 * γ t 2 * γ t 0 - aCoef e / bCoef e * FFun e (γ t) * γ t 1) / sFun e (γ t) := by
    funext t; rfl
  rw [hfun]
  exact h.congr_deriv (by (try simp only [Pi.sub_apply, Pi.add_apply, Pi.mul_apply, Pi.neg_apply]); ring)

theorem W7a_Landreman3DEquilibria_hasDerivAt_B1 (e : ℝ) (γ : ℝ → LVec) (d : LVec) (t0 : ℝ)
    (x : LVec) (hγ0 : γ t0 = x)
    (hγ : ∀ j, HasDerivAt (fun t => γ t j) (d j) t0) (hx : x ∈ domainU e) :
    HasDerivAt (fun t => Bfield e (γ t) 1)
      (((2 * d 2 * x 1 + 2 * x 2 * d 1 + bCoef e / aCoef e *
          ((2 * (1 - sFun e x) *
            (2 * x 0 * d 0 / aCoef e ^ 2 + 2 * x 1 * d 1 / bCoef e ^ 2)
            - 8 * x 2 * d 2) / (2 * FFun e x) * x 0 + FFun e x * d 0))
          * sFun e x -
        (2 * x 2 * x 1 + bCoef e / aCoef e * FFun e x * x 0) *
          (2 * x 0 * d 0 / aCoef e ^ 2 + 2 * x 1 * d 1 / bCoef e ^ 2))
        / sFun e x ^ 2) t0 := by
  have hs := W7a_Landreman3DEquilibria_hasDerivAt_s e γ d t0 x hγ0 hγ
  have hF := W7a_Landreman3DEquilibria_hasDerivAt_F e γ d t0 x hγ0 hγ hx
  have hsne := (W7a_Landreman3DEquilibria_s_pos e _ hx).ne'
  subst hγ0
  have h := ((((hγ 2).const_mul 2).mul (hγ 1)).add ((hF.const_mul (bCoef e / aCoef e)).mul
    (hγ 0))).div hs hsne
  have hfun : (fun t => Bfield e (γ t) 1) = fun t =>
      (2 * γ t 2 * γ t 1 + bCoef e / aCoef e * FFun e (γ t) * γ t 0) / sFun e (γ t) := by
    funext t; rfl
  rw [hfun]
  exact h.congr_deriv (by (try simp only [Pi.sub_apply, Pi.add_apply, Pi.mul_apply, Pi.neg_apply]); ring)

theorem W7a_Landreman3DEquilibria_hasDerivAt_B2 (e : ℝ) (γ : ℝ → LVec) (d : LVec) (t0 : ℝ)
    (x : LVec) (hγ0 : γ t0 = x) (hγ : ∀ j, HasDerivAt (fun t => γ t j) (d j) t0) :
    HasDerivAt (fun t => Bfield e (γ t) 2)
      (-(2 * x 0 * d 0 / aCoef e ^ 2 + 2 * x 1 * d 1 / bCoef e ^ 2)) t0 := by
  have hs := W7a_Landreman3DEquilibria_hasDerivAt_s e γ d t0 x hγ0 hγ
  have hfun : (fun t => Bfield e (γ t) 2) = fun t => 1 - sFun e (γ t) := by
    funext t; rfl
  rw [hfun]
  exact ((hasDerivAt_const t0 (1:ℝ)).sub hs).congr_deriv (by (try simp only [Pi.sub_apply, Pi.add_apply, Pi.mul_apply, Pi.neg_apply]); ring)

theorem W7a_Landreman3DEquilibria_Bcomp_diff (e : ℝ) (he : 0 < e) (he1 : e < 1) (x : LVec)
    (hx : x ∈ domainU e) (i : Fin 3) : DifferentiableAt ℝ (fun y => Bfield e y i) x := by
  have h := W7a_Landreman3DEquilibria_field_smooth_on_domainU e he he1
  rw [contDiffOn_pi] at h
  exact ((h i).contDiffAt ((W7a_Landreman3DEquilibria_domainU_open e).mem_nhds hx)).differentiableAt
    (by simp)

theorem W7a_Landreman3DEquilibria_Q_diff (x : LVec) : DifferentiableAt ℝ Qfun x := by
  unfold Qfun
  fun_prop

theorem W7a_Landreman3DEquilibria_divergence_free (e : ℝ) (he : 0 < e) (he1 : e < 1)
    (x : LVec) (hx : x ∈ domainU e) :
    divg (Bfield e) x = 0 := by
  have hγ0 : ∀ v : LVec, (fun t : ℝ => x + t • v) 0 = x := fun v => by simp
  unfold divg partialD
  rw [Fin.sum_univ_three,
    W7a_Landreman3DEquilibria_dir _ x _ (W7a_Landreman3DEquilibria_Bcomp_diff e he he1 x hx 0) _
      (W7a_Landreman3DEquilibria_hasDerivAt_B0 e _ _ _ x (hγ0 _)
        (W7a_Landreman3DEquilibria_line_comp x _) hx),
    W7a_Landreman3DEquilibria_dir _ x _ (W7a_Landreman3DEquilibria_Bcomp_diff e he he1 x hx 1) _
      (W7a_Landreman3DEquilibria_hasDerivAt_B1 e _ _ _ x (hγ0 _)
        (W7a_Landreman3DEquilibria_line_comp x _) hx),
    W7a_Landreman3DEquilibria_dir _ x _ (W7a_Landreman3DEquilibria_Bcomp_diff e he he1 x hx 2) _
      (W7a_Landreman3DEquilibria_hasDerivAt_B2 e _ _ _ x (hγ0 _)
        (W7a_Landreman3DEquilibria_line_comp x _))]
  simp only [Pi.single_apply]
  simp
  have ha : aCoef e ≠ 0 := (Real.sqrt_pos.mpr (by linarith)).ne'
  have hb : bCoef e ≠ 0 := (Real.sqrt_pos.mpr (by linarith)).ne'
  have hsne := (W7a_Landreman3DEquilibria_s_pos e _ hx).ne'
  have hF : FFun e x ≠ 0 := (Real.sqrt_pos.mpr (show 0 < radicand e x from hx)).ne'
  have hsdef : sFun e x = x 0 ^ 2 / aCoef e ^ 2 + x 1 ^ 2 / bCoef e ^ 2 := rfl
  field_simp
  rw [hsdef]
  field_simp
  ring

/-- The field derivative along the field itself. -/
theorem W7a_Landreman3DEquilibria_tension_dir (e : ℝ) (he : 0 < e) (he1 : e < 1)
    (x : LVec) (hx : x ∈ domainU e) (i : Fin 3) :
    HasDerivAt (fun t : ℝ => Bfield e (x + t • Bfield e x) i)
      (-(![x 0, x 1, 4 * x 2] i)) (0:ℝ) := by
  have hγ0 : (fun t : ℝ => x + t • Bfield e x) 0 = x := by simp
  have hl := W7a_Landreman3DEquilibria_line_comp x (Bfield e x)
  have ha : aCoef e ≠ 0 := (Real.sqrt_pos.mpr (by linarith)).ne'
  have hb : bCoef e ≠ 0 := (Real.sqrt_pos.mpr (by linarith)).ne'
  have hsne := (W7a_Landreman3DEquilibria_s_pos e _ hx).ne'
  have hF2 : FFun e x ^ 2 = 1 - (1 - sFun e x) ^ 2 - 4 * x 2 ^ 2 :=
    Real.sq_sqrt (show 0 < radicand e x from hx).le
  have hr1 : Bfield e x 0 * sFun e x = 2 * x 2 * x 0 - aCoef e / bCoef e * FFun e x * x 1 :=
    div_mul_cancel₀ _ hsne
  have hr2 : Bfield e x 1 * sFun e x = 2 * x 2 * x 1 + bCoef e / aCoef e * FFun e x * x 0 :=
    div_mul_cancel₀ _ hsne
  have hr3 : Bfield e x 2 = 1 - sFun e x := rfl
  have hsdef : sFun e x = x 0 ^ 2 / aCoef e ^ 2 + x 1 ^ 2 / bCoef e ^ 2 := rfl
  have hk : aCoef e / bCoef e / aCoef e ^ 2 = bCoef e / aCoef e / bCoef e ^ 2 := by
    rw [div_div, div_div, div_eq_div_iff (mul_ne_zero hb (pow_ne_zero 2 ha))
      (mul_ne_zero ha (pow_ne_zero 2 hb))]
    ring
  have hkk : aCoef e / bCoef e * (bCoef e / aCoef e) = 1 := by
    rw [div_mul_div_comm, mul_comm (bCoef e) (aCoef e), div_self (mul_ne_zero ha hb)]
  have hsd : 2 * x 0 * Bfield e x 0 / aCoef e ^ 2 + 2 * x 1 * Bfield e x 1 / bCoef e ^ 2 =
      4 * x 2 := by
    have h : (2 * x 0 * Bfield e x 0 / aCoef e ^ 2 + 2 * x 1 * Bfield e x 1 / bCoef e ^ 2) *
        sFun e x = 4 * x 2 * sFun e x := by
      linear_combination (2 * x 0 / aCoef e ^ 2) * hr1 + (2 * x 1 / bCoef e ^ 2) * hr2
        - 4 * x 2 * hsdef - 2 * FFun e x * x 0 * x 1 * hk
    exact mul_right_cancel₀ hsne h
  have hFd : (2 * (1 - sFun e x) *
      (2 * x 0 * Bfield e x 0 / aCoef e ^ 2 + 2 * x 1 * Bfield e x 1 / bCoef e ^ 2)
      - 8 * x 2 * Bfield e x 2) / (2 * FFun e x) = 0 := by
    rw [hsd, hr3]
    have : 2 * (1 - sFun e x) * (4 * x 2) - 8 * x 2 * (1 - sFun e x) = 0 := by ring
    rw [this, zero_div]
  fin_cases i
  · refine (W7a_Landreman3DEquilibria_hasDerivAt_B0 e _ _ _ x hγ0 hl hx).congr_deriv ?_
    rw [hFd, hsd, div_eq_iff (pow_ne_zero 2 hsne)]
    show _ = -x 0 * sFun e x ^ 2
    linear_combination (2 * x 0 * sFun e x) * hr3 + (2 * x 2) * hr1
      - (aCoef e / bCoef e * FFun e x) * hr2 - x 0 * hF2 - FFun e x ^ 2 * x 0 * hkk
  · refine (W7a_Landreman3DEquilibria_hasDerivAt_B1 e _ _ _ x hγ0 hl hx).congr_deriv ?_
    rw [hFd, hsd, div_eq_iff (pow_ne_zero 2 hsne)]
    show _ = -x 1 * sFun e x ^ 2
    linear_combination (2 * x 1 * sFun e x) * hr3 + (2 * x 2) * hr2
      + (bCoef e / aCoef e * FFun e x) * hr1 - x 1 * hF2 - FFun e x ^ 2 * x 1 * hkk
  · refine (W7a_Landreman3DEquilibria_hasDerivAt_B2 e _ _ _ x hγ0 hl).congr_deriv ?_
    rw [hsd]
    rfl

theorem W7a_Landreman3DEquilibria_gradQ (x : LVec) (i : Fin 3) :
    partialD Qfun i x = ![x 0, x 1, 4 * x 2] i := by
  have hγ0 : (fun t : ℝ => x + t • (Pi.single i 1 : LVec)) 0 = x := by simp
  unfold partialD
  rw [W7a_Landreman3DEquilibria_dir _ x _ (W7a_Landreman3DEquilibria_Q_diff x) _
    (W7a_Landreman3DEquilibria_hasDerivAt_Q _ _ _ x hγ0
      (W7a_Landreman3DEquilibria_line_comp x _))]
  fin_cases i <;> simp

theorem W7a_Landreman3DEquilibria_tension_eq_neg_grad_Q (e : ℝ) (he : 0 < e) (he1 : e < 1)
    (x : LVec) (hx : x ∈ domainU e) :
    tension (Bfield e) x = -grad Qfun x := by
  funext i
  show advect (Bfield e) (fun y => Bfield e y i) x = -(partialD Qfun i x)
  rw [W7a_Landreman3DEquilibria_advect_eq, W7a_Landreman3DEquilibria_gradQ,
    W7a_Landreman3DEquilibria_dir _ x _ (W7a_Landreman3DEquilibria_Bcomp_diff e he he1 x hx i) _
      (W7a_Landreman3DEquilibria_tension_dir e he he1 x hx i)]

theorem W7a_Landreman3DEquilibria_psi_diff (e : ℝ) (he : 0 < e) (he1 : e < 1) (x : LVec)
    (hx : x ∈ domainU e) : DifferentiableAt ℝ (psiFun e) x := by
  have h0 := W7a_Landreman3DEquilibria_Bcomp_diff e he he1 x hx 0
  have h1 := W7a_Landreman3DEquilibria_Bcomp_diff e he he1 x hx 1
  have h2 := W7a_Landreman3DEquilibria_Bcomp_diff e he he1 x hx 2
  have hQ := W7a_Landreman3DEquilibria_Q_diff x
  have hfun : psiFun e = fun y => (Qfun y + (Bfield e y 0 * Bfield e y 0 +
      Bfield e y 1 * Bfield e y 1 + Bfield e y 2 * Bfield e y 2) / 2 - 1 + e ^ 2 / 2) / 2 := by
    funext y; simp only [psiFun, Hfun, normSq, Fin.sum_univ_three]; ring
  rw [hfun]
  fun_prop

/-- Derivative of `ψ` along a line, in terms of the directional derivatives of `B`. -/
theorem W7a_Landreman3DEquilibria_psi_line (e : ℝ) (he : 0 < e) (he1 : e < 1) (x v : LVec)
    (hx : x ∈ domainU e) :
    HasDerivAt (fun t : ℝ => psiFun e (x + t • v))
      ((x 0 * v 0 + x 1 * v 1 + 4 * x 2 * v 2 +
        (Bfield e x 0 * fderiv ℝ (fun y => Bfield e y 0) x v +
         Bfield e x 1 * fderiv ℝ (fun y => Bfield e y 1) x v +
         Bfield e x 2 * fderiv ℝ (fun y => Bfield e y 2) x v)) / 2) (0:ℝ) := by
  have hγ0 : (fun t : ℝ => x + t • v) 0 = x := by simp
  have hQ := W7a_Landreman3DEquilibria_hasDerivAt_Q _ _ _ x hγ0
    (W7a_Landreman3DEquilibria_line_comp x v)
  have d0 := W7a_Landreman3DEquilibria_line_deriv _ x v
    (W7a_Landreman3DEquilibria_Bcomp_diff e he he1 x hx 0)
  have d1 := W7a_Landreman3DEquilibria_line_deriv _ x v
    (W7a_Landreman3DEquilibria_Bcomp_diff e he he1 x hx 1)
  have d2 := W7a_Landreman3DEquilibria_line_deriv _ x v
    (W7a_Landreman3DEquilibria_Bcomp_diff e he he1 x hx 2)
  have h := ((((hQ.add ((((d0.mul d0).add (d1.mul d1)).add (d2.mul d2)).div_const 2))).sub
    (hasDerivAt_const (0:ℝ) (1:ℝ))).add (hasDerivAt_const (0:ℝ) (e ^ 2 / 2))).div_const 2
  have hfun : (fun t : ℝ => psiFun e (x + t • v)) = fun t : ℝ =>
      ((Qfun (x + t • v) + (Bfield e (x + t • v) 0 * Bfield e (x + t • v) 0 +
        Bfield e (x + t • v) 1 * Bfield e (x + t • v) 1 +
        Bfield e (x + t • v) 2 * Bfield e (x + t • v) 2) / 2) - 1 + e ^ 2 / 2) / 2 := by
    funext t; simp only [psiFun, Hfun, normSq, Fin.sum_univ_three]; ring
  rw [hfun]
  refine h.congr_deriv ?_
  simp only [Pi.sub_apply, Pi.add_apply, Pi.mul_apply, zero_smul, add_zero]
  ring

theorem W7a_Landreman3DEquilibria_flux_label_invariant (e : ℝ) (he : 0 < e) (he1 : e < 1)
    (x : LVec) (hx : x ∈ domainU e) :
    advect (Bfield e) (psiFun e) x = 0 := by
  rw [W7a_Landreman3DEquilibria_advect_eq,
    W7a_Landreman3DEquilibria_dir _ x _ (W7a_Landreman3DEquilibria_psi_diff e he he1 x hx) _
      (W7a_Landreman3DEquilibria_psi_line e he he1 x (Bfield e x) hx)]
  rw [W7a_Landreman3DEquilibria_dir _ x _ (W7a_Landreman3DEquilibria_Bcomp_diff e he he1 x hx 0) _
      (W7a_Landreman3DEquilibria_tension_dir e he he1 x hx 0),
    W7a_Landreman3DEquilibria_dir _ x _ (W7a_Landreman3DEquilibria_Bcomp_diff e he he1 x hx 1) _
      (W7a_Landreman3DEquilibria_tension_dir e he he1 x hx 1),
    W7a_Landreman3DEquilibria_dir _ x _ (W7a_Landreman3DEquilibria_Bcomp_diff e he he1 x hx 2) _
      (W7a_Landreman3DEquilibria_tension_dir e he he1 x hx 2)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  ring

theorem W7a_Landreman3DEquilibria_force_balance (e pa : ℝ) (he : 0 < e) (he1 : e < 1) (x : LVec)
    (hx : x ∈ domainU e) :
    cross3 (curl (Bfield e) x) (Bfield e x) = grad (pressure e pa) x := by
  have hT : ∀ i : Fin 3, ∑ j : Fin 3, Bfield e x j * partialD (fun y => Bfield e y i) j x =
      -(![x 0, x 1, 4 * x 2] i) := fun i => by
    have := congrFun (W7a_Landreman3DEquilibria_tension_eq_neg_grad_Q e he he1 x hx) i
    have h2 : (-grad Qfun x) i = -(![x 0, x 1, 4 * x 2] i) := by
      show -(partialD Qfun i x) = _
      rw [W7a_Landreman3DEquilibria_gradQ]
    rw [h2] at this
    exact this
  have hP : ∀ i : Fin 3, partialD (pressure e pa) i x =
      -(![x 0, x 1, 4 * x 2] i + (Bfield e x 0 * partialD (fun y => Bfield e y 0) i x +
         Bfield e x 1 * partialD (fun y => Bfield e y 1) i x +
         Bfield e x 2 * partialD (fun y => Bfield e y 2) i x)) := fun i => by
    have hψ := W7a_Landreman3DEquilibria_psi_line e he he1 x (Pi.single i 1) hx
    have hp : HasDerivAt (fun t : ℝ => pressure e pa (x + t • (Pi.single i 1 : LVec))) _ 0 :=
      (hasDerivAt_const (0:ℝ) pa).sub (hψ.const_mul 2)
    have hpd : DifferentiableAt ℝ (pressure e pa) x := by
      have := W7a_Landreman3DEquilibria_psi_diff e he he1 x hx
      unfold pressure
      fun_prop
    unfold partialD
    rw [W7a_Landreman3DEquilibria_dir _ x _ hpd _ hp]
    fin_cases i <;> simp <;> ring
  have T0 := hT 0
  have T1 := hT 1
  have T2 := hT 2
  simp only [Fin.sum_univ_three] at T0 T1 T2
  funext i
  fin_cases i
  · show (partialD (fun y => Bfield e y 0) 2 x - partialD (fun y => Bfield e y 2) 0 x) *
        Bfield e x 2 - (partialD (fun y => Bfield e y 1) 0 x -
          partialD (fun y => Bfield e y 0) 1 x) * Bfield e x 1 = partialD (pressure e pa) 0 x
    rw [hP 0]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons] at T0 ⊢
    linear_combination T0
  · show (partialD (fun y => Bfield e y 1) 0 x - partialD (fun y => Bfield e y 0) 1 x) *
        Bfield e x 0 - (partialD (fun y => Bfield e y 2) 1 x -
          partialD (fun y => Bfield e y 1) 2 x) * Bfield e x 2 = partialD (pressure e pa) 1 x
    rw [hP 1]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons] at T1 ⊢
    linear_combination T1
  · show (partialD (fun y => Bfield e y 2) 1 x - partialD (fun y => Bfield e y 1) 2 x) *
        Bfield e x 1 - (partialD (fun y => Bfield e y 0) 2 x -
          partialD (fun y => Bfield e y 2) 0 x) * Bfield e x 0 = partialD (pressure e pa) 2 x
    rw [hP 2]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons] at T2 ⊢
    linear_combination T2


theorem W7a_Landreman3DEquilibria_Lfun_hasDerivAt_u (u v : ℝ) (huv : u ^ 2 + v ^ 2 < 1 / 4) :
    HasDerivAt (fun t => Lfun t v)
      (-u * (Lfun u v)⁻¹ * (Real.sqrt (1 - 4 * (u ^ 2 + v ^ 2)))⁻¹) u := by
  have hq : 0 < 1 - 4 * (u * u + v * v) := by nlinarith
  have hg : HasDerivAt (fun t => 1 - 4 * (t * t + v * v)) (-(4 * (1 * u + u * 1))) u :=
    ((((hasDerivAt_id' u).mul (hasDerivAt_id' u)).add_const (v * v)).const_mul 4).const_sub 1
  have hsq := hg.sqrt hq.ne'
  have hr0 : 0 < Real.sqrt (1 - 4 * (u * u + v * v)) := Real.sqrt_pos.mpr hq
  have hh := (hsq.const_add 1).div_const 2
  have hpos : 0 < (1 + Real.sqrt (1 - 4 * (u * u + v * v))) / 2 := by positivity
  have hL := hh.sqrt hpos.ne'
  have hfun : (fun t => Lfun t v) =
      fun t => Real.sqrt ((1 + Real.sqrt (1 - 4 * (t * t + v * v))) / 2) := by
    funext t; simp only [Lfun, sq]
  have hq2 : u * u + v * v = u ^ 2 + v ^ 2 := by ring
  rw [hfun]
  refine hL.congr_deriv ?_
  have hLdef : Lfun u v = Real.sqrt ((1 + Real.sqrt (1 - 4 * (u * u + v * v))) / 2) := by
    simp only [Lfun, sq]
  rw [hLdef, hq2]
  rw [hq2] at hr0 hpos
  have h1 : Real.sqrt ((1 + Real.sqrt (1 - 4 * (u ^ 2 + v ^ 2))) / 2) ≠ 0 :=
    (Real.sqrt_pos.mpr hpos).ne'
  field_simp
  ring

theorem W7a_Landreman3DEquilibria_Lfun_hasDerivAt_v (u v : ℝ) (huv : u ^ 2 + v ^ 2 < 1 / 4) :
    HasDerivAt (fun t => Lfun u t)
      (-v * (Lfun u v)⁻¹ * (Real.sqrt (1 - 4 * (u ^ 2 + v ^ 2)))⁻¹) v := by
  have hq : 0 < 1 - 4 * (u * u + v * v) := by nlinarith
  have hg : HasDerivAt (fun t => 1 - 4 * (u * u + t * t)) (-(4 * (1 * v + v * 1))) v := by
    have := ((((hasDerivAt_id' v).mul (hasDerivAt_id' v)).const_add (u * u)).const_mul 4).const_sub 1
    exact this
  have hsq := hg.sqrt hq.ne'
  have hr0 : 0 < Real.sqrt (1 - 4 * (u * u + v * v)) := Real.sqrt_pos.mpr hq
  have hh := (hsq.const_add 1).div_const 2
  have hpos : 0 < (1 + Real.sqrt (1 - 4 * (u * u + v * v))) / 2 := by positivity
  have hL := hh.sqrt hpos.ne'
  have hfun : (fun t => Lfun u t) =
      fun t => Real.sqrt ((1 + Real.sqrt (1 - 4 * (u * u + t * t))) / 2) := by
    funext t; simp only [Lfun, sq]
  have hq2 : u * u + v * v = u ^ 2 + v ^ 2 := by ring
  rw [hfun]
  refine hL.congr_deriv ?_
  have hLdef : Lfun u v = Real.sqrt ((1 + Real.sqrt (1 - 4 * (u * u + v * v))) / 2) := by
    simp only [Lfun, sq]
  rw [hLdef, hq2]
  rw [hq2] at hr0 hpos
  have h1 : Real.sqrt ((1 + Real.sqrt (1 - 4 * (u ^ 2 + v ^ 2))) / 2) ≠ 0 :=
    (Real.sqrt_pos.mpr hpos).ne'
  field_simp
  ring

theorem W7a_Landreman3DEquilibria_posMap_jacobian_det (e u v z : ℝ) (he : 0 < e) (he1 : e < 1)
    (huv : u ^ 2 + v ^ 2 < 1 / 4) :
    (Matrix.of
      ![![deriv (fun t => posMap e t v z 0) u, deriv (fun t => posMap e u t z 0) v,
          deriv (fun t => posMap e u v t 0) z],
        ![deriv (fun t => posMap e t v z 1) u, deriv (fun t => posMap e u t z 1) v,
          deriv (fun t => posMap e u v t 1) z],
        ![deriv (fun t => posMap e t v z 2) u, deriv (fun t => posMap e u t z 2) v,
          deriv (fun t => posMap e u v t 2) z]]).det = -(aCoef e * bCoef e) := by
  have hq : 0 < 1 - 4 * (u ^ 2 + v ^ 2) := by nlinarith
  have hr0 : 0 < Real.sqrt (1 - 4 * (u ^ 2 + v ^ 2)) := Real.sqrt_pos.mpr hq
  have hr2 : Real.sqrt (1 - 4 * (u ^ 2 + v ^ 2)) ^ 2 = 1 - 4 * (u ^ 2 + v ^ 2) :=
    Real.sq_sqrt hq.le
  have hLpos : 0 < Lfun u v := by unfold Lfun; exact Real.sqrt_pos.mpr (by positivity)
  have hL2 : Lfun u v ^ 2 = (1 + Real.sqrt (1 - 4 * (u ^ 2 + v ^ 2))) / 2 := by
    unfold Lfun; exact Real.sq_sqrt (by positivity)
  have hLne := hLpos.ne'
  have hLu := W7a_Landreman3DEquilibria_Lfun_hasDerivAt_u u v huv
  have hLv := W7a_Landreman3DEquilibria_Lfun_hasDerivAt_v u v huv
  have hLu' : ∀ t, Lfun t v ≠ 0 := fun t => by
    unfold Lfun
    apply (Real.sqrt_pos.mpr _).ne'
    have := Real.sqrt_nonneg (1 - 4 * (t ^ 2 + v ^ 2))
    linarith
  have hLv' : ∀ t, Lfun u t ≠ 0 := fun t => by
    unfold Lfun
    apply (Real.sqrt_pos.mpr _).ne'
    have := Real.sqrt_nonneg (1 - 4 * (u ^ 2 + t ^ 2))
    linarith
  -- entries
  have d00 : HasDerivAt (fun t => posMap e t v z 0) _ u :=
    ((hLu.mul_const (Real.cos z)).add ((((hasDerivAt_id' u).mul_const (Real.cos z)).add_const
      (v * Real.sin z)).div hLu hLne)).const_mul (aCoef e)
  have d01 : HasDerivAt (fun t => posMap e u t z 0) _ v :=
    ((hLv.mul_const (Real.cos z)).add ((((hasDerivAt_id' v).mul_const (Real.sin z)).const_add
      (u * Real.cos z)).div hLv hLne)).const_mul (aCoef e)
  have d02 : HasDerivAt (fun t => posMap e u v t 0) _ z :=
    ((((Real.hasDerivAt_cos z).const_mul (Lfun u v)).add
      ((((Real.hasDerivAt_cos z).const_mul u).add
        ((Real.hasDerivAt_sin z).const_mul v)).div_const (Lfun u v))).const_mul (aCoef e))
  have d10 : HasDerivAt (fun t => posMap e t v z 1) _ u :=
    ((hLu.mul_const (Real.sin z)).add ((((hasDerivAt_id' u).mul_const (Real.sin z)).const_sub
      (v * Real.cos z)).div hLu hLne)).const_mul (bCoef e)
  have d11 : HasDerivAt (fun t => posMap e u t z 1) _ v :=
    ((hLv.mul_const (Real.sin z)).add ((((hasDerivAt_id' v).mul_const (Real.cos z)).sub_const
      (u * Real.sin z)).div hLv hLne)).const_mul (bCoef e)
  have d12 : HasDerivAt (fun t => posMap e u v t 1) _ z :=
    ((((Real.hasDerivAt_sin z).const_mul (Lfun u v)).add
      ((((Real.hasDerivAt_cos z).const_mul v).sub
        ((Real.hasDerivAt_sin z).const_mul u)).div_const (Lfun u v))).const_mul (bCoef e))
  have d20 : HasDerivAt (fun t => posMap e t v z 2) _ u :=
    ((hasDerivAt_id' u).mul_const (Real.sin (2 * z))).const_sub (v * Real.cos (2 * z))
  have d21 : HasDerivAt (fun t => posMap e u t z 2) _ v :=
    ((hasDerivAt_id' v).mul_const (Real.cos (2 * z))).sub_const (u * Real.sin (2 * z))
  have d22 : HasDerivAt (fun t => posMap e u v t 2) _ z :=
    (((hasDerivAt_id' z).const_mul (2:ℝ)).cos.const_mul v).sub
      (((hasDerivAt_id' z).const_mul (2:ℝ)).sin.const_mul u)
  rw [d00.deriv, d01.deriv, d02.deriv, d10.deriv, d11.deriv, d12.deriv, d20.deriv, d21.deriv,
    d22.deriv, Matrix.det_fin_three]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  rw [Real.cos_two_mul, Real.sin_two_mul]
  have hcs : Real.cos z ^ 2 + Real.sin z ^ 2 = 1 := Real.cos_sq_add_sin_sq z
  have hrel : Lfun u v ^ 4 - Lfun u v ^ 2 + (u ^ 2 + v ^ 2) = 0 := by
    linear_combination (Lfun u v ^ 2 + (1 + Real.sqrt (1 - 4 * (u ^ 2 + v ^ 2))) / 2 - 1) * hL2
      + (1 / 4 : ℝ) * hr2
  have hR5 : Real.sqrt (1 - 4 * (u ^ 2 + v ^ 2)) = 2 * Lfun u v ^ 2 - 1 := by linarith
  have hR1 : Lfun u v * (Lfun u v)⁻¹ = 1 := mul_inv_cancel₀ hLne
  have hR2 : Real.sqrt (1 - 4 * (u ^ 2 + v ^ 2)) * (Real.sqrt (1 - 4 * (u ^ 2 + v ^ 2)))⁻¹ = 1 :=
    mul_inv_cancel₀ hr0.ne'
  have hdL : ∀ w : ℝ, w / Lfun u v = w * (Lfun u v)⁻¹ := fun w => div_eq_mul_inv _ _
  have hdL2 : ∀ w : ℝ, w / Lfun u v ^ 2 = w * (Lfun u v)⁻¹ ^ 2 := fun w => by
    rw [div_eq_mul_inv, inv_pow]
  simp only [hdL, hdL2]
  generalize (Lfun u v)⁻¹ = iL at *
  generalize (Real.sqrt (1 - 4 * (u ^ 2 + v ^ 2)))⁻¹ = ir at *
  generalize Real.sqrt (1 - 4 * (u ^ 2 + v ^ 2)) = R at *
  generalize Lfun u v = L at *
  generalize Real.cos z = c at *
  generalize Real.sin z = s at *
  linear_combination (aCoef e * bCoef e) * (((-1:ℝ)*R*ir + (4:ℝ)*iL^2*R*ir^2*v^2*c^2*s^2 + (-2:ℝ)*iL^2*R*ir^2*u*v*c*s + (-2:ℝ)*iL^2*R*ir^2*u*v*c*s^3 + (6:ℝ)*iL^2*R*ir^2*u*v*c^3*s + (1:ℝ)*iL^2*R*ir^2*u^2*s^2 + (-1:ℝ)*iL^2*R*ir^2*u^2*c^2 + (-2:ℝ)*iL^2*R*ir^2*u^2*c^2*s^2 + (2:ℝ)*iL^2*R*ir^2*u^2*c^4 + (-4:ℝ)*iL^4*R*ir^2*v^3*c*s^3 + (-4:ℝ)*iL^4*R*ir^2*v^3*c^3*s + (2:ℝ)*iL^4*R*ir^2*u*v^2*s^2 + (2:ℝ)*iL^4*R*ir^2*u*v^2*c^2 + (-4:ℝ)*iL^4*R*ir^2*u*v^2*c^2*s^2 + (-4:ℝ)*iL^4*R*ir^2*u*v^2*c^4 + (-4:ℝ)*iL^4*R*ir^2*u^2*v*c*s^3 + (-4:ℝ)*iL^4*R*ir^2*u^2*v*c^3*s + (2:ℝ)*iL^4*R*ir^2*u^3*s^2 + (2:ℝ)*iL^4*R*ir^2*u^3*c^2 + (-4:ℝ)*iL^4*R*ir^2*u^3*c^2*s^2 + (-4:ℝ)*iL^4*R*ir^2*u^3*c^4 + (-1:ℝ)*L*iL*R*ir + (-2:ℝ)*L*iL*R*ir^2*v*c*s^3 + (-2:ℝ)*L*iL*R*ir^2*v*c^3*s + (1:ℝ)*L*iL*R*ir^2*u*s^2 + (1:ℝ)*L*iL*R*ir^2*u*c^2 + (-2:ℝ)*L*iL*R*ir^2*u*c^2*s^2 + (-2:ℝ)*L*iL*R*ir^2*u*c^4 + (-2:ℝ)*L*iL^3*R*ir*v*c*s^3 + (-2:ℝ)*L*iL^3*R*ir*v*c^3*s + (1:ℝ)*L*iL^3*R*ir*u*s^2 + (1:ℝ)*L*iL^3*R*ir*u*c^2 + (-2:ℝ)*L*iL^3*R*ir*u*c^2*s^2 + (-2:ℝ)*L*iL^3*R*ir*u*c^4 + (-1:ℝ)*L^2*iL^2*R*ir + (1:ℝ)*L^2*iL^2*R*ir*s^2 + (-1:ℝ)*L^2*iL^2*R*ir*c^2 + (2:ℝ)*L^2*iL^2*R*ir*c^2*s^2 + (2:ℝ)*L^2*iL^2*R*ir*c^4 + (-2:ℝ)*L^2*iL^2*R*ir^2*v*c*s^3 + (-2:ℝ)*L^2*iL^2*R*ir^2*v*c^3*s + (1:ℝ)*L^2*iL^2*R*ir^2*u*s^2 + (1:ℝ)*L^2*iL^2*R*ir^2*u*c^2 + (-2:ℝ)*L^2*iL^2*R*ir^2*u*c^2*s^2 + (-2:ℝ)*L^2*iL^2*R*ir^2*u*c^4 + (-1:ℝ)*L^3*iL^3*R*ir + (1:ℝ)*L^3*iL^3*R*ir*s^2 + (-1:ℝ)*L^3*iL^3*R*ir*c^2 + (2:ℝ)*L^3*iL^3*R*ir*c^2*s^2 + (2:ℝ)*L^3*iL^3*R*ir*c^4 + (-2:ℝ)*L^3*iL^3*R*ir^2*v*c*s^3 + (-2:ℝ)*L^3*iL^3*R*ir^2*v*c^3*s + (1:ℝ)*L^3*iL^3*R*ir^2*u*s^2 + (1:ℝ)*L^3*iL^3*R*ir^2*u*c^2 + (-2:ℝ)*L^3*iL^3*R*ir^2*u*c^2*s^2 + (-2:ℝ)*L^3*iL^3*R*ir^2*u*c^4) * hR1 + ((-1:ℝ) + (4:ℝ)*iL^2*ir*v^2*c^2*s^2 + (-2:ℝ)*iL^2*ir*u*v*c*s + (-2:ℝ)*iL^2*ir*u*v*c*s^3 + (6:ℝ)*iL^2*ir*u*v*c^3*s + (1:ℝ)*iL^2*ir*u^2*s^2 + (-1:ℝ)*iL^2*ir*u^2*c^2 + (-2:ℝ)*iL^2*ir*u^2*c^2*s^2 + (2:ℝ)*iL^2*ir*u^2*c^4 + (-4:ℝ)*iL^4*ir*v^3*c*s^3 + (-4:ℝ)*iL^4*ir*v^3*c^3*s + (2:ℝ)*iL^4*ir*u*v^2*s^2 + (2:ℝ)*iL^4*ir*u*v^2*c^2 + (-4:ℝ)*iL^4*ir*u*v^2*c^2*s^2 + (-4:ℝ)*iL^4*ir*u*v^2*c^4 + (-4:ℝ)*iL^4*ir*u^2*v*c*s^3 + (-4:ℝ)*iL^4*ir*u^2*v*c^3*s + (2:ℝ)*iL^4*ir*u^3*s^2 + (2:ℝ)*iL^4*ir*u^3*c^2 + (-4:ℝ)*iL^4*ir*u^3*c^2*s^2 + (-4:ℝ)*iL^4*ir*u^3*c^4 + (-2:ℝ)*L*iL*ir*v*c*s^3 + (-2:ℝ)*L*iL*ir*v*c^3*s + (1:ℝ)*L*iL*ir*u*s^2 + (1:ℝ)*L*iL*ir*u*c^2 + (-2:ℝ)*L*iL*ir*u*c^2*s^2 + (-2:ℝ)*L*iL*ir*u*c^4 + (-2:ℝ)*L*iL^3*v*c*s^3 + (-2:ℝ)*L*iL^3*v*c^3*s + (1:ℝ)*L*iL^3*u*s^2 + (1:ℝ)*L*iL^3*u*c^2 + (-2:ℝ)*L*iL^3*u*c^2*s^2 + (-2:ℝ)*L*iL^3*u*c^4 + (-4:ℝ)*L*iL^3*ir*v^2*c^2*s^2 + (2:ℝ)*L*iL^3*ir*u*v*c*s + (2:ℝ)*L*iL^3*ir*u*v*c*s^3 + (-6:ℝ)*L*iL^3*ir*u*v*c^3*s + (-1:ℝ)*L*iL^3*ir*u^2*s^2 + (1:ℝ)*L*iL^3*ir*u^2*c^2 + (2:ℝ)*L*iL^3*ir*u^2*c^2*s^2 + (-2:ℝ)*L*iL^3*ir*u^2*c^4 + (4:ℝ)*L*iL^5*ir*v^3*c*s^3 + (4:ℝ)*L*iL^5*ir*v^3*c^3*s + (-2:ℝ)*L*iL^5*ir*u*v^2*s^2 + (-2:ℝ)*L*iL^5*ir*u*v^2*c^2 + (4:ℝ)*L*iL^5*ir*u*v^2*c^2*s^2 + (4:ℝ)*L*iL^5*ir*u*v^2*c^4 + (4:ℝ)*L*iL^5*ir*u^2*v*c*s^3 + (4:ℝ)*L*iL^5*ir*u^2*v*c^3*s + (-2:ℝ)*L*iL^5*ir*u^3*s^2 + (-2:ℝ)*L*iL^5*ir*u^3*c^2 + (4:ℝ)*L*iL^5*ir*u^3*c^2*s^2 + (4:ℝ)*L*iL^5*ir*u^3*c^4 + (1:ℝ)*L^2*iL^2*s^2 + (-1:ℝ)*L^2*iL^2*c^2 + (2:ℝ)*L^2*iL^2*c^2*s^2 + (2:ℝ)*L^2*iL^2*c^4 + (4:ℝ)*L^2*iL^4*v*c*s^3 + (4:ℝ)*L^2*iL^4*v*c^3*s + (-2:ℝ)*L^2*iL^4*u*s^2 + (-2:ℝ)*L^2*iL^4*u*c^2 + (4:ℝ)*L^2*iL^4*u*c^2*s^2 + (4:ℝ)*L^2*iL^4*u*c^4 + (2:ℝ)*L^4*iL^4*ir*v*c*s^3 + (2:ℝ)*L^4*iL^4*ir*v*c^3*s + (-1:ℝ)*L^4*iL^4*ir*u*s^2 + (-1:ℝ)*L^4*iL^4*ir*u*c^2 + (2:ℝ)*L^4*iL^4*ir*u*c^2*s^2 + (2:ℝ)*L^4*iL^4*ir*u*c^4) * hR2 + ((-2:ℝ)*L^2*iL^4*ir*v*c*s^3 + (-2:ℝ)*L^2*iL^4*ir*v*c^3*s + (1:ℝ)*L^2*iL^4*ir*u*s^2 + (1:ℝ)*L^2*iL^4*ir*u*c^2 + (-2:ℝ)*L^2*iL^4*ir*u*c^2*s^2 + (-2:ℝ)*L^2*iL^4*ir*u*c^4 + (1:ℝ)*L^4*iL^4*ir + (-1:ℝ)*L^4*iL^4*ir*s^2 + (1:ℝ)*L^4*iL^4*ir*c^2 + (-2:ℝ)*L^4*iL^4*ir*c^2*s^2 + (-2:ℝ)*L^4*iL^4*ir*c^4) * hR5 + ((-2:ℝ)*iL^4*ir*v^3*c*s + (1:ℝ)*iL^4*ir*u*v^2 + (-2:ℝ)*iL^4*ir*u*v^2*c^2 + (-2:ℝ)*iL^4*ir*u^2*v*c*s + (1:ℝ)*iL^4*ir*u^3 + (-2:ℝ)*iL^4*ir*u^3*c^2 + (2:ℝ)*L^2*iL^4*ir*v*c*s + (-1:ℝ)*L^2*iL^4*ir*u + (2:ℝ)*L^2*iL^4*ir*u*c^2 + (1:ℝ)*L^4*iL^4*ir + (2:ℝ)*L^4*iL^4*ir*c^2 + (-2:ℝ)*L^4*iL^4*ir*v*c*s + (1:ℝ)*L^4*iL^4*ir*u + (-2:ℝ)*L^4*iL^4*ir*u*c^2 + (-2:ℝ)*L^6*iL^4*ir + (-4:ℝ)*L^6*iL^4*ir*c^2) * hcs + ((-2:ℝ)*iL^4*ir*v*c*s + (1:ℝ)*iL^4*ir*u + (-2:ℝ)*iL^4*ir*u*c^2) * hrel)

theorem W7a_Landreman3DEquilibria_posMap_hasDerivAt (e u v z : ℝ) (huv : u ^ 2 + v ^ 2 < 1 / 4)
    (j : Fin 3) :
    HasDerivAt (fun t => posMap e t v z j) (deriv (fun t => posMap e t v z j) u) u ∧
    HasDerivAt (fun t => posMap e u t z j) (deriv (fun t => posMap e u t z j) v) v ∧
    HasDerivAt (fun t => posMap e u v t j) (deriv (fun t => posMap e u v t j) z) z := by
  have hq : 0 < 1 - 4 * (u ^ 2 + v ^ 2) := by nlinarith
  have hLpos : 0 < Lfun u v := by unfold Lfun; exact Real.sqrt_pos.mpr (by positivity)
  have hLne := hLpos.ne'
  have hLu := W7a_Landreman3DEquilibria_Lfun_hasDerivAt_u u v huv
  have hLv := W7a_Landreman3DEquilibria_Lfun_hasDerivAt_v u v huv
  have d00 : HasDerivAt (fun t => posMap e t v z 0) _ u :=
    ((hLu.mul_const (Real.cos z)).add ((((hasDerivAt_id' u).mul_const (Real.cos z)).add_const
      (v * Real.sin z)).div hLu hLne)).const_mul (aCoef e)
  have d01 : HasDerivAt (fun t => posMap e u t z 0) _ v :=
    ((hLv.mul_const (Real.cos z)).add ((((hasDerivAt_id' v).mul_const (Real.sin z)).const_add
      (u * Real.cos z)).div hLv hLne)).const_mul (aCoef e)
  have d02 : HasDerivAt (fun t => posMap e u v t 0) _ z :=
    ((((Real.hasDerivAt_cos z).const_mul (Lfun u v)).add
      ((((Real.hasDerivAt_cos z).const_mul u).add
        ((Real.hasDerivAt_sin z).const_mul v)).div_const (Lfun u v))).const_mul (aCoef e))
  have d10 : HasDerivAt (fun t => posMap e t v z 1) _ u :=
    ((hLu.mul_const (Real.sin z)).add ((((hasDerivAt_id' u).mul_const (Real.sin z)).const_sub
      (v * Real.cos z)).div hLu hLne)).const_mul (bCoef e)
  have d11 : HasDerivAt (fun t => posMap e u t z 1) _ v :=
    ((hLv.mul_const (Real.sin z)).add ((((hasDerivAt_id' v).mul_const (Real.cos z)).sub_const
      (u * Real.sin z)).div hLv hLne)).const_mul (bCoef e)
  have d12 : HasDerivAt (fun t => posMap e u v t 1) _ z :=
    ((((Real.hasDerivAt_sin z).const_mul (Lfun u v)).add
      ((((Real.hasDerivAt_cos z).const_mul v).sub
        ((Real.hasDerivAt_sin z).const_mul u)).div_const (Lfun u v))).const_mul (bCoef e))
  have d20 : HasDerivAt (fun t => posMap e t v z 2) _ u :=
    ((hasDerivAt_id' u).mul_const (Real.sin (2 * z))).const_sub (v * Real.cos (2 * z))
  have d21 : HasDerivAt (fun t => posMap e u t z 2) _ v :=
    ((hasDerivAt_id' v).mul_const (Real.cos (2 * z))).sub_const (u * Real.sin (2 * z))
  have d22 : HasDerivAt (fun t => posMap e u v t 2) _ z :=
    (((hasDerivAt_id' z).const_mul (2:ℝ)).cos.const_mul v).sub
      (((hasDerivAt_id' z).const_mul (2:ℝ)).sin.const_mul u)
  fin_cases j
  · exact ⟨d00.differentiableAt.hasDerivAt, d01.differentiableAt.hasDerivAt,
      d02.differentiableAt.hasDerivAt⟩
  · exact ⟨d10.differentiableAt.hasDerivAt, d11.differentiableAt.hasDerivAt,
      d12.differentiableAt.hasDerivAt⟩
  · exact ⟨d20.differentiableAt.hasDerivAt, d21.differentiableAt.hasDerivAt,
      d22.differentiableAt.hasDerivAt⟩

theorem W7a_Landreman3DEquilibria_psi_posMap (e u v z : ℝ) (he : 0 < e) (he1 : e < 1)
    (huv : u ^ 2 + v ^ 2 < 1 / 4) :
    psiFun e (posMap e u v z) = (u + e / 2) * (u + e / 2) + v * v := by
  rw [psiFun, W7a_Landreman3DEquilibria_Hval e u v z he he1 huv]
  ring

/-- Every point of `U_ε` lies on a field line. -/
theorem W7a_Landreman3DEquilibria_surj (e : ℝ) (he : 0 < e) (he1 : e < 1) (x : LVec)
    (hx : x ∈ domainU e) : ∃ u v z : ℝ, u ^ 2 + v ^ 2 < 1 / 4 ∧ posMap e u v z = x := by
  have hapos : 0 < aCoef e := Real.sqrt_pos.mpr (by linarith)
  have hbpos : 0 < bCoef e := Real.sqrt_pos.mpr (by linarith)
  have hane := hapos.ne'
  have hbne := hbpos.ne'
  have hs0 := W7a_Landreman3DEquilibria_s_pos e x hx
  have hrad : 0 < radicand e x := hx
  set X0 := x 0 / aCoef e with hX0
  set Y0 := x 1 / bCoef e with hY0
  have hsX : sFun e x = X0 ^ 2 + Y0 ^ 2 := by
    rw [sFun, hX0, hY0, div_pow, div_pow]
  set U := (sFun e x - 1) / 2 with hU
  set V := x 2 with hV
  have hUV : U ^ 2 + V ^ 2 < 1 / 4 := by
    unfold radicand at hrad
    rw [hU, hV]
    nlinarith
  have hq : 0 < 1 - 4 * (U ^ 2 + V ^ 2) := by linarith
  have hr2 : Real.sqrt (1 - 4 * (U ^ 2 + V ^ 2)) ^ 2 = 1 - 4 * (U ^ 2 + V ^ 2) :=
    Real.sq_sqrt hq.le
  have hr0 : 0 ≤ Real.sqrt (1 - 4 * (U ^ 2 + V ^ 2)) := Real.sqrt_nonneg _
  have hLpos : 0 < Lfun U V := by
    unfold Lfun
    exact Real.sqrt_pos.mpr (by positivity)
  have hL2 : Lfun U V ^ 2 = (1 + Real.sqrt (1 - 4 * (U ^ 2 + V ^ 2))) / 2 := by
    unfold Lfun
    exact Real.sq_sqrt (by positivity)
  have hrel : Lfun U V ^ 4 - Lfun U V ^ 2 + (U ^ 2 + V ^ 2) = 0 := by
    linear_combination (Lfun U V ^ 2 + (1 + Real.sqrt (1 - 4 * (U ^ 2 + V ^ 2))) / 2 - 1) * hL2
      + (1 / 4 : ℝ) * hr2
  set L := Lfun U V with hLdef
  have hLne := hLpos.ne'
  have hT := (W7a_Landreman3DEquilibria_aux L U V hLne hrel).1
  set A := L + U / L with hA
  set B := V / L with hB
  have hAB : A ^ 2 + B ^ 2 = sFun e x := by rw [hT, hU]; ring
  set ωr := (X0 * A + Y0 * B) / sFun e x with hωr
  set ωi := (Y0 * A - X0 * B) / sFun e x with hωi
  have hω1 : ωr ^ 2 + ωi ^ 2 = 1 := by
    rw [hωr, hωi, div_pow, div_pow, ← add_div, div_eq_one_iff_eq (pow_ne_zero 2 hs0.ne')]
    linear_combination (X0 ^ 2 + Y0 ^ 2) * hAB - (sFun e x) * hsX
  set ω : ℂ := ⟨ωr, ωi⟩ with hω
  have hωn : ‖ω‖ = 1 := by
    rw [Complex.norm_eq_sqrt_sq_add_sq]
    simp only [hω]
    rw [hω1, Real.sqrt_one]
  have hωne : ω ≠ 0 := by
    intro h; rw [h, norm_zero] at hωn; exact zero_ne_one hωn
  set z := Complex.arg ω with hz
  have hc : Real.cos z = ωr := by rw [hz, Complex.cos_arg hωne, hωn, div_one]
  have hsn : Real.sin z = ωi := by rw [hz, Complex.sin_arg, hωn, div_one]
  have hcs : Real.cos z ^ 2 + Real.sin z ^ 2 = 1 := Real.cos_sq_add_sin_sq z
  -- X0 = c A - s B, Y0 = s A + c B
  have hXc : X0 = Real.cos z * A - Real.sin z * B := by
    rw [hc, hsn, hωr, hωi]
    field_simp
    linear_combination (-X0) * hAB + X0 * hsX - X0 * hsX
  have hYc : Y0 = Real.sin z * A + Real.cos z * B := by
    rw [hc, hsn, hωr, hωi]
    field_simp
    linear_combination (-Y0) * hAB
  set c := Real.cos z
  set s := Real.sin z
  refine ⟨U * (c ^ 2 - s ^ 2) - V * (2 * s * c), U * (2 * s * c) + V * (c ^ 2 - s ^ 2), z,
    ?_, ?_⟩
  · have : (U * (c ^ 2 - s ^ 2) - V * (2 * s * c)) ^ 2 + (U * (2 * s * c) + V * (c ^ 2 - s ^ 2)) ^ 2
        = U ^ 2 + V ^ 2 := by
      linear_combination (U ^ 2 + V ^ 2) * ((c ^ 2 + s ^ 2) + 1) * hcs
    rw [this]; exact hUV
  · have hsq : (U * (c ^ 2 - s ^ 2) - V * (2 * s * c)) ^ 2 +
        (U * (2 * s * c) + V * (c ^ 2 - s ^ 2)) ^ 2 = U ^ 2 + V ^ 2 := by
      linear_combination (U ^ 2 + V ^ 2) * ((c ^ 2 + s ^ 2) + 1) * hcs
    have hLuv : Lfun (U * (c ^ 2 - s ^ 2) - V * (2 * s * c))
        (U * (2 * s * c) + V * (c ^ 2 - s ^ 2)) = L := by
      rw [hLdef]; unfold Lfun; rw [hsq]
    funext j
    fin_cases j
    · show aCoef e * (Lfun _ _ * c + ((U * (c ^ 2 - s ^ 2) - V * (2 * s * c)) * c +
          (U * (2 * s * c) + V * (c ^ 2 - s ^ 2)) * s) / Lfun _ _) = x 0
      rw [hLuv]
      have hn : (U * (c ^ 2 - s ^ 2) - V * (2 * s * c)) * c +
          (U * (2 * s * c) + V * (c ^ 2 - s ^ 2)) * s = U * c - V * s := by
        linear_combination (U * c - V * s) * hcs
      rw [hn]
      have hx0 : x 0 = aCoef e * X0 := by rw [hX0]; field_simp
      rw [hx0, hXc, hA, hB]
      ring
    · show bCoef e * (Lfun _ _ * s + ((U * (2 * s * c) + V * (c ^ 2 - s ^ 2)) * c -
          (U * (c ^ 2 - s ^ 2) - V * (2 * s * c)) * s) / Lfun _ _) = x 1
      rw [hLuv]
      have hn : (U * (2 * s * c) + V * (c ^ 2 - s ^ 2)) * c -
          (U * (c ^ 2 - s ^ 2) - V * (2 * s * c)) * s = U * s + V * c := by
        linear_combination (U * s + V * c) * hcs
      rw [hn]
      have hx1 : x 1 = bCoef e * Y0 := by rw [hY0]; field_simp
      rw [hx1, hYc, hA, hB]
      ring
    · show (U * (2 * s * c) + V * (c ^ 2 - s ^ 2)) * Real.cos (2 * z) -
          (U * (c ^ 2 - s ^ 2) - V * (2 * s * c)) * Real.sin (2 * z) = x 2
      rw [Real.cos_two_mul, Real.sin_two_mul]
      show _ = V
      linear_combination (2 * s * c * U + V * (2 * c ^ 2 + 1)) * hcs

/-- Chain rule in field-line coordinates. -/
theorem W7a_Landreman3DEquilibria_chain (e u v z : ℝ) (he : 0 < e) (he1 : e < 1)
    (huv : u ^ 2 + v ^ 2 < 1 / 4) (hxU : posMap e u v z ∈ domainU e) :
    (∑ j : Fin 3, deriv (fun t => posMap e t v z j) u *
        fderiv ℝ (psiFun e) (posMap e u v z) (Pi.single j 1) = 2 * (u + e / 2)) ∧
    (∑ j : Fin 3, deriv (fun t => posMap e u t z j) v *
        fderiv ℝ (psiFun e) (posMap e u v z) (Pi.single j 1) = 2 * v) ∧
    (∑ j : Fin 3, deriv (fun t => posMap e u v t j) z *
        fderiv ℝ (psiFun e) (posMap e u v z) (Pi.single j 1) = 0) := by
  have hψ := (W7a_Landreman3DEquilibria_psi_diff e he he1 _ hxU).hasFDerivAt
  have hD := W7a_Landreman3DEquilibria_posMap_hasDerivAt e u v z huv
  have cu : HasDerivAt (fun t => posMap e t v z)
      (fun j => deriv (fun t => posMap e t v z j) u) u := hasDerivAt_pi.2 (fun j => (hD j).1)
  have cv : HasDerivAt (fun t => posMap e u t z)
      (fun j => deriv (fun t => posMap e u t z j) v) v := hasDerivAt_pi.2 (fun j => (hD j).2.1)
  have cz : HasDerivAt (fun t => posMap e u v t)
      (fun j => deriv (fun t => posMap e u v t j) z) z := hasDerivAt_pi.2 (fun j => (hD j).2.2)
  have hopen : IsOpen {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < 1 / 4} :=
    isOpen_lt (by fun_prop) continuous_const
  refine ⟨?_, ?_, ?_⟩
  · rw [W7a_Landreman3DEquilibria_sum_fderiv]
    have h1 := hψ.comp_hasDerivAt u cu
    have hev : ∀ᶠ t in nhds u, t ^ 2 + v ^ 2 < 1 / 4 := by
      have : IsOpen {t : ℝ | t ^ 2 + v ^ 2 < 1 / 4} := isOpen_lt (by fun_prop) continuous_const
      exact this.mem_nhds huv
    have h2 : HasDerivAt (fun t => psiFun e (posMap e t v z)) (2 * (u + e / 2)) u := by
      have hp : HasDerivAt (fun t => (t + e / 2) * (t + e / 2) + v * v) (2 * (u + e / 2)) u :=
        ((((hasDerivAt_id' u).add_const (e / 2)).mul ((hasDerivAt_id' u).add_const (e / 2))).add_const
          (v * v)).congr_deriv (by ring)
      refine hp.congr_of_eventuallyEq ?_
      filter_upwards [hev] with t ht
      exact W7a_Landreman3DEquilibria_psi_posMap e t v z he he1 ht
    exact h1.unique h2
  · rw [W7a_Landreman3DEquilibria_sum_fderiv]
    have h1 := hψ.comp_hasDerivAt v cv
    have hev : ∀ᶠ t in nhds v, u ^ 2 + t ^ 2 < 1 / 4 := by
      have : IsOpen {t : ℝ | u ^ 2 + t ^ 2 < 1 / 4} := isOpen_lt (by fun_prop) continuous_const
      exact this.mem_nhds huv
    have h2 : HasDerivAt (fun t => psiFun e (posMap e u t z)) (2 * v) v := by
      have hp : HasDerivAt (fun t => (u + e / 2) * (u + e / 2) + t * t) (2 * v) v :=
        (((hasDerivAt_id' v).mul (hasDerivAt_id' v)).const_add ((u + e / 2) * (u + e / 2))).congr_deriv
          (by ring)
      refine hp.congr_of_eventuallyEq ?_
      filter_upwards [hev] with t ht
      exact W7a_Landreman3DEquilibria_psi_posMap e u t z he he1 ht
    exact h1.unique h2
  · rw [W7a_Landreman3DEquilibria_sum_fderiv]
    have h1 := hψ.comp_hasDerivAt z cz
    have h2 : HasDerivAt (fun t => psiFun e (posMap e u v t)) 0 z := by
      have hfun : (fun t => psiFun e (posMap e u v t)) =
          fun _ => (u + e / 2) * (u + e / 2) + v * v := by
        funext t; exact W7a_Landreman3DEquilibria_psi_posMap e u v t he he1 huv
      rw [hfun]; exact hasDerivAt_const _ _
    exact h1.unique h2

theorem W7a_Landreman3DEquilibria_grad_psi_vanishes_only_on_axis (e d : ℝ) (he : 0 < e)
    (he1 : e < 1) (hd : 0 < d) (hd' : d < (1 - e) ^ 2 / 4) (x : LVec) (hx : x ∈ domainOmega e d) :
    grad (psiFun e) x = 0 ↔ psiFun e x = 0 := by
  have hxU : x ∈ domainU e := hx.1
  obtain ⟨u, v, z, huv, rfl⟩ := W7a_Landreman3DEquilibria_surj e he he1 x hxU
  have hval := W7a_Landreman3DEquilibria_psi_posMap e u v z he he1 huv
  obtain ⟨hU, hV, hZ⟩ := W7a_Landreman3DEquilibria_chain e u v z he he1 huv hxU
  simp only [Fin.sum_univ_three] at hU hV hZ
  have hdet := W7a_Landreman3DEquilibria_posMap_jacobian_det e u v z he he1 huv
  have hapos : 0 < aCoef e := Real.sqrt_pos.mpr (by linarith)
  have hbpos : 0 < bCoef e := Real.sqrt_pos.mpr (by linarith)
  constructor
  · intro hg
    have hg' : ∀ j, fderiv ℝ (psiFun e) (posMap e u v z) (Pi.single j 1) = 0 := fun j =>
      congrFun hg j
    rw [hg' 0, hg' 1, hg' 2] at hU hV
    have h1 : u + e / 2 = 0 := by linarith
    have h2 : v = 0 := by linarith
    rw [hval, h1, h2]; ring
  · intro h0
    rw [hval] at h0
    have h1 : u + e / 2 = 0 := by nlinarith [mul_self_nonneg (u + e / 2), mul_self_nonneg v]
    have h2 : v = 0 := by nlinarith [mul_self_nonneg (u + e / 2), mul_self_nonneg v]
    by_contra hne
    have hex : ∃ w : Fin 3 → ℝ, w ≠ 0 ∧ Matrix.vecMul w (Matrix.of
      ![![deriv (fun t => posMap e t v z 0) u, deriv (fun t => posMap e u t z 0) v,
          deriv (fun t => posMap e u v t 0) z],
        ![deriv (fun t => posMap e t v z 1) u, deriv (fun t => posMap e u t z 1) v,
          deriv (fun t => posMap e u v t 1) z],
        ![deriv (fun t => posMap e t v z 2) u, deriv (fun t => posMap e u t z 2) v,
          deriv (fun t => posMap e u v t 2) z]]) = 0 := by
      refine ⟨grad (psiFun e) (posMap e u v z), hne, ?_⟩
      funext k
      fin_cases k
      · simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_three, Matrix.of_apply,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
          Matrix.tail_cons, grad, partialD, Pi.zero_apply, Fin.zero_eta, Fin.isValue, Fin.mk_one,
          Fin.reduceFinMk]
        linear_combination hU + 2 * h1
      · simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_three, Matrix.of_apply,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
          Matrix.tail_cons, grad, partialD, Pi.zero_apply, Fin.zero_eta, Fin.isValue, Fin.mk_one,
          Fin.reduceFinMk]
        linear_combination hV + 2 * h2
      · simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_three, Matrix.of_apply,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
          Matrix.tail_cons, grad, partialD, Pi.zero_apply, Fin.zero_eta, Fin.isValue, Fin.mk_one,
          Fin.reduceFinMk]
        linear_combination hZ
    rw [Matrix.exists_vecMul_eq_zero_iff, hdet] at hex
    have : 0 < aCoef e * bCoef e := mul_pos hapos hbpos
    linarith

theorem W7a_Landreman3DEquilibria_posMap_mem (e u v z : ℝ) (he : 0 < e) (he1 : e < 1)
    (huv : u ^ 2 + v ^ 2 < 1 / 4) : posMap e u v z ∈ domainU e := by
  obtain ⟨L, U, V, R, -, -, -, hUV, -, -, -, -, -, -, -, h2, hs, -⟩ :=
    W7a_Landreman3DEquilibria_setup e u v z he he1 huv
  show 0 < radicand e (posMap e u v z)
  rw [radicand, hs, h2]
  nlinarith

theorem W7a_Landreman3DEquilibria_smooth_nonsymmetric_toroidal_equilibrium (e d pa : ℝ)
    (he : 0 < e) (he1 : e < 1) (hd : 0 < d) (hd' : d < (1 - e) ^ 2 / 4) :
    ContDiffOn ℝ (⊤ : ℕ∞) (Bfield e) (domainU e) ∧
      ContDiffOn ℝ (⊤ : ℕ∞) (pressure e pa) (domainU e) ∧
      (∀ x ∈ domainU e, divg (Bfield e) x = 0) ∧
      (∀ x ∈ domainU e, cross3 (curl (Bfield e) x) (Bfield e x) = grad (pressure e pa) x) ∧
      (∀ x ∈ domainU e, advect (Bfield e) (pressure e pa) x = 0) ∧
      (∀ x ∈ domainOmega e d, grad (pressure e pa) x = 0 ↔ psiFun e x = 0) ∧
      (∃ t : ℝ, ∃ x ∈ domainOmega e d, rotZ t x ∈ domainOmega e d ∧
        pressure e pa (rotZ t x) ≠ pressure e pa x) := by
  have hBs := W7a_Landreman3DEquilibria_field_smooth_on_domainU e he he1
  have hpd : ∀ x ∈ domainU e, DifferentiableAt ℝ (pressure e pa) x := fun x hx => by
    have := W7a_Landreman3DEquilibria_psi_diff e he he1 x hx
    unfold pressure
    fun_prop
  -- directional derivatives of the pressure
  have hpdir : ∀ x ∈ domainU e, ∀ w : LVec,
      fderiv ℝ (pressure e pa) x w = -(2 * fderiv ℝ (psiFun e) x w) := fun x hx w => by
    have hl := W7a_Landreman3DEquilibria_line_deriv (psiFun e) x w
      (W7a_Landreman3DEquilibria_psi_diff e he he1 x hx)
    have hp : HasDerivAt (fun t : ℝ => pressure e pa (x + t • w)) _ 0 :=
      (hasDerivAt_const (0:ℝ) pa).sub (hl.const_mul 2)
    rw [W7a_Landreman3DEquilibria_dir _ x _ (hpd x hx) _ hp]
    ring
  refine ⟨hBs, ?_, fun x hx => W7a_Landreman3DEquilibria_divergence_free e he he1 x hx,
    fun x hx => W7a_Landreman3DEquilibria_force_balance e pa he he1 x hx, ?_, ?_, ?_⟩
  · have hB := hBs
    rw [contDiffOn_pi] at hB
    have hQ : ContDiff ℝ (⊤ : ℕ∞) Qfun := by unfold Qfun; fun_prop
    have hfun : pressure e pa = fun y => pa - 2 * ((Qfun y + (Bfield e y 0 * Bfield e y 0 +
        Bfield e y 1 * Bfield e y 1 + Bfield e y 2 * Bfield e y 2) / 2 - 1 + e ^ 2 / 2) / 2) := by
      funext y; simp only [pressure, psiFun, Hfun, normSq, Fin.sum_univ_three]; ring
    rw [hfun]
    exact contDiffOn_const.sub (contDiffOn_const.mul ((((hQ.contDiffOn.add
      (((((hB 0).mul (hB 0)).add ((hB 1).mul (hB 1))).add ((hB 2).mul (hB 2))).div_const 2)).sub
        contDiffOn_const).add contDiffOn_const).div_const 2))
  · intro x hx
    rw [W7a_Landreman3DEquilibria_advect_eq, hpdir x hx]
    have := W7a_Landreman3DEquilibria_flux_label_invariant e he he1 x hx
    rw [W7a_Landreman3DEquilibria_advect_eq] at this
    rw [this]; ring
  · intro x hx
    have hxU : x ∈ domainU e := hx.1
    have hpi : ∀ i, partialD (pressure e pa) i x = -(2 * partialD (psiFun e) i x) :=
      fun i => hpdir x hxU _
    rw [← W7a_Landreman3DEquilibria_grad_psi_vanishes_only_on_axis e d he he1 hd hd' x hx]
    constructor
    · intro h
      funext i
      have h1 : partialD (pressure e pa) i x = 0 := congrFun h i
      show partialD (psiFun e) i x = 0
      rw [hpi] at h1
      linarith
    · intro h
      funext i
      have h1 : partialD (psiFun e) i x = 0 := congrFun h i
      show partialD (pressure e pa) i x = 0
      rw [hpi, h1]; ring
  · -- break of rotational symmetry near the magnetic axis
    have hax := solution e 0 he he1
    set x0 := axisCurve e 0 with hx0def
    have hsmall : (-(e / 2)) ^ 2 + (0:ℝ) ^ 2 < 1 / 4 := by nlinarith
    have hx0U : x0 ∈ domainU e := by
      rw [← hax.1]; exact W7a_Landreman3DEquilibria_posMap_mem e _ _ _ he he1 hsmall
    have hψ0 : psiFun e x0 = 0 := hax.2
    have hRa : 0 < Real.sqrt (1 - e ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
    have hx0v : x0 = ![Real.sqrt (1 - e ^ 2), 0, 0] := by
      rw [hx0def]; funext j; fin_cases j <;> simp [axisCurve]
    have hrot_cont : Continuous (fun t : ℝ => rotZ t x0) := by
      apply continuous_pi
      intro j
      fin_cases j <;> simp [rotZ] <;> fun_prop
    have hrot0 : rotZ 0 x0 = x0 := by
      funext j; fin_cases j <;> simp [rotZ]
    have hev1 : ∀ᶠ t in nhds (0:ℝ), rotZ t x0 ∈ domainU e := by
      have h : Filter.Tendsto (fun t => rotZ t x0) (nhds 0) (nhds x0) := by
        simpa only [hrot0] using hrot_cont.tendsto 0
      exact h ((W7a_Landreman3DEquilibria_domainU_open e).mem_nhds hx0U)
    have hev2 : ∀ᶠ t in nhds (0:ℝ), psiFun e (rotZ t x0) < d := by
      have hc : ContinuousAt (fun t => psiFun e (rotZ t x0)) 0 := by
        have h1 : ContinuousAt (psiFun e) (rotZ 0 x0) := by
          rw [hrot0]
          exact (W7a_Landreman3DEquilibria_psi_diff e he he1 x0 hx0U).continuousAt
        exact ContinuousAt.comp (f := fun t => rotZ t x0) (x := 0) h1 hrot_cont.continuousAt
      have : psiFun e (rotZ 0 x0) < d := by rw [hrot0, hψ0]; exact hd
      exact hc.eventually_lt continuousAt_const this
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 (hev1.and hev2)
    set t := min (δ / 2) (Real.pi / 4) with ht
    have ht0 : 0 < t := lt_min (by linarith) (by positivity)
    have htδ : t < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have htpi : t ≤ Real.pi / 4 := min_le_right _ _
    have hdist : dist t 0 < δ := by rw [Real.dist_eq, sub_zero, abs_of_pos ht0]; exact htδ
    obtain ⟨hU1, hψ1⟩ := hball hdist
    refine ⟨t, x0, ⟨hx0U, by rw [hψ0]; exact hd.le⟩, ⟨hU1, hψ1.le⟩, ?_⟩
    intro hEq
    have hψeq : psiFun e (rotZ t x0) = 0 := by
      unfold pressure at hEq; rw [hψ0] at hEq; linarith
    obtain ⟨u, v, z, huv, hpos⟩ := W7a_Landreman3DEquilibria_surj e he he1 _ hU1
    have hval := W7a_Landreman3DEquilibria_psi_posMap e u v z he he1 huv
    rw [hpos, hψeq] at hval
    have hsq1 : (u + e / 2) * (u + e / 2) = 0 := by
      nlinarith [mul_self_nonneg (u + e / 2), mul_self_nonneg v]
    have hsq2 : v * v = 0 := by nlinarith [mul_self_nonneg (u + e / 2), mul_self_nonneg v]
    have hu : u = -(e / 2) := by linarith [mul_self_eq_zero.mp hsq1]
    have hv : v = 0 := mul_self_eq_zero.mp hsq2
    rw [hu, hv, (solution e z he he1).1] at hpos
    have c0 := congrFun hpos 0
    have c1 := congrFun hpos 1
    have c2 := congrFun hpos 2
    rw [hx0v] at c0 c1 c2
    simp only [rotZ, axisCurve, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, mul_zero, sub_zero, add_zero] at c0 c1 c2
    have hcz : Real.cos z = Real.cos t := by
      have h : Real.sqrt (1 - e ^ 2) * (Real.cos z - Real.cos t) = 0 := by linarith
      rcases mul_eq_zero.mp h with h | h
      · exact absurd h hRa.ne'
      · linarith
    have hsz : Real.sin z = Real.sin t := by
      have h : Real.sqrt (1 - e ^ 2) * (Real.sin z - Real.sin t) = 0 := by linarith
      rcases mul_eq_zero.mp h with h | h
      · exact absurd h hRa.ne'
      · linarith
    have hst : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht0 (by linarith [Real.pi_pos])
    have hct : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    rw [Real.sin_two_mul, hcz, hsz] at c2
    have : 0 < e / 2 * (2 * Real.sin t * Real.cos t) := by positivity
    linarith
