-- Prove2me | solution 1 for HodgeComputer.FourPlusTwoResidual.homogenized_chart_source_a6t3_iff_ratio_chart_t4
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-25T16:12:23.18561+00:00
-- url     : https://prove2.me/submissions/40085ebe-ccdf-4f1f-9fe5-7730768499aa

import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false
noncomputable section

/-- **Chart derivative table.** The Leibniz computations that turn the homogenized
chart source into the ratio-chart identity. -/
private lemma chart_derivs {K : Type*} [Field K] [CharZero K]
    (Dr Ds Dt : Derivation ℤ K K) (a s t P qr qs qt : K)
    (ha : a ≠ 0) (ht : t ≠ 0)
    (hDr_a : Dr a = 0) (hDs_a : Ds a = 0) (hDt_a : Dt a = 0)
    (hDr_t : Dr t = 0) (hDs_t : Ds t = 0) (hDt_t : Dt t = 1) (hDs_s : Ds s = 1) :
    (Dr (a ^ 6 * P) = a ^ 6 * Dr P) ∧
    (Dt (a ^ 6 * P) = a ^ 6 * Dt P) ∧
    (Ds (a ^ 6 * P) = a ^ 6 * Ds P) ∧
    (Dr ((2 : K) * a * qr / (3 * t)) = (2 : K) * a * Dr qr / (3 * t)) ∧
    (Dt ((2 : K) * a * qt / (3 * t)) =
      (2 : K) * a * (t * Dt qt - qt) / (3 * t * t)) ∧
    (Ds ((2 : K) * a * qt / (3 * t)) = (2 : K) * a * Ds qt / (3 * t)) ∧
    (Ds ((2 : K) * a * (s * qt + t * qs) / (3 * t)) =
      (2 : K) * a * (s * Ds qt + qt + t * Ds qs) / (3 * t)) := by
  have h2 : (2 : K) ≠ 0 := by norm_num
  have h3 : (3 : K) ≠ 0 := by norm_num
  have h3t : (3 : K) * t ≠ 0 := mul_ne_zero h3 ht
  have h3t2 : (3 : K) * t * t ≠ 0 := mul_ne_zero h3t ht
  have hat : a * t ≠ 0 := mul_ne_zero ha ht
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h6 : Dr (a ^ 6) = 0 := by
      rw [Derivation.leibniz_pow, hDr_a]
      simp
    rw [Derivation.leibniz, h6]
    simp [smul_eq_mul]
  · have h6 : Dt (a ^ 6) = 0 := by
      rw [Derivation.leibniz_pow, hDt_a]
      simp
    rw [Derivation.leibniz, h6]
    simp [smul_eq_mul]
  · have h6 : Ds (a ^ 6) = 0 := by
      rw [Derivation.leibniz_pow, hDs_a]
      simp
    rw [Derivation.leibniz, h6]
    simp [smul_eq_mul]
  · have h3tDr : Dr ((3 : K) * t) = 0 := by
      rw [Derivation.leibniz]
      have h3' : Dr 3 = 0 := by simpa using Dr.map_natCast 3
      rw [h3', hDr_t]
      simp
    have h2aDr : Dr ((2 : K) * a) = 0 := by
      rw [Derivation.leibniz]
      have h2' : Dr 2 = 0 := by simpa using Dr.map_natCast 2
      rw [h2', hDr_a]
      simp
    have h2aqr : Dr ((2 : K) * a * qr) = (2 : K) * a * Dr qr := by
      rw [Derivation.leibniz, h2aDr]
      simp [smul_eq_mul]
    rw [Derivation.leibniz_div_const Dr _ _ h3tDr, h2aqr]
    simp only [smul_eq_mul]
    field_simp [h2, h3, h3t, h3t2, hat, ha, ht] <;> ring
  · have h2aDt : Dt ((2 : K) * a) = 0 := by
      rw [Derivation.leibniz]
      have h2' : Dt 2 = 0 := by simpa using Dt.map_natCast 2
      rw [h2', hDt_a]
      simp
    have h2aqt : Dt ((2 : K) * a * qt) = (2 : K) * a * Dt qt := by
      rw [Derivation.leibniz, h2aDt]
      simp [smul_eq_mul]
    have h3tDt : Dt ((3 : K) * t) = 3 := by
      rw [Derivation.leibniz]
      have h3' : Dt 3 = 0 := by simpa using Dt.map_natCast 3
      rw [h3', hDt_t]
      simp
    rw [Derivation.leibniz_div Dt _ _, h2aqt, h3tDt]
    simp only [smul_eq_mul]
    field_simp [h2, h3, h3t, h3t2, hat, ha, ht] <;> ring
  · have h3tDs : Ds ((3 : K) * t) = 0 := by
      rw [Derivation.leibniz]
      have h3' : Ds 3 = 0 := by simpa using Ds.map_natCast 3
      rw [h3', hDs_t]
      simp
    have h2aDs : Ds ((2 : K) * a) = 0 := by
      rw [Derivation.leibniz]
      have h2' : Ds 2 = 0 := by simpa using Ds.map_natCast 2
      rw [h2', hDs_a]
      simp
    have h2aqt : Ds ((2 : K) * a * qt) = (2 : K) * a * Ds qt := by
      rw [Derivation.leibniz, h2aDs]
      simp only [smul_eq_mul]
      ring
    rw [Derivation.leibniz_div_const Ds _ _ h3tDs, h2aqt]
    simp only [smul_eq_mul]
    field_simp [h2, h3, h3t, h3t2, hat, ha, ht] <;> ring
  · have h3tDs : Ds ((3 : K) * t) = 0 := by
      rw [Derivation.leibniz]
      have h3' : Ds 3 = 0 := by simpa using Ds.map_natCast 3
      rw [h3', hDs_t]
      simp
    have h2aDs : Ds ((2 : K) * a) = 0 := by
      rw [Derivation.leibniz]
      have h2' : Ds 2 = 0 := by simpa using Ds.map_natCast 2
      rw [h2', hDs_a]
      simp
    have hY1 : Ds (s * qt) = s * Ds qt + qt := by
      rw [Derivation.leibniz Ds]
      simp only [smul_eq_mul, hDs_s]
      ring
    have hY2 : Ds (t * qs) = t * Ds qs := by
      rw [Derivation.leibniz Ds]
      simp only [smul_eq_mul, hDs_t]
      ring
    have hY : Ds (s * qt + t * qs) = s * Ds qt + qt + t * Ds qs := by
      rw [Derivation.map_add Ds, hY1, hY2] <;> ring
    have h2aY : Ds ((2 : K) * a * (s * qt + t * qs))
        = (2 : K) * a * (s * Ds qt + qt + t * Ds qs) := by
      rw [Derivation.leibniz, h2aDs, hY]
      simp only [smul_eq_mul]
      ring
    rw [Derivation.leibniz_div_const Ds _ _ h3tDs, h2aY]
    simp only [smul_eq_mul]
    field_simp [h2, h3, h3t, h3t2, hat, ha, ht] <;> ring

theorem solution
    {K : Type*} [Field K] [CharZero K]
    (Dr Ds Dt : Derivation ℤ K K) (a s t P qr qs qt : K)
    (ha : a ≠ 0) (ht : t ≠ 0)
    (hDr_a : Dr a = 0) (hDs_a : Ds a = 0) (hDt_a : Dt a = 0)
    (hDr_t : Dr t = 0) (hDs_t : Ds t = 0) (hDt_t : Dt t = 1) (hDs_s : Ds s = 1) :
    (let H := a ^ 6 * P
     let db := fun z : K => Dr z / a
     let dc := fun z : K => (Dt z - s / t * Ds z) / a
     let dd := fun z : K => Ds z / (a * t)
     let pb := (2 : K) * a * qr / (3 * t)
     let pc := (2 : K) * a * qt / (3 * t)
     let pd := (2 : K) * a * (s * qt + t * qs) / (3 * t)
     pb * db H + pc * dc H + pd * dd H -
       (3 / 2 : K) * H * (db pb + dc pc + dd pd)) = a ^ 6 * t ^ 3 ↔
    (-(P * (Dr qr + Ds qs + Dt qt) - (2 / 3 : K) * (qr * Dr P + qs * Ds P + qt * Dt P))) = t ^ 4 := by
  obtain ⟨hDrH, hDtH, hDsH, hDrpb, hDtpc, hDspc, hDspd⟩ :=
    chart_derivs Dr Ds Dt a s t P qr qs qt ha ht hDr_a hDs_a hDt_a hDr_t hDs_t hDt_t hDs_s
  have h2 : (2 : K) ≠ 0 := by norm_num
  have h3 : (3 : K) ≠ 0 := by norm_num
  have h3t : (3 : K) * t ≠ 0 := mul_ne_zero h3 ht
  have h3t2 : (3 : K) * t * t ≠ 0 := mul_ne_zero h3t ht
  have hat : a * t ≠ 0 := mul_ne_zero ha ht
  have hid : t * (let H := a ^ 6 * P
     let db := fun z : K => Dr z / a
     let dc := fun z : K => (Dt z - s / t * Ds z) / a
     let dd := fun z : K => Ds z / (a * t)
     let pb := (2 : K) * a * qr / (3 * t)
     let pc := (2 : K) * a * qt / (3 * t)
     let pd := (2 : K) * a * (s * qt + t * qs) / (3 * t)
     pb * db H + pc * dc H + pd * dd H -
       (3 / 2 : K) * H * (db pb + dc pc + dd pd)) = a ^ 6 * (-(P * (Dr qr + Ds qs + Dt qt) - (2 / 3 : K) * (qr * Dr P + qs * Ds P + qt * Dt P))) := by
    dsimp only
    rw [hDrH, hDtH, hDsH, hDrpb, hDtpc, hDspc, hDspd]
    field_simp [h2, h3, h3t, h3t2, hat, ha, ht]
    ring
  constructor
  · intro hsrc
    have h1 : a ^ 6 * (-(P * (Dr qr + Ds qs + Dt qt) - (2 / 3 : K) * (qr * Dr P + qs * Ds P + qt * Dt P))) = t * (let H := a ^ 6 * P
     let db := fun z : K => Dr z / a
     let dc := fun z : K => (Dt z - s / t * Ds z) / a
     let dd := fun z : K => Ds z / (a * t)
     let pb := (2 : K) * a * qr / (3 * t)
     let pc := (2 : K) * a * qt / (3 * t)
     let pd := (2 : K) * a * (s * qt + t * qs) / (3 * t)
     pb * db H + pc * dc H + pd * dd H -
       (3 / 2 : K) * H * (db pb + dc pc + dd pd)) := by rw [hid]
    have h2' : a ^ 6 * (-(P * (Dr qr + Ds qs + Dt qt) - (2 / 3 : K) * (qr * Dr P + qs * Ds P + qt * Dt P))) = a ^ 6 * t ^ 4 := by
      calc a ^ 6 * (-(P * (Dr qr + Ds qs + Dt qt) - (2 / 3 : K) * (qr * Dr P + qs * Ds P + qt * Dt P))) = t * (let H := a ^ 6 * P
     let db := fun z : K => Dr z / a
     let dc := fun z : K => (Dt z - s / t * Ds z) / a
     let dd := fun z : K => Ds z / (a * t)
     let pb := (2 : K) * a * qr / (3 * t)
     let pc := (2 : K) * a * qt / (3 * t)
     let pd := (2 : K) * a * (s * qt + t * qs) / (3 * t)
     pb * db H + pc * dc H + pd * dd H -
       (3 / 2 : K) * H * (db pb + dc pc + dd pd)) := h1
        _ = t * (a ^ 6 * t ^ 3) := by rw [hsrc]
        _ = a ^ 6 * t ^ 4 := by ring
    have hz : a ^ 6 * ((-(P * (Dr qr + Ds qs + Dt qt) - (2 / 3 : K) * (qr * Dr P + qs * Ds P + qt * Dt P))) - t ^ 4) = 0 := by
      calc a ^ 6 * ((-(P * (Dr qr + Ds qs + Dt qt) - (2 / 3 : K) * (qr * Dr P + qs * Ds P + qt * Dt P))) - t ^ 4) = a ^ 6 * (-(P * (Dr qr + Ds qs + Dt qt) - (2 / 3 : K) * (qr * Dr P + qs * Ds P + qt * Dt P))) - a ^ 6 * t ^ 4 := by ring
        _ = 0 := by rw [h2']; ring
    have ha6 : a ^ 6 ≠ 0 := pow_ne_zero 6 ha
    have hz2 : (-(P * (Dr qr + Ds qs + Dt qt) - (2 / 3 : K) * (qr * Dr P + qs * Ds P + qt * Dt P))) - t ^ 4 = 0 := (mul_eq_zero.mp hz).resolve_left ha6
    exact sub_eq_zero.mp hz2
  · intro hrt4
    have h1 : t * (let H := a ^ 6 * P
     let db := fun z : K => Dr z / a
     let dc := fun z : K => (Dt z - s / t * Ds z) / a
     let dd := fun z : K => Ds z / (a * t)
     let pb := (2 : K) * a * qr / (3 * t)
     let pc := (2 : K) * a * qt / (3 * t)
     let pd := (2 : K) * a * (s * qt + t * qs) / (3 * t)
     pb * db H + pc * dc H + pd * dd H -
       (3 / 2 : K) * H * (db pb + dc pc + dd pd)) = a ^ 6 * t ^ 4 := by
      calc t * (let H := a ^ 6 * P
     let db := fun z : K => Dr z / a
     let dc := fun z : K => (Dt z - s / t * Ds z) / a
     let dd := fun z : K => Ds z / (a * t)
     let pb := (2 : K) * a * qr / (3 * t)
     let pc := (2 : K) * a * qt / (3 * t)
     let pd := (2 : K) * a * (s * qt + t * qs) / (3 * t)
     pb * db H + pc * dc H + pd * dd H -
       (3 / 2 : K) * H * (db pb + dc pc + dd pd)) = a ^ 6 * (-(P * (Dr qr + Ds qs + Dt qt) - (2 / 3 : K) * (qr * Dr P + qs * Ds P + qt * Dt P))) := hid
        _ = a ^ 6 * t ^ 4 := by rw [hrt4]
    have h2' : (let H := a ^ 6 * P
     let db := fun z : K => Dr z / a
     let dc := fun z : K => (Dt z - s / t * Ds z) / a
     let dd := fun z : K => Ds z / (a * t)
     let pb := (2 : K) * a * qr / (3 * t)
     let pc := (2 : K) * a * qt / (3 * t)
     let pd := (2 : K) * a * (s * qt + t * qs) / (3 * t)
     pb * db H + pc * dc H + pd * dd H -
       (3 / 2 : K) * H * (db pb + dc pc + dd pd)) - a ^ 6 * t ^ 3 = 0 := by
      have hz : t * ((let H := a ^ 6 * P
     let db := fun z : K => Dr z / a
     let dc := fun z : K => (Dt z - s / t * Ds z) / a
     let dd := fun z : K => Ds z / (a * t)
     let pb := (2 : K) * a * qr / (3 * t)
     let pc := (2 : K) * a * qt / (3 * t)
     let pd := (2 : K) * a * (s * qt + t * qs) / (3 * t)
     pb * db H + pc * dc H + pd * dd H -
       (3 / 2 : K) * H * (db pb + dc pc + dd pd)) - a ^ 6 * t ^ 3) = 0 := by
        calc t * ((let H := a ^ 6 * P
     let db := fun z : K => Dr z / a
     let dc := fun z : K => (Dt z - s / t * Ds z) / a
     let dd := fun z : K => Ds z / (a * t)
     let pb := (2 : K) * a * qr / (3 * t)
     let pc := (2 : K) * a * qt / (3 * t)
     let pd := (2 : K) * a * (s * qt + t * qs) / (3 * t)
     pb * db H + pc * dc H + pd * dd H -
       (3 / 2 : K) * H * (db pb + dc pc + dd pd)) - a ^ 6 * t ^ 3) = t * (let H := a ^ 6 * P
     let db := fun z : K => Dr z / a
     let dc := fun z : K => (Dt z - s / t * Ds z) / a
     let dd := fun z : K => Ds z / (a * t)
     let pb := (2 : K) * a * qr / (3 * t)
     let pc := (2 : K) * a * qt / (3 * t)
     let pd := (2 : K) * a * (s * qt + t * qs) / (3 * t)
     pb * db H + pc * dc H + pd * dd H -
       (3 / 2 : K) * H * (db pb + dc pc + dd pd)) - t * (a ^ 6 * t ^ 3) := by ring
          _ = a ^ 6 * t ^ 4 - a ^ 6 * t ^ 4 := by rw [h1]; ring
          _ = 0 := by ring
      exact (mul_eq_zero.mp hz).resolve_left ht
    exact sub_eq_zero.mp h2'
