-- Prove2me | solution 1 for Ironclad.relPerf_one_gt_one
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T17:49:18.06846+00:00
-- url     : https://prove2.me/submissions/5437c5df-2c5f-4338-b997-04913741ce0c

import Mathlib
import Definitions.Def_Ironclad_ClosedForms

namespace Aux_Ironclad_rp
open Ironclad

theorem main (q u v : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (hu0 : 0 < u) (hv0 : 0 < v)
    (hLu : Real.log u < 0) (hlog : q * Real.log v ≤ Real.log u) :
    1 < (1 - q) ^ 2 * u + q * (1 - q) * (u ^ 2 / v) + q * (u ^ 2 / v ^ 2) := by
  have hw1 : 0 ≤ (1 - q) ^ 2 := sq_nonneg _
  have hw2 : 0 ≤ q * (1 - q) := mul_nonneg hq0.le (by linarith)
  have hw3 : 0 ≤ q := hq0.le
  have hP2 : 0 < u ^ 2 / v := by positivity
  have hP3 : 0 < u ^ 2 / v ^ 2 := by positivity
  have hamgm := Real.geom_mean_le_arith_mean3_weighted hw1 hw2 hw3 hu0.le hP2.le hP3.le
    (by ring)
  have hGpos : 0 < u ^ (1 - q) ^ 2 * (u ^ 2 / v) ^ (q * (1 - q)) * (u ^ 2 / v ^ 2) ^ q := by
    positivity
  have hlogG : Real.log (u ^ (1 - q) ^ 2 * (u ^ 2 / v) ^ (q * (1 - q)) * (u ^ 2 / v ^ 2) ^ q) =
      (1 - q) ^ 2 * Real.log u + q * (1 - q) * (2 * Real.log u - Real.log v) +
        q * (2 * Real.log u - 2 * Real.log v) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_rpow hu0, Real.log_rpow hP2, Real.log_rpow hP3,
      Real.log_div (by positivity) hv0.ne', Real.log_div (by positivity) (by positivity),
      Real.log_pow, Real.log_pow]
    push_cast; ring
  have hpos : 0 < Real.log (u ^ (1 - q) ^ 2 * (u ^ 2 / v) ^ (q * (1 - q)) * (u ^ 2 / v ^ 2) ^ q) := by
    rw [hlogG]
    have h3 : 0 < 3 - q := by linarith
    have := mul_le_mul_of_nonneg_left hlog h3.le
    have h4 : 0 < -Real.log u * ((1 - q) * (2 - q)) :=
      mul_pos (by linarith) (mul_pos (by linarith) (by linarith))
    nlinarith
  have hG : 1 < u ^ (1 - q) ^ 2 * (u ^ 2 / v) ^ (q * (1 - q)) * (u ^ 2 / v ^ 2) ^ q :=
    (Real.log_pos_iff hGpos.le).mp hpos
  linarith

end Aux_Ironclad_rp

open Ironclad Aux_Ironclad_rp in
theorem solution (ph q : ℝ) (Δ : ℕ) (hph0 : 0 < ph) (hph1 : ph < 1) (hq0 : 0 < q)
    (hq1 : q < 1) (hΔ : 1 ≤ Δ) :
    1 < relPerf ph q Δ 1 (alphaClosed ph q Δ 1) := by
  have hb1 : 0 < 1 - q * ph := by nlinarith
  have hb1' : 1 - q * ph < 1 := by nlinarith
  have hb2 : 0 < 1 - ph := by linarith
  obtain ⟨u, hu⟩ : ∃ u, u = (1 - q * ph) ^ Δ := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v, v = (1 - ph) ^ Δ := ⟨_, rfl⟩
  have hu0 : 0 < u := by rw [hu]; positivity
  have hv0 : 0 < v := by rw [hv]; positivity
  have hLu : Real.log u < 0 := by
    rw [hu, Real.log_pow]
    have : Real.log (1 - q * ph) < 0 := Real.log_neg hb1 hb1'
    have : (1 : ℝ) ≤ Δ := by exact_mod_cast hΔ
    nlinarith
  have hconc : q * Real.log (1 - ph) ≤ Real.log (1 - q * ph) := by
    have h := strictConcaveOn_log_Ioi.concaveOn.2 (Set.mem_Ioi.mpr hb2)
      (Set.mem_Ioi.mpr one_pos) hq0.le (by linarith : (0 : ℝ) ≤ 1 - q) (by ring : q + (1 - q) = 1)
    simp only [smul_eq_mul, Real.log_one, mul_zero, add_zero] at h
    have e : q * (1 - ph) + (1 - q) * 1 = 1 - q * ph := by ring
    rw [e] at h
    exact h
  have hlog : q * Real.log v ≤ Real.log u := by
    rw [hu, hv, Real.log_pow, Real.log_pow]
    have : (0 : ℝ) ≤ Δ := Nat.cast_nonneg _
    nlinarith
  have hmain := main q u v hq0 hq1 hu0 hv0 hLu hlog
  have hrel : relPerf ph q Δ 1 (alphaClosed ph q Δ 1) =
      (1 - q) ^ 2 * u + q * (1 - q) * (u ^ 2 / v) + q * (u ^ 2 / v ^ 2) := by
    unfold relPerf alphaClosed qh qH
    rw [show (1 - ph) ^ (2 * Δ) = ((1 - ph) ^ Δ) ^ 2 by rw [← pow_mul, mul_comm], ← hu, ← hv]
    simp only [zero_mul, sub_zero, one_pow, mul_zero, add_zero, one_mul, mul_one]
    field_simp
    ring
  rw [hrel]; exact hmain
