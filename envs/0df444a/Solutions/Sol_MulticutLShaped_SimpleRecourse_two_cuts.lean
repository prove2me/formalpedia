-- Prove2me | solution 1 for MulticutLShaped.SimpleRecourse.two_cuts
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T03:00:45.482886+00:00
-- url     : https://prove2.me/submissions/1209cf06-1dc6-4f35-be88-7461fb3a50c3

import Mathlib
import Definitions.Def_MulticutLShaped_SimpleRecourse_Model

open MulticutLShaped.SimpleRecourse in
theorem c122b7dc_psiVal_eq (qp qm h χ : ℝ) (hq : 0 ≤ qp + qm) :
    psiVal qp qm h χ = ((max (qm * (χ - h)) (qp * (h - χ)) : ℝ) : EReal) := by
  unfold psiVal
  apply IsLeast.csInf_eq
  constructor
  · rcases le_total 0 (h - χ) with hd | hd
    · refine ⟨h - χ, 0, hd, le_refl _, by ring, ?_⟩
      congr 1
      rw [max_eq_right (by nlinarith)]
      ring
    · refine ⟨0, χ - h, le_refl _, by linarith, by ring, ?_⟩
      congr 1
      rw [max_eq_left (by nlinarith)]
      ring
  · rintro z ⟨yp, ym, hyp, hym, hd, rfl⟩
    refine EReal.coe_le_coe_iff.mpr ?_
    have e1 : χ - h = ym - yp := by linarith
    have e2 : h - χ = yp - ym := by linarith
    rw [e1, e2]
    apply max_le
    · nlinarith [mul_nonneg hq hyp]
    · nlinarith [mul_nonneg hq hym]

open MulticutLShaped.SimpleRecourse in
theorem solution (qp qm h χ : ℝ) (hq : 0 ≤ qp + qm) :
    (∃ yp ym : ℝ, 0 ≤ yp ∧ 0 ≤ ym ∧ yp - ym = h - χ ∧
      qp * yp + qm * ym = max (qm * (χ - h)) (qp * (h - χ))) ∧
    psiVal qp qm h χ = ((max (qm * (χ - h)) (qp * (h - χ)) : ℝ) : EReal) ∧
    ∀ p : ℝ, 0 ≤ p →
      (p : EReal) * psiVal qp qm h χ = ((max (p * qm * (χ - h)) (p * qp * (h - χ)) : ℝ) : EReal) := by
  refine ⟨?_, c122b7dc_psiVal_eq qp qm h χ hq, ?_⟩
  · rcases le_total 0 (h - χ) with hd | hd
    · refine ⟨h - χ, 0, hd, le_refl _, by ring, ?_⟩
      rw [max_eq_right (by nlinarith)]
      ring
    · refine ⟨0, χ - h, le_refl _, by linarith, by ring, ?_⟩
      rw [max_eq_left (by nlinarith)]
      ring
  · intro p hp
    rw [c122b7dc_psiVal_eq qp qm h χ hq, ← EReal.coe_mul, mul_max_of_nonneg _ _ hp]
    congr 2 <;> ring
