-- Prove2me | solution 1 for OAI.TriangularHilbert.Heat.weight_hasDerivAt_variance
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T02:28:44.83812+00:00
-- url     : https://prove2.me/submissions/aea4c64d-6e14-4017-8cf8-15addc394166

import Mathlib
import Definitions.Def_TriangularHilbert
import Definitions.Def_OAI_Analysis_TriangularHilbert_Gaussian

open OAI OAI.TriangularHilbert OAI.TriangularHilbert.Heat
open MeasureTheory Filter
open scoped Topology


theorem solution (h u p σ : ℝ) (hσ : 0 < σ) :
    HasDerivAt (fun s => weight h u p s)
      ((1 / 2 : ℝ) * (score u p σ ^ 2 - σ⁻¹) * weight h u p σ) σ := by
  unfold weight density score
  have hσ0 : σ ≠ 0 := ne_of_gt hσ
  have hpos : 0 < 2 * Real.pi * σ := by positivity
  have hsq : 0 < Real.sqrt (2 * Real.pi * σ) := Real.sqrt_pos.mpr hpos
  have hs2 : Real.sqrt (2 * Real.pi * σ) ^ 2 = 2 * Real.pi * σ := Real.sq_sqrt hpos.le
  have hA : HasDerivAt (fun s => Real.sqrt (2 * Real.pi * s))
      ((2 * Real.pi) / (2 * Real.sqrt (2 * Real.pi * σ))) σ := by
    refine (((hasDerivAt_id σ).const_mul (2 * Real.pi)).sqrt (by simp only [id]; exact hpos.ne')).congr_deriv ?_
    simp only [id, mul_one]
  have hB := hA.inv hsq.ne'
  have hC : HasDerivAt (fun s => -(u - p) ^ 2 / (2 * s)) ((u - p) ^ 2 / (2 * σ ^ 2)) σ := by
    have h0 : HasDerivAt (fun s => -(u - p) ^ 2 * (2 * s)⁻¹) (-(u - p) ^ 2 * (-(2 * 1) / (2 * σ) ^ 2)) σ :=
      (((hasDerivAt_id σ).const_mul 2).inv (by simp only [id]; positivity)).const_mul (-(u - p) ^ 2)
    have hf : (fun s => -(u - p) ^ 2 / (2 * s)) = (fun s => -(u - p) ^ 2 * (2 * s)⁻¹) := by
      funext s; rw [div_eq_mul_inv]
    rw [hf]
    refine h0.congr_deriv ?_
    field_simp
  have hD := (hB.mul hC.exp).const_mul h
  have hf : (fun s => h * ((Real.sqrt (2 * Real.pi * s))⁻¹ * Real.exp (-(u - p) ^ 2 / (2 * s)))) =
      (fun s => h * ((fun s => Real.sqrt (2 * Real.pi * s))⁻¹ s * Real.exp (-(u - p) ^ 2 / (2 * s)))) := rfl
  rw [hf]
  refine hD.congr_deriv ?_
  simp only [Pi.inv_apply]
  field_simp
  rw [hs2]
  ring

