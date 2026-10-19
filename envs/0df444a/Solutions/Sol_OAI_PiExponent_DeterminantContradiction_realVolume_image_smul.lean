-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.realVolume_image_smul
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T13:17:13.149534+00:00
-- url     : https://prove2.me/submissions/656cd476-4855-4f50-8792-a88a0ca8a776

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open scoped BigOperators Topology

theorem solution
    (n : ℕ) (r : ℝ) (hr : 0 < r) (s : Set (Fin n → ℝ))
    (hs : MeasurableSet s) :
    ENNReal.toReal (MeasureTheory.volume ((fun x : Fin n → ℝ => r • x) '' s)) =
      r ^ n * ENNReal.toReal (MeasureTheory.volume s) := by
  classical
  let f : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) := r • LinearMap.id
  have hdet : LinearMap.det f = r ^ n := by
    simp [f]
  have hdet0 : LinearMap.det f ≠ 0 := by
    rw [hdet]
    exact pow_ne_zero _ (ne_of_gt hr)
  have hinj : Function.Injective f := by
    intro x y hxy
    ext i
    have hcoord : r * x i = r * y i := by
      simpa [f, Pi.smul_apply, smul_eq_mul] using congrFun hxy i
    exact mul_left_cancel₀ (ne_of_gt hr) hcoord
  have hmeas : MeasurableEmbedding f :=
    (f.continuous_of_finiteDimensional).measurableEmbedding hinj
  have himage : (MeasureTheory.volume.map f) (f '' s) = MeasureTheory.volume s := by
    rw [hmeas.map_apply, Set.preimage_image_eq s hinj]
  rw [show (fun x : Fin n → ℝ => r • x) = f by
        funext x
        simp [f]]
  have hscale := Real.map_linearMap_volume_pi_eq_smul_volume_pi hdet0
  rw [hscale] at himage
  have hreal := congrArg ENNReal.toReal himage
  rw [MeasureTheory.Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (abs_nonneg _), hdet,
    abs_of_pos (inv_pos.mpr (pow_pos hr n))] at hreal
  calc
    ENNReal.toReal (MeasureTheory.volume (f '' s)) =
        (r ^ n * (r ^ n)⁻¹) * ENNReal.toReal (MeasureTheory.volume (f '' s)) := by
      rw [mul_inv_cancel₀ (pow_ne_zero n (ne_of_gt hr)), one_mul]
    _ = r ^ n * ((r ^ n)⁻¹ * ENNReal.toReal (MeasureTheory.volume (f '' s))) :=
      mul_assoc _ _ _
    _ = r ^ n * ENNReal.toReal (MeasureTheory.volume s) := by
      rw [hreal]
