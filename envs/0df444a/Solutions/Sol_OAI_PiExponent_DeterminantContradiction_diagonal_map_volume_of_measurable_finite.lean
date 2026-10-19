-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.diagonal_map_volume_of_measurable_finite
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T22:06:30.157097+00:00
-- url     : https://prove2.me/submissions/5646a0cb-f90c-4791-b789-d9ae9ab79376

import Mathlib.LinearAlgebra.Determinant
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

open scoped BigOperators Topology

theorem solution (m : ℕ) (w : Fin m → ℝ) (hw : ∀ i, 0 < w i)
    (s : Set (Fin m → ℝ)) (hs : MeasurableSet s)
    (hfin : MeasureTheory.volume s < ⊤) :
    ENNReal.toReal (MeasureTheory.volume ((fun x i => w i * x i) '' s)) =
      (∏ i : Fin m, w i) * ENNReal.toReal (MeasureTheory.volume s) := by
  let f : (Fin m → ℝ) →ₗ[ℝ] Fin m → ℝ := Matrix.toLin' (Matrix.diagonal w)
  have hf (x : Fin m → ℝ) : f x = (fun i => w i * x i) := by
    ext i
    simp [f, Matrix.diagonal_toLin']
  have hdet : LinearMap.det f = ∏ i : Fin m, w i := by
    simp [f, Matrix.det_diagonal]
  have himage : f '' s = (fun x i => w i * x i) '' s := by
    congr 1
    funext x
    exact hf x
  rw [← himage,
    MeasureTheory.Measure.addHaar_image_linearMap (μ := MeasureTheory.volume) f s,
    hdet]
  have hprod : 0 < ∏ i : Fin m, w i := Finset.prod_pos fun i hi => hw i
  rw [abs_of_pos hprod, ENNReal.toReal_mul, ENNReal.toReal_ofReal hprod.le]
