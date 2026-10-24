-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.diagonal_preimage_volume
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T12:55:55.824902+00:00
-- url     : https://prove2.me/submissions/031e6d59-951f-4409-86f6-0537b75fef2c

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped BigOperators

theorem solution
    (n : Nat) (c : Fin n → Real) (hc : ∀ i, 0 < c i)
    (s : Set (Fin n → Real)) (hs : MeasurableSet s) :
    MeasureTheory.volume {x : Fin n → Real | (fun i => c i * x i) ∈ s} =
      (∏ i, ENNReal.ofReal (1 / c i)) * MeasureTheory.volume s := by
  classical
  let M : Matrix (Fin n) (Fin n) Real := Matrix.diagonal c
  have hprod : 0 < ∏ i, c i := Finset.prod_pos fun i hi => hc i
  have hdet : Matrix.det M ≠ 0 := by
    rw [show M = Matrix.diagonal c from rfl, Matrix.det_diagonal]
    exact ne_of_gt hprod
  have hmap := Real.map_matrix_volume_pi_eq_smul_volume_pi hdet
  have hm : Measurable (Matrix.toLin' M) :=
    (Matrix.toLin' M).continuous_of_finiteDimensional.measurable
  have hMx (x : Fin n → Real) : (Matrix.toLin' M) x = fun i => c i * x i := by
    funext i
    simp [M, Matrix.diagonal_toLin', LinearMap.pi_apply]
  have hpre : {x : Fin n → Real | (fun i => c i * x i) ∈ s} =
      (Matrix.toLin' M) ⁻¹' s := by
    ext x
    change ((fun i => c i * x i) ∈ s) ↔ (Matrix.toLin' M x ∈ s)
    rw [hMx x]
  have hfac : ENNReal.ofReal ((abs (Matrix.det M))⁻¹) =
      ∏ i, ENNReal.ofReal (1 / c i) := by
    have hdet_eq : Matrix.det M = ∏ i, c i := by simp [M, Matrix.det_diagonal]
    rw [hdet_eq, abs_of_pos hprod, ← Finset.prod_inv_distrib]
    rw [ENNReal.ofReal_prod_of_nonneg (fun i hi => inv_nonneg.mpr (le_of_lt (hc i)))]
    apply Finset.prod_congr rfl
    intro i hi
    rw [one_div]
  calc
    MeasureTheory.volume {x : Fin n → Real | (fun i => c i * x i) ∈ s} =
        MeasureTheory.Measure.map (Matrix.toLin' M) MeasureTheory.volume s := by
      rw [hpre]
      symm
      exact MeasureTheory.Measure.map_apply hm hs
    _ = (ENNReal.ofReal (abs (Matrix.det M)⁻¹) • MeasureTheory.volume) s := by
      rw [hmap]
    _ = (∏ i, ENNReal.ofReal (1 / c i)) * MeasureTheory.volume s := by
      simp [hfac, abs_inv]