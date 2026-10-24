-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.diagonal_preimage_volume_toReal
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T07:13:13.228203+00:00
-- url     : https://prove2.me/submissions/f56c5f8e-c992-4e8a-8ec5-08793fbed45a

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open Filter Topology
open scoped BigOperators

theorem solution {m : Nat} (w : Fin m → Real) (hw : ∀ i, 0 < w i)
    (s : Set (Fin m → Real)) (hs : IsCompact s) :
    (MeasureTheory.volume ((fun x : Fin m → Real => fun i => w i * x i) ⁻¹' s)).toReal =
      (MeasureTheory.volume s).toReal / ∏ i : Fin m, w i := by
  classical
  have hprod : 0 < ∏ i : Fin m, w i := Finset.prod_pos fun i _ => hw i
  have hdet : Matrix.det (Matrix.diagonal w) ≠ 0 := by
    rw [Matrix.det_diagonal]
    exact (ne_of_gt hprod)
  have hfun : (fun x : Fin m → Real => fun i => w i * x i) =
      Matrix.toLin' (Matrix.diagonal w) := by
    funext x i
    simp [Matrix.diagonal_toLin']
  have hmap := Real.map_matrix_volume_pi_eq_smul_volume_pi
    (M := Matrix.diagonal w) hdet
  have hpre : MeasureTheory.volume ((fun x : Fin m → Real => fun i => w i * x i) ⁻¹' s) =
      ENNReal.ofReal ((∏ i : Fin m, w i)⁻¹) * MeasureTheory.volume s := by
    rw [hfun]
    calc
      MeasureTheory.volume (Matrix.toLin' (Matrix.diagonal w) ⁻¹' s) =
          (MeasureTheory.Measure.map (Matrix.toLin' (Matrix.diagonal w)) MeasureTheory.volume) s :=
        (MeasureTheory.Measure.map_apply
          (Continuous.measurable (LinearMap.continuous_on_pi _)) hs.measurableSet).symm
      _ = (ENNReal.ofReal (abs (Matrix.det (Matrix.diagonal w))⁻¹) •
          MeasureTheory.volume) s := by rw [hmap]
      _ = ENNReal.ofReal ((∏ i : Fin m, w i)⁻¹) * MeasureTheory.volume s := by
        rw [MeasureTheory.Measure.smul_apply, smul_eq_mul]
        simp [Matrix.det_diagonal, abs_of_pos hprod]
  rw [hpre, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (inv_nonneg.mpr hprod.le), div_eq_mul_inv]
  ring