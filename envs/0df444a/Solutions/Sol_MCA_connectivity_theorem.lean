-- Prove2me | solution 1 for MCA.connectivity_theorem
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T09:45:58.217954+00:00
-- url     : https://prove2.me/submissions/d9dd81e1-28ac-44fd-972f-c8ea98a41806

import Mathlib
namespace MCA

theorem connectivity_theorem
    {n m : ℕ}
    (Fv : Matrix (Fin m) (Fin n) ℝ)
    (vS : Matrix (Fin n) (Fin m) ℝ)
    (ve : Matrix (Fin n) (Fin n) ℝ)
    (Se : Matrix (Fin m) (Fin n) ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ)
    (veInv : Matrix (Fin n) (Fin n) ℝ)
    (fsInv : Matrix (Fin m) (Fin m) ℝ)
    (hfs_left : fsInv * (Fv * vS) = 1)
    (hfs_right : (Fv * vS) * fsInv = 1)
    (hve_left : veInv * ve = 1)
    (hve_right : ve * veInv = 1)
    (h_chain : (Fv * vS) * Se + Fv * ve = 0)
    (h_total : W = vS * Se + ve) :
    (Se * veInv) * vS = -1 ∧
      (W * veInv) * vS = 0 := by
  have hc : Fv * vS * Se = -(Fv * ve) := eq_neg_of_add_eq_zero_left h_chain
  have hSe : Se = -(fsInv * Fv * ve) := by
    calc Se = fsInv * (Fv * vS) * Se := by rw [hfs_left, Matrix.one_mul]
      _ = fsInv * (Fv * vS * Se) := by rw [Matrix.mul_assoc]
      _ = fsInv * (-(Fv * ve)) := by rw [hc]
      _ = -(fsInv * Fv * ve) := by rw [Matrix.mul_neg, Matrix.mul_assoc]
  have h1 : Se * veInv * vS = -1 := by
    rw [hSe, Matrix.neg_mul, Matrix.neg_mul, Matrix.mul_assoc (fsInv * Fv) ve veInv, hve_right,
      Matrix.mul_one, Matrix.mul_assoc, hfs_left]
  refine ⟨h1, ?_⟩
  calc W * veInv * vS = vS * (Se * veInv * vS) + ve * veInv * vS := by
        rw [h_total, Matrix.add_mul, Matrix.add_mul, Matrix.mul_assoc vS Se veInv,
          Matrix.mul_assoc vS (Se * veInv) vS]
    _ = 0 := by rw [h1, hve_right, Matrix.one_mul, Matrix.mul_neg, Matrix.mul_one, neg_add_cancel]

end MCA

theorem solution
    {n m : ℕ}
    (Fv : Matrix (Fin m) (Fin n) ℝ)
    (vS : Matrix (Fin n) (Fin m) ℝ)
    (ve : Matrix (Fin n) (Fin n) ℝ)
    (Se : Matrix (Fin m) (Fin n) ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ)
    (veInv : Matrix (Fin n) (Fin n) ℝ)
    (fsInv : Matrix (Fin m) (Fin m) ℝ)
    (hfs_left : fsInv * (Fv * vS) = 1)
    (hfs_right : (Fv * vS) * fsInv = 1)
    (hve_left : veInv * ve = 1)
    (hve_right : ve * veInv = 1)
    (h_chain : (Fv * vS) * Se + Fv * ve = 0)
    (h_total : W = vS * Se + ve) :
    (Se * veInv) * vS = -1 ∧
      (W * veInv) * vS = 0 :=
  MCA.connectivity_theorem Fv vS ve Se W veInv fsInv hfs_left hfs_right hve_left hve_right h_chain h_total
