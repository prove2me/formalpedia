-- Prove2me | solution 1 for ModernConvex.Ellipsoids.inner_sum_sdp
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-21T12:57:36.059466+00:00
-- url     : https://prove2.me/submissions/f286c9ba-c6e1-4601-9327-d3a04ca5283f

import Mathlib
import Definitions.Def_ModernConvex_Ellipsoids_Ellipsoid
import Definitions.Def_ModernConvex_Ellipsoids_Programs

open Matrix
open ModernConvex.Ellipsoids

theorem solution : ¬ (∀ {m n : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i, (A i).PosDef),
    (∀ (X : Fin m → Matrix (Fin n) (Fin n) ℝ) (t : ℝ), IFeasible A X t →
      ellipsoid (∑ i, A i * X i) 0 ⊆ minkowskiSum (fun i => ellipsoid (A i) 0) ∧
        ENNReal.ofReal (t ^ n) ≤ Vol (ellipsoid (∑ i, A i * X i) 0)) ∧
    (∀ (Xs : Fin m → Matrix (Fin n) (Fin n) ℝ) (ts : ℝ), IOptimal A Xs ts →
      ∀ (X : Fin m → Matrix (Fin n) (Fin n) ℝ) (t : ℝ), IFeasible A X t →
        Vol (ellipsoid (∑ i, A i * X i) 0) ≤ Vol (ellipsoid (∑ i, A i * Xs i) 0))) := by
  intro H
  have hA : ∀ i : Fin 1, (1 : Matrix (Fin 2) (Fin 2) ℝ).PosDef := fun _ => PosDef.one
  have hfeas : IFeasible (fun _ : Fin 1 => (1 : Matrix (Fin 2) (Fin 2) ℝ)) (fun _ => 0) (-1) := by
    refine ⟨?_, ?_, ?_⟩
    · simp only [transpose_zero, Matrix.zero_mul, Matrix.mul_zero, add_zero,
        Finset.sum_const_zero, smul_zero]
      exact le_trans (by norm_num) (Real.rpow_nonneg (by simp) _)
    · simp only [transpose_zero, Matrix.zero_mul, Matrix.mul_zero, add_zero,
        Finset.sum_const_zero]
      exact PosSemidef.zero
    · intro i
      simp only [transpose_zero, neg_zero, fromBlocks_one]
      exact PosSemidef.one
  have h := ((H _ hA).1 _ _ hfeas).2
  have hE : ellipsoid (∑ i : Fin 1, (1 : Matrix (Fin 2) (Fin 2) ℝ) * (0 : Matrix (Fin 2) (Fin 2) ℝ))
      (0 : Fin 2 → ℝ) = {0} := by
    ext x
    simp only [ellipsoid, Matrix.mul_zero, Finset.sum_const_zero, zero_mulVec, zero_add,
      Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨u, -, rfl⟩; rfl
    · rintro rfl; exact ⟨0, by simp, rfl⟩
  rw [hE] at h
  unfold Vol at h
  rw [MeasureTheory.measure_singleton, ENNReal.zero_div] at h
  norm_num at h
