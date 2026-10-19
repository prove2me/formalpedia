-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.weightedSeriesJet_columnCombination_eq_matrix_mulVec
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T12:56:10.117351+00:00
-- url     : https://prove2.me/submissions/a8816077-a9ce-4205-a45c-bd747e76753a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_ColumnCombination
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_weightedSeriesJet_columnCombination_eq_sum
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_weightedSeriesJet_columnMonomial_eq_matrix_entry
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_matrix_mulVecLin_apply

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution
    {m : ℕ} (K : ℕ) (w0 v0 theta : ℝ) (w : Fin m → ℝ) (H : ℝ)
    (r : Fin m → ℂ) (G : Fin m → Polynomial ℂ)
    (x : InterpolationMatrix.Column w0 w H → ℂ) :
    ∀ rho : InterpolationMatrix.Row K v0 theta w H,
      weightedSeriesJet v0 (fun i => w i / theta) H
        (fun i => (rho.1.val : ℂ) * r i) (fun i => (G i : PowerSeries ℂ))
        (columnCombination w0 w H x) rho.2 =
      ((InterpolationMatrix.matrix K w0 v0 theta w H r G).mulVecLin x) rho := by
  intro rho
  calc
    weightedSeriesJet v0 (fun i => w i / theta) H
        (fun i => (rho.1.val : ℂ) * r i) (fun i => (G i : PowerSeries ℂ))
        (columnCombination w0 w H x) rho.2 =
      ∑ c : InterpolationMatrix.Column w0 w H,
        x c * weightedSeriesJet v0 (fun i => w i / theta) H
          (fun i => (rho.1.val : ℂ) * r i) (fun i => (G i : PowerSeries ℂ))
          (columnMonomial w0 w H c) rho.2 := by
            exact OAI.PiExponent.AdmissibleFormalInterpolation.weightedSeriesJet_columnCombination_eq_sum
              K w0 v0 theta w H r G x rho
    _ = ∑ c : InterpolationMatrix.Column w0 w H,
        InterpolationMatrix.matrix K w0 v0 theta w H r G rho c * x c := by
          apply Finset.sum_congr rfl
          intro c hc
          rw [OAI.PiExponent.AdmissibleFormalInterpolation.weightedSeriesJet_columnMonomial_eq_matrix_entry
            K w0 v0 theta w H r G x rho c]
          ring
    _ = ((InterpolationMatrix.matrix K w0 v0 theta w H r G).mulVecLin x) rho := by
          exact (OAI.PiExponent.AdmissibleFormalInterpolation.matrix_mulVecLin_apply
            K w0 v0 theta w H r G x rho).symm