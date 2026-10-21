-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.matrix_mulVec_weightedSeriesJet
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T12:48:35.755535+00:00
-- url     : https://prove2.me/submissions/acfb1ea2-4f92-411a-beb0-ca96dacd666b

import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_columnCombination_weightedSupport
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_weightedSeriesJet_columnCombination_eq_matrix_mulVec

open OAI.PiExponent OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution
    {m : ℕ} (K : ℕ) (w0 v0 theta : ℝ) (w : Fin m → ℝ) (H : ℝ)
    (r : Fin m → ℂ) (G : Fin m → Polynomial ℂ)
    (x : InterpolationMatrix.Column w0 w H → ℂ) :
    ∃ P : WeightedPolynomial w0 w H,
      ∀ rho : InterpolationMatrix.Row K v0 theta w H,
        weightedSeriesJet v0 (fun i => w i / theta) H
          (fun i => (rho.1.val : ℂ) * r i) (fun i => (G i : PowerSeries ℂ)) P.val rho.2 =
        ((InterpolationMatrix.matrix K w0 v0 theta w H r G).mulVecLin x) rho := by
  let Q := columnCombination w0 w H x
  refine ⟨⟨Q, columnCombination_weightedSupport w0 w H x⟩, ?_⟩
  intro rho
  exact weightedSeriesJet_columnCombination_eq_matrix_mulVec K w0 v0 theta w H r G x rho