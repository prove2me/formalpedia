-- Prove2me | solution 2 for OAI.PiExponent.AdmissibleFormalInterpolation.truncated_surjective_of_packet_surjective
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T06:28:05.056505+00:00
-- url     : https://prove2.me/submissions/4f1a6c3e-e4e6-4fce-8d21-424a3caa7271
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_truncatedLogMatrix_mulVec_coeff_eq_shear_packet
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_finitePacketShearMatrix_bijective
import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_FormalJetShear
import Mathlib.RingTheory.PowerSeries.Log

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.AdmissibleFormalInterpolation

/-- Any truncated-matrix target lifts through the invertible finite
packet shear, then through formal packet surjectivity. -/
theorem solution
    {m : ℕ} (K : ℕ) (w0 v0 theta : ℝ)
    (w : Fin m → ℝ) (H : ℝ) (r : Fin m → ℂ) (T : Fin m → ℕ)
    (hw0 : 0 < w0) (hv0 : 0 < v0) (htheta : 0 < theta)
    (hw : ∀ i, 0 < w i)
    (hT : ∀ i, w i / theta ≤ (T i : ℝ) * v0) :
    Function.Surjective (packetMap K w0 v0 theta w H r) →
      Function.Surjective
        (InterpolationMatrix.truncatedLogMatrix K w0 v0 theta w H r T).mulVecLin := by
  intro hpacket y
  let S := strictWeightedSimplex (InterpolationMatrix.rowWeights v0 theta w) H
  let delta : Fin m → PowerSeries ℂ := fun i =>
    (InterpolationMatrix.truncatedLog (T i) : PowerSeries ℂ) - PowerSeries.log ℂ
  obtain ⟨z, hz⟩ :=
    (OAI.PiExponent.AdmissibleFormalInterpolation.finitePacketShearMatrix_bijective
      K S delta).2 y
  obtain ⟨P, hP⟩ := hpacket z
  refine ⟨(fun c => MvPolynomial.coeff
    (InterpolationMatrix.exponentVector c.val) P.val), ?_⟩
  have hmatrix :=
    OAI.PiExponent.AdmissibleFormalInterpolation.truncatedLogMatrix_mulVec_coeff_eq_shear_packet
      K w0 v0 theta w H r T hw0 hv0 htheta hw hT P
  change
    (InterpolationMatrix.truncatedLogMatrix K w0 v0 theta w H r T).mulVecLin
      (fun c => MvPolynomial.coeff (InterpolationMatrix.exponentVector c.val) P.val) =
    (finitePacketShearMatrix K S delta).mulVecLin (packetMap K w0 v0 theta w H r P)
    at hmatrix
  rw [hmatrix, hP, hz]
