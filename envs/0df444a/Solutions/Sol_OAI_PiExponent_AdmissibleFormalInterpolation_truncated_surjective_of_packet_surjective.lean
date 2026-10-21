-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.truncated_surjective_of_packet_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T11:59:11.558302+00:00
-- url     : https://prove2.me/submissions/1bbbd732-76fc-4c73-939c-fddd23df97fe

import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_FormalJetShear
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_finitePacketShearMatrix_bijective
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_truncatedLogMatrix_mulVec_coeff_eq_shear_packet

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution
    {m : ℕ} (K : ℕ) (w0 v0 theta : ℝ)
    (w : Fin m → ℝ) (H : ℝ) (r : Fin m → ℂ) (T : Fin m → ℕ)
    (hw0 : 0 < w0) (hv0 : 0 < v0) (htheta : 0 < theta)
    (hw : ∀ i, 0 < w i)
    (hT : ∀ i, w i / theta ≤ (T i : ℝ) * v0) :
    Function.Surjective (packetMap K w0 v0 theta w H r) →
      Function.Surjective
        (InterpolationMatrix.truncatedLogMatrix K w0 v0 theta w H r T).mulVecLin := by
  classical
  intro hpacket
  let S : Finset (Fin (m + 1) → ℕ) :=
    strictWeightedSimplex (InterpolationMatrix.rowWeights v0 theta w) H
  let delta : Fin m → PowerSeries ℂ :=
    fun i => (InterpolationMatrix.truncatedLog (T i) : PowerSeries ℂ) -
      PowerSeries.log ℂ
  have hshear : Function.Surjective (finitePacketShearMatrix K S delta).mulVecLin :=
    (finitePacketShearMatrix_bijective K S delta).2
  intro y
  obtain ⟨z, hz⟩ := hshear y
  obtain ⟨P, hP⟩ := hpacket z
  refine ⟨fun c => MvPolynomial.coeff (InterpolationMatrix.exponentVector c.val) P.val, ?_⟩
  rw [truncatedLogMatrix_mulVec_coeff_eq_shear_packet
    K w0 v0 theta w H r T hw0 hv0 htheta hw hT P]
  change (finitePacketShearMatrix K S delta).mulVecLin
    (packetMap K w0 v0 theta w H r P) = y
  rw [hP]
  exact hz