-- Prove2me | solution 2 for OAI.PiExponent.AdmissibleFormalInterpolation.truncated_matrix_of_packets
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-15T20:41:17.451288+00:00
-- url     : https://prove2.me/submissions/aaec292c-2cee-4e8a-aa03-2cdc291c2b0e

import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_packet_truncated_surjective_iff

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution {m : ℕ} (K : ℕ) (w0 v0 theta : ℝ)
    (w : Fin m → ℝ) (H : ℝ) (r : Fin m → ℂ) (T : Fin m → ℕ)
    (hw0 : 0 < w0) (hv0 : 0 < v0) (htheta : 0 < theta)
    (hw : ∀ i, 0 < w i) (hT : ∀ i, w i / theta ≤ (T i : ℝ) * v0)
    (hpacket : Function.Surjective (packetMap K w0 v0 theta w H r)) :
    Function.Surjective
      (InterpolationMatrix.truncatedLogMatrix K w0 v0 theta w H r T).mulVecLin := by
  exact (OAI.PiExponent.AdmissibleFormalInterpolation.packet_truncated_surjective_iff
    K w0 v0 theta w H r T hw0 hv0 htheta hw hT).mp hpacket