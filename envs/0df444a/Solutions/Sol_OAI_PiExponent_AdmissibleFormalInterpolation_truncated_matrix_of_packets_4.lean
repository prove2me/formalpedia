-- Prove2me | solution 4 for OAI.PiExponent.AdmissibleFormalInterpolation.truncated_matrix_of_packets
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-16T19:36:13.23553+00:00
-- url     : https://prove2.me/submissions/9ae47155-d47c-4251-bc88-74d0628870c5

import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_truncated_surjective_of_packet_surjective
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution {m : ℕ} (K : ℕ) (w0 v0 theta : ℝ)
    (w : Fin m → ℝ) (H : ℝ) (r : Fin m → ℂ) (T : Fin m → ℕ)
    (hw0 : 0 < w0) (hv0 : 0 < v0) (htheta : 0 < theta)
    (hw : ∀ i, 0 < w i) (hT : ∀ i, w i / theta ≤ (T i : ℝ) * v0)
    (hpacket : Function.Surjective (packetMap K w0 v0 theta w H r)) :
    Function.Surjective
      (InterpolationMatrix.truncatedLogMatrix K w0 v0 theta w H r T).mulVecLin := by
  exact truncated_surjective_of_packet_surjective
    K w0 v0 theta w H r T hw0 hv0 htheta hw hT hpacket
