-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.packet_truncated_surjective_iff
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-15T20:48:09.441411+00:00
-- url     : https://prove2.me/submissions/9f9ee5e7-9e56-41cd-b8e5-285afcedef58

import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_packet_surjective_of_truncated_surjective
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_truncated_surjective_of_packet_surjective

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution
    {m : ℕ} (K : ℕ) (w0 v0 theta : ℝ)
    (w : Fin m → ℝ) (H : ℝ) (r : Fin m → ℂ) (T : Fin m → ℕ)
    (hw0 : 0 < w0) (hv0 : 0 < v0) (htheta : 0 < theta)
    (hw : ∀ i, 0 < w i)
    (hT : ∀ i, w i / theta ≤ (T i : ℝ) * v0) :
    Function.Surjective (packetMap K w0 v0 theta w H r) ↔
      Function.Surjective
        (InterpolationMatrix.truncatedLogMatrix K w0 v0 theta w H r T).mulVecLin := by
  constructor
  · exact OAI.PiExponent.AdmissibleFormalInterpolation.truncated_surjective_of_packet_surjective
      K w0 v0 theta w H r T hw0 hv0 htheta hw hT
  · exact OAI.PiExponent.AdmissibleFormalInterpolation.packet_surjective_of_truncated_surjective
      K w0 v0 theta w H r T hw0 hv0 htheta hw hT