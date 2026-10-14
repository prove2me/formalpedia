-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.truncated_matrix_of_packets
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-12T20:27:49.350551+00:00
-- url     : https://prove2.me/submissions/ac9fa28b-41e9-4c7b-8c1b-02562f6d37b4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_packet_matrix_representation

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution {m : ℕ} (K : ℕ) (w0 v0 theta : ℝ)
    (w : Fin m → ℝ) (H : ℝ) (r : Fin m → ℂ) (T : Fin m → ℕ)
    (hw0 : 0 < w0) (hv0 : 0 < v0) (htheta : 0 < theta)
    (hw : ∀ i, 0 < w i) (hT : ∀ i, w i / theta ≤ (T i : ℝ) * v0)
    (hpacket : Function.Surjective (packetMap K w0 v0 theta w H r)) :
    Function.Surjective
      (InterpolationMatrix.truncatedLogMatrix K w0 v0 theta w H r T).mulVecLin := by
  intro y
  obtain ⟨P, hP⟩ := hpacket y
  obtain ⟨x, hx⟩ :=
    OAI.PiExponent.AdmissibleFormalInterpolation.packet_matrix_representation
      K w0 v0 theta w H r T hw0 hv0 htheta hw hT P
  exact ⟨x, hx.symm.trans hP⟩
