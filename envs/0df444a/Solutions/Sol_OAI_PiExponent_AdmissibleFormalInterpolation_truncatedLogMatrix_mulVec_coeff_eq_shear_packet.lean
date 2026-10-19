-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.truncatedLogMatrix_mulVec_coeff_eq_shear_packet
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T12:32:05.118613+00:00
-- url     : https://prove2.me/submissions/936eaba9-ecf9-48fc-a2f0-6c74b803ca3d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_FormalJetShear
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation_TruncatedJet
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_truncatedLogMatrix_mulVec_coeff_eq_truncatedFormalJet
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_finitePacketShearMatrix_mulVec_packetMap_eq_truncatedFormalJet

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution
    {m : ℕ} (K : ℕ) (w0 v0 theta : ℝ)
    (w : Fin m → ℝ) (H : ℝ) (r : Fin m → ℂ) (T : Fin m → ℕ)
    (hw0 : 0 < w0) (hv0 : 0 < v0) (htheta : 0 < theta)
    (hw : ∀ i, 0 < w i)
    (hT : ∀ i, w i / theta ≤ (T i : ℝ) * v0)
    (P : WeightedPolynomial w0 w H) :
    (InterpolationMatrix.truncatedLogMatrix K w0 v0 theta w H r T).mulVecLin
        (fun c => MvPolynomial.coeff (InterpolationMatrix.exponentVector c.val) P.val) =
      (finitePacketShearMatrix K
        (strictWeightedSimplex (InterpolationMatrix.rowWeights v0 theta w) H)
        (fun i => (InterpolationMatrix.truncatedLog (T i) : PowerSeries ℂ) -
          PowerSeries.log ℂ)).mulVecLin
        (packetMap K w0 v0 theta w H r P) := by
  have h₁ := OAI.PiExponent.AdmissibleFormalInterpolation.truncatedLogMatrix_mulVec_coeff_eq_truncatedFormalJet
    K w0 v0 theta w H r T hw0 hv0 htheta hw hT P
  have h₂ := OAI.PiExponent.AdmissibleFormalInterpolation.finitePacketShearMatrix_mulVec_packetMap_eq_truncatedFormalJet
    K w0 v0 theta w H r T hw0 hv0 htheta hw hT P
  exact h₁.trans h₂.symm
