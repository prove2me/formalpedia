-- Prove2me | solution 1 for GlobalTheory.T.frame_isotropic_orthonormal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:29:10.762549+00:00
-- url     : https://prove2.me/submissions/53da8d07-bb9b-4a8a-9fbb-9b2f1d60d04c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FrameIsotropicOrthonormal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FrameIsotropicOrthonormalStatement
import Theorems.Thm_GlobalTheory_HCXi_FrameOrth_frame_orthonormal_isotropic


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ k r : ℕ, 1 ≤ k → (frame k r)ᴴ * frame k r = 1 ∧ (frame k r)ᴴ * Hpk k r * frame k r = 0 := by
  first | exact @GlobalTheory.HCXi.FrameOrth.frame_orthonormal_isotropic | exact GlobalTheory.HCXi.FrameOrth.frame_orthonormal_isotropic | (intros; apply GlobalTheory.HCXi.FrameOrth.frame_orthonormal_isotropic <;> assumption)
end _root_.GlobalTheory.T
