-- Prove2me | solution 1 for GlobalTheory.HCXi.FrameOrth.star_isoVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:02:15.218083+00:00
-- url     : https://prove2.me/submissions/8b341403-c450-4608-9808-99afa4af0334

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FrameIsotropicOrthonormal

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
open GlobalTheory GlobalTheory.HCXi GlobalTheory.HCXi.FrameOrth
namespace GlobalTheory.HCXi.FrameOrth
theorem _root_.solution (k r : ℕ) : star (isoVec k r) = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) •
    (star (bvec (wI k r 0)) + star (bvec (wI k r (Fin.last k)))) := by
  rw [isoVec, star_smul, star_add, Complex.star_def, Complex.conj_ofReal]
end GlobalTheory.HCXi.FrameOrth
