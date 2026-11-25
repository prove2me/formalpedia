-- Prove2me | solution 1 for GlobalTheory.HCXi.FrameOrth.fvec_castSucc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:41:28.874468+00:00
-- url     : https://prove2.me/submissions/a72cdd86-ad1c-4ac8-b8f3-82d3bf0a2edc

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
theorem _root_.solution (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    fvec k r z a.castSucc = bvec (eI k r a) := by
  simp [fvec]
end GlobalTheory.HCXi.FrameOrth
