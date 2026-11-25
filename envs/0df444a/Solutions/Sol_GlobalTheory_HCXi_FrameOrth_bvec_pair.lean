-- Prove2me | solution 1 for GlobalTheory.HCXi.FrameOrth.bvec_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:01:12.622367+00:00
-- url     : https://prove2.me/submissions/147269cc-bb0c-4ad9-8c29-5f54d9a5fe01

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
theorem _root_.solution {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    star (bvec i) ⬝ᵥ (M *ᵥ bvec j) = M i j := by
  simp [bvec, Pi.star_single]
end GlobalTheory.HCXi.FrameOrth
