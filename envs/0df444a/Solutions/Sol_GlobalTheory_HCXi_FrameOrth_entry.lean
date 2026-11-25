-- Prove2me | solution 1 for GlobalTheory.HCXi.FrameOrth.entry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:02:13.102809+00:00
-- url     : https://prove2.me/submissions/b9240c05-1a11-497c-b1c3-48bc953d62d1

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
theorem _root_.solution (k r : ℕ) (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (a b : Fin (r + 1)) :
    ((frame k r)ᴴ * M * frame k r) a b =
      star (fvec k r (isoVec k r) a) ⬝ᵥ (M *ᵥ fvec k r (isoVec k r) b) := by
  rw [Matrix.mul_assoc]
  simp only [Matrix.mul_apply, frame, Matrix.conjTranspose_apply, Matrix.of_apply, dotProduct,
    Matrix.mulVec, Pi.star_apply]
end GlobalTheory.HCXi.FrameOrth
