-- Prove2me | solution 1 for GlobalTheory.HCXi.GramPos.frame_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:02:17.881937+00:00
-- url     : https://prove2.me/submissions/b462a801-2d3a-483e-a9af-689e15ecfa44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_GramPositiveVolumeContinuous

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
open GlobalTheory GlobalTheory.HCXi GlobalTheory.HCXi.GramPos
namespace GlobalTheory.HCXi.GramPos
theorem _root_.solution (k r : ℕ) (M : Mat k r) (a b : Fin (r + 1)) :
    ((frame k r)ᴴ * M * frame k r) a b =
      star (fvec k r (isoVec k r) a) ⬝ᵥ M *ᵥ fvec k r (isoVec k r) b := by
  rw [Matrix.mul_assoc]
  simp [Matrix.mul_apply, frame, dotProduct, mulVec]
end GlobalTheory.HCXi.GramPos
