-- Prove2me | solution 1 for GlobalTheory.HCXi.GramPos.pair_iso_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:35:58.403542+00:00
-- url     : https://prove2.me/submissions/cf5daed3-87f6-47b5-bb3b-15d1e265d38a

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
theorem _root_.solution (k r : ℕ) (M : Mat k r) (v) :
    star v ⬝ᵥ M *ᵥ isoVec k r =
      (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (star v ⬝ᵥ M *ᵥ bvec (wI k r 0) + star v ⬝ᵥ M *ᵥ bvec (wI k r (Fin.last k))) := by
  rw [isoVec, mulVec_smul, mulVec_add, dotProduct_smul, dotProduct_add]
  simp
end GlobalTheory.HCXi.GramPos
