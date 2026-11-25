-- Prove2me | solution 1 for GlobalTheory.HCXi.GramPos.gram_measurable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:15:53.694861+00:00
-- url     : https://prove2.me/submissions/5657c6ae-e024-4696-bbeb-e18ad39c9d55

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_GramPositiveVolumeContinuous
import Theorems.Thm_GlobalTheory_HCXi_GramPos_gram_continuous

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
theorem _root_.solution (k r : ℕ) (a : Fin (r + 1)) :
    Measurable fun x : Mt k r => gram k r (Matrix.of x) a := by
  have h : Continuous fun x : Mt k r => gram k r (Matrix.of x) a := gram_continuous k r a
  exact h.measurable
end GlobalTheory.HCXi.GramPos
