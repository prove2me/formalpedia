-- Prove2me | solution 1 for GlobalTheory.T.gram_positive_volume_continuous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:59:08.944438+00:00
-- url     : https://prove2.me/submissions/fc361b6b-6f7a-475f-ae54-96cf2d96f1dc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_GramPositiveVolumeContinuous
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_GramPositiveVolumeContinuousStatement
import Theorems.Thm_GlobalTheory_HCXi_GramPos_gram_vHalf_pos_measurable_continuousOn


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
theorem _root_.solution : ∀ k r : ℕ, 1 ≤ k → (∀ g ∈ GV k r, ∀ a : Fin (r + 1), 0 < gram k r g a) ∧ (∀ g ∈ GV k r, 0 < vHalf k r g) ∧ (Measurable fun x : Mt k r => vHalf k r (Matrix.of x)) ∧ ContinuousOn (vHalf k r) (GV k r) := by
  first | exact @GlobalTheory.HCXi.GramPos.gram_vHalf_pos_measurable_continuousOn | exact GlobalTheory.HCXi.GramPos.gram_vHalf_pos_measurable_continuousOn | (intros; apply GlobalTheory.HCXi.GramPos.gram_vHalf_pos_measurable_continuousOn <;> assumption)
end _root_.GlobalTheory.T
