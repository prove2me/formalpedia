-- Prove2me | solution 1 for GlobalTheory.HCXi.ConePolar.measurable_sqLen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:01:07.925514+00:00
-- url     : https://prove2.me/submissions/5bcbd865-ac65-4ca4-a291-aee396379315

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LintegralHyperboloidFibration

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
open GlobalTheory GlobalTheory.HCXi GlobalTheory.HCXi.ConePolar
namespace GlobalTheory.HCXi.ConePolar
theorem _root_.solution (k : ℕ) : Measurable (sqLen : (Fin k → ℂ) → ℝ) := by
  unfold sqLen
  exact Finset.measurable_sum _ fun i _ => Complex.continuous_normSq.measurable.comp (measurable_pi_apply i)
end GlobalTheory.HCXi.ConePolar
