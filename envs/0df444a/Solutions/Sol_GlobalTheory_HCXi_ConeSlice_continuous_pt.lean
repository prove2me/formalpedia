-- Prove2me | solution 1 for GlobalTheory.HCXi.ConeSlice.continuous_pt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:06:46.601351+00:00
-- url     : https://prove2.me/submissions/8889c917-a036-4145-aac6-267620dfe06f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LintegralHyperboloidFibrationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LintegralGaussianHyperboloidFiber
import Theorems.Thm_GlobalTheory_HCXi_ConeSlice_continuous_sqLen

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
open GlobalTheory GlobalTheory.HCXi GlobalTheory.HCXi.ConeSlice
namespace GlobalTheory.HCXi.ConeSlice
theorem _root_.solution {k : ℕ} :
    Continuous (fun q : ℝ × ((Fin k → ℂ) × ℝ) => pt q.1 q.2) := by
  refine Continuous.finSnoc (by fun_prop) ?_
  have := @continuous_sqLen k
  fun_prop
end GlobalTheory.HCXi.ConeSlice
