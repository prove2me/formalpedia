-- Prove2me | solution 1 for GlobalTheory.HCXi.ConeZero.sqLen_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:54:43.107527+00:00
-- url     : https://prove2.me/submissions/adb59522-8c0d-4f03-9440-fc171568fe3a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LintegralGaussianHyperboloidFiberStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsConeMeasure

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
noncomputable section
open GlobalTheory GlobalTheory.HCXi GlobalTheory.HCXi.ConeZero
namespace GlobalTheory.HCXi.ConeZero
theorem _root_.solution {n : ℕ} (w : Fin n → ℂ) : 0 ≤ sqLen w :=
  Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
end GlobalTheory.HCXi.ConeZero
