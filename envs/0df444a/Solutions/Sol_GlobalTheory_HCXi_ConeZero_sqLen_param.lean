-- Prove2me | solution 1 for GlobalTheory.HCXi.ConeZero.sqLen_param
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:02:08.747215+00:00
-- url     : https://prove2.me/submissions/7b6d1146-c286-4652-a187-e9337583beff

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LintegralGaussianHyperboloidFiberStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsConeMeasure
import Theorems.Thm_GlobalTheory_HCXi_ConeZero_normSq_param_last

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
theorem _root_.solution (n : ℕ) (p : (Fin n → ℂ) × ℝ) : sqLen (param n p) = 2 * sqLen p.1 := by
  rw [sqLen, Fin.sum_univ_castSucc, normSq_param_last]
  simp only [param, Fin.snoc_castSucc]
  rw [sqLen]; ring
end GlobalTheory.HCXi.ConeZero
