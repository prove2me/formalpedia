-- Prove2me | solution 1 for GlobalTheory.HCXi.ConeZero.normSq_param_last
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:13:51.331404+00:00
-- url     : https://prove2.me/submissions/452d63af-c601-46e9-b6b0-a72d85f11416

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LintegralGaussianHyperboloidFiberStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsConeMeasure
import Theorems.Thm_GlobalTheory_HCXi_ConeZero_sqLen_nonneg

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
theorem _root_.solution (n : ℕ) (p : (Fin n → ℂ) × ℝ) :
    Complex.normSq (param n p (Fin.last n)) = sqLen p.1 := by
  simp only [param, Fin.snoc_last, map_mul, add_zero, Complex.normSq_ofReal]
  rw [Real.mul_self_sqrt (sqLen_nonneg _), Complex.normSq_eq_norm_sq, mul_comm Complex.I,
    Complex.norm_exp_ofReal_mul_I]
  ring
end GlobalTheory.HCXi.ConeZero
