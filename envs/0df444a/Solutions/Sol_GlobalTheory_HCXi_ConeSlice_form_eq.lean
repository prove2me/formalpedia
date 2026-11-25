-- Prove2me | solution 1 for GlobalTheory.HCXi.ConeSlice.form_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:34:06.589846+00:00
-- url     : https://prove2.me/submissions/59f48603-1a5f-4829-983b-e023695e2ed5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LintegralHyperboloidFibrationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LintegralGaussianHyperboloidFiber

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
theorem _root_.solution {k : ℕ} (v : Fin (k + 1) → ℂ) :
    star v ⬝ᵥ (sgnMat k *ᵥ v) =
      ((sqLen (Fin.init v : Fin k → ℂ) - Complex.normSq (v (Fin.last k)) : ℝ) : ℂ) := by
  simp only [dotProduct, sgnMat, Matrix.mulVec_diagonal, Fin.sum_univ_castSucc, sqLen, Fin.init,
    Pi.star_apply, Fin.castSucc_ne_last, if_false, if_true, one_mul]
  push_cast
  simp only [Complex.normSq_eq_conj_mul_self, Complex.star_def]
  ring
end GlobalTheory.HCXi.ConeSlice
