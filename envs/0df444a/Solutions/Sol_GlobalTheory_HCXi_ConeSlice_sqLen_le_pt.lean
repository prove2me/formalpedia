-- Prove2me | solution 1 for GlobalTheory.HCXi.ConeSlice.sqLen_le_pt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:34:25.283873+00:00
-- url     : https://prove2.me/submissions/fccffc7f-6263-442a-a12b-25e9af9d9896

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
theorem _root_.solution {k : ℕ} (τ : ℝ) (p : (Fin k → ℂ) × ℝ) : sqLen p.1 ≤ sqLen (pt τ p) := by
  unfold sqLen
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc]
  linarith [Complex.normSq_nonneg (pt τ p (Fin.last k))]
end GlobalTheory.HCXi.ConeSlice
