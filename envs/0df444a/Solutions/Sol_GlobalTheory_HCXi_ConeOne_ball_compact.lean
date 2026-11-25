-- Prove2me | solution 1 for GlobalTheory.HCXi.ConeOne.ball_compact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:44:59.96653+00:00
-- url     : https://prove2.me/submissions/1d243667-c882-4627-81e0-a5ee0d60bcd0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsConeMeasurePosRank
import Theorems.Thm_GlobalTheory_HCXi_ConeOne_sqLen_cont

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.HCXi GlobalTheory.HCXi.ConeOne
open Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x8
namespace GlobalTheory.HCXi.ConeOne
theorem _root_.solution {n : ℕ} : IsCompact {v : Fin n → ℂ | sqLen v ≤ 1} := by
  refine (isCompact_closedBall (0 : Fin n → ℂ) 1).of_isClosed_subset (isClosed_le sqLen_cont continuous_const) ?_
  intro v hv
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  have h1 : Complex.normSq (v i) ≤ sqLen v :=
    Finset.single_le_sum (f := fun i => Complex.normSq (v i)) (fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
  have h2 : sqLen v ≤ 1 := hv
  rw [Complex.normSq_eq_norm_sq] at h1
  nlinarith [norm_nonneg (v i)]
end GlobalTheory.HCXi.ConeOne
