-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.EisTube.norm_lin_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:28:36.084876+00:00
-- url     : https://prove2.me/submissions/88442249-182e-40cf-bfa5-65c2896829e4

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IntegrableExpNegSumAbs
import Theorems.Thm_GlobalTheory_CompanionTheory_EisTube_lin_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
universe u
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.EisTube
namespace GlobalTheory.CompanionTheory.EisTube
theorem _root_.solution {ι : Type} [Fintype ι] (t : ι → ℝ) :
    ‖lin t‖ ≤ 2 * Real.pi * ∑ i, |t i| := by
  have h00 : 0 ≤ 2 * Real.pi * ∑ i, |t i| := by positivity
  refine ContinuousLinearMap.opNorm_le_bound _ h00 fun z => ?_
  rw [lin_apply, norm_mul]
  have h0 : ‖(2 * (Real.pi : ℂ))‖ = 2 * Real.pi := by
    simp [abs_of_pos Real.pi_pos]
  have h2pi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  rw [h0, mul_assoc (2 * Real.pi)]
  refine mul_le_mul_of_nonneg_left ?_ h2pi
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_mul, mul_comm, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (norm_le_pi_norm z i) (abs_nonneg _)
end GlobalTheory.CompanionTheory.EisTube
