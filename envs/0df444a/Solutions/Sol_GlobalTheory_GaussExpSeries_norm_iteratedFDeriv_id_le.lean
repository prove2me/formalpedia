-- Prove2me | solution 1 for GlobalTheory.GaussExpSeries.norm_iteratedFDeriv_id_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:10:02.004997+00:00
-- url     : https://prove2.me/submissions/37391b0e-b9f1-4a2b-b14d-cd3290e94662

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzContinuousAtOfPointwiseOfBounded
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PolyMulGaussianBounded
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIteratedFDerivTruncExpICompLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open scoped Nat
noncomputable section
open GlobalTheory GlobalTheory.GaussExpSeries
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
namespace GlobalTheory.GaussExpSeries
theorem _root_.solution (j : ℕ) (x : V) :
    ‖iteratedFDeriv ℝ j (id : V → V) x‖ ≤ 1 + ‖x‖ := by
  rcases j with _ | n
  · rw [norm_iteratedFDeriv_zero]; simp
  · rw [← norm_iteratedFDeriv_fderiv,
      show fderiv ℝ (id : V → V) = fun _ => ContinuousLinearMap.id ℝ V from funext fun _ => fderiv_id]
    rcases n with _ | n
    · rw [norm_iteratedFDeriv_zero]
      exact (ContinuousLinearMap.norm_id_le).trans (by linarith [norm_nonneg x])
    · rw [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero n)]
      simp only [Pi.zero_apply, norm_zero]
      positivity
end GlobalTheory.GaussExpSeries
