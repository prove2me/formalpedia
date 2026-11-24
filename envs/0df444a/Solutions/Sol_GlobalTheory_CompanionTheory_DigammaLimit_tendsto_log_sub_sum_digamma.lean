-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DigammaLimit.tendsto_log_sub_sum_digamma
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:16:28.870604+00:00
-- url     : https://prove2.me/submissions/12eeef4f-022a-43e6-ac39-98917acbe70f

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_DigammaTendstoLogSubHarmonic
import Theorems.Thm_GlobalTheory_CompanionTheory_DigammaLimit_logDeriv_GammaSeq
import Theorems.Thm_GlobalTheory_CompanionTheory_DigammaLimit_tendsto_deriv_GammaSeq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology Metric Set
open scoped Nat Real
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DigammaLimit
namespace GlobalTheory.CompanionTheory.DigammaLimit
theorem _root_.solution : ∀ z : ℂ, 0 < z.re →
    Filter.Tendsto (fun n : ℕ => ((Real.log n : ℝ) : ℂ) -
      ∑ k ∈ Finset.range (n + 1), 1 / (z + (k : ℂ))) Filter.atTop (nhds (Complex.digamma z)) := by
  intro z hz
  have h1 := (tendsto_deriv_GammaSeq hz).div (GammaSeq_tendsto_Gamma z)
    (Gamma_ne_zero_of_re_pos hz)
  rw [digamma_def, logDeriv_apply]
  refine Tendsto.congr' ?_ h1
  filter_upwards [eventually_ne_atTop 0] with n hn
  rw [← logDeriv_GammaSeq hz hn, logDeriv_apply]
  rfl
end GlobalTheory.CompanionTheory.DigammaLimit
