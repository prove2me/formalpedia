-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DigammaBound.digamma_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:33:32.710472+00:00
-- url     : https://prove2.me/submissions/1b6b637c-169c-48a3-b784-32ceb69c956f

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_DigammaTendstoLogSubHarmonic
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_DigammaLogBoundRightHalfPlane
import Theorems.Thm_GlobalTheory_CompanionTheory_DigammaBound_partial_le
import Theorems.Thm_GlobalTheory_CompanionTheory_DigammaLimit_tendsto_log_sub_sum_digamma


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DigammaBound
open Finset
namespace GlobalTheory.CompanionTheory.DigammaBound
theorem _root_.solution :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, 1 / 2 ≤ z.re → ‖Complex.digamma z‖ ≤ C * Real.log (‖z‖ + 2) := by
  refine ⟨11, by norm_num, fun z hz => ?_⟩
  have hzn : 1 / 2 ≤ ‖z‖ := hz.trans ((le_abs_self _).trans (Complex.abs_re_le_norm z))
  set M : ℕ := ⌈‖z‖⌉₊ + 1 with hMdef
  have hM : 1 ≤ M := by omega
  have hzM : ‖z‖ ≤ M := by
    rw [hMdef]
    push_cast
    linarith [Nat.le_ceil ‖z‖]
  have hMle : (M : ℝ) ≤ ‖z‖ + 2 := by
    rw [hMdef]
    push_cast
    linarith [Nat.ceil_lt_add_one (norm_nonneg z)]
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hlogM : Real.log M ≤ Real.log (‖z‖ + 2) := Real.log_le_log hM0 hMle
  have hlim := (GlobalTheory.CompanionTheory.DigammaLimit.tendsto_log_sub_sum_digamma z (by linarith)).norm
  have hbd : ‖Complex.digamma z‖ ≤ 6 + 2 * Real.log M :=
    le_of_tendsto hlim ((Filter.eventually_ge_atTop M).mono fun n hn =>
      partial_le z hz M hM hzM n hn)
  have hL : (2 : ℝ) / 3 ≤ Real.log (‖z‖ + 2) := by
    have h2 : Real.log 2 ≤ Real.log (‖z‖ + 2) :=
      Real.log_le_log (by norm_num) (by linarith)
    linarith [Real.log_two_gt_d9]
  linarith
end GlobalTheory.CompanionTheory.DigammaBound
