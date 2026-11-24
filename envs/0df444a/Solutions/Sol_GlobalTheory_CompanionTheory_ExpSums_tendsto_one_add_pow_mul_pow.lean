-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ExpSums.tendsto_one_add_pow_mul_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:29:57.680292+00:00
-- url     : https://prove2.me/submissions/f237fa10-9867-45b7-b275-d35bdc814fd1

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_FibreFactorHolds
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_VandermondeSeparation
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RegularizedExponentialSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open scoped Classical
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ExpSums
namespace GlobalTheory.CompanionTheory.ExpSums
theorem _root_.solution {t : ℝ} (h0 : 0 ≤ t) (h1 : t < 1) (N : ℕ) :
    Tendsto (fun n : ℕ => (1 + (n : ℝ)) ^ N * t ^ n) atTop (𝓝 0) := by
  have ht : |t| < 1 := by rw [abs_of_nonneg h0]; exact h1
  have hlim : Tendsto (fun n : ℕ => (2 : ℝ) ^ N * ((n : ℝ) ^ N * t ^ n)) atTop (𝓝 0) := by
    have h := (tendsto_pow_const_mul_const_pow_of_abs_lt_one N ht).const_mul ((2 : ℝ) ^ N)
    rwa [mul_zero] at h
  refine squeeze_zero' (Filter.Eventually.of_forall fun n => mul_nonneg (by positivity) (pow_nonneg h0 n)) ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hle : (1 + (n : ℝ)) ^ N ≤ (2 * (n : ℝ)) ^ N := by
    gcongr
    linarith
  calc (1 + (n : ℝ)) ^ N * t ^ n ≤ (2 * (n : ℝ)) ^ N * t ^ n :=
        mul_le_mul_of_nonneg_right hle (pow_nonneg h0 n)
    _ = (2 : ℝ) ^ N * ((n : ℝ) ^ N * t ^ n) := by ring
end GlobalTheory.CompanionTheory.ExpSums
