-- Prove2me | solution 1 for GlobalTheory.RapidFourier.norm_iteratedFDeriv_term_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:11:34.236841+00:00
-- url     : https://prove2.me/submissions/b72fbc1f-47bf-45bc-bb70-b0a63e77982b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ContDiffAndFderivTsumFourierOfRapid
import Theorems.Thm_GlobalTheory_RapidFourier_norm_linForm_le
import Theorems.Thm_GlobalTheory_RapidFourier_contDiff_wave
import Theorems.Thm_GlobalTheory_RapidFourier_iteratedDeriv_wave
import Theorems.Thm_GlobalTheory_RapidFourier_norm_wave
import Theorems.Thm_GlobalTheory_RapidFourier_norm_two_pi_I

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix
open scoped ContDiff BigOperators Real
open GlobalTheory
open GlobalTheory.RapidFourier
namespace GlobalTheory.RapidFourier
theorem _root_.solution {n : ℕ} (a : ℂ) (ν : Fin n → ℤ) (m : ℕ) (x : Fin n → ℝ) :
    ‖iteratedFDeriv ℝ m (wave a ∘ linForm ν) x‖
      ≤ (2 * π) ^ m * (‖a‖ * (1 + ∑ k, |(ν k : ℝ)|) ^ m) := by
  rw [ContinuousLinearMap.iteratedFDeriv_comp_right _ (contDiff_wave a) x
    (by exact_mod_cast le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_wave, norm_wave, norm_mul,
    norm_pow, norm_two_pi_I, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hL : ‖linForm ν‖ ≤ 1 + ∑ k, |(ν k : ℝ)| := (norm_linForm_le ν).trans (le_add_of_nonneg_left zero_le_one)
  have hpow : ‖linForm ν‖ ^ m ≤ (1 + ∑ k, |(ν k : ℝ)|) ^ m := pow_le_pow_left₀ (norm_nonneg _) hL m
  calc (2 * π) ^ m * ‖a‖ * ‖linForm ν‖ ^ m ≤ (2 * π) ^ m * ‖a‖ * (1 + ∑ k, |(ν k : ℝ)|) ^ m :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = (2 * π) ^ m * (‖a‖ * (1 + ∑ k, |(ν k : ℝ)|) ^ m) := by ring
end GlobalTheory.RapidFourier
