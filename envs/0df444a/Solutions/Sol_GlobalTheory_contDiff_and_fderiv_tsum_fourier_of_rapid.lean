-- Prove2me | solution 1 for GlobalTheory.contDiff_and_fderiv_tsum_fourier_of_rapid
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:42:47.597731+00:00
-- url     : https://prove2.me/submissions/ed09eedb-c1a6-4c5d-81e9-295154560c19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ContDiffAndFderivTsumFourierOfRapid
import Theorems.Thm_GlobalTheory_RapidFourier_linForm_apply
import Theorems.Thm_GlobalTheory_RapidFourier_norm_linForm_le
import Theorems.Thm_GlobalTheory_RapidFourier_contDiff_wave
import Theorems.Thm_GlobalTheory_RapidFourier_norm_wave
import Theorems.Thm_GlobalTheory_RapidFourier_norm_two_pi_I
import Theorems.Thm_GlobalTheory_RapidFourier_term_eq
import Theorems.Thm_GlobalTheory_RapidFourier_norm_iteratedFDeriv_term_le
import Theorems.Thm_GlobalTheory_RapidFourier_summable_weighted
import Theorems.Thm_GlobalTheory_RapidFourier_hasFDerivAt_term

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
open RapidFourier
namespace GlobalTheory
theorem _root_.solution :
    ∀ (n : ℕ) (c : (Fin n → ℤ) → ℂ), (∀ N : ℕ, ∃ C : ℝ, ∀ ν, ‖c ν‖ * (1 + ∑ k, |(ν k : ℝ)|) ^ N ≤ C) → ContDiff ℝ ∞ (fun x : Fin n → ℝ => ∑' ν, c ν * cexp (2 * π * I * ∑ k, (ν k : ℂ) * (x k : ℂ))) ∧ ∀ (x : Fin n → ℝ) (j : Fin n), fderiv ℝ (fun x : Fin n → ℝ => ∑' ν, c ν * cexp (2 * π * I * ∑ k, (ν k : ℂ) * (x k : ℂ))) x (Pi.single j 1) = ∑' ν, 2 * π * I * (ν j : ℂ) * c ν * cexp (2 * π * I * ∑ k, (ν k : ℂ) * (x k : ℂ)) := by
  intro n c hc
  have hfun : (fun x : Fin n → ℝ => ∑' ν, c ν * cexp (2 * π * I * ∑ k, (ν k : ℂ) * (x k : ℂ))) =
      fun x => ∑' ν, (wave (c ν) ∘ linForm ν) x := by
    funext x
    exact tsum_congr fun ν => term_eq (c ν) ν x
  have hL : ∀ ν : Fin n → ℤ, ‖linForm ν‖ ≤ 1 + ∑ k, |(ν k : ℝ)| := fun ν =>
    (norm_linForm_le ν).trans (le_add_of_nonneg_left zero_le_one)
  have hsum : ∀ m : ℕ, Summable fun ν : Fin n → ℤ =>
      (2 * π) ^ m * (‖c ν‖ * (1 + ∑ k, |(ν k : ℝ)|) ^ m) := fun m =>
    (summable_weighted hc m).mul_left _
  have hD : ∀ (ν : Fin n → ℤ) (y : Fin n → ℝ),
      ‖(linForm ν).smulRight (wave (2 * π * I * c ν) (linForm ν y))‖ ≤
        (2 * π) ^ 1 * (‖c ν‖ * (1 + ∑ k, |(ν k : ℝ)|) ^ 1) := by
    intro ν y
    rw [ContinuousLinearMap.norm_smulRight_apply, norm_wave, norm_mul, norm_two_pi_I, pow_one,
      pow_one]
    calc ‖linForm ν‖ * (2 * π * ‖c ν‖) ≤ (1 + ∑ k, |(ν k : ℝ)|) * (2 * π * ‖c ν‖) :=
          mul_le_mul_of_nonneg_right (hL ν) (by positivity)
      _ = 2 * π * (‖c ν‖ * (1 + ∑ k, |(ν k : ℝ)|)) := by ring
  rw [hfun]
  refine ⟨contDiff_tsum (fun ν => (contDiff_wave (c ν)).comp (linForm ν).contDiff)
    (fun m _ => hsum m) (fun m ν x _ => norm_iteratedFDeriv_term_le (c ν) ν m x), fun x j => ?_⟩
  have h0 : Summable fun ν : Fin n → ℤ => (wave (c ν) ∘ linForm ν) x := by
    refine Summable.of_norm_bounded (hsum 0) fun ν => ?_
    simp [norm_wave]
  have hder := hasFDerivAt_tsum (hsum 1) (fun ν y => hasFDerivAt_term (c ν) ν y) hD h0 x
  have hs : Summable fun ν : Fin n → ℤ =>
      (linForm ν).smulRight (wave (2 * π * I * c ν) (linForm ν x)) :=
    Summable.of_norm_bounded (hsum 1) fun ν => hD ν x
  have hap := (ContinuousLinearMap.apply ℝ ℂ (Pi.single j (1 : ℝ))).map_tsum hs
  simp only [ContinuousLinearMap.apply_apply] at hap
  rw [hder.fderiv, hap]
  refine tsum_congr fun ν => ?_
  rw [ContinuousLinearMap.smulRight_apply, ← term_eq, linForm_apply]
  simp [Pi.single_apply, Complex.real_smul]
  ring
end GlobalTheory
