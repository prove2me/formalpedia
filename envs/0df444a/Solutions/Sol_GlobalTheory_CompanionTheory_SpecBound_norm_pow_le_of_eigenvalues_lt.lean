-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SpecBound.norm_pow_le_of_eigenvalues_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:48:25.851474+00:00
-- url     : https://prove2.me/submissions/d702de2e-558c-4a90-a126-8b6f9916be43

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NormPowLeOfEigenvaluesLt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open scoped NNReal ENNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SpecBound
namespace GlobalTheory.CompanionTheory.SpecBound
theorem _root_.solution (W : Type) [NormedAddCommGroup W] [NormedSpace ℂ W]
    [FiniteDimensional ℂ W] (T : W →L[ℂ] W) (ρ : ℝ)
    (h : ∀ μ : ℂ, Module.End.HasEigenvalue (T : Module.End ℂ W) μ → ‖μ‖ < ρ) :
    ∃ C : ℝ, ∀ j : ℕ, ‖T ^ j‖ ≤ C * ρ ^ j := by
  rcases subsingleton_or_nontrivial W with hW | hW
  · refine ⟨0, fun j => ?_⟩
    have h0 : T ^ j = 0 := by
      ext x
      exact Subsingleton.elim _ _
    simp [h0]
  have : CompleteSpace W := FiniteDimensional.complete ℂ W
  have : Nontrivial (W →L[ℂ] W) :=
    (Module.End.toContinuousLinearMap (𝕜 := ℂ) W).injective.nontrivial
  obtain ⟨z, hz, hzr⟩ := spectrum.exists_nnnorm_eq_spectralRadius T
  have hzE : Module.End.HasEigenvalue (T : Module.End ℂ W) z := by
    rw [Module.End.hasEigenvalue_iff_mem_spectrum]
    have hT : (Module.End.toContinuousLinearMap (𝕜 := ℂ) W) (T : Module.End ℂ W) = T := by
      ext x
      rfl
    rw [← AlgEquiv.spectrum_eq (Module.End.toContinuousLinearMap (𝕜 := ℂ) W), hT]
    exact hz
  have hlt : ‖z‖ < ρ := h z hzE
  have hρ : 0 < ρ := (norm_nonneg z).trans_lt hlt
  let ρ' : ℝ≥0 := ⟨ρ, hρ.le⟩
  have hr : spectralRadius ℂ T < (ρ' : ℝ≥0∞) := by
    rw [← hzr]
    have : ‖z‖₊ < ρ' := by
      rw [← NNReal.coe_lt_coe]
      exact hlt
    exact_mod_cast this
  have hev := (spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius T).eventually_lt_const hr
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hev.and (eventually_gt_atTop 0))
  have key : ∀ n, N ≤ n → ‖T ^ n‖ ≤ ρ ^ n := by
    intro n hn
    obtain ⟨h1, h0⟩ := hN n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast h0.ne'
    have h2 : (‖T ^ n‖₊ : ℝ≥0∞) ≤ (ρ' : ℝ≥0∞) ^ n := by
      have h3 := ENNReal.rpow_le_rpow h1.le (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))
      rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hn0, ENNReal.rpow_one,
        ENNReal.rpow_natCast] at h3
      exact h3
    have h4 : ‖T ^ n‖₊ ≤ ρ' ^ n := by exact_mod_cast h2
    have h5 : ((‖T ^ n‖₊ : ℝ≥0) : ℝ) ≤ ((ρ' ^ n : ℝ≥0) : ℝ) := NNReal.coe_le_coe.2 h4
    rw [NNReal.coe_pow, coe_nnnorm] at h5
    exact h5
  refine ⟨1 + ∑ i ∈ Finset.range N, ‖T ^ i‖ / ρ ^ i, fun j => ?_⟩
  have hpow : 0 < ρ ^ j := pow_pos hρ j
  have hsum : 0 ≤ ∑ i ∈ Finset.range N, ‖T ^ i‖ / ρ ^ i :=
    Finset.sum_nonneg fun i _ => div_nonneg (norm_nonneg _) (pow_pos hρ i).le
  by_cases hj : j < N
  · have h6 : ‖T ^ j‖ / ρ ^ j ≤ ∑ i ∈ Finset.range N, ‖T ^ i‖ / ρ ^ i :=
      Finset.single_le_sum (f := fun i => ‖T ^ i‖ / ρ ^ i)
        (fun i _ => div_nonneg (norm_nonneg _) (pow_pos hρ i).le) (Finset.mem_range.2 hj)
    have h7 : ‖T ^ j‖ / ρ ^ j ≤ 1 + ∑ i ∈ Finset.range N, ‖T ^ i‖ / ρ ^ i := by linarith
    exact (div_le_iff₀ hpow).1 h7
  · have h8 := key j (not_lt.1 hj)
    nlinarith [mul_nonneg hsum hpow.le]
end GlobalTheory.CompanionTheory.SpecBound
