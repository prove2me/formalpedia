-- Prove2me | solution 1 for GlobalTheory.GallagherLemma.exp_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:05:13.435456+00:00
-- url     : https://prove2.me/submissions/6515e119-68f9-440d-bf49-02e4952840ab

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IntegralNormSqLp
import Theorems.Thm_GlobalTheory_GallagherLemma_plancherel
import Theorems.Thm_GlobalTheory_GallagherLemma_fourier_indicator
import Theorems.Thm_GlobalTheory_GallagherLemma_kernel_lower

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open scoped FourierTransform SchwartzMap Real
open GlobalTheory GlobalTheory.GallagherLemma
namespace GlobalTheory.GallagherLemma
theorem _root_.solution (S : Finset ℕ) (a : ℕ → ℂ) (l : ℕ → ℝ) (T : ℝ) (hT : 0 < T) :
    (∫ t in (-T)..T, ‖∑ n ∈ S, a n * cexp (-(t * l n : ℝ) * I)‖ ^ 2) ≤
      8 * π * T ^ 2 *
        ∫ v : ℝ, ‖∑ n ∈ S, (Set.Ico (l n - 1 / T) (l n)).indicator (fun _ => a n) v‖ ^ 2 := by
  set f : ℝ → ℂ := fun v => ∑ n ∈ S, (Set.Ico (l n - 1 / T) (l n)).indicator (fun _ => a n) v
    with hf
  have hmem : ∀ (p : ENNReal) (n : ℕ),
      MemLp ((Set.Ico (l n - 1 / T) (l n)).indicator (fun _ => a n)) p volume := fun p n =>
    memLp_indicator_const p measurableSet_Ico _ (Or.inr (by simp))
  have hint : ∀ n, Integrable ((Set.Ico (l n - 1 / T) (l n)).indicator (fun _ => a n)) volume :=
    fun n => memLp_one_iff_integrable.1 (hmem 1 n)
  have hf1 : Integrable f := integrable_finsetSum _ fun n _ => hint n
  have hf2 : MemLp f 2 := memLp_finsetSum _ fun n _ => hmem 2 n
  obtain ⟨hI, hP⟩ := plancherel hf1 hf2
  have hδ : 0 ≤ 1 / T := by positivity
  have hF : ∀ w : ℝ, 𝓕 f w = (∑ n ∈ S, a n * cexp (-(2 * π * w * l n : ℝ) * I)) *
      ∫ u in (0 : ℝ)..(1 / T), cexp ((2 * π * w * u : ℝ) * I) := by
    intro w
    rw [Finset.sum_mul]
    simp_rw [← fourier_indicator _ _ hδ]
    simp_rw [Real.fourier_real_eq, hf, Finset.smul_sum]
    refine integral_finsetSum _ fun n _ => ?_
    simpa [mul_comm] using (Real.fourierIntegral_convergent_iff w).2 (hint n)
  have hpi : (0 : ℝ) < 2 * π := by positivity
  set D : ℝ → ℝ := fun t => ‖∑ n ∈ S, a n * cexp (-(t * l n : ℝ) * I)‖ ^ 2 with hD
  have hDc : Continuous D := by fun_prop
  have h1 : ∫ t in (-T)..T, D t = (2 * π) * ∫ w in (-T / (2 * π))..(T / (2 * π)), D (2 * π * w) := by
    have := intervalIntegral.mul_integral_comp_mul_left (f := D) (a := -T / (2 * π))
      (b := T / (2 * π)) (2 * π)
    rw [this, mul_div_cancel₀ _ hpi.ne', mul_div_cancel₀ _ hpi.ne']
  have hle : -T / (2 * π) ≤ T / (2 * π) := by gcongr; linarith
  have h2 : ∫ w in (-T / (2 * π))..(T / (2 * π)), D (2 * π * w) ≤
      ∫ w in (-T / (2 * π))..(T / (2 * π)), 4 * T ^ 2 * ‖𝓕 f w‖ ^ 2 := by
    refine intervalIntegral.integral_mono_on hle
      ((hDc.comp (by fun_prop : Continuous fun w : ℝ => 2 * π * w)).intervalIntegrable _ _)
      ((hI.const_mul _).intervalIntegrable) fun w hw => ?_
    have hw' : |2 * π * w| ≤ T := by
      rw [abs_le]
      constructor
      · have := (div_le_iff₀ hpi).1 hw.1
        linarith
      · have := (le_div_iff₀ hpi).1 hw.2
        linarith
    have hk := kernel_lower (1 / T) (2 * π * w) hδ (by rw [mul_one_div, div_le_one hT]; exact hw')
    rw [hF, norm_mul, mul_pow]
    set k := ‖∫ u in (0 : ℝ)..(1 / T), cexp ((2 * π * w * u : ℝ) * I)‖
    have hk1 : 1 ≤ 2 * T * k := by
      have : 2 * T * (1 / T / 2) = 1 := by field_simp
      rw [← this]; gcongr
    have hk2 : 1 ≤ 4 * T ^ 2 * k ^ 2 := by nlinarith
    have hD0 : 0 ≤ D (2 * π * w) := by positivity
    change D (2 * π * w) ≤ 4 * T ^ 2 * (D (2 * π * w) * k ^ 2)
    nlinarith
  have h3 : ∫ w in (-T / (2 * π))..(T / (2 * π)), 4 * T ^ 2 * ‖𝓕 f w‖ ^ 2 ≤
      4 * T ^ 2 * ∫ v, ‖f v‖ ^ 2 := by
    rw [intervalIntegral.integral_const_mul, ← hP, intervalIntegral.integral_of_le hle]
    exact mul_le_mul_of_nonneg_left
      (setIntegral_le_integral hI (Filter.Eventually.of_forall fun w => by positivity))
      (by positivity)
  rw [h1]
  calc _ ≤ (2 * π) * (4 * T ^ 2 * ∫ v, ‖f v‖ ^ 2) := by
        gcongr; exact h2.trans h3
    _ = _ := by ring
end GlobalTheory.GallagherLemma
