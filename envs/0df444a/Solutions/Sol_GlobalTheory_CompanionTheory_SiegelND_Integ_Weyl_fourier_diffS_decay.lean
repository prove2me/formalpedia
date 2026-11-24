-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.fourier_diffS_decay
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:15:16.115984+00:00
-- url     : https://prove2.me/submissions/6cd2c29b-b694-4dbc-a0e6-33512c57652d

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SecondCountableHermC
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContinuousSeminormDiffSLe
import Theorems.Thm_GlobalTheory_CompanionTheory_SiegelND_Integ_Weyl_continuous_seminorm_diffS_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl
open MeasureTheory
open scoped ComplexConjugate FourierTransform
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl
theorem _root_.solution (f : SchwartzMap V ℂ) (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ξ : V,
      ‖𝓕 (diffS f y) ξ‖ ≤ C * (((1 + ‖y‖) ^ K)⁻¹ * ((1 + ‖ξ‖) ^ K)⁻¹) := by
  have hp : ∀ m : ℕ × ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ y : V,
      SchwartzMap.seminorm ℂ m.1 m.2 (𝓕 (diffS f y)) ≤ C * ((1 + ‖y‖) ^ K)⁻¹ := by
    intro m
    refine continuous_seminorm_diffS_le f K
      ((SchwartzMap.seminorm ℂ m.1 m.2).comp
        (SchwartzMap.fourierTransformCLM ℂ (V := V) (E := ℂ)).toLinearMap) ?_
    exact ((schwartz_withSeminorms ℂ V ℂ).continuous_seminorm m).comp
      (SchwartzMap.fourierTransformCLM ℂ (V := V) (E := ℂ)).continuous
  choose D hD0 hD using hp
  set s := Finset.Iic ((K, 0) : ℕ × ℕ)
  refine ⟨2 ^ K * ∑ m ∈ s, D m,
    mul_nonneg (by positivity) (Finset.sum_nonneg fun m _ => hD0 m), fun y ξ => ?_⟩
  have hy : 0 ≤ ((1 + ‖y‖) ^ K)⁻¹ := by positivity
  have hξ : 0 < (1 + ‖ξ‖) ^ K := by positivity
  have h1 := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (K, 0)) (k := K) (n := 0)
    le_rfl le_rfl (𝓕 (diffS f y)) ξ
  have hsup : (s.sup fun m => SchwartzMap.seminorm ℂ m.1 m.2) (𝓕 (diffS f y)) ≤
      (∑ m ∈ s, D m) * ((1 + ‖y‖) ^ K)⁻¹ := by
    refine Seminorm.finset_sup_apply_le
      (mul_nonneg (Finset.sum_nonneg fun m _ => hD0 m) hy) fun m hm => ?_
    refine (hD m y).trans (mul_le_mul_of_nonneg_right ?_ hy)
    exact Finset.single_le_sum (f := D) (fun i _ => hD0 i) hm
  rw [norm_iteratedFDeriv_zero] at h1
  have h2 : (1 + ‖ξ‖) ^ K * ‖𝓕 (diffS f y) ξ‖ ≤ 2 ^ K * ((∑ m ∈ s, D m) * ((1 + ‖y‖) ^ K)⁻¹) :=
    h1.trans (mul_le_mul_of_nonneg_left hsup (by positivity))
  have h3 : ‖𝓕 (diffS f y) ξ‖ ≤ 2 ^ K * ((∑ m ∈ s, D m) * ((1 + ‖y‖) ^ K)⁻¹) / (1 + ‖ξ‖) ^ K := by
    rw [le_div_iff₀ hξ]; linarith
  calc _ ≤ _ := h3
    _ = _ := by rw [div_eq_mul_inv]; ring
end GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl
