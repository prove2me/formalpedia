-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.sobolev_embedding
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:29:27.578601+00:00
-- url     : https://prove2.me/submissions/f02c20f2-37cc-420d-9380-3d54cf3286ba

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_Sobolev
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevEmbedding
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_toDistribution_apply_eq_integral
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_integrable_pow_mul_norm_fourierFun_neg
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_toDistribution_lineDerivCLM
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_fourierFun_aestronglyMeasurable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Sobolev.SobolevSpace.toDistribution_lineDerivCLM



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.Sobolev
open TemperedDistribution MeasureTheory FourierTransform
open scoped SchwartzMap ENNReal ContDiff
noncomputable section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
namespace GroundTheory.Automorphic.Sobolev
theorem _root_.solution {s : ℝ} (k : ℕ)
    (hs : (k : ℝ) + (Module.finrank ℝ E : ℝ) / 2 < s) (u : SobolevSpace E F s) :
    ∃ g : E → F, ContDiff ℝ k g ∧
      (∀ i : ℕ, i ≤ k → ∃ C, ∀ x, ‖iteratedFDeriv ℝ i g x‖ ≤ C) ∧
      ∀ φ : 𝓢(E, ℂ), SobolevSpace.toDistribution u φ = ∫ x, φ x • g x := by
  have hj : ∀ j : ℕ, j ≤ k → (Module.finrank ℝ E : ℝ) < 2 * (s - j) := fun j hj ↦ by
    have : (j : ℝ) ≤ k := by exact_mod_cast hj
    linarith
  have hs0 : (Module.finrank ℝ E : ℝ) < 2 * s := by simpa using hj 0 (Nat.zero_le _)
  set f : E → F := fun ξ ↦ fourierFun u (-ξ)
  have hg : 𝓕⁻ (fourierFun u) = 𝓕 f := Real.fourierInv_eq_fourier_comp_neg _
  have hint : ∀ n : ℕ, (n : ℕ∞) ≤ (k : ℕ∞) → Integrable (fun v ↦ ‖v‖ ^ n * ‖f v‖)
      (volume : Measure E) := fun n hn ↦
    integrable_pow_mul_norm_fourierFun_neg (hj n (by exact_mod_cast hn)) u
  have hmeas : AEStronglyMeasurable f (volume : Measure E) :=
    (fourierFun_aestronglyMeasurable u).comp_measurePreserving
      (Measure.measurePreserving_neg (volume : Measure E))
  refine ⟨𝓕⁻ (fourierFun u), ?_, ?_, toDistribution_apply_eq_integral hs0 u⟩
  · rw [hg]
    exact Real.contDiff_fourier hint
  · intro i hi
    refine ⟨∫ v, ‖(fun v ↦ VectorFourier.fourierPowSMulRight (innerSL ℝ) f v i) v‖, fun x ↦ ?_⟩
    rw [hg, Real.iteratedFDeriv_fourier hint hmeas (by exact_mod_cast hi)]
    exact VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
end GroundTheory.Automorphic.Sobolev
