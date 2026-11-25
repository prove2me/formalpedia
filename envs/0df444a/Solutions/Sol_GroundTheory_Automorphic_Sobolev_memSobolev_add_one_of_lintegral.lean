-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.memSobolev_add_one_of_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:20:49.721689+00:00
-- url     : https://prove2.me/submissions/442c7cb4-6748-4e44-847f-9e6245117cb7

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMollifier
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevFriedrichs
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_aestronglyMeasurable_weight_mul_sq
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_toDistribution_convolutionCLM
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_toDistribution_lineDerivCLM
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_toDistribution_sub
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_dualEquiv_apply
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_fourierFun_aestronglyMeasurable
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_fourier_apply_eq_integral
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_integrable_weight_mul_norm_sq_fourierFun
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_memSobolev_iff_fourier
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Sobolev.SobolevSpace.toDistribution_convolutionCLM
attribute [local simp] GroundTheory.Automorphic.Sobolev.SobolevSpace.toDistribution_lineDerivCLM
attribute [local simp] GroundTheory.Automorphic.Sobolev.SobolevSpace.toDistribution_sub
attribute [local simp] GroundTheory.Automorphic.Sobolev.dualEquiv_apply



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.Sobolev
open TemperedDistribution MeasureTheory FourierTransform
open scoped SchwartzMap ENNReal ContDiff
noncomputable section
set_option linter.unusedSectionVars false
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
namespace GroundTheory.Automorphic.Sobolev
theorem _root_.solution {s : ℝ} (u : SobolevSpace E F s)
    (h : ∀ v : E, ∫⁻ ξ, ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ s * inner ℝ ξ v ^ 2 *
      ‖fourierFun u ξ‖ ^ 2) < ⊤) :
    MemSobolev (s + 1) 2 (SobolevSpace.toDistribution u) := by
  rw [memSobolev_iff_fourier]
  refine ⟨fourierFun u, ?_, fourier_apply_eq_integral u⟩
  set b := stdOrthonormalBasis ℝ E
  have hmeas : AEStronglyMeasurable (fun ξ ↦ weight (s + 1) ξ • fourierFun u ξ)
      (volume : Measure E) :=
    (weight_hasTemperateGrowth (s + 1)).1.continuous.aestronglyMeasurable.smul
      (fourierFun_aestronglyMeasurable u)
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  refine ⟨hmeas.norm.pow 2, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ ↦ by positivity)]
  have hpt : ∀ ξ, ENNReal.ofReal (‖weight (s + 1) ξ • fourierFun u ξ‖ ^ 2) =
      ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ s * 1 * ‖fourierFun u ξ‖ ^ 2) +
        ∑ i, ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ s * inner ℝ ξ (b i) ^ 2 * ‖fourierFun u ξ‖ ^ 2) := by
    intro ξ
    have h0 : (0 : ℝ) < 1 + ‖ξ‖ ^ 2 := by positivity
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ by positivity),
      ← ENNReal.ofReal_add (by positivity) (Finset.sum_nonneg fun i _ ↦ by positivity)]
    congr 1
    have hsum : ∑ i, (1 + ‖ξ‖ ^ 2) ^ s * inner ℝ ξ (b i) ^ 2 * ‖fourierFun u ξ‖ ^ 2 =
        (1 + ‖ξ‖ ^ 2) ^ s * ‖ξ‖ ^ 2 * ‖fourierFun u ξ‖ ^ 2 := by
      calc ∑ i, (1 + ‖ξ‖ ^ 2) ^ s * inner ℝ ξ (b i) ^ 2 * ‖fourierFun u ξ‖ ^ 2
          = (1 + ‖ξ‖ ^ 2) ^ s * (∑ i, inner ℝ ξ (b i) ^ 2) * ‖fourierFun u ξ‖ ^ 2 := by
            rw [Finset.mul_sum, Finset.sum_mul]
        _ = _ := by rw [b.sum_sq_inner_left ξ]
    have hw : ((1 + ‖ξ‖ ^ 2) ^ ((s + 1) / 2)) ^ 2 = (1 + ‖ξ‖ ^ 2) ^ s * (1 + ‖ξ‖ ^ 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul h0.le, ← Real.rpow_add_one h0.ne']
      congr 1; push_cast; ring
    rw [hsum, norm_smul, norm_weight, mul_pow, hw]
    ring
  simp_rw [hpt]
  have hm : ∀ g : E → ℝ, Continuous g → AEMeasurable (fun ξ ↦ ENNReal.ofReal
      ((1 + ‖ξ‖ ^ 2) ^ s * g ξ * ‖fourierFun u ξ‖ ^ 2)) (volume : Measure E) :=
    fun g hg ↦ (aestronglyMeasurable_weight_mul_sq u g hg).aemeasurable.ennreal_ofReal
  rw [lintegral_add_left' (hm _ continuous_const),
    lintegral_finsetSum' _ fun i _ ↦ hm (fun ξ ↦ inner ℝ ξ (b i) ^ 2) (by fun_prop)]
  refine ENNReal.add_lt_top.2 ⟨?_, ENNReal.sum_lt_top.2 fun i _ ↦ h (b i)⟩
  have := (integrable_weight_mul_norm_sq_fourierFun u).lintegral_lt_top
  simpa using this
end GroundTheory.Automorphic.Sobolev
