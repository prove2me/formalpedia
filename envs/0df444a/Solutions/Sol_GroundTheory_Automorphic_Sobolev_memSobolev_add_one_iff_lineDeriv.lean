-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.memSobolev_add_one_iff_lineDeriv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:43:30.312888+00:00
-- url     : https://prove2.me/submissions/0e86e6c6-77dc-4ea5-bc90-1765066a7e60

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMollifier
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevFriedrichs
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_memSobolev_add_one_of_lintegral
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_locallyIntegrable_fourierFun
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_memSobolev_toDistribution
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_toDistribution_convolutionCLM
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_toDistribution_lineDerivCLM
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_toDistribution_sub
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_ae_eq_of_integral_schwartz_smul_eq
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_dualEquiv_apply
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_fourierFun_multiplier
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_fourier_apply_eq_integral
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_integrable_weight_mul_norm_sq_fourierFun
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
open LineDeriv
namespace GroundTheory.Automorphic.Sobolev
theorem _root_.solution {s : ℝ} (u : SobolevSpace E F s) :
    MemSobolev (s + 1) 2 (SobolevSpace.toDistribution u) ↔
      ∀ v : E, MemSobolev s 2 (∂_{v} (SobolevSpace.toDistribution u)) := by
  constructor
  · intro hu v
    have := SobolevSpace.memSobolev_toDistribution
      (SobolevSpace.lineDerivCLM v (SobolevSpace.mk (s := s + 1) _ hu))
    rwa [SobolevSpace.toDistribution_lineDerivCLM, SobolevSpace.toDistribution_mk,
      add_sub_cancel_right] at this
  · intro hv
    apply memSobolev_add_one_of_lintegral
    intro v
    set w : SobolevSpace E F s := SobolevSpace.mk _ (hv v)
    set d := SobolevSpace.lineDerivCLM (s := s) v u
    have hd := (fourierFun_multiplier (m := fun ξ ↦ (2 * Real.pi * Complex.I) *
      ((inner ℝ ξ v : ℝ) : ℂ)) (by fun_prop) (SobolevSpace.lineDeriv_bound v) u).1
    have hwd : fourierFun w =ᵐ[volume] fourierFun d := by
      apply ae_eq_of_integral_schwartz_smul_eq (locallyIntegrable_fourierFun w)
        (locallyIntegrable_fourierFun d)
      intro φ _
      rw [← fourier_apply_eq_integral, ← fourier_apply_eq_integral]
      simp [w, d]
    have hint := (integrable_weight_mul_norm_sq_fourierFun w).lintegral_lt_top
    have hc : (0 : ℝ) < (2 * Real.pi) ^ 2 := by positivity
    have hpt : ∀ᵐ ξ ∂(volume : Measure E),
        ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ s * inner ℝ ξ v ^ 2 * ‖fourierFun u ξ‖ ^ 2) =
          ENNReal.ofReal (((2 * Real.pi) ^ 2)⁻¹) *
            ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ s * ‖fourierFun w ξ‖ ^ 2) := by
      filter_upwards [hwd, hd] with ξ h1 h2
      rw [← ENNReal.ofReal_mul (by positivity), h1]
      congr 1
      change _ = _ * ((1 + ‖ξ‖ ^ 2) ^ s * ‖fourierFun (SobolevSpace.multiplier _ _ u) ξ‖ ^ 2)
      have h2pi : ‖(2 : ℂ) * (Real.pi : ℂ)‖ = 2 * Real.pi := by
        rw [norm_mul, Complex.norm_two, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
      rw [h2, norm_smul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, h2pi,
        Real.norm_eq_abs, mul_one, mul_pow, mul_pow, mul_pow, sq_abs]
      field_simp
    rw [lintegral_congr_ae hpt, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hint
end GroundTheory.Automorphic.Sobolev
