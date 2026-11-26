-- Prove2me | solution 1 for Malliavin.ClarkOconeFamily.inner_elementaryIntegralValue_eq_inner_elementaryPredictable_same
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:30:44.965522+00:00
-- url     : https://prove2.me/submissions/52538545-0fba-456a-9062-0e0eb9b0970b

import Definitions.Def_Malliavin_ClarkOcone
import Definitions.Def_Malliavin_ElementaryIto
import Theorems.Thm_Malliavin_CameronMartin_covarianceMap_apply
import Theorems.Thm_Malliavin_CameronMartin_densityExponent_zero
import Theorems.Thm_Malliavin_CameronMartin_density_toReal
import Theorems.Thm_Malliavin_CameronMartin_density_zero
import Theorems.Thm_Malliavin_CameronMartin_expectationMap_apply
import Theorems.Thm_Malliavin_CameronMartin_inclusion_apply
import Theorems.Thm_Malliavin_CameronMartin_realDensity_zero
import Theorems.Thm_Malliavin_CameronMartin_translated_zero
import Theorems.Thm_Malliavin_ClarkOconeFamily_coeFn_elementaryIntegralValue
import Theorems.Thm_Malliavin_mem_symmetricSubmodule
import Theorems.Thm_Malliavin_wienerIntegral_indicatorConstLp_Ioc
attribute [local simp] Malliavin.CameronMartin.covarianceMap_apply
attribute [local simp] Malliavin.CameronMartin.densityExponent_zero
attribute [local simp] Malliavin.CameronMartin.density_toReal
attribute [local simp] Malliavin.CameronMartin.density_zero
attribute [local simp] Malliavin.CameronMartin.expectationMap_apply
attribute [local simp] Malliavin.CameronMartin.inclusion_apply
attribute [local simp] Malliavin.CameronMartin.realDensity_zero
attribute [local simp] Malliavin.CameronMartin.translated_zero
attribute [local simp] Malliavin.mem_symmetricSubmodule



set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}
namespace Malliavin
namespace ClarkOconeFamily
theorem _root_.solution
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›} (C : ClarkOconeFamily B P 𝓕)
    {a b : ℝ≥0} (hab : a ≤ b)
    (Z Y : lpMeas ℝ ℝ (𝓕 a) 2 P) :
    inner ℝ (C.elementaryIntegralValue hab Z) (C.elementaryIntegralValue hab Y) =
      inner ℝ (elementaryPredictable 𝓕 a b Z) (elementaryPredictable 𝓕 a b Y) := by
  have hZY : AEStronglyMeasurable[𝓕 a]
      (fun w ↦ (Z : W → ℝ) w * (Y : W → ℝ) w) P :=
    (lpMeas.aestronglyMeasurable Z).mul (lpMeas.aestronglyMeasurable Y)
  have hindSq : IndepFun (fun w ↦ (B b w - B a w) ^ 2)
      (fun w ↦ (Z : W → ℝ) w * (Y : W → ℝ) w) P :=
    (C.indep_increment_of_adapted hab hZY).comp
      (measurable_id.pow_const 2) measurable_id
  have hΔ : MemLp (fun w ↦ B b w - B a w) 2 P :=
    C.isPreBrownian.isGaussianProcess.hasGaussianLaw_sub.memLp_two
  have hfactor := hindSq.integral_mul_eq_mul_integral
    hΔ.integrable_sq.aestronglyMeasurable
    (AEStronglyMeasurable.mono (𝓕.le a) hZY)
  have hout : inner ℝ (C.elementaryIntegralValue hab Z)
      (C.elementaryIntegralValue hab Y) =
        (∫ w, (B b w - B a w) ^ 2 ∂P) *
          ∫ w, (Z : W → ℝ) w * (Y : W → ℝ) w ∂P := by
    rw [L2.inner_def]
    calc
      ∫ w, ⟪C.elementaryIntegralValue hab Z w,
          C.elementaryIntegralValue hab Y w⟫_ℝ ∂P =
          ∫ w, (B b w - B a w) ^ 2 *
            ((Z : W → ℝ) w * (Y : W → ℝ) w) ∂P := by
        apply integral_congr_ae
        filter_upwards [C.coeFn_elementaryIntegralValue hab Z,
          C.coeFn_elementaryIntegralValue hab Y] with w hfirst hsecond
        rw [hfirst, hsecond]
        simp only [RCLike.inner_apply, conj_trivial]
        ring
      _ = (∫ w, (B b w - B a w) ^ 2 ∂P) *
          ∫ w, (Z : W → ℝ) w * (Y : W → ℝ) w ∂P := by
        simpa only [Pi.mul_apply] using hfactor
  have hinc : inner ℝ
      (brownianLp C.isPreBrownian b - brownianLp C.isPreBrownian a)
      (brownianLp C.isPreBrownian b - brownianLp C.isPreBrownian a) =
        inner ℝ (iocIndicator a b) (iocIndicator a b) := by
    rw [← wienerIntegral_indicatorConstLp_Ioc C.isPreBrownian hab,
      inner_wienerIntegral]
    rfl
  have hΔtime : (∫ w, (B b w - B a w) ^ 2 ∂P) =
      inner ℝ (iocIndicator a b) (iocIndicator a b) := by
    rw [← hinc, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (brownianLp C.isPreBrownian b)
      (brownianLp C.isPreBrownian a), coeFn_brownianLp C.isPreBrownian b,
      coeFn_brownianLp C.isPreBrownian a] with w hsub hb ha
    rw [hsub]
    simp only [Pi.sub_apply, RCLike.inner_apply, conj_trivial]
    rw [hb, ha]
    ring
  have hZYinner : (∫ w, (Z : W → ℝ) w * (Y : W → ℝ) w ∂P) =
      inner ℝ (Z : RandomL2 P) (Y : RandomL2 P) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards with w
    simp only [RCLike.inner_apply, conj_trivial]
    ring
  rw [hout, hΔtime, hZYinner]
  change inner ℝ (iocIndicator a b) (iocIndicator a b) *
      inner ℝ (Z : RandomL2 P) (Y : RandomL2 P) =
    inner ℝ (tensor (iocIndicator a b) (Z : RandomL2 P))
      (tensor (iocIndicator a b) (Y : RandomL2 P))
  rw [inner_tensor]
end ClarkOconeFamily
end Malliavin
