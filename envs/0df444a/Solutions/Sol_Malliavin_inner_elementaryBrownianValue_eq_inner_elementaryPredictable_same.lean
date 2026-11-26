-- Prove2me | solution 1 for Malliavin.inner_elementaryBrownianValue_eq_inner_elementaryPredictable_same
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:21:43.900664+00:00
-- url     : https://prove2.me/submissions/a02bca3b-5679-4c3e-80d3-bc4bd4be238a

import Definitions.Def_Malliavin_ClarkOcone
import Definitions.Def_Malliavin_ElementaryIto
import Theorems.Thm_Malliavin_elementaryBrownianValueLinear_apply
import Theorems.Thm_Malliavin_CameronMartin_covarianceMap_apply
import Theorems.Thm_Malliavin_CameronMartin_densityExponent_zero
import Theorems.Thm_Malliavin_CameronMartin_density_toReal
import Theorems.Thm_Malliavin_CameronMartin_density_zero
import Theorems.Thm_Malliavin_CameronMartin_expectationMap_apply
import Theorems.Thm_Malliavin_CameronMartin_inclusion_apply
import Theorems.Thm_Malliavin_CameronMartin_realDensity_zero
import Theorems.Thm_Malliavin_CameronMartin_translated_zero
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


attribute [local simp] Malliavin.elementaryBrownianValueLinear_apply

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
omit [CompleteSpace W] [BorelSpace W]
namespace Malliavin
theorem _root_.solution
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm)
    {a b : ℝ≥0} (hab : a ≤ b) (Z Y : lpMeas ℝ ℝ (𝓕 a) 2 P) :
    inner ℝ (elementaryBrownianValue hB hsm hnat hab Z)
      (elementaryBrownianValue hB hsm hnat hab Y) =
    inner ℝ (elementaryPredictable 𝓕 a b Z)
      (elementaryPredictable 𝓕 a b Y) := by
  have hZY : AEStronglyMeasurable[𝓕 a]
      (fun w ↦ (Z : W → ℝ) w * (Y : W → ℝ) w) P :=
    (lpMeas.aestronglyMeasurable Z).mul (lpMeas.aestronglyMeasurable Y)
  have hindSq : IndepFun (fun w ↦ (B b w - B a w) ^ 2)
      (fun w ↦ (Z : W → ℝ) w * (Y : W → ℝ) w) P :=
    (indep_increment_of_natural_adapted hB hsm hnat hab hZY).comp
      (measurable_id.pow_const 2) measurable_id
  have hΔ : MemLp (fun w ↦ B b w - B a w) 2 P :=
    hB.isGaussianProcess.hasGaussianLaw_sub.memLp_two
  have hfactor := hindSq.integral_mul_eq_mul_integral
    hΔ.integrable_sq.aestronglyMeasurable
    (AEStronglyMeasurable.mono (𝓕.le a) hZY)
  have hout : inner ℝ (elementaryBrownianValue hB hsm hnat hab Z)
      (elementaryBrownianValue hB hsm hnat hab Y) =
        (∫ w, (B b w - B a w) ^ 2 ∂P) *
          ∫ w, (Z : W → ℝ) w * (Y : W → ℝ) w ∂P := by
    rw [L2.inner_def]
    calc
      ∫ w, ⟪elementaryBrownianValue hB hsm hnat hab Z w,
          elementaryBrownianValue hB hsm hnat hab Y w⟫_ℝ ∂P =
          ∫ w, (B b w - B a w) ^ 2 *
            ((Z : W → ℝ) w * (Y : W → ℝ) w) ∂P := by
        apply integral_congr_ae
        filter_upwards [coeFn_elementaryBrownianValue hB hsm hnat hab Z,
          coeFn_elementaryBrownianValue hB hsm hnat hab Y] with w hfirst hsecond
        rw [hfirst, hsecond]
        simp only [RCLike.inner_apply, conj_trivial]
        ring
      _ = (∫ w, (B b w - B a w) ^ 2 ∂P) *
          ∫ w, (Z : W → ℝ) w * (Y : W → ℝ) w ∂P := by
        simpa only [Pi.mul_apply] using hfactor
  have hinc : inner ℝ (brownianLp hB b - brownianLp hB a)
      (brownianLp hB b - brownianLp hB a) =
        inner ℝ (iocIndicator a b) (iocIndicator a b) := by
    rw [← wienerIntegral_indicatorConstLp_Ioc hB hab, inner_wienerIntegral]
    rfl
  have hΔtime : (∫ w, (B b w - B a w) ^ 2 ∂P) =
      inner ℝ (iocIndicator a b) (iocIndicator a b) := by
    rw [← hinc, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (brownianLp hB b) (brownianLp hB a),
      coeFn_brownianLp hB b, coeFn_brownianLp hB a] with w hsub hb ha
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
end Malliavin
