-- Prove2me | solution 1 for Malliavin.inner_elementaryBrownianValue_eq_zero_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:30:59.63481+00:00
-- url     : https://prove2.me/submissions/7932be6b-0bfe-4cc4-9311-9ac43b1fb2cb

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
omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P]
namespace Malliavin
theorem _root_.solution
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm)
    {a b c d : ℝ≥0} (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (Z : lpMeas ℝ ℝ (𝓕 a) 2 P) (Y : lpMeas ℝ ℝ (𝓕 c) 2 P) :
    inner ℝ (elementaryBrownianValue hB hsm hnat hab Z)
      (elementaryBrownianValue hB hsm hnat hcd Y) = 0 := by
  have hac : a ≤ c := hab.trans hbc
  have hBadapted : StronglyAdapted 𝓕 B := by
    rw [hnat]
    exact Filtration.stronglyAdapted_natural hsm
  have hZc : AEStronglyMeasurable[𝓕 c] (Z : W → ℝ) P :=
    AEStronglyMeasurable.mono (𝓕.mono hac) (lpMeas.aestronglyMeasurable Z)
  have hYc : AEStronglyMeasurable[𝓕 c] (Y : W → ℝ) P :=
    lpMeas.aestronglyMeasurable Y
  have hΔabc : AEStronglyMeasurable[𝓕 c] (fun w ↦ B b w - B a w) P :=
    ((hBadapted.stronglyMeasurable_le hbc).sub
      (hBadapted.stronglyMeasurable_le hac)).aestronglyMeasurable
  have hG : AEStronglyMeasurable[𝓕 c]
      (fun w ↦ ((Z : W → ℝ) w * (B b w - B a w)) * (Y : W → ℝ) w) P :=
    (hZc.mul hΔabc).mul hYc
  have hind := indep_increment_of_natural_adapted hB hsm hnat hcd hG
  have hΔcd : AEStronglyMeasurable (fun w ↦ B d w - B c w) P :=
    hB.isGaussianProcess.hasGaussianLaw_sub.memLp_two.aestronglyMeasurable
  have hGamb : AEStronglyMeasurable
      (fun w ↦ ((Z : W → ℝ) w * (B b w - B a w)) * (Y : W → ℝ) w) P :=
    AEStronglyMeasurable.mono (𝓕.le c) hG
  have hfactor := hind.integral_mul_eq_mul_integral hΔcd hGamb
  rw [L2.inner_def]
  calc
    ∫ w, ⟪elementaryBrownianValue hB hsm hnat hab Z w,
        elementaryBrownianValue hB hsm hnat hcd Y w⟫_ℝ ∂P =
        ∫ w, (B d w - B c w) *
          (((Z : W → ℝ) w * (B b w - B a w)) * (Y : W → ℝ) w) ∂P := by
      apply integral_congr_ae
      filter_upwards [coeFn_elementaryBrownianValue hB hsm hnat hab Z,
        coeFn_elementaryBrownianValue hB hsm hnat hcd Y] with w hfirst hsecond
      rw [hfirst, hsecond]
      simp only [RCLike.inner_apply, conj_trivial]
      ring
    _ = (∫ w, B d w - B c w ∂P) *
        ∫ w, ((Z : W → ℝ) w * (B b w - B a w)) * (Y : W → ℝ) w ∂P := by
      simpa only [Pi.mul_apply] using hfactor
    _ = 0 := by
      rw [integral_sub (hB.integrable_eval d) (hB.integrable_eval c),
        hB.integral_eval, hB.integral_eval, sub_zero, zero_mul]
end Malliavin
