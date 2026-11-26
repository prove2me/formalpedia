-- Prove2me | solution 1 for Malliavin.inner_elementaryPredictable_eq_zero_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:21:02.535216+00:00
-- url     : https://prove2.me/submissions/ef7042bf-ad9e-4ae9-bd02-a6e2e50c8942

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
import Theorems.Thm_Malliavin_elementaryPredictable_coeLp
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
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) {a b c d : ℝ≥0} (hbc : b ≤ c)
    (Z : lpMeas ℝ ℝ (𝓕 a) 2 P) (Y : lpMeas ℝ ℝ (𝓕 c) 2 P) :
    inner ℝ (elementaryPredictable 𝓕 a b Z) (elementaryPredictable 𝓕 c d Y) = 0 := by
  change inner ℝ (elementaryPredictable 𝓕 a b Z : TimeProcessL2 P)
    (elementaryPredictable 𝓕 c d Y : TimeProcessL2 P) = 0
  rw [elementaryPredictable_coeLp, elementaryPredictable_coeLp, L2.inner_def]
  apply integral_eq_zero_of_ae
  have habInd : ∀ᵐ p : ℝ≥0 × W ∂nonnegativeLebesgueMeasure.prod P,
      (iocIndicator a b : ℝ≥0 → ℝ) p.1 =
        (Set.Ioc a b).indicator (1 : ℝ≥0 → ℝ) p.1 :=
    Measure.quasiMeasurePreserving_fst.ae_eq_comp
      (indicatorConstLp_coeFn (p := 2) (hs := measurableSet_Ioc)
        (hμs := nonnegativeLebesgueMeasure_Ioc_ne_top a b) (c := (1 : ℝ)))
  have hcdInd : ∀ᵐ p : ℝ≥0 × W ∂nonnegativeLebesgueMeasure.prod P,
      (iocIndicator c d : ℝ≥0 → ℝ) p.1 =
        (Set.Ioc c d).indicator (1 : ℝ≥0 → ℝ) p.1 :=
    Measure.quasiMeasurePreserving_fst.ae_eq_comp
      (indicatorConstLp_coeFn (p := 2) (hs := measurableSet_Ioc)
        (hμs := nonnegativeLebesgueMeasure_Ioc_ne_top c d) (c := (1 : ℝ)))
  have hdisj : Disjoint (Set.Ioc a b) (Set.Ioc c d) := by
    rw [Set.Ioc_disjoint_Ioc]
    exact (min_le_left b d).trans (hbc.trans (le_max_right a c))
  filter_upwards [coeFn_tensor (iocIndicator a b) (Z : RandomL2 P),
    coeFn_tensor (iocIndicator c d) (Y : RandomL2 P), habInd, hcdInd]
    with p hfirst hsecond habp hcdp
  rw [hfirst, hsecond, habp, hcdp]
  simp only [RCLike.inner_apply, conj_trivial]
  by_cases hp : p.1 ∈ Set.Ioc a b
  · have hp' : p.1 ∉ Set.Ioc c d := Set.disjoint_left.mp hdisj hp
    simp only [hp', not_false_eq_true, Set.indicator_of_notMem, zero_mul, hp, Set.indicator_of_mem, Pi.one_apply,
      one_mul, Pi.zero_apply]
  · simp only [hp, not_false_eq_true, Set.indicator_of_notMem, zero_mul, mul_zero, Pi.zero_apply]
end Malliavin
