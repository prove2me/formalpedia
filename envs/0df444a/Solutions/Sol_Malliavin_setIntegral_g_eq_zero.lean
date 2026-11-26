-- Prove2me | solution 1 for Malliavin.setIntegral_g_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:44:40.613985+00:00
-- url     : https://prove2.me/submissions/ce642bb1-4270-4f93-82d7-5880d98c2e7d

import Definitions.Def_Malliavin_ClarkOcone
import Definitions.Def_Malliavin_WienerChaos
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.ConditionalExpectation
import Definitions.Def_Malliavin_PointwiseCondExp
import Theorems.Thm_Malliavin_setIntegral_timeSection_sub_eq_zero
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



set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›)
omit [CompleteSpace W] [BorelSpace W]
namespace Malliavin
theorem _root_.solution (U : TimeProcessL2 P) {a : ℝ≥0} {A : Set W}
    (hA : MeasurableSet[𝓕 a] A) (D : TimeProcessL2 P)
    (hD : (D : ℝ≥0 × W → ℝ) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      fun x ↦ (predictableProjection 𝓕 U : ℝ≥0 × W → ℝ) x - U x)
    (b : ℝ≥0) {s : Set ℝ≥0} (hs : MeasurableSet s) :
    ∫ t in s, (∫ ω in A, (D : ℝ≥0 × W → ℝ) (t, ω) ∂P)
      ∂(nonnegativeLebesgueMeasure.restrict (Set.Ioc a b)) = 0 := by
  set g : ℝ≥0 → ℝ := fun t ↦ ∫ ω in A, (D : ℝ≥0 × W → ℝ) (t, ω) ∂P with hg
  have hrect : (nonnegativeLebesgueMeasure.prod P) (Set.Ioc a b ×ˢ A) ≠ ∞ := by
    rw [Measure.prod_prod]
    exact ENNReal.mul_ne_top measure_Ioc_lt_top.ne (measure_lt_top P A).ne
  have hDint := integrableOn_Lp_of_measure_ne_top D fact_one_le_two_ennreal.elim hrect
  have hgint : Integrable g (nonnegativeLebesgueMeasure.restrict (Set.Ioc a b)) := by
    have h1 : Integrable (D : ℝ≥0 × W → ℝ)
        ((nonnegativeLebesgueMeasure.restrict (Set.Ioc a b)).prod (P.restrict A)) := by
      rw [Measure.prod_restrict]
      exact hDint
    exact h1.integral_prod_left
  -- the property holds on the generating π-system of intervals
  have hbase : ∀ c d : ℝ≥0, ∫ t in Set.Ioc c d, g t
      ∂(nonnegativeLebesgueMeasure.restrict (Set.Ioc a b)) = 0 := by
    intro c d
    rw [Measure.restrict_restrict measurableSet_Ioc, Set.Ioc_inter_Ioc]
    exact setIntegral_timeSection_sub_eq_zero 𝓕 U hA D hD (le_max_right c a)
  -- extend to all measurable sets
  induction s, hs using MeasurableSpace.induction_on_inter
    (m := (inferInstance : MeasurableSpace ℝ≥0))
    (s := { S : Set ℝ≥0 | ∃ l u : ℝ≥0, l < u ∧ Set.Ioc l u = S })
    (h_eq := BorelSpace.measurable_eq.trans (borel_eq_generateFrom_Ioc ℝ≥0))
    (h_inter := isPiSystem_Ioc (id : ℝ≥0 → ℝ≥0) (id : ℝ≥0 → ℝ≥0)) with
  | empty => simp
  | basic s hs =>
      obtain ⟨c, d, -, rfl⟩ := hs
      exact hbase c d
  | compl s hs hind =>
      have htotal : ∫ t, g t ∂(nonnegativeLebesgueMeasure.restrict (Set.Ioc a b)) = 0 := by
        have := hbase a b
        rwa [Measure.restrict_restrict measurableSet_Ioc, Set.inter_self] at this
      have hsplit := integral_add_compl hs hgint
      rw [hind, zero_add] at hsplit
      rw [hsplit, htotal]
  | iUnion f hdis hmeas hind =>
      rw [integral_iUnion hmeas hdis hgint.integrableOn]
      simp only [hind, tsum_zero]
end Malliavin
