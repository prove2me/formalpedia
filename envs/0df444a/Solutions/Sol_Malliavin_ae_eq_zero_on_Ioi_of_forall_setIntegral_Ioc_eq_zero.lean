-- Prove2me | solution 1 for Malliavin.ae_eq_zero_on_Ioi_of_forall_setIntegral_Ioc_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:43:43.486769+00:00
-- url     : https://prove2.me/submissions/2779fe56-3dfd-4df3-a3a5-be0ab897bf17

import Definitions.Def_Malliavin_ClarkOcone
import Definitions.Def_Malliavin_WienerChaos
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.ConditionalExpectation
import Definitions.Def_Malliavin_PointwiseCondExp
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
theorem _root_.solution {h : ℝ≥0 → ℝ} {a : ℝ≥0}
    (hloc : ∀ b : ℝ≥0, IntegrableOn h (Set.Ioc a b) nonnegativeLebesgueMeasure)
    (hzero : ∀ c d : ℝ≥0, a ≤ c →
      ∫ t in Set.Ioc c d, h t ∂nonnegativeLebesgueMeasure = 0) :
    ∀ᵐ t ∂nonnegativeLebesgueMeasure, a < t → h t = 0 := by
  have hwin : ∀ n : ℕ, ∀ᵐ t ∂nonnegativeLebesgueMeasure,
      t ∈ Set.Ioc a (a + (n + 1 : ℕ)) → h t = 0 := by
    intro n
    refine ae_imp_of_ae_restrict ?_
    set ν := nonnegativeLebesgueMeasure.restrict (Set.Ioc a (a + (n + 1 : ℕ))) with hν
    have hbase : ∀ c d : ℝ≥0, ∫ t in Set.Ioc c d, h t ∂ν = 0 := by
      intro c d
      rw [hν, Measure.restrict_restrict measurableSet_Ioc, Set.Ioc_inter_Ioc]
      exact hzero _ _ (le_max_right c a)
    have hint : Integrable h ν := hloc _
    have hall : ∀ s : Set ℝ≥0, MeasurableSet s → ∫ t in s, h t ∂ν = 0 := by
      intro s hs
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
          have htotal : ∫ t, h t ∂ν = 0 := by
            have := hbase a (a + (n + 1 : ℕ))
            rwa [hν, Measure.restrict_restrict measurableSet_Ioc, Set.inter_self] at this
          have hsplit := integral_add_compl hs hint
          rw [hind, zero_add] at hsplit
          rw [hsplit, htotal]
      | iUnion f hdis hmeas hind =>
          rw [integral_iUnion hmeas hdis hint.integrableOn]
          simp only [hind, tsum_zero]
    exact ae_eq_zero_of_forall_setIntegral_eq_of_sigmaFinite
      (fun s hs _ ↦ hint.integrableOn) (fun s hs _ ↦ hall s hs)
  have hwin' := ae_all_iff.mpr hwin
  filter_upwards [hwin'] with t hwt hat
  obtain ⟨n, hn⟩ := exists_nat_ge (t - a)
  refine hwt n ⟨hat, ?_⟩
  have : t - a ≤ (n + 1 : ℕ) := hn.trans (by exact_mod_cast Nat.le_succ n)
  calc t = a + (t - a) := by rw [add_tsub_cancel_of_le hat.le]
    _ ≤ a + (n + 1 : ℕ) := by gcongr
end Malliavin
