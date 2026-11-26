-- Prove2me | solution 1 for Malliavin.integral_set_eq_zero_of_rectangles
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:34:06.831005+00:00
-- url     : https://prove2.me/submissions/6c2a762a-19e3-4a73-98b5-9c72fb81299b

import Definitions.Def_Malliavin_ClarkOcone
import Definitions.Def_Malliavin_PredictableDensity
import Theorems.Thm_Malliavin_integral_restrict_frame_eq_zero_of_rectangles
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
open MeasureTheory ProbabilityTheory Filter Topology Function
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5
noncomputable section
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
omit [CompleteSpace W] [BorelSpace W]
namespace Malliavin
theorem _root_.solution
    (𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace W))
    (g : PredictableProcessL2 𝓕 P)
    (hrect : ∀ R ∈ predictableRectangle 𝓕,
      ∫ z in R, (g : ℝ≥0 × W → ℝ) z
        ∂nonnegativeLebesgueMeasure.prod P = 0)
    (s : Set (ℝ≥0 × W)) (hs : MeasurableSet[𝓕.predictable] s)
    (hμs : (nonnegativeLebesgueMeasure.prod P) s < ∞) :
    ∫ z in s, (g : ℝ≥0 × W → ℝ) z
      ∂nonnegativeLebesgueMeasure.prod P = 0 := by
  let μ₀ := nonnegativeLebesgueMeasure.prod P
  let Φ : ℕ → Set (ℝ≥0 × W) :=
    fun n ↦ Set.Ioc 0 ((n : ℝ≥0) + 1) ×ˢ Set.univ
  have hΦmeas : ∀ n, MeasurableSet (Φ n) :=
    fun _ ↦ measurableSet_Ioc.prod MeasurableSet.univ
  have hΦmono : Monotone Φ := by
    intro n m hnm z hz
    refine ⟨⟨hz.1.1, ?_⟩, hz.2⟩
    apply le_trans hz.1.2
    gcongr
  have hzero : ∀ n,
      ∫ z in s ∩ Φ n, (g : ℝ≥0 × W → ℝ) z ∂μ₀ = 0 := by
    intro n
    have hn := integral_restrict_frame_eq_zero_of_rectangles 𝓕 g hrect n s hs
    have heq : ∫ z in s, (g : ℝ≥0 × W → ℝ) z ∂μ₀.restrict (Φ n) =
        ∫ z in s ∩ Φ n, (g : ℝ≥0 × W → ℝ) z ∂μ₀ := by
      rw [show ∫ z in s, (g : ℝ≥0 × W → ℝ) z ∂μ₀.restrict (Φ n) =
          ∫ z, (g : ℝ≥0 × W → ℝ) z
            ∂((μ₀.restrict (Φ n)).restrict s) from rfl,
        Measure.restrict_restrict (predictable_le_prod 𝓕 s hs)]
    exact heq ▸ hn
  have hint : IntegrableOn (g : ℝ≥0 × W → ℝ) s μ₀ :=
    integrableOn_Lp_of_measure_ne_top (g : TimeProcessL2 P) one_le_two hμs.ne
  have htend := tendsto_setIntegral_of_monotone
    (fun n ↦ (predictable_le_prod 𝓕 s hs).inter (hΦmeas n))
    (fun _ _ hnm ↦ Set.inter_subset_inter_right _ (hΦmono hnm))
    (hint.mono_set (Set.iUnion_subset fun _ ↦ Set.inter_subset_left))
  have hzeroUnion :
      ∫ z in ⋃ n, s ∩ Φ n, (g : ℝ≥0 × W → ℝ) z ∂μ₀ = 0 := by
    apply tendsto_nhds_unique htend
    simpa only [hzero] using (tendsto_const_nhds :
      Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 0))
  have hbotnull : μ₀ ({(0 : ℝ≥0)} ×ˢ (Set.univ : Set W)) = 0 := by
    rw [Measure.prod_prod, measure_singleton, zero_mul]
  have hpositive : {z : ℝ≥0 × W | z.1 ≠ 0} ∈ ae μ₀ := by
    rw [show {z : ℝ≥0 × W | z.1 ≠ 0} =
        ({(0 : ℝ≥0)} ×ˢ (Set.univ : Set W))ᶜ by ext ⟨t, w⟩; simp]
    exact compl_mem_ae_iff.mpr hbotnull
  have hcov : ∀ᵐ z ∂μ₀, z ∈ ⋃ n, Φ n := by
    filter_upwards [hpositive] with z hz
    obtain ⟨t, w⟩ := z
    obtain ⟨n, hn⟩ := exists_nat_ge (t : ℝ≥0)
    refine Set.mem_iUnion.mpr ⟨n, ?_⟩
    exact ⟨⟨pos_iff_ne_zero.mpr hz,
      le_trans hn (le_add_of_nonneg_right zero_le_one)⟩, Set.mem_univ w⟩
  have hset : s =ᵐ[μ₀] ⋃ n, s ∩ Φ n := by
    filter_upwards [hcov] with z hz
    apply propext
    constructor
    · intro hzs
      obtain ⟨n, hzn⟩ := Set.mem_iUnion.mp hz
      exact Set.mem_iUnion.mpr ⟨n, hzs, hzn⟩
    · intro hzunion
      obtain ⟨n, hzs, _hzn⟩ := Set.mem_iUnion.mp hzunion
      exact hzs
  exact (setIntegral_congr_set hset).trans hzeroUnion
end Malliavin
