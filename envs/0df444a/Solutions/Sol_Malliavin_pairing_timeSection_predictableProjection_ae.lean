-- Prove2me | solution 1 for Malliavin.pairing_timeSection_predictableProjection_ae
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:55:12.599383+00:00
-- url     : https://prove2.me/submissions/4720e4ad-4cf4-44ab-864d-292b7096b754

import Definitions.Def_Malliavin_ClarkOcone
import Definitions.Def_Malliavin_WienerChaos
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.ConditionalExpectation
import Definitions.Def_Malliavin_PointwiseCondExp
import Theorems.Thm_Malliavin_ae_eq_zero_on_Ioi_of_forall_setIntegral_Ioc_eq_zero
import Theorems.Thm_Malliavin_inner_tensor_iocIndicator
import Theorems.Thm_Malliavin_inner_predictableProjection_sub
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
theorem _root_.solution (U : TimeProcessL2 P) (a : ℝ≥0)
    (Z : lpMeas ℝ ℝ (𝓕 a) 2 P) :
    ∀ᵐ t ∂nonnegativeLebesgueMeasure, a < t →
      ∫ ω, ((predictableProjection 𝓕 U : ℝ≥0 × W → ℝ) (t, ω) - U (t, ω))
        * (Z : Lp ℝ 2 P) ω ∂P = 0 := by
  set D : TimeProcessL2 P := (predictableProjection 𝓕 U : TimeProcessL2 P) - U with hDdef
  have hZmeas : AEStronglyMeasurable[𝓕 a] ((Z : Lp ℝ 2 P) : W → ℝ) P :=
    lpMeas.aestronglyMeasurable Z
  -- interval integrals of the pairing function vanish
  have hzero : ∀ c d : ℝ≥0, a ≤ c →
      ∫ t in Set.Ioc c d, (∫ ω, (D : ℝ≥0 × W → ℝ) (t, ω) * (Z : Lp ℝ 2 P) ω ∂P)
        ∂nonnegativeLebesgueMeasure = 0 := by
    intro c d hac
    rw [← inner_tensor_iocIndicator D c d (Z : Lp ℝ 2 P)]
    have hZc : (Z : Lp ℝ 2 P) ∈ lpMeas ℝ ℝ (𝓕 c) 2 P :=
      mem_lpMeas_iff_aestronglyMeasurable.mpr
        ⟨hZmeas.mk _, hZmeas.stronglyMeasurable_mk.mono (𝓕.mono hac), hZmeas.ae_eq_mk⟩
    have hcoe := elementaryPredictable_coeLp 𝓕 c d ⟨(Z : Lp ℝ 2 P), hZc⟩
    rw [← hcoe]
    exact inner_predictableProjection_sub 𝓕 U _
  -- local integrability of the pairing function
  have hloc : ∀ b : ℝ≥0,
      IntegrableOn (fun t ↦ ∫ ω, (D : ℝ≥0 × W → ℝ) (t, ω) * (Z : Lp ℝ 2 P) ω ∂P)
        (Set.Ioc a b) nonnegativeLebesgueMeasure := by
    intro b
    set T : TimeProcessL2 P := tensor (iocIndicator a b) (Z : Lp ℝ 2 P) with hT
    have hint : Integrable (fun p : ℝ≥0 × W ↦ (D : ℝ≥0 × W → ℝ) p * (T : ℝ≥0 × W → ℝ) p)
        (nonnegativeLebesgueMeasure.prod P) := by
      have := L2.integrable_inner (𝕜 := ℝ) D T
      simpa [RCLike.inner_apply, conj_trivial, mul_comm] using this
    have hH : Integrable (fun t ↦ ∫ ω, (D : ℝ≥0 × W → ℝ) (t, ω) * (T : ℝ≥0 × W → ℝ) (t, ω) ∂P)
        nonnegativeLebesgueMeasure := hint.integral_prod_left
    have hTfn : (T : ℝ≥0 × W → ℝ) =ᵐ[nonnegativeLebesgueMeasure.prod P]
        fun p ↦ (Set.Ioc a b).indicator (1 : ℝ≥0 → ℝ) p.1 * (Z : Lp ℝ 2 P) p.2 := by
      have hg : ∀ᵐ p : ℝ≥0 × W ∂nonnegativeLebesgueMeasure.prod P,
          (iocIndicator a b : ℝ≥0 → ℝ) p.1 = (Set.Ioc a b).indicator (1 : ℝ≥0 → ℝ) p.1 :=
        Measure.quasiMeasurePreserving_fst.ae_eq_comp
          (indicatorConstLp_coeFn (p := 2) (hs := measurableSet_Ioc)
            (hμs := nonnegativeLebesgueMeasure_Ioc_ne_top a b) (c := (1 : ℝ)))
      filter_upwards [coeFn_tensor (iocIndicator a b) (Z : Lp ℝ 2 P), hg] with p hp hg'
      rw [hp, hg']
    have hsec := Measure.ae_ae_of_ae_prod hTfn
    refine (hH.restrict (s := Set.Ioc a b)).congr ?_
    have hsec' : ∀ᵐ t ∂nonnegativeLebesgueMeasure.restrict (Set.Ioc a b),
        (fun ω ↦ (T : ℝ≥0 × W → ℝ) (t, ω)) =ᵐ[P]
          fun ω ↦ (Set.Ioc a b).indicator (1 : ℝ≥0 → ℝ) t * (Z : Lp ℝ 2 P) ω :=
      ae_restrict_of_ae hsec
    filter_upwards [hsec', ae_restrict_mem measurableSet_Ioc] with t hst htmem
    have hind : (Set.Ioc a b).indicator (1 : ℝ≥0 → ℝ) t = 1 := by
      simp only [htmem, Set.indicator_of_mem, Pi.one_apply]
    refine integral_congr_ae (hst.mono fun ω hω ↦ ?_)
    dsimp only at hω ⊢
    rw [hω, hind, one_mul]
  have h0 := ae_eq_zero_on_Ioi_of_forall_setIntegral_Ioc_eq_zero hloc hzero
  have hDsec := Measure.ae_ae_of_ae_prod
    (Lp.coeFn_sub (predictableProjection 𝓕 U : TimeProcessL2 P) U)
  filter_upwards [h0, hDsec] with t h0t hst hat
  rw [← h0t hat]
  refine integral_congr_ae (hst.mono fun ω hω ↦ ?_)
  dsimp only at hω ⊢
  rw [hω]
  simp only [mul_comm, Pi.sub_apply]
end Malliavin
