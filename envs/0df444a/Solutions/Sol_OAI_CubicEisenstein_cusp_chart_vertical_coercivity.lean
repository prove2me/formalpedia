-- Prove2me | solution 1 for OAI.CubicEisenstein.cusp_chart_vertical_coercivity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-08T20:05:51.162583+00:00
-- url     : https://prove2.me/submissions/072d2dfe-6b70-4f16-aa7f-c424323cd740

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_PrincipalDensity
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_CuspCoercivity
import Theorems.Thm_OAI_CubicEisenstein_cusp_hardy_halfline_lintegral
import Theorems.Thm_OAI_CubicEisenstein_cusp_weight_mass_identity
import Theorems.Thm_OAI_CubicEisenstein_cusp_weight_velocity_identity
import Theorems.Thm_OAI_CubicEisenstein_quadraticHeightDenominator_continuous
attribute [local fun_prop] OAI.CubicEisenstein.quadraticHeightDenominator_continuous



set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators Classical
open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace
open OAI.CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace ENNReal
namespace OAI.CubicEisenstein
theorem _root_.solution (F : CuspChartCoordinates → ℂ) (a : ℝ)
    (ha : 0<a) (hF : Continuous F) (hD : Continuous (cuspVerticalDerivative F))
    (hFa : ∀z : ℝ×ℝ,F (z,a)=0)
    (hDiff : ∀z : ℝ×ℝ,∀v∈Set.Ici a,DifferentiableAt ℝ (fun t => F (z,t)) v) :
    (∫⁻q,ENNReal.ofReal (‖F q‖^2) ∂cuspChartVolume a)≤
      ∫⁻q,ENNReal.ofReal (‖cuspVerticalVelocity F q‖^2) ∂cuspChartVolume a := by
  have hw : Measurable (fun q : CuspChartCoordinates => ENNReal.ofReal ((q.2^3)⁻¹)) := by
    fun_prop
  have hFm : Measurable (fun q : CuspChartCoordinates => ENNReal.ofReal (‖F q‖^2)) := by fun_prop
  have hVm : Measurable (fun q : CuspChartCoordinates => ENNReal.ofReal (‖cuspVerticalVelocity F q‖^2)) := by
    unfold cuspVerticalVelocity
    fun_prop
  unfold cuspChartVolume
  rw [lintegral_withDensity_eq_lintegral_mul _ hw hFm,
    lintegral_withDensity_eq_lintegral_mul _ hw hVm,
    lintegral_prod _ ((hw.mul hFm).aemeasurable),
    lintegral_prod _ ((hw.mul hVm).aemeasurable)]
  apply lintegral_mono
  intro z
  calc
    _ = ∫⁻v in Set.Ioi a,ENNReal.ofReal (‖F (z,v)‖^2/v^3) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      exact cusp_weight_mass_identity _ _ (ha.trans hv)
    _ ≤ ∫⁻v in Set.Ioi a,ENNReal.ofReal (‖deriv (fun t => F (z,t)) v‖^2/v) := by
      apply cusp_hardy_halfline_lintegral _ a ha (hFa z) (hDiff z)
      exact (hD.comp (continuous_const.prodMk continuous_id)).continuousOn
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      exact (cusp_weight_velocity_identity _ _ (ha.trans hv)).symm
end OAI.CubicEisenstein
