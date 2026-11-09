-- Prove2me | solution 1 for OAI.CubicEisenstein.cusp_chart_memLp_of_vertical
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-08T20:11:18.271169+00:00
-- url     : https://prove2.me/submissions/b761cbb1-07e4-4a67-beb1-4694271a8149

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_PrincipalDensity
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_CuspCoercivity
import Theorems.Thm_OAI_CubicEisenstein_cusp_chart_vertical_coercivity
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
    (hDiff : ∀z : ℝ×ℝ,∀v∈Set.Ici a,DifferentiableAt ℝ (fun t => F (z,t)) v)
    (hEnergy : MemLp (cuspVerticalVelocity F) 2 (cuspChartVolume a)) :
    MemLp F 2 (cuspChartVolume a) := by
  have hV : Continuous (cuspVerticalVelocity F) := by
    unfold cuspVerticalVelocity
    fun_prop
  have hEi := (memLp_two_iff_integrable_sq_norm hV.aestronglyMeasurable).mp hEnergy
  have hEfin := (hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall (fun q => sq_nonneg ‖cuspVerticalVelocity F q‖))).mp hEi.2
  apply (memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable).mpr
  refine ⟨(hF.norm.pow 2).aestronglyMeasurable,?_⟩
  apply (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (fun q => sq_nonneg ‖F q‖))).mpr
  exact (cusp_chart_vertical_coercivity F a ha hF hD hFa hDiff).trans_lt hEfin
end OAI.CubicEisenstein
