-- Prove2me | solution 1 for OAI.CubicEisenstein.kernelLocalizedH1_graph_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T20:08:17.765742+00:00
-- url     : https://prove2.me/submissions/fa05b158-36d7-4e1b-a856-652993ea5eb3

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_LocalCutoffs
import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_HarmonicAggregation
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_PaddedPassage
import Theorems.Thm_OAI_CubicEisenstein_kernelLocalizedH1_bounded
import Theorems.Thm_OAI_CubicEisenstein_kernelEnergyGraphCore_norm_sq

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
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical SchwartzMap ContDiff
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff
open OAI.CubicEisenstein
namespace OAI.CubicEisenstein
theorem _root_.solution (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func)) :
    ∃C : ℝ,∀f : kernelSmoothTests,
      ‖kernelLocalizedH1Linear χ f‖≤C*‖kernelEnergyGraphCore f‖ := by
  obtain ⟨C,hC,hbound⟩ := kernelLocalizedH1_bounded χ hinj
  refine ⟨Real.sqrt C,fun f => ?_⟩
  have hh := hbound f
  rw [←kernelEnergyGraphCore_norm_sq] at hh
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg C) (norm_nonneg _))).mp
  change ‖kernelLocalizedH1 χ f‖^2≤(Real.sqrt C*‖kernelEnergyGraphCore f‖)^2
  rw [mul_pow,Real.sq_sqrt hC]
  exact hh
end OAI.CubicEisenstein
