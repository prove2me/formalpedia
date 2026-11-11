-- Prove2me | solution 1 for OAI.CubicEisenstein.kernelCuspHeightFourier_uniform_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T20:19:19.392756+00:00
-- url     : https://prove2.me/submissions/e5484e24-87a2-4211-986c-c28e7efc21e3

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_GaussFactorization
import Definitions.Def_OAI_NumberTheory_DirichletL_Reciprocity_KubotaCharacter
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_ResidualFourierBounds
import Theorems.Thm_OAI_CubicEisenstein_cuspPeriodStripFiniteVolume


set_option autoImplicit false
open OAI
noncomputable section
open OAI.CubicEisenstein
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
open scoped BigOperators Classical
open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace ENNReal
open Finset AddChar MulChar EisensteinEmbedding
local notation "O" => ActualEisensteinCubic.O
namespace OAI.CubicEisenstein
theorem _root_.solution (a b : ℝ) (ha : 0<a) :
    ∃C : ℝ,0≤C ∧ ∀(ρ : BoundedContinuousFunction ℝ ℂ)(h : ActualEisensteinCubic.O)(F : KernelQuotientL2),
      ‖kernelCuspHeightFourier a b ha ρ h F‖≤C*‖ρ‖*‖F‖ := by
  let := cuspPeriodStripFiniteVolume a b ha
  let mass : ℝ := (measureUnivNNReal (hyperbolicVolume.restrict (cuspPeriodStrip a b)):ℝ)^((2:ℝ≥0∞).toReal)⁻¹
  have hmass : 0≤mass := Real.rpow_nonneg (by positivity) _
  refine ⟨mass*‖kernelCuspHeightPullback a b ha‖,mul_nonneg hmass (norm_nonneg _),?_⟩
  intro ρ h F
  have htest : ‖cuspHeightFourierTestL2 a b ha ρ h‖≤mass*‖ρ‖ := by
    apply Lp.norm_le_of_ae_bound (norm_nonneg ρ)
    filter_upwards [MemLp.coeFn_toLp (cuspHeightFourierTest_memLp a b ha ρ h)] with w hw
    change ‖cuspHeightFourierTestL2 a b ha ρ h w‖≤‖ρ‖
    rw [cuspHeightFourierTestL2,hw,norm_star]
    exact cuspWeightedFourierPhase_bound ρ h w
  change ‖inner ℂ (cuspHeightFourierTestL2 a b ha ρ h) (kernelCuspHeightPullback a b ha F)‖≤_
  calc
    _ ≤ ‖cuspHeightFourierTestL2 a b ha ρ h‖*‖kernelCuspHeightPullback a b ha F‖ := norm_inner_le_norm _ _
    _ ≤ (mass*‖ρ‖)*(‖kernelCuspHeightPullback a b ha‖*‖F‖) :=
      mul_le_mul htest ((kernelCuspHeightPullback a b ha).le_opNorm F) (norm_nonneg _)
        (mul_nonneg hmass (norm_nonneg _))
    _ = _ := by ring
end OAI.CubicEisenstein
