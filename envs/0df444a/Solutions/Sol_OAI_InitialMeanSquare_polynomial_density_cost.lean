-- Prove2me | solution 1 for OAI.InitialMeanSquare.polynomial_density_cost
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T15:23:40.318783+00:00
-- url     : https://prove2.me/submissions/b3f961a9-c766-4274-9b26-11dfe185bf4f

import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_ReflectedDyadicSeries
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_BranchScaling
import Theorems.Thm_OAI_InitialMeanSquare_positive_nested_density_bound
import Theorems.Thm_OAI_FirstPassCubeLabels_firstLogDensity_nonneg
import Theorems.Thm_OAI_JointLogSeparation_density_weight_identity


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
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open OAI.InitialMeanSquare
open MeasureTheory
open scoped BigOperators Classical
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels
namespace OAI.InitialMeanSquare
theorem _root_.solution (B G : Frequency → ℝ) (J : ℕ) (S C E : ℝ)
    (hS : 0 < S) (hC : 0 ≤ C) (_hE : 0 ≤ E)
    (hB : ∀ q, 0 ≤ B q) (hG : ∀ q, 0 ≤ G q)
    (hdec : ∀ q, S*B q ≤ C*firstLogDensity J q.1*firstLogDensity J q.2.1*firstLogDensity J q.2.2)
    (henergy : ∀ q, G q ≤ E*(1+‖q.1‖)^J*(1+‖q.2.1‖)^J*(1+‖q.2.2‖)^J) :
    (∫ x : ℝ, ∫ y : ℝ, ∫ z : ℝ,B (x,y,z)*G (x,y,z)) ≤
      (C*E/S)*(∫ t : ℝ,firstLogDensity 0 t)^3 := by
  apply positive_nested_density_bound _ (C*E/S)
    (fun q => mul_nonneg (hB q) (hG q))
  intro q
  have hc : 0 ≤ C*firstLogDensity J q.1*firstLogDensity J q.2.1*firstLogDensity J q.2.2 := by
    exact mul_nonneg (mul_nonneg (mul_nonneg hC (firstLogDensity_nonneg _ _))
      (firstLogDensity_nonneg _ _)) (firstLogDensity_nonneg _ _)
  have hb := mul_le_mul (hdec q) (henergy q) (hG q) hc
  have heq :
      (C*firstLogDensity J q.1*firstLogDensity J q.2.1*firstLogDensity J q.2.2)*
        (E*(1+‖q.1‖)^J*(1+‖q.2.1‖)^J*(1+‖q.2.2‖)^J) =
      C*E*firstLogDensity 0 q.1*firstLogDensity 0 q.2.1*firstLogDensity 0 q.2.2 := by
    rw [←density_weight_identity J q.1,←density_weight_identity J q.2.1,
      ←density_weight_identity J q.2.2]
    ring
  rw [heq] at hb
  calc
    _ ≤ (C*E*firstLogDensity 0 q.1*firstLogDensity 0 q.2.1*firstLogDensity 0 q.2.2)/S := by
      apply (le_div_iff₀ hS).mpr
      convert hb using 1 ; ring
    _ = _ := by ring
end OAI.InitialMeanSquare
