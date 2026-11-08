-- Prove2me | solution 1 for OAI.JointLogSeparation.difference_height_weight_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T10:23:39.905919+00:00
-- url     : https://prove2.me/submissions/4ad14d2a-2a9e-4856-abdf-c83f0f2f0f4f

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_TruncatedSecondTransfer
import Definitions.Def_OAI_NumberTheory_DirichletL_Fourier_LogDensity
import Theorems.Thm_OAI_JointLogSeparation_one_add_norm_sub_le

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
open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform
open OAI.JointLogSeparation
open FirstPassCubeLabels
namespace OAI.JointLogSeparation
theorem _root_.solution (x y z : ℝ) (J : ℕ) :
    (1+‖x-z‖)^J * (1+‖y-z‖)^J ≤
      (1+‖x‖)^(2*J) * (1+‖y‖)^(2*J) * (1+‖z‖)^(2*J) := by
  have hx := pow_le_pow_left₀ (by positivity : 0 ≤ 1+‖x-z‖) (one_add_norm_sub_le x z) J
  have hy := pow_le_pow_left₀ (by positivity : 0 ≤ 1+‖y-z‖) (one_add_norm_sub_le y z) J
  calc
    _ ≤ ((1+‖x‖)*(1+‖z‖))^J * ((1+‖y‖)*(1+‖z‖))^J :=
      mul_le_mul hx hy (by positivity) (by positivity)
    _ = (1+‖x‖)^J * (1+‖y‖)^J * (1+‖z‖)^(2*J) := by
      rw [mul_pow, mul_pow, two_mul, pow_add]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul
        (pow_le_pow_right₀ (by linarith [norm_nonneg x] : 1 ≤ 1+‖x‖) (by omega : J ≤ 2*J))
        (pow_le_pow_right₀ (by linarith [norm_nonneg y] : 1 ≤ 1+‖y‖) (by omega : J ≤ 2*J))
        (by positivity) (by positivity)
end OAI.JointLogSeparation
