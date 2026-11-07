-- Prove2me | solution 1 for OAI.TwoPassProfiles.first_profile_logshape
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:54:04.71744+00:00
-- url     : https://prove2.me/submissions/1da0c31f-2d07-4b16-9e08-34a5b445d16b

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_CompactScale
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_CompactWeights

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
open OAI.TwoPassProfiles
namespace OAI.TwoPassProfiles
theorem _root_.solution
    (K y d f E t c x₁ x₂ : ℝ)
    (hK : 0 < K) (hy : 0 < y) (hd : 0 < d)
    (hf : 0 < f) (hE : 0 < E) (ht : 0 < t)
    (hc : 0 < c) (hx₁ : 0 < x₁) (hx₂ : 0 < x₂) :
    Real.log (K * y / (d * f ^ 2 * E * t ^ 2 * c * x₁ * x₂)) =
      Real.log K + Real.log y - Real.log d -
      2 * Real.log f - Real.log E - 2 * Real.log t -
      Real.log c - Real.log x₁ - Real.log x₂ := by
  have hden : 0 < d * f ^ 2 * E * t ^ 2 * c * x₁ * x₂ := by positivity
  rw [Real.log_div (by positivity) (ne_of_gt hden)]
  rw [Real.log_mul (ne_of_gt hK) (ne_of_gt hy)]
  rw [Real.log_mul (ne_of_gt (by positivity : 0 < d * f ^ 2 * E * t ^ 2 * c * x₁)) (ne_of_gt hx₂)]
  rw [Real.log_mul (ne_of_gt (by positivity : 0 < d * f ^ 2 * E * t ^ 2 * c)) (ne_of_gt hx₁)]
  rw [Real.log_mul (ne_of_gt (by positivity : 0 < d * f ^ 2 * E * t ^ 2)) (ne_of_gt hc)]
  rw [Real.log_mul (ne_of_gt (by positivity : 0 < d * f ^ 2 * E)) (ne_of_gt (by positivity : 0 < t ^ 2))]
  rw [Real.log_mul (ne_of_gt (by positivity : 0 < d * f ^ 2)) (ne_of_gt hE)]
  rw [Real.log_mul (ne_of_gt hd) (ne_of_gt (by positivity : 0 < f ^ 2))]
  rw [Real.log_pow, Real.log_pow]
  ring
end OAI.TwoPassProfiles
