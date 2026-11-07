-- Prove2me | solution 1 for OAI.TwoPassProfiles.second_profile_logshape
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:54:19.064478+00:00
-- url     : https://prove2.me/submissions/42e67846-804a-4950-9aeb-8ef01e3a8d2f

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
    (Y k d e v n₁ n₂ : ℝ)
    (hY : 0 < Y) (hk : 0 < k) (hd : 0 < d)
    (he : 0 < e) (hv : 0 < v)
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) :
    Real.log (Y * k / (d * e ^ 2 * v ^ 2 * n₁ * n₂)) =
      Real.log Y + Real.log k - Real.log d -
      2 * Real.log e - 2 * Real.log v -
      Real.log n₁ - Real.log n₂ := by
  have hden : 0 < d * e ^ 2 * v ^ 2 * n₁ * n₂ := by positivity
  rw [Real.log_div (by positivity) (ne_of_gt hden)]
  rw [Real.log_mul (ne_of_gt hY) (ne_of_gt hk)]
  rw [Real.log_mul (ne_of_gt (by positivity : 0 < d * e ^ 2 * v ^ 2 * n₁)) (ne_of_gt hn₂)]
  rw [Real.log_mul (ne_of_gt (by positivity : 0 < d * e ^ 2 * v ^ 2)) (ne_of_gt hn₁)]
  rw [Real.log_mul (ne_of_gt (by positivity : 0 < d * e ^ 2)) (ne_of_gt (by positivity : 0 < v ^ 2))]
  rw [Real.log_mul (ne_of_gt hd) (ne_of_gt (by positivity : 0 < e ^ 2))]
  rw [Real.log_pow, Real.log_pow]
  ring
end OAI.TwoPassProfiles
