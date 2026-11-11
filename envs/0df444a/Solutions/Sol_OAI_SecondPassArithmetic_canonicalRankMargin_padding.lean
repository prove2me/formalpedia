-- Prove2me | solution 1 for OAI.SecondPassArithmetic.canonicalRankMargin_padding
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T12:36:34.696188+00:00
-- url     : https://prove2.me/submissions/fb432759-7284-4af0-a73c-0788a0ddc280

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CoordinateLaplacian
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_DensityBudgets
import Theorems.Thm_OAI_SecondPassArithmetic_canonicalRankMargin_step

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
open scoped BigOperators Classical
open MeasureTheory
open scoped BigOperators Classical
open scoped BigOperators Classical
open OAI.SecondPassArithmetic
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open FirstPassCubeLabels (primeProduct)
namespace OAI.SecondPassArithmetic
theorem _root_.solution (Z σ η a : ℝ) (r s : ℕ)
    (hZ : 1<Z) (hη : 0≤η) (hr : r≤3000) (hs : s+1≤r)
    (ha : 0≤a) (hbound : a≤Z^(-canonicalRankMargin σ η r)) :
    Z^η*(a/Real.exp 3)≤Z^(-canonicalRankMargin σ η s) := by
  have hZ0 : 0<Z := zero_lt_one.trans hZ
  have hmargin := canonicalRankMargin_step σ η hη r s hr hs
  calc
    Z^η*(a/Real.exp 3) ≤ Z^η*a :=
      mul_le_mul_of_nonneg_left (div_le_self ha (Real.one_le_exp (by norm_num)))
        (Real.rpow_nonneg hZ0.le _)
    _ ≤ Z^η*Z^(-canonicalRankMargin σ η r) :=
      mul_le_mul_of_nonneg_left hbound (Real.rpow_nonneg hZ0.le _)
    _ = Z^(η-canonicalRankMargin σ η r) := by
      rw [sub_eq_add_neg,Real.rpow_add hZ0]
    _ ≤ Z^(-canonicalRankMargin σ η s) :=
      Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
end OAI.SecondPassArithmetic
