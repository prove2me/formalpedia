-- Prove2me | solution 1 for OAI.CanonicalQuadraticSieve.columnDyadicLength_scale_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T06:04:25.553688+00:00
-- url     : https://prove2.me/submissions/76d67ffe-b3bf-4f73-b35e-68f8f81713f0

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_GlobalScales
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_AnnularLifting

set_option autoImplicit false
open OAI
noncomputable section
open OAI.CanonicalQuadraticSieve
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
open ActualEisensteinCubic CompletedGauss
namespace OAI.CanonicalQuadraticSieve
theorem _root_.solution (N : ℝ) (hN : 1≤N) :
    (2:ℝ)^columnDyadicLength N≤2*N := by
  have hlog : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hq : 0≤Real.log N/Real.log 2 := div_nonneg (Real.log_nonneg hN) hlog.le
  have hceil := Nat.ceil_lt_add_one hq
  calc
    _ = (2:ℝ)^((columnDyadicLength N:ℕ):ℝ) := (Real.rpow_natCast _ _).symm
    _ ≤ (2:ℝ)^(Real.log N/Real.log 2+1) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hceil.le
    _ = 2*N := by
      rw [Real.rpow_add (by norm_num : (0:ℝ)<2),Real.rpow_one]
      have he : (2:ℝ)^(Real.log N/Real.log 2)=N :=
        Real.rpow_logb (by norm_num) (by norm_num) (by linarith)
      rw [he,mul_comm]
end OAI.CanonicalQuadraticSieve
