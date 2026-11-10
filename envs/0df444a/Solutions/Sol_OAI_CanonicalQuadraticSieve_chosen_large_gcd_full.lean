-- Prove2me | solution 1 for OAI.CanonicalQuadraticSieve.chosen_large_gcd_full
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T06:17:44.027337+00:00
-- url     : https://prove2.me/submissions/448df9ed-6240-41f9-8e9c-2cb3f4bbfb26

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_GlobalScales
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_AnnularLifting
import Theorems.Thm_OAI_CanonicalQuadraticSieve_largeGcdThreshold_bounds
import Theorems.Thm_OAI_CanonicalQuadraticSieve_chosen_large_gcd_main

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
namespace OAI.CanonicalQuadraticSieve
theorem _root_.solution (α deltaLoss C M N K : ℝ) (hα1 : 1≤α) (hα2 : α≤2)
    (hδ : 0≤deltaLoss) (hC : 0≤C) (hM : 0<M) (hN : 4≤N) (hK : 0<K)
    (hcut : N^2/M≤K) :
    C*((2*M)*(N/largeGcdThreshold α N))^deltaLoss*
      (2*M+Real.sqrt ((2*M)/K)*(N/largeGcdThreshold α N)^α) ≤
        (4*C*2^deltaLoss)*(M*N)^deltaLoss*M := by
  have hh := largeGcdThreshold_bounds α N hα1 hα2 hN
  have hH : 0<largeGcdThreshold α N := by linarith
  have hN0 : 0<N := by linarith
  have hp : ((2*M)*(N/largeGcdThreshold α N))^deltaLoss≤(2*(M*N))^deltaLoss := by
    apply Real.rpow_le_rpow (by positivity) _ hδ
    have hn := div_le_self hN0.le hh.1
    nlinarith
  have hm := chosen_large_gcd_main α M N K (by linarith) hM hN0 hK hcut
  calc
    _ ≤ C*(2*(M*N))^deltaLoss*(4*M) := by gcongr
    _ = _ := by rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) (by positivity)]; ring
end OAI.CanonicalQuadraticSieve
