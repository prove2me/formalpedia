-- Prove2me | solution 1 for OAI.CanonicalQuadraticSieve.sieveNorm_small_columns
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T06:25:58.806392+00:00
-- url     : https://prove2.me/submissions/17d9c0b6-9512-4d23-ba18-517049cf6d6c

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_SelectedExponents
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_LogarithmicLoss
import Theorems.Thm_OAI_CanonicalQuadraticSieve_sieveNorm_initial
import Theorems.Thm_OAI_QuadraticInitialBound_initialSieveConstant_pos


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
open scoped BigOperators Classical
open OAI.CanonicalQuadraticSieve
namespace OAI.CanonicalQuadraticSieve
theorem _root_.solution (M N : ℝ) (hM : 1≤M) (hN : 1≤N) (hN28 : N≤28) :
    sieveNorm M N≤785*QuadraticInitialBound.initialSieveConstant*M := by
  have hceil : (⌈N⌉₊:ℝ)≤28 := by
    exact_mod_cast (Nat.ceil_le.mpr hN28 : ⌈N⌉₊≤28)
  have hs : (⌈N⌉₊:ℝ)^2≤784 := by
    nlinarith [Nat.cast_nonneg (α:=ℝ) ⌈N⌉₊]
  have hc := QuadraticInitialBound.initialSieveConstant_pos
  have hb := sieveNorm_initial M N hM hN
  have ht : M+(⌈N⌉₊:ℝ)^2≤785*M := by linarith
  calc
    _ ≤ QuadraticInitialBound.initialSieveConstant*(M+(⌈N⌉₊:ℝ)^2) := hb
    _ ≤ QuadraticInitialBound.initialSieveConstant*(785*M) := mul_le_mul_of_nonneg_left ht hc.le
    _ = _ := by ring
end OAI.CanonicalQuadraticSieve
