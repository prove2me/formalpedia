-- Prove2me | solution 1 for OAI.CanonicalQuadraticSieve.sieveNorm_large_rows
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T06:19:37.1402+00:00
-- url     : https://prove2.me/submissions/e08339c0-dd6a-433b-b39f-d745aa5d0753

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_AnnularLifting
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_PoissonConstants
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_SelectedExponents
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
open scoped BigOperators Classical SchwartzMap
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Matrix Pointwise
open OAI.CanonicalQuadraticSieve
namespace OAI.CanonicalQuadraticSieve
theorem _root_.solution (M N : ℝ) (hM : 1≤M) (hN : 1≤N) (hlarge : N^2≤M) :
    sieveNorm M N≤5*QuadraticInitialBound.initialSieveConstant*M := by
  have hceil : (⌈N⌉₊:ℝ)≤2*N := by
    have h := Nat.ceil_lt_add_one (by linarith : 0≤N)
    linarith
  have hsq : (⌈N⌉₊:ℝ)^2≤4*M := by
    calc
      _ ≤ (2*N)^2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hceil 2
      _ = 4*N^2 := by ring
      _ ≤ 4*M := by linarith
  have hh := sieveNorm_initial M N hM hN
  have hC := QuadraticInitialBound.initialSieveConstant_pos
  nlinarith
end OAI.CanonicalQuadraticSieve
