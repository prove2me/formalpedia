-- Prove2me | solution 1 for OAI.CanonicalQuadraticSieve.improved_threshold_low
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T06:27:10.298947+00:00
-- url     : https://prove2.me/submissions/a4934104-f9c9-495c-9040-8bee1edac1d8

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_AnnularLifting
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_PoissonConstants
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_SelectedExponents
import Theorems.Thm_OAI_CanonicalQuadraticSieve_improved_threshold_reciprocal

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
theorem _root_.solution (α C η N M : ℝ) (hα : 0<α) (hC : 0<C)
    (hN : 0<N) (hM0 : 0<M) (hM : N^(2-1/α)≤M) :
    (selectedPoissonK C M N η)^α≤C^α*(M*N)^(η*α)*N := by
  have hk : selectedPoissonK C M N η≤C*(M*N)^η*N^(1/α) := by
    unfold selectedPoissonK selectedPoissonT
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (improved_threshold_reciprocal α N M hα hN hM0 hM) (by positivity)
  have hk0 : 0≤selectedPoissonK C M N η := by
    unfold selectedPoissonK selectedPoissonT
    positivity
  calc
    _ ≤ (C*(M*N)^η*N^(1/α))^α := Real.rpow_le_rpow hk0 hk hα.le
    _ = _ := by
      rw [Real.mul_rpow (by positivity : 0≤C*(M*N)^η) (by positivity),
        Real.mul_rpow hC.le (by positivity),←Real.rpow_mul (by positivity : 0≤M*N),
        ←Real.rpow_mul hN.le]
      have he : (1/α)*α=1 := by field_simp
      rw [he,Real.rpow_one]
end OAI.CanonicalQuadraticSieve
