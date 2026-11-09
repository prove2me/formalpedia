-- Prove2me | solution 1 for OAI.CanonicalQuadraticSieve.selectedPoisson_middle_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T04:35:00.717264+00:00
-- url     : https://prove2.me/submissions/c2f944a2-2bbe-4b17-9b8d-4bb4db6660b5

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_PoissonComparison
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_ArithmeticBins
import Theorems.Thm_OAI_CanonicalQuadraticSieve_cutoff_middle_identity

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
open OAI.CanonicalQuadraticSieve
namespace OAI.CanonicalQuadraticSieve
theorem _root_.solution (C M X η α : ℝ)
    (hC : 4≤C) (hM : 1≤M) (hX : 1≤X) (hη : 0≤η) (hα : α≤2) :
    selectedPoissonT C M X η*Real.sqrt M*(2*selectedPoissonK C M X η)^(α-1/2) ≤
      4*C^3*(M*X)^(3*η)*(X^(2*α-1)*M^(1-α)) := by
  have hM0 : 0<M := by linarith
  have hX0 : 0<X := by linarith
  have hP : 0<M*X := by positivity
  have hP1 : 1≤M*X := by nlinarith
  have hpow : 1≤(M*X)^η := Real.one_le_rpow hP1 hη
  have hT : 1≤selectedPoissonT C M X η := by unfold selectedPoissonT; nlinarith
  have hT0 : 0<selectedPoissonT C M X η := by linarith
  have hK0 : 0<selectedPoissonK C M X η := by unfold selectedPoissonK; positivity
  have htwo : (2:ℝ)^(α-1/2)≤4 := by
    calc
      _ ≤ (2:ℝ)^(2:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 4 := by norm_num
  have hp3 : ((M*X)^η)^3 = (M*X)^(3*η) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hP.le]
    congr 1
    ring
  have hT3 : (selectedPoissonT C M X η)^(α+1/2)≤C^3*(M*X)^(3*η) := by
    calc
      _ ≤ (selectedPoissonT C M X η)^(3:ℝ) := Real.rpow_le_rpow_of_exponent_le hT (by linarith)
      _ = C^3*(M*X)^(3*η) := by norm_num only [selectedPoissonT,Real.rpow_ofNat,mul_pow,hp3]
  rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) hK0.le]
  calc
    _ ≤ 4*(selectedPoissonT C M X η*Real.sqrt M*(selectedPoissonK C M X η)^(α-1/2)) := by
      have hh := mul_le_mul_of_nonneg_right htwo
        (show 0≤selectedPoissonT C M X η*Real.sqrt M*(selectedPoissonK C M X η)^(α-1/2) by positivity)
      nlinarith [hh]
    _ = 4*((selectedPoissonT C M X η)^(α+1/2)*X^(2*α-1)*M^(1-α)) := by
      rw [selectedPoissonK,cutoff_middle_identity M X _ α hM0 hX0 hT0]
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_right hT3
        (show 0≤X^(2*α-1)*M^(1-α) by positivity)
      nlinarith [hh]
end OAI.CanonicalQuadraticSieve
