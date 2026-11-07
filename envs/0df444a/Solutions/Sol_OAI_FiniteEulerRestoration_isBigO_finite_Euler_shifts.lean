-- Prove2me | solution 1 for OAI.FiniteEulerRestoration.isBigO_finite_Euler_shifts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:20:02.08791+00:00
-- url     : https://prove2.me/submissions/05709feb-3f41-4626-8499-c54ef9224693

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_PrimeExtraction
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_FiniteEulerRestoration
import Theorems.Thm_OAI_FiniteEulerRestoration_isBigO_power_atTop_div_const
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk



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
open OAI.FiniteEulerRestoration
namespace OAI.FiniteEulerRestoration
theorem _root_.solution {ι : Type*} (s : Finset ι)
    (A : ℝ → ℂ) (c : ι → ℂ) (N : ι → ℝ) {σ : ℝ}
    (hN : ∀ i ∈ s, 0 < N i)
    (hA : A =O[atTop] fun D : ℝ => D ^ σ) :
    (fun D : ℝ => ∑ i ∈ s, c i * A (D / N i)) =O[atTop]
      (fun D : ℝ => D ^ σ) := by
  have hsum : (∑ i ∈ s, fun D : ℝ => c i * A (D / N i)) =O[atTop]
      (fun D : ℝ => D ^ σ) := by
    apply IsBigO.sum
    intro i hi
    exact (isBigO_power_atTop_div_const (hN i hi) hA).const_mul_left (c i)
  exact hsum.congr_left (by
    intro D
    simp only [Finset.sum_apply])
end OAI.FiniteEulerRestoration
