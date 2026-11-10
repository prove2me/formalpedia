-- Prove2me | solution 1 for OAI.CompletedDyadic.normMajorant_sum_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T13:14:36.360208+00:00
-- url     : https://prove2.me/submissions/8a2e784f-e428-4cf8-99a5-b6e4c2655944

import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_PoissonSource
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_QuantitativePassage
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_DyadicKernel
import Theorems.Thm_OAI_CompletedDyadic_triple_product_kernel_sum_bound
import Theorems.Thm_OAI_CompletedDyadic_normMajorant_eq_triples

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
open scoped BigOperators
open OAI.CompletedDyadic
namespace OAI.CompletedDyadic
theorem _root_.solution (deltaLoss A ρ q : ℝ)
    (hδ : 0<deltaLoss) (hA : deltaLoss+1/2<A) (hρ : 0<ρ) (hq : 1<q) :
    ∃C : ℝ,0<C ∧ ∀K Y H : ℝ,0<K → 0<Y → 0<H →
      Summable (fun i : ℕ×ℕ×ℕ =>
        normMajorant deltaLoss A K Y⁻¹ (ramifiedScale ρ q i.1) H ((2:ℝ)^i.2.2) ((2:ℝ)^i.2.1)) ∧
      (∑'i : ℕ×ℕ×ℕ,
        normMajorant deltaLoss A K Y⁻¹ (ramifiedScale ρ q i.1) H ((2:ℝ)^i.2.2) ((2:ℝ)^i.2.1))
        ≤C*(K*Y)^deltaLoss*(Real.sqrt K+Real.sqrt Y)/Real.sqrt H := by
  obtain ⟨C₁,hC₁,h₁⟩ := triple_product_kernel_sum_bound deltaLoss A (deltaLoss-1/2) ρ q hδ
    (by linarith) (by linarith) hρ hq
  obtain ⟨C₂,hC₂,h₂⟩ := triple_product_kernel_sum_bound (deltaLoss+1/2) A deltaLoss ρ q
    (by linarith) hA (by linarith) hρ hq
  refine ⟨C₁+C₂,by positivity,?_⟩
  intro K Y H hK hY hH
  obtain ⟨hs₁,hb₁⟩ := h₁ Y⁻¹ (by positivity)
  obtain ⟨hs₂,hb₂⟩ := h₂ Y⁻¹ (by positivity)
  simp_rw [normMajorant_eq_triples]
  refine ⟨((hs₁.mul_left (Real.sqrt K)).add hs₂).mul_left (K^deltaLoss/Real.sqrt H),?_⟩
  rw [tsum_mul_left,(hs₁.mul_left (Real.sqrt K)).tsum_add hs₂,tsum_mul_left]
  have hp₁ : (Y⁻¹)^(-deltaLoss)=Y^deltaLoss := by rw [Real.inv_rpow hY.le,Real.rpow_neg hY.le,inv_inv]
  have hp₂ : (Y⁻¹)^(-(deltaLoss+1/2))=Y^deltaLoss*Real.sqrt Y := by
    rw [Real.inv_rpow hY.le,Real.rpow_neg hY.le,inv_inv,Real.rpow_add hY,←Real.sqrt_eq_rpow]
  rw [hp₁] at hb₁
  rw [hp₂] at hb₂
  calc
    _ ≤ K^deltaLoss/Real.sqrt H*(Real.sqrt K*(C₁*Y^deltaLoss)+C₂*(Y^deltaLoss*Real.sqrt Y)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add (mul_le_mul_of_nonneg_left hb₁ (Real.sqrt_nonneg _)) hb₂
    _ ≤ K^deltaLoss/Real.sqrt H*((C₁+C₂)*Y^deltaLoss*(Real.sqrt K+Real.sqrt Y)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith [mul_nonneg (le_of_lt hC₁) (show 0≤Y^deltaLoss*Real.sqrt Y by positivity),
        mul_nonneg (le_of_lt hC₂) (show 0≤Y^deltaLoss*Real.sqrt K by positivity)]
    _ = _ := by rw [Real.mul_rpow hK.le hY.le]; ring
end OAI.CompletedDyadic
