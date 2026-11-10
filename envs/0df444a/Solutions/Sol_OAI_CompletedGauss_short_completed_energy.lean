-- Prove2me | solution 1 for OAI.CompletedGauss.short_completed_energy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T08:34:06.429729+00:00
-- url     : https://prove2.me/submissions/94f1c0ce-9119-48aa-9d89-0d685804c2d3

import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_TransformedColumns
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_ProductColumns
import Theorems.Thm_OAI_CompletedGauss_mem_shortCubeRange
import Theorems.Thm_OAI_CompletedGauss_shortCompletedSum_eq
import Theorems.Thm_OAI_CompletedGauss_cube_inverse_weight_norm
import Theorems.Thm_OAI_CanonicalQuadraticSieve_finite_inverse_norm_sum
import Theorems.Thm_OAI_CanonicalQuadraticSieve_ideal_reciprocal_cauchy


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
open OAI.CompletedGauss
open ActualEisensteinCubic CanonicalQuadraticSieve ConcretePrimeRowBridge
namespace OAI.CompletedGauss
theorem _root_.solution {κ : Type*} [Fintype κ]
    (Ψ : κ → O →* ℂ) (hΨ : ∀k z,‖Ψ k z‖≤1)
    (W : ℝ → ℂ) (X H₀ A : ℝ) (hA : 0≤A)
    (hcompleted : ∀H∈shortCubeRange H₀,
      (∑k,‖completedT (Ψ k) W (X/(Ideal.absNorm H:ℝ)^3)‖^2)≤A) :
    (∑k,‖shortCompletedSum (Ψ k) W X H₀‖^2)≤
      A*(256*(columnDyadicLength H₀+1:ℝ))^2 := by
  let S := shortCubeRange H₀
  let lengthScale : ℝ := ∑H∈S,1/(Ideal.absNorm H:ℝ)
  have hS (H : Ideal O) (hH : H∈S) : H≠0 := ((mem_shortCubeRange H₀ H).mp hH).1
  have hn (H : Ideal O) (hH : H∈S) : 0<(Ideal.absNorm H:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz => hS H hH (Ideal.absNorm_eq_zero_iff.mp hz))
  have hL : 0≤lengthScale := Finset.sum_nonneg (fun H hH => by positivity)
  have hb (k : κ) : ‖shortCompletedSum (Ψ k) W X H₀‖^2≤
      lengthScale*∑H∈S,(1/(Ideal.absNorm H:ℝ))*‖completedT (Ψ k) W (X/(Ideal.absNorm H:ℝ)^3)‖^2 := by
    rw [shortCompletedSum_eq]
    apply (ideal_reciprocal_cauchy S hS _).trans
    apply mul_le_mul_of_nonneg_left _ hL
    apply Finset.sum_le_sum
    intro H hH
    rw [norm_mul]
    calc
      _ ≤ (Ideal.absNorm H:ℝ)*((1/(Ideal.absNorm H:ℝ))*‖completedT (Ψ k) W (X/(Ideal.absNorm H:ℝ)^3)‖)^2 := by
        gcongr
        exact cube_inverse_weight_norm (Ψ k) (hΨ k) H
      _ = _ := by field_simp [(hn H hH).ne']
  have hsum : (∑k,‖shortCompletedSum (Ψ k) W X H₀‖^2)≤A*lengthScale^2 := by
    calc
      _ ≤ ∑k,lengthScale*∑H∈S,(1/(Ideal.absNorm H:ℝ))*‖completedT (Ψ k) W (X/(Ideal.absNorm H:ℝ)^3)‖^2 :=
        Finset.sum_le_sum (fun k _ => hb k)
      _ = lengthScale*∑H∈S,(1/(Ideal.absNorm H:ℝ))*∑k,‖completedT (Ψ k) W (X/(Ideal.absNorm H:ℝ)^3)‖^2 := by
        rw [←Finset.mul_sum,Finset.sum_comm]
        congr 1
        apply Finset.sum_congr rfl
        intro H hH
        rw [←Finset.mul_sum]
      _ ≤ lengthScale*∑H∈S,(1/(Ideal.absNorm H:ℝ))*A := by
        gcongr with H hH
        exact hcompleted H hH
      _ = A*lengthScale^2 := by rw [←Finset.sum_mul]; change lengthScale*(lengthScale*A)=A*lengthScale^2; ring
  have hbound : lengthScale≤256*(columnDyadicLength H₀+1:ℝ) :=
    finite_inverse_norm_sum S H₀ hS (fun H hH => ((mem_shortCubeRange H₀ H).mp hH).2.le)
  exact hsum.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hL hbound 2) hA)
end OAI.CompletedGauss
