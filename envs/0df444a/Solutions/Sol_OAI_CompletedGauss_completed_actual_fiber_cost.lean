-- Prove2me | solution 1 for OAI.CompletedGauss.completed_actual_fiber_cost
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T13:55:19.532205+00:00
-- url     : https://prove2.me/submissions/6b80ce34-519f-4d6f-8e1b-38eef127b40a

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_DyadicKernel
import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_ReflectedDyadicSeries
import Theorems.Thm_OAI_CompletedGauss_completed_fiber_scalar_cost
import Theorems.Thm_OAI_CompletedGauss_completed_conductor_norm_bound
import Theorems.Thm_OAI_CompletedGauss_reflectionConductorCost_bound
import Theorems.Thm_OAI_CompletedGauss_reflectionExtractedDivisor_ne_zero
import Theorems.Thm_OAI_CompletedGauss_rowPowerfulPart_ne_zero
import Theorems.Thm_OAI_CompletedGauss_squarefreeMaskPart_ne_zero


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
open scoped BigOperators Classical SchwartzMap ContDiff
open OAI.CompletedGauss
open ActualEisensteinCubic
namespace OAI.CompletedGauss
theorem _root_.solution {ι : Type*} [Fintype ι]
    (deltaLoss K X : ℝ) (hδ : 0≤deltaLoss) (hK : 1≤K) (hX : 1≤X)
    (I F Q : Ideal O) (hI : I≠0) (hQ : Q≠0) (hIK : (Ideal.absNorm I:ℝ)≤K)
    (P : ι→Ideal O) [∀i,(P i).IsMaximal]
    (hcop : Pairwise (fun i j => IsCoprime (P i) (P j)))
    (hpool : ∀i,P i∣I*Q) (hres : ∀i,¬P i∣rowResidualPart I Q) (e : ι→Fin 3) :
    let j := fun i => completedLocalExponent I F (P i)
    let k := K/((Ideal.absNorm (rowPowerfulPart I):ℝ)*(Ideal.absNorm (rowMaskPart I Q):ℝ))
    let D := (Ideal.absNorm (reflectionExtractedDivisor P j e 1):ℝ)
    let S := (Ideal.absNorm (reflectionExtractedDivisor P j e 0):ℝ)
    let E := (Ideal.absNorm (reflectionExtractedDivisor P j e 2):ℝ)
    let y := k^2*(Ideal.absNorm (∏i,P i):ℝ)^2/(X*D*E^3)
    (k*y)^(2*deltaLoss)*(k+y)/(S*E)≤
      (K*(Ideal.absNorm Q:ℝ))^(10*deltaLoss)*(K+K^2*(Ideal.absNorm Q:ℝ)/X)/
        (Ideal.absNorm (rowPowerfulPart I):ℝ) := by
  have hn (J : Ideal O) (hJ : J≠0) : 1≤(Ideal.absNorm J:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => hJ (Ideal.absNorm_eq_zero_iff.mp hz))
  have hprod : (∏i,P i)≠0 := Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne (P i))
  have hc := (completed_conductor_norm_bound I Q hI hQ P hcop hpool).trans
    (mul_le_mul_of_nonneg_right hIK (Nat.cast_nonneg _))
  have hh := completed_fiber_scalar_cost deltaLoss K X
    (Ideal.absNorm (rowPowerfulPart I):ℝ) (Ideal.absNorm (rowMaskPart I Q):ℝ)
    (Ideal.absNorm Q:ℝ) (Ideal.absNorm (∏i,P i):ℝ)
    (Ideal.absNorm (reflectionExtractedDivisor P (fun i => completedLocalExponent I F (P i)) e 1):ℝ)
    (Ideal.absNorm (reflectionExtractedDivisor P (fun i => completedLocalExponent I F (P i)) e 0):ℝ)
    (Ideal.absNorm (reflectionExtractedDivisor P (fun i => completedLocalExponent I F (P i)) e 2):ℝ)
    hδ hK hX (hn _ (rowPowerfulPart_ne_zero I))
    (hn _ (squarefreeMaskPart_ne_zero (rowSimplePart I) Q)) (hn _ hQ)
    (lt_of_lt_of_le (by norm_num) (hn _ hprod)) hc
    (hn _ (reflectionExtractedDivisor_ne_zero P (fun i => NeZero.ne (P i)) _ e 1))
    (hn _ (reflectionExtractedDivisor_ne_zero P (fun i => NeZero.ne (P i)) _ e 0))
    (hn _ (reflectionExtractedDivisor_ne_zero P (fun i => NeZero.ne (P i)) _ e 2))
    (reflectionConductorCost_bound I F Q hI hQ P hcop hpool hres e)
  exact hh
end OAI.CompletedGauss
