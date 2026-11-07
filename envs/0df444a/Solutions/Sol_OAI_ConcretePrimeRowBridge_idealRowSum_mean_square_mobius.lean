-- Prove2me | solution 1 for OAI.ConcretePrimeRowBridge.idealRowSum_mean_square_mobius
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:00:53.541708+00:00
-- url     : https://prove2.me/submissions/250d8962-7686-40f1-80fc-ff8d3f1b4193

import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_NormFiberExtraction
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SecondPoissonScale
import Theorems.Thm_OAI_ActualEisensteinCubic_finiteSquarefreeRow_mean_square_mobius
import Theorems.Thm_OAI_ActualEisensteinCubic_prime_product_moebius
import Theorems.Thm_OAI_ActualEisensteinCubic_mem_prime_product_iff
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
open OAI.ConcretePrimeRowBridge
open ActualEisensteinCubic ShortDraftHeckeBridge
open scoped BigOperators Classical
namespace OAI.ConcretePrimeRowBridge
theorem _root_.solution
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I,
        goodLambda ∉ P)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (W : ℕ → ℂ)
    (R : Finset O) (V : O → ℂ) :
    (∑ u ∈ R, V u * (↑(‖idealRowSum F hFpos hFgood χ W u‖ ^ 2) : ℂ)) =
      ∑ I ∈ F, ∑ J ∈ F,
        star (baseChangeWeight χ I * W (Ideal.absNorm I)) *
          (baseChangeWeight χ J * W (Ideal.absNorm J)) *
        ∑ E ∈ (idealSupport F I ∩ idealSupport F J).powerset,
          (UniqueFactorizationMonoid.moebius (primeSubsetProduct F E) : ℂ) *
          ∑ u ∈ R.filter (fun u => u ∈ primeSubsetProduct F E),
            V u * star (residualSexticRow F hFpos hFgood I J u) *
              residualSexticRow F hFpos hFgood J I u := by
  classical
  let : ∀ i : primePool F, (i.1).IsMaximal := primePool_maximal F hFpos
  have hprime (i : primePool F) : Prime i.1 := by
    obtain ⟨I, hIF, hi⟩ := mem_primePool_iff.mp i.property
    exact UniqueFactorizationMonoid.prime_of_normalized_factor i.1 hi
  change (∑ u ∈ R, V u * (↑(‖∑ I ∈ F,
    (baseChangeWeight χ I * W (Ideal.absNorm I)) *
      finiteSquarefreeRow (fun i : primePool F => i.1)
        (primePool_good F hFgood) (idealSupport F I) u‖ ^ 2) : ℂ)) = _
  erw [finiteSquarefreeRow_mean_square_mobius]
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro J hJ
  congr 1
  apply Finset.sum_congr rfl
  intro E hE
  rw [show (UniqueFactorizationMonoid.moebius (primeSubsetProduct F E) : ℂ) =
    (-1 : ℂ) ^ E.card from
      prime_product_moebius (fun i : primePool F => i.1)
        hprime Subtype.val_injective E]
  congr 1
  apply Finset.sum_congr
  · ext u
    simp only [Finset.mem_filter]
    exact and_congr_right fun hu =>
      (mem_prime_product_iff (fun i : primePool F => i.1)
        Subtype.val_injective E u).symm
  · intro u hu
    rfl
end OAI.ConcretePrimeRowBridge
