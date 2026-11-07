-- Prove2me | solution 1 for OAI.ConcretePrimeRowBridge.baseChange_prime_extraction_from_MS
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:23:35.43591+00:00
-- url     : https://prove2.me/submissions/7cd713f9-012c-4a40-90ad-32aa3b4437b8

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_PrimeExtraction
import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_NormFiberExtraction
import Theorems.Thm_OAI_ConcretePrimeRowBridge_span_idealGenerator
import Theorems.Thm_OAI_ConcretePrimeRowBridge_idealGenerator_injective
import Theorems.Thm_OAI_ConcretePrimeRowBridge_columnWeight_idealGenerator
import Theorems.Thm_OAI_ConcretePrimeRowBridge_idealGenerator_mem_prime_of_support
import Theorems.Thm_OAI_ConcretePrimeRowBridge_columnWeight_norm_le_one
import Theorems.Thm_OAI_ConcretePrimeRowBridge_elementRow_eq_idealRowSum
import Theorems.Thm_OAI_ConcretePrimeRowBridge_sixth_power_rows_in_rowNormDisk
import Theorems.Thm_OAI_ActualEisensteinCubic_finite_actual_prime_extraction_dyadic
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
open OAI.ConcretePrimeRowBridge
open ActualEisensteinCubic ShortDraftHeckeBridge
open ActualEisensteinCubic ShortDraftHeckeBridge
open scoped Classical
namespace OAI.ConcretePrimeRowBridge
theorem _root_.solution
    {β : Type*} {q : ℕ}
    (χ : DirichletCharacter ℂ q) (W : ℕ → ℂ)
    (F : Finset (Ideal O))
    (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I,
        goodLambda ∉ P)
    (hW : ∀ n, ‖W n‖ ≤ 1)
    (selected : Finset β) (p : β → O)
    (D H : ℕ) (ε : ℝ) (hD : 1 ≤ D) (hε : 0 ≤ ε)
    (hFnorm : ∀ I ∈ F, Ideal.absNorm I ≤ D)
    (hp : ∀ i ∈ selected, p i ≠ 0)
    (hprime : ∀ i ∈ selected, (Ideal.span {p i} : Ideal O).IsMaximal)
    (hinj : Set.InjOn (fun i => (Ideal.span {p i} : Ideal O)) (selected : Set β))
    (hnormlower : ∀ i ∈ selected,
      (D : ℝ) ^ (11 / 60 : ℝ) / 2 ≤
        (Ideal.absNorm (Ideal.span {p i}) : ℝ))
    (hnormupper : ∀ i ∈ selected,
      (Ideal.absNorm (Ideal.span {p i}) : ℝ) ≤
        (D : ℝ) ^ (11 / 60 : ℝ))
    (hH : Nat.floor ((D : ℝ) ^ (11 / 10 : ℝ)) ≤ H)
    (hcount : (D : ℝ) ^ ((11 / 60 : ℝ) - ε) ≤ (selected.card : ℝ))
    (hmean :
      (∑ u ∈ rowNormDisk H,
        ‖idealRowSum F hFpos hFgood χ W u‖ ^ 2) ≤
        (D : ℝ) ^ ((21 / 10 : ℝ) + ε)) :
    ‖∑ I ∈ F, baseChangeWeight χ I * W (Ideal.absNorm I)‖ ≤
      384 * (D : ℝ) ^ ((23 / 24 : ℝ) + ε) := by
  classical
  let : ∀ i : primePool F, (i.1).IsMaximal := primePool_maximal F hFpos
  let P : primePool F → Ideal O := fun i => i.1
  let support : O → Finset (primePool F) :=
    fun x => idealSupport F (Ideal.span {x})
  let columns : Finset O := F.image idealGenerator
  let weight : O → ℂ := columnWeight χ W
  have hsupport : ∀ x ∈ columns, ∀ i ∈ support x, x ∈ P i := by
    intro x hx i hi
    obtain ⟨I, hIF, rfl⟩ := Finset.mem_image.mp hx
    dsimp [support, P] at hi ⊢
    rw [span_idealGenerator I] at hi
    exact idealGenerator_mem_prime_of_support F hFpos I hIF i hi
  have hcolnorm : ∀ x ∈ columns,
      Ideal.absNorm (Ideal.span {x}) ≤ D := by
    intro x hx
    obtain ⟨I, hIF, rfl⟩ := Finset.mem_image.mp hx
    rw [span_idealGenerator I]
    exact hFnorm I hIF
  have hweight : ∀ x ∈ columns, ‖weight x‖ ≤ 1 := by
    intro x hx
    exact columnWeight_norm_le_one χ W hW x
  have hmean' :
      (∑ u ∈ rowNormDisk H,
        ‖∑ x ∈ columns,
          weight x * finiteSquarefreeRow P (primePool_good F hFgood)
            (support x) u‖ ^ 2) ≤
        (D : ℝ) ^ ((21 / 10 : ℝ) + ε) := by
    calc
      _ = ∑ u ∈ rowNormDisk H,
          ‖idealRowSum F hFpos hFgood χ W u‖ ^ 2 := by
            apply Finset.sum_congr rfl
            intro u hu
            change ‖elementRow F hFpos hFgood χ W u‖ ^ 2 =
              ‖idealRowSum F hFpos hFgood χ W u‖ ^ 2
            rw [elementRow_eq_idealRowSum]
      _ ≤ _ := hmean
  have hrows : selected.image (fun i => p i ^ 6) ⊆ rowNormDisk H :=
    sixth_power_rows_in_rowNormDisk selected p D H hD hp hnormupper hH
  have hbound := finite_actual_prime_extraction_dyadic
    P (primePool_good F hFgood) columns support weight selected p
    (rowNormDisk H) D ε hD hε hp hprime hinj hrows
    hsupport hcolnorm hweight hnormlower hcount hmean'
  have hsum :
      (∑ x ∈ columns, weight x) =
        ∑ I ∈ F, baseChangeWeight χ I * W (Ideal.absNorm I) := by
    change (∑ x ∈ F.image idealGenerator, columnWeight χ W x) = _
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro I hIF
      exact columnWeight_idealGenerator χ W I
    · intro I hIF J hJF h
      exact idealGenerator_injective h
  rwa [hsum] at hbound
end OAI.ConcretePrimeRowBridge
