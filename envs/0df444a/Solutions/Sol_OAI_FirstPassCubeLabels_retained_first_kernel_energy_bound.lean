-- Prove2me | solution 1 for OAI.FirstPassCubeLabels.retained_first_kernel_energy_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:23:00.879823+00:00
-- url     : https://prove2.me/submissions/b07ab0c6-1211-4d10-ae7f-7e92077df1f8

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_IdealQuotients
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_KernelEnergy
import Theorems.Thm_OAI_FirstPassCubeLabels_firstColumnEnergy_nonneg
import Theorems.Thm_OAI_FirstPassCubeLabels_actual_first_kernel_energy_bound
import Theorems.Thm_OAI_ActualEisensteinCubic_primeSubsetGenerator_ne_zero


set_option autoImplicit false
open OAI
noncomputable section
open OAI.FirstPassCubeLabels
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
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
namespace OAI.FirstPassCubeLabels
theorem _root_.solution {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (F B : Finset ι) (hFB : Disjoint F B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (V₁ V₂ : ℝ → ℂ) (X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (M₁ M₂ : ℝ) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hV₁ : ∀ x, V₁ x ≠ 0 → |x| ≤ M₁) (hV₂ : ∀ y, V₂ y ≠ 0 → |y| ≤ M₂)
    (A J : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ lengthScale : ℝ, 0 < lengthScale →
      ∀ (Ω : Finset (Finset ι × O)) (w : Finset ι × O → ℂ),
      (∀ x ∈ Ω, x.2 ≠ 0) → ∃ b : (Finset ι × O) → 𝓢(ℝ, ℂ),
      (∀ x ∈ Ω, Integrable (fun t : ℝ => (1 + ‖t‖) ^ J * ‖b x t‖) volume ∧
        (1 + firstDualScale p (cubeActiveSupport B v ε₁ ε₂) lengthScale X₁ X₂
          (primeSubsetGenerator (fun i => Ideal.span {p i}) x.1) x.2) ^ A *
            (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b x t‖) ≤ K) ∧
      ‖∑ x ∈ Ω, (w x * firstDivisorWeight p x.1) *
        actualFirstKernel p hp hcop hg F B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ lengthScale
          (primeSubsetGenerator (fun i => Ideal.span {p i}) x.1) x.2‖ ≤
      (lengthScale / ‖eisEmbedding (∏ i ∈ cubeActiveSupport B v ε₁ ε₂, p i)‖) *
        Real.sqrt (∑ x ∈ Ω, ‖w x * firstDivisorWeight p x.1‖ *
          firstColumnEnergy p hp hcop hg F B v ε₁ ε₂ true C₁ V₁ X₁
            (primeSubsetGenerator (fun i => Ideal.span {p i}) x.1) x.2 (b x)) *
        Real.sqrt (∑ x ∈ Ω, ‖w x * firstDivisorWeight p x.1‖ *
          firstColumnEnergy p hp hcop hg F B v ε₁ ε₂ false C₂ V₂ X₂
            (primeSubsetGenerator (fun i => Ideal.span {p i}) x.1) x.2 (b x)) := by
  obtain ⟨K, hK, hs⟩ := actual_first_kernel_energy_bound p hp hinj hcop hg hc hpr F B hFB
    v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ hX₁ hX₂ M₁ M₂ hM₁ hM₂ hV₁ hV₂ A J
  refine ⟨K, hK, ?_⟩
  intro lengthScale hL Ω w hΩ
  let d := fun x : Finset ι × O => primeSubsetGenerator (fun i => Ideal.span {p i}) x.1
  have hfam : ∀ x : Finset ι × O, ∃ b : 𝓢(ℝ, ℂ), x ∈ Ω →
      Integrable (fun t : ℝ => (1 + ‖t‖) ^ J * ‖b t‖) volume ∧
      (1 + firstDualScale p (cubeActiveSupport B v ε₁ ε₂) lengthScale X₁ X₂ (d x) x.2) ^ A *
        (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) ≤ K ∧
      ‖actualFirstKernel p hp hcop hg F B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ lengthScale (d x) x.2‖ ≤
      (lengthScale / ‖eisEmbedding (∏ i ∈ cubeActiveSupport B v ε₁ ε₂, p i)‖) *
        Real.sqrt (firstColumnEnergy p hp hcop hg F B v ε₁ ε₂ true C₁ V₁ X₁ (d x) x.2 b) *
        Real.sqrt (firstColumnEnergy p hp hcop hg F B v ε₁ ε₂ false C₂ V₂ X₂ (d x) x.2 b) := by
    intro x
    by_cases hx : x ∈ Ω
    · obtain ⟨b, hb⟩ := hs lengthScale hL (d x) x.2 (primeSubsetGenerator_ne_zero _ _) (hΩ x hx)
      exact ⟨b, fun _ => hb⟩
    · exact ⟨0, fun hx' => (hx hx').elim⟩
  choose b hb using hfam
  refine ⟨b, fun x hx => ⟨(hb x hx).1, (hb x hx).2.1⟩, ?_⟩
  let U := fun x => firstColumnEnergy p hp hcop hg F B v ε₁ ε₂ true C₁ V₁ X₁ (d x) x.2 (b x)
  let V := fun x => firstColumnEnergy p hp hcop hg F B v ε₁ ε₂ false C₂ V₂ X₂ (d x) x.2 (b x)
  let a := fun x => ‖w x * firstDivisorWeight p x.1‖
  let q := lengthScale / ‖eisEmbedding (∏ i ∈ cubeActiveSupport B v ε₁ ε₂, p i)‖
  have hq : 0 ≤ q := div_nonneg hL.le (norm_nonneg _)
  have hU (x) : 0 ≤ U x := firstColumnEnergy_nonneg p hp hcop hg F B v ε₁ ε₂ true C₁ V₁ X₁ _ _ _
  have hV (x) : 0 ≤ V x := firstColumnEnergy_nonneg p hp hcop hg F B v ε₁ ε₂ false C₂ V₂ X₂ _ _ _
  have hterm (x) : a x * (Real.sqrt (U x) * Real.sqrt (V x)) =
      Real.sqrt (a x * U x) * Real.sqrt (a x * V x) := by
    rw [Real.sqrt_mul (norm_nonneg _), Real.sqrt_mul (norm_nonneg _)]
    calc
      _ = (Real.sqrt (a x)) ^ 2 * (Real.sqrt (U x) * Real.sqrt (V x)) := by
        rw [Real.sq_sqrt (norm_nonneg _)]
      _ = _ := by ring
  calc
    _ ≤ ∑ x ∈ Ω, ‖(w x * firstDivisorWeight p x.1) *
        actualFirstKernel p hp hcop hg F B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ lengthScale (d x) x.2‖ :=
      norm_sum_le _ _
    _ ≤ ∑ x ∈ Ω, q * (Real.sqrt (a x * U x) * Real.sqrt (a x * V x)) := by
      apply Finset.sum_le_sum
      intro x hx
      rw [norm_mul, ← hterm]
      calc
        _ ≤ a x * (q * Real.sqrt (U x) * Real.sqrt (V x)) :=
          mul_le_mul_of_nonneg_left (hb x hx).2.2 (norm_nonneg _)
        _ = _ := by ring
    _ = q * (∑ x ∈ Ω, Real.sqrt (a x * U x) * Real.sqrt (a x * V x)) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ q * (Real.sqrt (∑ x ∈ Ω, a x * U x) * Real.sqrt (∑ x ∈ Ω, a x * V x)) :=
      mul_le_mul_of_nonneg_left (Real.sum_sqrt_mul_sqrt_le Ω
        (fun x => mul_nonneg (norm_nonneg _) (hU x))
        (fun x => mul_nonneg (norm_nonneg _) (hV x))) hq
    _ = _ := (mul_assoc _ _ _).symm
end OAI.FirstPassCubeLabels
