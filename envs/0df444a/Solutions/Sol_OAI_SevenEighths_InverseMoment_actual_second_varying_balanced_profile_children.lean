-- Prove2me | solution 1 for OAI.SevenEighths.InverseMoment.actual_second_varying_balanced_profile_children
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T02:00:36.168504+00:00
-- url     : https://prove2.me/submissions/709827f1-ac4f-4348-b6ff-62b346177b2a

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIHecke78B019

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.RamifiedTracePhase
namespace OAI

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

namespace ActualEisensteinCubic

theorem finiteSquarefreeRow_sixth_power
    {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i) (S : Finset ι) (a : O) :
    finiteSquarefreeRow P hgood S (a ^ 6) =
      if ∃ i ∈ S, a ∈ P i then 0 else 1 := by
  classical
  simp only [finiteSquarefreeRow]
  by_cases hex : ∃ i ∈ S, a ∈ P i
  · obtain ⟨i, hi, hai⟩ := hex
    rw [if_pos ⟨i, hi, hai⟩]
    apply Finset.prod_eq_zero hi
    rw [canonicalSextic_sixth_power_mask]
    simp [hai]
  · rw [if_neg hex]
    apply Finset.prod_eq_one
    intro i hi
    rw [canonicalSextic_sixth_power_mask]
    simp [show a ∉ P i by intro hai; exact hex ⟨i, hi, hai⟩]

end ActualEisensteinCubic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.IdealGenerators
namespace OAI

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

namespace ActualEisensteinCubic

theorem primeSubsetGenerator_ne_zero {ι : Type*}
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (E : Finset ι) :
    primeSubsetGenerator P E ≠ 0 := by
  apply ConcretePrimeRowBridge.idealGenerator_ne_zero
  change (∏ i ∈ E, P i) ≠ 0
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne (P i))

open ConcreteTraceCRT

open ConcreteTraceCRT EisensteinSchwartzPoisson

end ActualEisensteinCubic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Arithmetic.SquarefreeDivisors
namespace OAI

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

open scoped BigOperators Classical
namespace FirstPassCubeLabels
open ActualEisensteinCubic

section Rows
variable {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
  (hg : ∀ i, lambda ∉ P i) (S : Finset ι)

theorem row_pow (a : O) (m : ℕ) :
    finiteSquarefreeRow P hg S (a ^ m) = finiteSquarefreeRow P hg S a ^ m := by
  simp only [finiteSquarefreeRow, map_pow, Finset.prod_pow]

theorem row_sixth (a : O) :
    finiteSquarefreeRow P hg S a ^ 6 = rowCoprimeMask P S a := by
  rw [← row_pow, finiteSquarefreeRow_sixth_power]
  rfl

include hg

theorem mask_mul (a b : O) :
    rowCoprimeMask P S (a * b) = rowCoprimeMask P S a * rowCoprimeMask P S b := by
  simp only [← row_sixth P hg S, finiteSquarefreeRow_mul, mul_pow]

theorem row_zero_of_mask_zero (a : O) (h : rowCoprimeMask P S a = 0) :
    finiteSquarefreeRow P hg S a = 0 := by
  have hq := row_sixth P hg S a
  rw [h] at hq
  exact (pow_eq_zero_iff (by decide : (6 : ℕ) ≠ 0)).mp hq

end Rows

theorem b0Exponent_pos_of_not_retained (m : ℕ) (ε₁ ε₂ : Bool) (hm : 0 < m)
    (hret : retained (parity m) ε₁ ε₂ = false) : 0 < b0Exponent m ε₁ ε₂ := by
  have hmod := Nat.mod_lt m (by decide : 0 < 2)
  have hdiv := Nat.mod_add_div m 2
  cases ε₁ <;> cases ε₂ <;> by_cases h : m % 2 = 1 <;>
    simp_all [b0Exponent, evenDouble, parity, retained, bit] <;> omega

end FirstPassCubeLabels

open scoped BigOperators Classical SchwartzMap

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.RayExpansion
namespace OAI

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

open scoped BigOperators Classical
namespace FirstPassCubeLabels

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory

open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)
open EisensteinSchwartzPoisson (paperRadialFourier)

theorem primeProductNorm_pos {ι : Type*} (p : ι → O) (hp : ∀ i, p i ≠ 0) (S : Finset ι) :
    0 < primeProductNorm p S :=
  pow_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)))) 2

theorem primeProductNorm_union {ι : Type*} [DecidableEq ι]
    (p : ι → O) (S T : Finset ι) (hd : Disjoint S T) :
    primeProductNorm p (S ∪ T) = primeProductNorm p S * primeProductNorm p T := by
  simp only [primeProductNorm, Finset.prod_union hd, map_mul, norm_mul, mul_pow]

end FirstPassCubeLabels

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Fourier.FrequencyTwists
namespace OAI

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

namespace JointLogSeparation

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform
open FourierBridge

lemma logPhase_add_frequency (t s x : ℝ) :
    logPhase (t + s) x = logPhase t x * logPhase s x := by
  unfold logPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

@[simp] lemma frequencyTwist_twice (g : 𝓢(ℝ, ℂ)) (t s : ℝ) :
    frequencyTwist (frequencyTwist g t) s = frequencyTwist g (t + s) := by
  ext x
  simp only [frequencyTwist_apply, logPhase_add_frequency]
  ring

end JointLogSeparation

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.ChildTransfer
namespace OAI

noncomputable section

namespace SecondPassArithmetic

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

section

open scoped BigOperators Classical

section
open ActualEisensteinCubic
open FirstCauchyArithmetic (supportMobius)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
include hg

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] hg in
theorem secondMaskQuotient_spec (E G : Finset ι) (hEG : E ⊆ G) :
    (∏ i ∈ G, p i) = primeSubsetGenerator (fun i => Ideal.span {p i}) E *
      secondMaskQuotient p E G hEG :=
  Classical.choose_spec (poisson_mask_generator_dvd p E G hEG)

end

open ActualEisensteinCubic

theorem secondMaskQuotient_span {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (E G : Finset ι) (hEG : E ⊆ G) :
    Ideal.span {secondMaskQuotient p E G hEG} =
      ∏ i ∈ G \ E, Ideal.span {p i} := by
  have hE : (∏ i ∈ E, Ideal.span {p i}) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne (Ideal.span {p i}))
  have he : Ideal.span {primeSubsetGenerator (fun i => Ideal.span {p i}) E} =
      ∏ i ∈ E, Ideal.span {p i} := by
    rw [primeSubsetGenerator, ConcretePrimeRowBridge.span_idealGenerator]
  apply mul_left_cancel₀ hE
  calc
    _ = Ideal.span {primeSubsetGenerator (fun i => Ideal.span {p i}) E *
        secondMaskQuotient p E G hEG} := by rw [← he, Ideal.span_singleton_mul_span_singleton]
    _ = Ideal.span {∏ i ∈ G, p i} := by rw [← secondMaskQuotient_spec]
    _ = ∏ i ∈ G, Ideal.span {p i} := FiniteGaussPhase.span_finset_prod G p
    _ = _ := by simpa only [mul_comm] using
      (Finset.prod_sdiff (f := fun i => Ideal.span {p i}) hEG).symm

end

open scoped BigOperators Classical
open ActualEisensteinCubic
open FirstPassCubeLabels (cubeCoreCoefficient cubeOddSupport coreRayCoefficient coreRayTwist
  coreRayCharacter dilatedCoreRow dilatedRayColumn afterDilationLabel b0Label jLabel)
open FirstCauchyArithmetic (supportMobius supportRay supportConjugateSum)
open RayFourExpansion (RayCharacter)
open FourierBridge (logPhase)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

end SecondPassArithmetic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.FrequencyBlocks
namespace OAI

noncomputable section

namespace SecondPassArithmetic

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

section

open scoped BigOperators Classical

section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct cubeRadical aLabel jLabel j2Label squarefreeLabel b0Label
  bit retained parity b0Exponent)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem cubeRadical_dvd_jLabel_b0 (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (hv : ∀ i ∈ B, 0 < v i) : cubeRadical p B ∣ jLabel p B v ε₁ ε₂ * b0Label p B v ε₁ ε₂ := by
  have hle (i : ι) (hi : i ∈ B) :
      1 ≤ bit (retained (parity (v i)) (ε₁ i) (ε₂ i)) + b0Exponent (v i) (ε₁ i) (ε₂ i) := by
    cases h : retained (parity (v i)) (ε₁ i) (ε₂ i)
    · have hp := FirstPassCubeLabels.b0Exponent_pos_of_not_retained (v i) (ε₁ i) (ε₂ i) (hv i hi) h
      simp only [bit,  Bool.false_eq_true, ite_false, zero_add]
      omega
    · simp only [bit,  ite_true]
      omega
  have hd := Finset.prod_dvd_prod_of_dvd (s := B) (fun i => p i ^ 1)
    (fun i => p i ^ (bit (retained (parity (v i)) (ε₁ i) (ε₂ i)) + b0Exponent (v i) (ε₁ i) (ε₂ i)))
    (fun i hi => pow_dvd_pow (p i) (hle i hi))
  simpa only [cubeRadical, jLabel, b0Label, primeProduct, pow_one, pow_add,
    Finset.prod_mul_distrib] using hd

end

open ActualEisensteinCubic
open FirstPassCubeLabels (jLabel b0Label primeProductNorm)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]

end

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform
open ActualEisensteinCubic
open JointLogSeparation
open FirstPassCubeLabels (b0Label)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

end SecondPassArithmetic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.ConjugateProfiles
namespace OAI

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

open scoped BigOperators Classical SchwartzMap ContDiff FourierTransform
namespace SecondPassIntegration
open JointLogSeparation FourierBridge

lemma logPhase_conjugate (t x : ℝ) : star (logPhase t x) = logPhase (-t) x := by
  unfold logPhase
  simp only [Complex.star_def, ← Complex.exp_conj, map_mul, Complex.conj_ofReal,
    Complex.conj_I]
  congr 1
  push_cast
  ring

end SecondPassIntegration

open scoped BigOperators Classical

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.FrequencyCutoffs
namespace OAI

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
open ActualEisensteinCubic ShortDraftLatticeCount
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
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog primeProductNorm primeProductNorm_pos)
open ConcreteTraceCRT (eisEmbedding)

theorem mem_secondFrequencyCutoff (scale H : ℝ) (k : O)
    (hk : ‖eisEmbedding k‖^2 ≤ H/scale) : k ∈ secondFrequencyCutoff scale H := by
  apply ShortDraftLatticeCount.mem_rowNormBall_of_absNorm_le
  rw [eisEmbedding_norm_sq_eq_absNorm_span] at hk
  exact_mod_cast hk.trans (Nat.le_ceil (H/scale))

end

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff FourierTransform
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open FirstPassCubeLabels (columnLog jLabel b0Label )
open JointLogSeparation (tripleCoefficient)

end SecondPassArithmetic

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.SeedDefects
namespace OAI

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

open scoped BigOperators Classical

open scoped BigOperators Classical
namespace SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct primeProductNorm squarefreeLabel jLabel j2Label b0Label
  bit parity conductorExponent cubeActiveSupport)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]

include hp in
omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
lemma primeProduct_ne_zero (B : Finset ι) (v : ι → ℕ) : primeProduct p B v ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun i _hi => pow_ne_zero _ (hp i))

end SecondPassArithmetic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.GlobalEncoding
namespace OAI

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

open scoped BigOperators Classical SchwartzMap

open scoped BigOperators Classical
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct aLabel b0Label jLabel cubeActiveSupport primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

namespace CubeCoordinates
variable {ι : Type*} [DecidableEq ι]

theorem support_pos (x : CubeCoordinates ι) (i : ι) (hi : i ∈ x.support) :
    0 < x.leftExponent i+x.rightExponent i := by
  simp only [support,Finset.mem_union,Finsupp.mem_support_iff] at hi
  omega

end CubeCoordinates

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]

end

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct aLabel)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hinj : Function.Injective (fun i => Ideal.span {p i}))
include hinj

end SecondPassArithmetic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.PrincipalNormalization
namespace OAI

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
open ActualEisensteinCubic ShortDraftLatticeCount
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
namespace SecondPassArithmetic

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm b0Label jLabel cubeRadical)
open ConcretePrimeRowBridge (idealGenerator span_idealGenerator)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem rowCoprimeMask_congr_span (S : Finset ι) {a b : O}
    (h : Ideal.span {a}=Ideal.span {b}) :
    rowCoprimeMask (fun i => Ideal.span {p i}) S a = rowCoprimeMask (fun i => Ideal.span {p i}) S b := by
  have hm (i : ι) : a ∈ Ideal.span {p i} ↔ b ∈ Ideal.span {p i} := by
    rw [← Ideal.span_singleton_le_iff_mem, h, Ideal.span_singleton_le_iff_mem]
  simp only [rowCoprimeMask,hm]

theorem fixedChildRow_congr_mask_span (F : Finset ι) (Ψ : O →* ℂ) {a b : O}
    (h : Ideal.span {a}=Ideal.span {b}) (H : Finset ι → ℂ) (f y : O) :
    fixedChildRow p hp hcop hg F Ψ a H f y = fixedChildRow p hp hcop hg F Ψ b H f y := by
  simp only [fixedChildRow,secondChildColumn,rowCoprimeMask_congr_span p _ h]

theorem secondChildColumn_zero_of_mask_label_mem (Ψ : O →* ℂ) (m f y : O)
    (H : Finset ι → ℂ) (S : Finset ι) (i : ι) (hi : i ∈ S)
    (hmf : m*f ∈ Ideal.span {p i}) :
    secondChildColumn p hp hcop hg Ψ m f y H S = 0 := by
  rcases (inferInstance : (Ideal.span {p i}).IsPrime).mem_or_mem hmf with hm|hf
  · have hz : rowCoprimeMask (fun i => Ideal.span {p i}) S m=0 := by
      simp only [rowCoprimeMask,if_pos (show ∃ i∈S,m ∈ Ideal.span {p i} from ⟨i,hi,hm⟩)]
    simp only [secondChildColumn,hz,mul_zero,zero_mul]
  · have hz : rowCoprimeMask (fun i => Ideal.span {p i}) S f=0 := by
      simp only [rowCoprimeMask,if_pos (show ∃ i∈S,f ∈ Ideal.span {p i} from ⟨i,hi,hf⟩)]
    have hr := FirstPassCubeLabels.row_zero_of_mask_zero (fun i => Ideal.span {p i}) hg S f hz
    simp only [secondChildColumn,hr,zero_pow (by decide : (4 : ℕ) ≠ 0),mul_zero,zero_mul]

theorem fixedChildRow_restore_killed_pool (F B : Finset ι) (Ψ : O →* ℂ)
    (m f y : O) (H : Finset ι → ℂ) (hB : ∀ i∈B,m*f ∈ Ideal.span {p i}) :
    fixedChildRow p hp hcop hg (F\B) Ψ m H f y = fixedChildRow p hp hcop hg F Ψ m H f y := by
  unfold fixedChildRow
  apply Finset.sum_subset (Finset.powerset_mono.mpr Finset.sdiff_subset)
  intro S hS hn
  have hd : ¬ Disjoint B S := by
    intro hd
    apply hn
    apply Finset.mem_powerset.mpr
    intro i hi
    exact Finset.mem_sdiff.mpr ⟨(Finset.mem_powerset.mp hS) hi,
      fun hiB => Finset.disjoint_left.mp hd hiB hi⟩
  obtain ⟨i,hiB,hiS⟩ := Finset.not_disjoint_iff.mp hd
  exact secondChildColumn_zero_of_mask_label_mem p hp hcop hg Ψ m f y H S i hiS (hB i hiB)

end SecondPassArithmetic

open scoped BigOperators Classical SchwartzMap

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.WindowFourier
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge JointLogSeparation
noncomputable section

variable {ι : Type*} [Fintype ι]

 theorem pureProfileMode_norm (a₁ a₂ ak : ι → ℝ) (y : ι → ℝ)
    (t : Frequency) (u : ι → ℝ) : ‖pureProfileMode a₁ a₂ ak y t u‖ = 1 := by
  simp [pureProfileMode, norm_prod,  logPhase_norm]

lemma logPhase_scaled_coordinate (t a y : ℝ) : logPhase t (a*y) = logPhase (a*t) y := by
  unfold logPhase
  congr 1
  push_cast
  ring

theorem pureProfileMode_height (a₁ a₂ ak y : ι → ℝ) (t : Frequency) (u : ι → ℝ) :
    pureProfileMode a₁ a₂ ak y t u = ∏ i, logPhase (profileHeight a₁ a₂ ak t u i) (y i) := by
  apply Finset.prod_congr rfl
  intro i hi
  simp only [profileHeight, logPhase_add_frequency, logPhase_scaled_coordinate]

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.Marks
namespace OAI

namespace SevenEighths.InverseMoment

open scoped BigOperators

noncomputable section

variable {σ ι : Type*} [DecidableEq σ] [DecidableEq ι]

theorem primeSlot_priority (L A B : Finset ι) (a : ι → ℂ) :
    primeSlot L a (A ∪ B) = primeSlot L a A + primeSlot L a (B \ A) := by
  unfold primeSlot
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hA : p ∈ A <;> by_cases hB : p ∈ B <;> simp [hA, hB]

theorem primeMark_priority (I : Finset σ) (L : σ → Finset ι)
    (a : σ → ι → ℂ) (A B : Finset ι) :
    primeMark I L a (A ∪ B) =
      ∑ J ∈ I.powerset, primeMark J L a A * primeMark (I \ J) L a (B \ A) := by
  unfold primeMark
  simp_rw [primeSlot_priority]
  exact Finset.prod_add _ _ I

theorem primeSlot_residual_list (L A B : Finset ι) (a : ι → ℂ) :
    primeSlot L a (B \ A) = primeSlot (L \ A) a B := by
  simp only [primeSlot, Finset.sum_ite_mem]
  congr 1
  ext p
  simp only [Finset.mem_inter, Finset.mem_sdiff]
  tauto

omit [DecidableEq σ] in
theorem primeMark_residual_lists (I : Finset σ) (L : σ → Finset ι)
    (a : σ → ι → ℂ) (A B : Finset ι) :
    primeMark I L a (B \ A) = primeMark I (fun i => L i \ A) a B := by
  unfold primeMark
  apply Finset.prod_congr rfl
  intro i hi
  exact primeSlot_residual_list _ _ _ _

end

end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.Canonical
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem secondChildSum_marked_canonical
    (F V A : Finset ι) (Ψ : Eis →* ℂ) (m r c d e k : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (W : ℝ → ℂ) (X : ℝ) :
    secondChildSum p hp hcop hg F V Ψ m r c d e k
      (fun U => primeMark slots lists a (A ∪ U) * W (primeProductNorm p U / X)) =
    ∑ J ∈ slots.powerset, primeMark J lists a (A ∪ V) *
      finiteCanonicalMarkedRow p hp hcop hg (F \ V) Ψ (m * r)
        (c * e * ∏ i ∈ V, p i) (d * e * k)
        (slots \ J) (fun i => lists i \ (A ∪ V)) a W (X / primeProductNorm p V) := by
  unfold secondChildSum finiteCanonicalMarkedRow fixedChildRow
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro N hN
  have hd : Disjoint V N := Finset.disjoint_left.mpr (fun i hi hn =>
    (Finset.mem_sdiff.mp (Finset.mem_powerset.mp hN hn)).2 hi)
  have hn : primeProductNorm p (V ∪ N) / X = primeProductNorm p N / (X / primeProductNorm p V) := by
    rw [primeProductNorm_union p V N hd]
    simp only [div_div_eq_mul_div]
    ring
  have hmark := primeMark_priority slots lists a (A ∪ V) N
  simp only [primeMark_residual_lists] at hmark
  simp only [secondChildColumn, ← Finset.union_assoc, hn]
  rw [hmark]
  simp only [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J hJ
  ring

omit [DecidableEq σ] in
theorem finiteCanonicalMarkedRow_restore_pool
    (pool B : Finset ι) (Ψ : Eis →* ℂ) (m f k : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (W : ℝ → ℂ) (X : ℝ)
    (hB : ∀ i ∈ B, m * f ∈ Ideal.span {p i}) :
    finiteCanonicalMarkedRow p hp hcop hg (pool \ B) Ψ m f k slots lists a W X =
      finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots lists a W X :=
  fixedChildRow_restore_killed_pool p hp hcop hg pool B Ψ m f k _ hB

omit [DecidableEq σ] in
theorem finiteCanonicalMarkedRow_restore_lists
    (pool B : Finset ι) (Ψ : Eis →* ℂ) (m f k : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (W : ℝ → ℂ) (X : ℝ)
    (hB : ∀ i ∈ B, m * f ∈ Ideal.span {p i}) :
    finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots (fun i => lists i \ B) a W X =
      finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots lists a W X := by
  unfold finiteCanonicalMarkedRow fixedChildRow
  apply Finset.sum_congr rfl
  intro U hU
  by_cases hd : Disjoint B U
  · have he : U \ B = U := Finset.sdiff_eq_self_of_disjoint hd.symm
    simp only [secondChildColumn, ← primeMark_residual_lists, he]
  · obtain ⟨i, hiB, hiU⟩ := Finset.not_disjoint_iff.mp hd
    rw [secondChildColumn_zero_of_mask_label_mem p hp hcop hg Ψ m f k _ U i hiU (hB i hiB),
      secondChildColumn_zero_of_mask_label_mem p hp hcop hg Ψ m f k _ U i hiU (hB i hiB)]

theorem secondChildSum_marked_fixed_pool
    (F V A : Finset ι) (Ψ : Eis →* ℂ) (m r c d e k : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (W : ℝ → ℂ) (X : ℝ) :
    secondChildSum p hp hcop hg F V Ψ m r c d e k
      (fun U => primeMark slots lists a (A ∪ U) * W (primeProductNorm p U / X)) =
    ∑ J ∈ slots.powerset, primeMark J lists a (A ∪ V) *
      finiteCanonicalMarkedRow p hp hcop hg F Ψ (m * r)
        (c * e * ∏ i ∈ V, p i) (d * e * k)
        (slots \ J) (fun i => lists i \ A) a W (X / primeProductNorm p V) := by
  rw [secondChildSum_marked_canonical]
  apply Finset.sum_congr rfl
  intro J hJ
  congr 1
  have hV (i : ι) (hi : i ∈ V) : (m * r) * (c * e * ∏ j ∈ V, p j) ∈ Ideal.span {p i} :=
    Ideal.mem_span_singleton.mpr (dvd_mul_of_dvd_right
      (dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem p hi) (c * e)) (m * r))
  rw [finiteCanonicalMarkedRow_restore_pool p hp hcop hg F V Ψ (m * r)
    (c * e * ∏ i ∈ V, p i) (d * e * k) _ _ _ _ _ hV]
  have hlists : (fun i => lists i \ (A ∪ V)) = (fun i => (lists i \ A) \ V) := by
    funext i
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_union]
    tauto
  rw [hlists]
  exact finiteCanonicalMarkedRow_restore_lists p hp hcop hg F V Ψ (m * r)
    (c * e * ∏ i ∈ V, p i) (d * e * k) _ _ _ _ _ hV

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.SecondProfileIdentity
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open EisensteinSchwartzPoisson
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma secondPoissonProfile_log (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ))
    (V : Fin 6 → ℝ → ℂ) (R : ℝ) (q : Fin 6 → ℝ) (hq : ∀ i, 0 < q i) :
    secondPoissonProfile W₁ W₂ Φ V R (fun i => Real.log (q i)) =
      secondNormProfile W₁ W₂ Φ V R q := by
  have hleft : (∑ i, secondLeftSlope i * Real.log (q i)) =
      Real.log (q 0)+Real.log (q 2)+Real.log (q 4) := by
    simp [Fin.sum_univ_succ,secondLeftSlope]; ring
  have hright : (∑ i, secondRightSlope i * Real.log (q i)) =
      Real.log (q 0)+Real.log (q 2)+Real.log (q 5) := by
    simp [Fin.sum_univ_succ,secondRightSlope]; ring
  have hker : (∑ i, secondKernelSlope i * Real.log (q i)) =
      Real.log (q 3) - (Real.log (q 1)+Real.log (q 2)+Real.log (q 2)+Real.log (q 4)+Real.log (q 5)) := by
    simp [Fin.sum_univ_succ,secondKernelSlope]; ring
  unfold secondPoissonProfile secondNormProfile
  rw [hleft,hright,hker]
  simp only [Real.exp_add,Real.exp_sub,Real.exp_log (hq _)]
  have hk : R * (q 3/(q 1*q 2*q 2*q 4*q 5)) = R*q 3/(q 1*(q 2)^2*q 4*q 5) := by ring
  rw [hk]
  simp only [Fin.prod_univ_succ,secondRootWindows,inverseNormWindow,inverseRootWindow,
    Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.isValue,Real.exp_log (hq _),Fin.prod_univ_zero,mul_one]
  simp only [Fin.succ,  Fin.val_mk]
  ((try simp ) <;> norm_num )
  ring

theorem secondSourcePairKernel_profile {ι : Type*} [DecidableEq ι]
    (p : ι → Eis) (hp : ∀ i, p i ≠ 0)
    (G V N M : Finset ι) (hVN : Disjoint V N) (hVM : Disjoint V M)
    (e k : Eis) (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (Y : ℝ) :
    (‖eisEmbedding e‖^2 : ℂ)⁻¹ * secondSourcePairKernel p e k
      (fun U => W₁ (primeProductNorm p G * primeProductNorm p U))
      (fun U => W₂ (primeProductNorm p G * primeProductNorm p U)) Φ Y (V ∪ N) (V ∪ M) =
    secondNormProfile (fun x => star (W₁ x)) W₂ Φ (fun _ _ => 1) Y
      ![primeProductNorm p G, ‖eisEmbedding e‖^2, primeProductNorm p V,
        ‖eisEmbedding k‖^2, primeProductNorm p N, primeProductNorm p M] := by
  have hs (S : Finset ι) : ‖eisEmbedding (∏ i ∈ S, p i)‖ = Real.sqrt (primeProductNorm p S) := by
    simp only [primeProductNorm, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
  have hV : 0 ≤ primeProductNorm p V := (primeProductNorm_pos p hp V).le
  have hroots : Real.sqrt (primeProductNorm p V*primeProductNorm p N) *
      Real.sqrt (primeProductNorm p V*primeProductNorm p M) =
      primeProductNorm p V * Real.sqrt (primeProductNorm p N) * Real.sqrt (primeProductNorm p M) := by
    rw [Real.sqrt_mul hV, Real.sqrt_mul hV]
    calc
      _ = (Real.sqrt (primeProductNorm p V))^2 * Real.sqrt (primeProductNorm p N) * Real.sqrt (primeProductNorm p M) := by ring
      _ = _ := by rw [Real.sq_sqrt hV]
  unfold secondSourcePairKernel secondNormProfile
  simp only [hs,primeProductNorm_union p V N hVN,primeProductNorm_union p V M hVM,
    Matrix.cons_val_zero,  Fin.isValue, Finset.prod_const_one, one_mul]
  have harg : Y * ‖eisEmbedding k‖^2 /
      (‖eisEmbedding e‖^2 * (primeProductNorm p V*primeProductNorm p N *
        (primeProductNorm p V*primeProductNorm p M))) =
      Y * ‖eisEmbedding k‖^2 / (‖eisEmbedding e‖^2 * (primeProductNorm p V)^2 *
        primeProductNorm p N * primeProductNorm p M) := by ring
  rw [harg]
  rw [← Complex.ofReal_mul, hroots]
  push_cast
  ring_nf

theorem secondNormProfile_nominal (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ))
    (G₀ E₀ V₀ K₀ X₀ Y : ℝ)
    (_hG : 0 < G₀) (hE : 0 < E₀) (hV : 0 < V₀) (hK : 0 < K₀) (hX : 0 < X₀)
    (q : Fin 6 → ℝ) (hq : ∀ i, 0 < q i) :
    secondNormProfile (fun x => W₁ (x/(G₀*V₀*X₀)))
      (fun x => W₂ (x/(G₀*V₀*X₀))) Φ (fun _ _ => 1) Y q =
      ((E₀*V₀*X₀ : ℝ):ℂ)⁻¹ *
        secondNormProfile W₁ W₂ Φ (fun _ _ => 1)
          (Y*K₀/(E₀*V₀^2*X₀^2))
          ![q 0/G₀,q 1/E₀,q 2/V₀,q 3/K₀,q 4/X₀,q 5/X₀] := by
  have hleft : (q 0/G₀)*(q 2/V₀)*(q 4/X₀) = q 0*q 2*q 4/(G₀*V₀*X₀) := by ring
  have hright : (q 0/G₀)*(q 2/V₀)*(q 5/X₀) = q 0*q 2*q 5/(G₀*V₀*X₀) := by ring
  have harg : (Y*K₀/(E₀*V₀^2*X₀^2))*(q 3/K₀)/
      ((q 1/E₀)*(q 2/V₀)^2*(q 4/X₀)*(q 5/X₀)) =
      Y*q 3/(q 1*(q 2)^2*q 4*q 5) := by
    field_simp
  have hroot : Real.sqrt (q 4/X₀)*Real.sqrt (q 5/X₀) =
      Real.sqrt (q 4)*Real.sqrt (q 5)/X₀ := by
    rw [Real.sqrt_div (hq 4).le,Real.sqrt_div (hq 5).le]
    rw [div_mul_div_comm, ← pow_two, Real.sq_sqrt hX.le]
  have hc0 : ![q 0/G₀,q 1/E₀,q 2/V₀,q 3/K₀,q 4/X₀,q 5/X₀] (0:Fin 6) = q 0/G₀ := rfl
  have hc1 : ![q 0/G₀,q 1/E₀,q 2/V₀,q 3/K₀,q 4/X₀,q 5/X₀] (1:Fin 6) = q 1/E₀ := rfl
  have hc2 : ![q 0/G₀,q 1/E₀,q 2/V₀,q 3/K₀,q 4/X₀,q 5/X₀] (2:Fin 6) = q 2/V₀ := rfl
  have hc3 : ![q 0/G₀,q 1/E₀,q 2/V₀,q 3/K₀,q 4/X₀,q 5/X₀] (3:Fin 6) = q 3/K₀ := rfl
  have hc4 : ![q 0/G₀,q 1/E₀,q 2/V₀,q 3/K₀,q 4/X₀,q 5/X₀] (4:Fin 6) = q 4/X₀ := rfl
  have hc5 : ![q 0/G₀,q 1/E₀,q 2/V₀,q 3/K₀,q 4/X₀,q 5/X₀] (5:Fin 6) = q 5/X₀ := rfl
  unfold secondNormProfile
  simp only [Finset.prod_const_one,one_mul,hc0,hc1,hc2,hc3,hc4,hc5]
  rw [hleft,hright,harg]
  have hrootC : (Real.sqrt (q 4/X₀):ℂ)*(Real.sqrt (q 5/X₀):ℂ) =
      (Real.sqrt (q 4):ℂ)*(Real.sqrt (q 5):ℂ)/(X₀:ℂ) := by exact_mod_cast hroot
  rw [show (↑(q 1/E₀):ℂ)*↑(q 2/V₀)*↑(Real.sqrt (q 4/X₀))*↑(Real.sqrt (q 5/X₀)) =
      (↑(q 1/E₀):ℂ)*↑(q 2/V₀)*(↑(Real.sqrt (q 4/X₀))*↑(Real.sqrt (q 5/X₀))) from by ring,
    hrootC]
  have hEc : (E₀:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hE.ne'
  have hVc : (V₀:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hV.ne'
  have hXc : (X₀:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hX.ne'
  push_cast
  field_simp [hEc,hVc,hXc]

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.SecondKernelMeasure
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge JointLogSeparation
noncomputable section

lemma secondRelativeNorm_pos (q : Fin 6 → ℝ) (hq : ∀ i, 0 < q i)
    (G E V K X : ℝ) (hG : 0 < G) (hE : 0 < E) (hV : 0 < V) (hK : 0 < K) (hX : 0 < X) :
    ∀ i, 0 < secondRelativeNorm q G E V K X i := by
  intro i
  fin_cases i
  · exact div_pos (hq 0) hG
  · exact div_pos (hq 1) hE
  · exact div_pos (hq 2) hV
  · exact div_pos (hq 3) hK
  · exact div_pos (hq 4) hX
  · exact div_pos (hq 5) hX

lemma secondNormProfile_eq_full_of_windows (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ))
    (V : Fin 6 → ℝ → ℂ) (R : ℝ) (q : Fin 6 → ℝ) (hq : ∀ i, 0 < q i)
    (hV : ∀ i, V i (Real.log (q i)) = 1) :
    secondNormProfile W₁ W₂ Φ (fun _ _ => 1) R q =
      secondPoissonProfile W₁ W₂ Φ V R (fun i => Real.log (q i)) := by
  rw [secondPoissonProfile_log W₁ W₂ Φ V R q hq]
  simp only [secondNormProfile, hV, Finset.prod_const_one]

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.SecondWholeKernel
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma secondSourcePairKernel_mark_factors {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
    (p : ι → Eis) (e k : Eis)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (A₁ A₂ : Finset ι) (H₁ H₂ : Finset ι → ℂ) (W : 𝓢(ℝ,ℂ)) (Y : ℝ) (S T : Finset ι) :
    secondSourcePairKernel p e k
      (fun U => primeMark slots₁ lists₁ a₁ (A₁ ∪ U)*H₁ U)
      (fun U => primeMark slots₂ lists₂ a₂ (A₂ ∪ U)*H₂ U) W Y S T =
      star (primeMark slots₁ lists₁ a₁ (A₁ ∪ S)) * primeMark slots₂ lists₂ a₂ (A₂ ∪ T) *
        secondSourcePairKernel p e k H₁ H₂ W Y S T := by
  simp only [secondSourcePairKernel,star_mul]
  ring

theorem secondChildKernelPair_whole_profile {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
    (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (F G V A₁ A₂ : Finset ι) (Ψ₁ Ψ₂ : Eis →* ℂ) (m r c d e k : Eis)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (Y : ℝ) :
    (‖eisEmbedding e‖^2 : ℂ)⁻¹ * secondChildKernelPair p hp hcop hg F V Ψ₁ Ψ₂
      m r c d e k (-k)
      (secondSourcePairKernel p e k
        (fun U => primeMark slots₁ lists₁ a₁ (A₁ ∪ U)*W₁ (primeProductNorm p G*primeProductNorm p U))
        (fun U => primeMark slots₂ lists₂ a₂ (A₂ ∪ U)*W₂ (primeProductNorm p G*primeProductNorm p U)) Φ Y) =
    ∑ N ∈ (F \ V).powerset, ∑ M ∈ (F \ V).powerset,
      (star (secondChildColumn p hp hcop hg Ψ₁ (m*r) (c*e*∏ i ∈ V,p i)
        (d*e*k) (fun _ => 1) N) *
        secondChildColumn p hp hcop hg Ψ₂ (m*r) (c*e*∏ i ∈ V,p i)
          (d*e*(-k)) (fun _ => 1) M) *
      (star (primeMark slots₁ lists₁ a₁ (A₁ ∪ (V ∪ N))) *
        primeMark slots₂ lists₂ a₂ (A₂ ∪ (V ∪ M))) *
      secondNormProfile (fun x => star (W₁ x)) W₂ Φ (fun _ _ => 1) Y
        ![primeProductNorm p G,‖eisEmbedding e‖^2,primeProductNorm p V,
          ‖eisEmbedding k‖^2,primeProductNorm p N,primeProductNorm p M] := by
  unfold secondChildKernelPair
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro N hN
  apply Finset.sum_congr rfl
  intro M hM
  have hVN : Disjoint V N := Finset.disjoint_of_subset_right
    (Finset.mem_powerset.mp hN) disjoint_sdiff_self_right
  have hVM : Disjoint V M := Finset.disjoint_of_subset_right
    (Finset.mem_powerset.mp hM) disjoint_sdiff_self_right
  rw [secondSourcePairKernel_mark_factors]
  have hp := secondSourcePairKernel_profile p hp G V N M hVN hVM e k W₁ W₂ Φ Y
  rw [← hp]
  ring

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.ActualSecondProfile
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma secondActualNorms_pos {ι : Type*} (p : ι → Eis) (hp : ∀ i, p i ≠ 0)
    (x : SecondProfileData ι) (he : x.divisor ≠ 0) (hk : x.frequency ≠ 0) (N M : Finset ι) :
    ∀ i, 0 < secondActualNorms p x N M i := by
  intro i
  fin_cases i
  · exact primeProductNorm_pos p hp x.common
  · exact sq_pos_of_pos (norm_pos_iff.mpr (ConcreteTraceCRT.eisEmbedding_ne_zero he))
  · exact primeProductNorm_pos p hp x.overlap
  · exact sq_pos_of_pos (norm_pos_iff.mpr (ConcreteTraceCRT.eisEmbedding_ne_zero hk))
  · exact primeProductNorm_pos p hp N
  · exact primeProductNorm_pos p hp M

theorem actualSecondProfileRow_eq_whole {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
    (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (F : Finset ι) (x : SecondProfileData ι) (slots₁ slots₂ : Finset σ)
    (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (Y X : ℝ) :
    actualSecondProfileRow p hp hcop hg F x slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ Φ Y X =
      ∑ N ∈ (F \ x.overlap).powerset, ∑ M ∈ (F \ x.overlap).powerset,
        secondActualCoefficient p hp hcop hg x slots₁ slots₂ lists₁ lists₂ a₁ a₂ N M *
          secondNormProfile (fun z => star (W₁ (z/X))) (fun z => W₂ (z/X)) Φ (fun _ _ => 1) Y
            (secondActualNorms p x N M) :=
  secondChildKernelPair_whole_profile p hp hcop hg F x.common x.overlap x.extractedLeft x.extractedRight
    x.rayLeft x.rayRight x.puncture x.quotient x.oldLabel x.oldDivisor x.divisor x.frequency
    slots₁ slots₂ lists₁ lists₂ a₁ a₂ (fun z => W₁ (z/X)) (fun z => W₂ (z/X)) Φ Y

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.ActualSecondMeasure
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge JointLogSeparation
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma mem_secondProfileIndices {κ ι : Type*} [DecidableEq ι]
    (source : Finset κ) (F : Finset ι) (x : κ → SecondProfileData ι)
    (j : Σ _ : κ, Finset ι × Finset ι) : j ∈ secondProfileIndices source F x ↔
      j.1 ∈ source ∧ j.2.1 ∈ (F \ (x j.1).overlap).powerset ∧
        j.2.2 ∈ (F \ (x j.1).overlap).powerset := by
  simp only [secondProfileIndices,Finset.mem_sigma,Finset.mem_product]

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.ChildCutoff
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma mem_childFrequencyBall (a : Eis) (ha : a ≠ 0) (R : ℝ) (k : Eis) :
    k ∈ childFrequencyBall a R ↔ ‖eisEmbedding (a*k)‖^2 ≤ R := by
  have hn : 0 < ‖eisEmbedding a‖^2 := sq_pos_of_pos
    (norm_pos_iff.mpr (ConcreteTraceCRT.eisEmbedding_ne_zero ha))
  simp only [childFrequencyBall, Finset.mem_filter]
  refine ⟨fun h => h.2, fun h => ⟨?_,h⟩⟩
  apply mem_secondFrequencyCutoff
  apply (le_div_iff₀ hn).mpr
  simpa only [map_mul, norm_mul, mul_pow, mul_comm] using h

lemma mem_nonzeroChildFrequencyBall (a : Eis) (ha : a ≠ 0) (R : ℝ) (k : Eis) :
    k ∈ nonzeroChildFrequencyBall a R ↔
      0 < ‖eisEmbedding (a*k)‖^2 ∧ ‖eisEmbedding (a*k)‖^2 ≤ R := by
  have hn : 0 < ‖eisEmbedding (a*k)‖^2 ↔ k ≠ 0 := by
    rw [sq_pos_iff, norm_ne_zero_iff]
    constructor
    · intro h hk; apply h; simp [hk]
    · intro hk; exact ConcreteTraceCRT.eisEmbedding_ne_zero (mul_ne_zero ha hk)
  simp only [nonzeroChildFrequencyBall, Finset.mem_erase,
    mem_childFrequencyBall a ha, hn]

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.DensityAssembly
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open MeasureTheory FourierBridge JointLogSeparation
noncomputable section

theorem integrable_density_mode {ι : Type*} [Fintype ι]
    (D : Frequency × (ι → ℝ) → ℂ) (hD : Integrable D) (a₁ a₂ ak y : ι → ℝ) :
    Integrable (fun z : Frequency × (ι → ℝ) => D z *
      pureProfileMode a₁ a₂ ak y z.1 z.2) := by
  have hc : Continuous (fun z : Frequency × (ι → ℝ) => pureProfileMode a₁ a₂ ak y z.1 z.2) := by
    unfold pureProfileMode logPhase
    fun_prop
  exact hD.mul_bdd hc.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun z => (pureProfileMode_norm a₁ a₂ ak y z.1 z.2).le))

theorem density_finite_sum {ι κ : Type*} [Fintype ι] (s : Finset κ)
    (D : Frequency × (ι → ℝ) → ℂ) (hD : Integrable D) (a₁ a₂ ak : ι → ℝ)
    (c : κ → ℂ) (y : κ → ι → ℝ) :
    (∑ k ∈ s,c k * ∫ z : Frequency × (ι → ℝ),D z*pureProfileMode a₁ a₂ ak (y k) z.1 z.2) =
    ∫ z : Frequency × (ι → ℝ),D z * ∑ k ∈ s,c k*pureProfileMode a₁ a₂ ak (y k) z.1 z.2 := by
  simp only [← integral_const_mul]
  rw [← integral_finsetSum s (fun k hk => (integrable_density_mode D hD a₁ a₂ ak (y k)).const_mul (c k))]
  apply integral_congr_ae
  filter_upwards with z
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.FreshWindows
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem secondChildKernelPair_separated_marked {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
    (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (F V A₁ A₂ : Finset ι) (Ψ₁ Ψ₂ : Eis →* ℂ) (m r c d e k₁ k₂ : Eis)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ : ℝ) :
    secondChildKernelPair p hp hcop hg F V Ψ₁ Ψ₂ m r c d e k₁ k₂
      (fun S T => star (primeMark slots₁ lists₁ a₁ (A₁ ∪ S)*W₁ (primeProductNorm p S/X₁)) *
        (primeMark slots₂ lists₂ a₂ (A₂ ∪ T)*W₂ (primeProductNorm p T/X₂))) =
      star (canonicalMarkedSplit p hp hcop hg F V A₁ Ψ₁ m r c d e k₁ slots₁ lists₁ a₁ W₁ X₁) *
        canonicalMarkedSplit p hp hcop hg F V A₂ Ψ₂ m r c d e k₂ slots₂ lists₂ a₂ W₂ X₂ := by
  have hs (Ψ : Eis →* ℂ) (A : Finset ι) (k : Eis) (slots : Finset σ)
      (lists : σ → Finset ι) (a : σ → ι → ℂ) (W : ℝ → ℂ) (X : ℝ) :=
    secondChildSum_marked_fixed_pool p hp hcop hg F V A Ψ m r c d e k slots lists a W X
  unfold canonicalMarkedSplit
  rw [← hs Ψ₁ A₁ k₁ slots₁ lists₁ a₁ W₁ X₁, ← hs Ψ₂ A₂ k₂ slots₂ lists₂ a₂ W₂ X₂]
  unfold secondChildKernelPair secondChildSum
  rw [star_sum, Finset.sum_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro N hN
  apply Finset.sum_congr rfl
  intro M hM
  simp only [secondChildColumn,star_mul,mul_one]
  ring

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.GeneratorTransport
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem secondChildColumn_label_transfer (Ψ : Eis →* ℂ) (m a f k : Eis)
    (H : Finset ι → ℂ) (S : Finset ι) :
    secondChildColumn p hp hcop hg Ψ m (a*f) k H S =
      secondChildColumn p hp hcop hg Ψ m f (a^4*k) H S := by
  simp only [secondChildColumn, finiteSquarefreeRow, map_mul, map_pow,
    Finset.prod_mul_distrib, Finset.prod_pow, mul_pow]
  ring

omit [DecidableEq σ] in
theorem finiteCanonicalMarkedRow_label_transfer (F : Finset ι) (Ψ : Eis →* ℂ)
    (m a f k : Eis) (slots : Finset σ) (lists : σ → Finset ι) (coeff : σ → ι → ℂ)
    (W : ℝ → ℂ) (X : ℝ) :
    finiteCanonicalMarkedRow p hp hcop hg F Ψ m (a*f) k slots lists coeff W X =
      finiteCanonicalMarkedRow p hp hcop hg F Ψ m f (a^4*k) slots lists coeff W X := by
  simp only [finiteCanonicalMarkedRow,fixedChildRow,secondChildColumn_label_transfer]

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.SecondSeparatedColumns
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open FourierBridge JointLogSeparation ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma second_mode_split (y : Fin 6 → ℝ) (t : Frequency) (u : Fin 6 → ℝ) :
    pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope y t u =
      secondOuterPhase (profileHeight secondLeftSlope secondRightSlope secondKernelSlope t u) y *
        logPhase (profileHeight secondLeftSlope secondRightSlope secondKernelSlope t u 4) (y 4) *
        logPhase (profileHeight secondLeftSlope secondRightSlope secondKernelSlope t u 5) (y 5) := by
  rw [pureProfileMode_height]
  simp only [Fin.prod_univ_succ, secondOuterPhase]
  simp only [Fin.succ,  Fin.val_mk]
  ((try simp ) <;> norm_num )
  ring

lemma second_fresh_scale {ι : Type*} [DecidableEq ι] (p : ι → Eis)
    (hp : ∀ i, p i ≠ 0) (V N : Finset ι) (hVN : Disjoint V N) (X : ℝ) :
    primeProductNorm p (V ∪ N)/(primeProductNorm p V*X) = primeProductNorm p N/X := by
  rw [primeProductNorm_union p V N hVN]
  field_simp [(primeProductNorm_pos p hp V).ne']

theorem actual_second_columns_separated {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
    (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (F : Finset ι) (x : SecondProfileData ι) (slots₁ slots₂ : Finset σ)
    (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (ω₁ ω₂ : ℝ → ℂ) (X : ℝ) (h₁ h₂ : ℝ) :
    (∑ N ∈ (F \ x.overlap).powerset, ∑ M ∈ (F \ x.overlap).powerset,
      secondActualCoefficient p hp hcop hg x slots₁ slots₂ lists₁ lists₂ a₁ a₂ N M *
        (star (ω₁ (primeProductNorm p N/X)) * ω₂ (primeProductNorm p M/X)) *
        logPhase h₁ (Real.log (primeProductNorm p N/X)) *
        logPhase h₂ (Real.log (primeProductNorm p M/X))) =
    star (canonicalMarkedSplit p hp hcop hg F x.overlap x.extractedLeft x.rayLeft
      x.puncture x.quotient x.oldLabel x.oldDivisor x.divisor x.frequency
      slots₁ lists₁ a₁ (childLogTest ω₁ (-h₁)) (primeProductNorm p x.overlap*X)) *
      canonicalMarkedSplit p hp hcop hg F x.overlap x.extractedRight x.rayRight
      x.puncture x.quotient x.oldLabel x.oldDivisor x.divisor (-x.frequency)
      slots₂ lists₂ a₂ (childLogTest ω₂ h₂) (primeProductNorm p x.overlap*X) := by
  rw [← secondChildKernelPair_separated_marked]
  unfold secondChildKernelPair
  apply Finset.sum_congr rfl
  intro N hN
  apply Finset.sum_congr rfl
  intro M hM
  have hVN : Disjoint x.overlap N := by
    apply Finset.disjoint_left.mpr
    intro i hi hiN
    exact (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hN) hiN)).2 hi
  have hVM : Disjoint x.overlap M := by
    apply Finset.disjoint_left.mpr
    intro i hi hiM
    exact (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hM) hiM)).2 hi
  dsimp only
  rw [second_fresh_scale p hp x.overlap N hVN,second_fresh_scale p hp x.overlap M hVM]
  simp only [secondActualCoefficient,childLogTest,secondChildColumn,
    star_mul,SecondPassIntegration.logPhase_conjugate,neg_neg,mul_one]
  ring

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.SecondFreshAssembly
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open MeasureTheory FourierBridge JointLogSeparation ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem actual_second_full_mode_columns (F : Finset ι) (x : SecondProfileData ι)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (ω₁ ω₂ : ℝ → ℂ) (G₀ E₀ V₀ K₀ X₀ : ℝ) (v : Frequency × (Fin 6 → ℝ)) :
    (∑ N ∈ (F \ x.overlap).powerset, ∑ M ∈ (F \ x.overlap).powerset,
      secondActualCoefficient p hp hcop hg x slots₁ slots₂ lists₁ lists₂ a₁ a₂ N M *
        (star (ω₁ (primeProductNorm p N/X₀)) * ω₂ (primeProductNorm p M/X₀)) *
        pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope
          (secondRelativeLog (secondActualNorms p x N M) G₀ E₀ V₀ K₀ X₀) v.1 v.2) =
      secondSeparatedPair p hp hcop hg F x slots₁ slots₂ lists₁ lists₂ a₁ a₂ ω₁ ω₂ G₀ E₀ V₀ K₀ X₀ v := by
  let h := profileHeight secondLeftSlope secondRightSlope secondKernelSlope v.1 v.2
  let O := secondOuterPhase h (secondRelativeLog (secondActualNorms p x ∅ ∅) G₀ E₀ V₀ K₀ X₀)
  calc
    _ = O * (∑ N ∈ (F \ x.overlap).powerset, ∑ M ∈ (F \ x.overlap).powerset,
        secondActualCoefficient p hp hcop hg x slots₁ slots₂ lists₁ lists₂ a₁ a₂ N M *
          (star (ω₁ (primeProductNorm p N/X₀)) * ω₂ (primeProductNorm p M/X₀)) *
          logPhase (h 4) (Real.log (primeProductNorm p N/X₀)) *
          logPhase (h 5) (Real.log (primeProductNorm p M/X₀))) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro N hN
      apply Finset.sum_congr rfl
      intro M hM
      have hm : pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope
          (secondRelativeLog (secondActualNorms p x N M) G₀ E₀ V₀ K₀ X₀) v.1 v.2 =
          O * logPhase (h 4) (Real.log (primeProductNorm p N/X₀)) *
            logPhase (h 5) (Real.log (primeProductNorm p M/X₀)) := by
        rw [second_mode_split]
        simp [secondOuterPhase,secondRelativeLog,secondRelativeNorm,secondActualNorms,O,h]
      rw [hm]
      ring
    _ = _ := by
      rw [actual_second_columns_separated]
      simp only [secondSeparatedPair,h,O,mul_assoc]

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.SecondGenerator
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma secondUnitFrequency_neg (u v : Eisˣ) (k : Eis) :
    secondUnitFrequency u v (-k) = -secondUnitFrequency u v k := by
  simp only [secondUnitFrequency,mul_neg]

variable {ι σ : Type*} [DecidableEq ι]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem secondCanonical_generator_transport
    (F : Finset ι) (Ψ : Eis →* ℂ) (m label d e k : Eis)
    (L D E : Ideal Eis) (u v : Eisˣ)
    (hl : label = (u:Eis)*primaryGenerator L)
    (hd : d*e = (v:Eis)*(primaryGenerator D*primaryGenerator E))
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (W : ℝ → ℂ) (X : ℝ) :
    finiteCanonicalMarkedRow p hp hcop hg F Ψ m label (d*e*k) slots lists a W X =
      finiteCanonicalMarkedRow p hp hcop hg F Ψ m (primaryGenerator L)
        (primaryGenerator D*primaryGenerator E*secondUnitFrequency u v k) slots lists a W X := by
  rw [hl,finiteCanonicalMarkedRow_label_transfer,hd]
  congr 1
  unfold secondUnitFrequency
  change (u:Eis)^4*((v:Eis)*(primaryGenerator D*primaryGenerator E)*k) =
    primaryGenerator D*primaryGenerator E*(((u:Eis)^4*(v:Eis))*k)
  ring

theorem exists_second_generator_sectors (label d e : Eis) (L D E : Ideal Eis)
    (hl : Ideal.span {label} = L) (hd : Ideal.span {d} = D) (he : Ideal.span {e} = E)
    (hL : primaryGenerator L ≠ 0) (hD : primaryGenerator D ≠ 0) (hE : primaryGenerator E ≠ 0) :
    ∃ u v : Eisˣ, label = (u:Eis)*primaryGenerator L ∧
      d*e = (v:Eis)*(primaryGenerator D*primaryGenerator E) := by
  obtain ⟨u,hu⟩ := generator_eq_unit_primary L label hl hL
  have hspan : Ideal.span {d*e} = D*E := by
    rw [← Ideal.span_singleton_mul_span_singleton,hd,he]
  obtain ⟨v,hv⟩ := generator_eq_unit_primary (D*E) (d*e) hspan
    (by rw [primaryGenerator_mul]; exact mul_ne_zero hD hE)
  exact ⟨u,v,hu,by simpa only [primaryGenerator_mul] using hv⟩

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.SecondFixedFamily
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem secondChildColumn_drop_puncture (Ψ : Eis →* ℂ) (m d f k : Eis)
    (hd : d ∣ m*f) (H : Finset ι → ℂ) (S : Finset ι) :
    secondChildColumn p hp hcop hg Ψ (m*d) f k H S =
      secondChildColumn p hp hcop hg Ψ m f k H S := by
  by_cases hz : ∃ i ∈ S, d ∈ Ideal.span {p i}
  · obtain ⟨i,hi,hdI⟩ := hz
    have hr : m*f ∈ Ideal.span {p i} := by
      obtain ⟨a,ha⟩ := hd
      rw [ha]
      exact Ideal.mul_mem_right _ _ hdI
    have hl : (m*d)*f ∈ Ideal.span {p i} := by
      exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hdI)
    rw [secondChildColumn_zero_of_mask_label_mem p hp hcop hg Ψ (m*d) f k H S i hi hl,
      secondChildColumn_zero_of_mask_label_mem p hp hcop hg Ψ m f k H S i hi hr]
  · have hm : rowCoprimeMask (fun i => Ideal.span {p i}) S d = 1 := by
      simp only [rowCoprimeMask,if_neg hz]
    simp only [secondChildColumn,FirstPassCubeLabels.mask_mul _ hg S,hm,mul_one]

omit [DecidableEq σ] in
theorem finiteCanonicalMarkedRow_drop_puncture (F : Finset ι) (Ψ : Eis →* ℂ)
    (m d f k : Eis) (hd : d ∣ m*f)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ) (W : ℝ → ℂ) (X : ℝ) :
    finiteCanonicalMarkedRow p hp hcop hg F Ψ (m*d) f k slots lists a W X =
      finiteCanonicalMarkedRow p hp hcop hg F Ψ m f k slots lists a W X := by
  simp only [finiteCanonicalMarkedRow,fixedChildRow,secondChildColumn_drop_puncture p hp hcop hg Ψ m d f k hd]

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem actual_first_divisor_dvd_child
    (B C D V : Finset ι) (hCB : Disjoint C B) (hD : D ⊆ C∪B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hv : ∀ i ∈ B, 0 < v i)
    (m r e : Eis) :
    primeSubsetGenerator (fun i => Ideal.span {p i}) D ∣
      ((m*b0Label p B v ε₁ ε₂)*r)*
        (((∏ i ∈ C,p i)*jLabel p B v ε₁ ε₂)*e*∏ i ∈ V,p i) := by
  have hd := poisson_mask_generator_dvd p D (C∪B) hD
  rw [Finset.prod_union hCB] at hd
  have hb := cubeRadical_dvd_jLabel_b0 p B v ε₁ ε₂ hv
  change (∏ i ∈ B,p i) ∣ jLabel p B v ε₁ ε₂*b0Label p B v ε₁ ε₂ at hb
  apply (hd.trans (mul_dvd_mul_left (∏ i ∈ C,p i) hb)).trans
  refine ⟨m*r*e*∏ i ∈ V,p i,?_⟩
  ring

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem actual_second_extracted_support_killed
    (B C G E V A : Finset ι) (hEG : E ⊆ G) (hA : A ⊆ (B∪C)∪G)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hv : ∀ i ∈ B, 0 < v i) (m : Eis) :
    ∀ i ∈ A,
      ((m*b0Label p B v ε₁ ε₂)*secondMaskQuotient p E G hEG)*
        (((∏ j ∈ C,p j)*jLabel p B v ε₁ ε₂)*
          primeSubsetGenerator (fun j => Ideal.span {p j}) E*∏ j ∈ V,p j) ∈ Ideal.span {p i} := by
  let r := secondMaskQuotient p E G hEG
  let e := primeSubsetGenerator (fun j => Ideal.span {p j}) E
  let T := ((m*b0Label p B v ε₁ ε₂)*r)*
    (((∏ j ∈ C,p j)*jLabel p B v ε₁ ε₂)*e*∏ j ∈ V,p j)
  have hb : (∏ j ∈ B,p j) ∣ T := by
    apply (cubeRadical_dvd_jLabel_b0 p B v ε₁ ε₂ hv).trans
    refine ⟨m*r*(∏ j ∈ C,p j)*e*∏ j ∈ V,p j,?_⟩
    dsimp [T]
    ring
  have hc : (∏ j ∈ C,p j) ∣ T := by
    refine ⟨m*b0Label p B v ε₁ ε₂*r*jLabel p B v ε₁ ε₂*e*∏ j ∈ V,p j,?_⟩
    dsimp [T]
    ring
  have hg' : (∏ j ∈ G,p j) ∣ T := by
    rw [secondMaskQuotient_spec p E G hEG]
    refine ⟨m*b0Label p B v ε₁ ε₂*(∏ j ∈ C,p j)*jLabel p B v ε₁ ε₂*∏ j ∈ V,p j,?_⟩
    dsimp [T,r,e]
    ring
  intro i hi
  apply Ideal.mem_span_singleton.mpr
  change p i ∣ T
  rcases Finset.mem_union.mp (hA hi) with hi|hi
  · rcases Finset.mem_union.mp hi with hi|hi
    · exact (Finset.dvd_prod_of_mem p hi).trans hb
    · exact (Finset.dvd_prod_of_mem p hi).trans hc
  · exact (Finset.dvd_prod_of_mem p hi).trans hg'

theorem actual_second_split_fixed_family
    (F B C D G E V A : Finset ι) (hCB : Disjoint C B) (hD : D ⊆ C∪B)
    (hEG : E ⊆ G) (hA : A ⊆ (B∪C)∪G)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hv : ∀ i ∈ B, 0 < v i)
    (Ψ : Eis →* ℂ) (m k : Eis) (slots : Finset σ) (lists : σ → Finset ι)
    (a : σ → ι → ℂ) (W : ℝ → ℂ) (X : ℝ) :
    let d := primeSubsetGenerator (fun i => Ideal.span {p i}) D
    let e := primeSubsetGenerator (fun i => Ideal.span {p i}) E
    let r := secondMaskQuotient p E G hEG
    let c := (∏ i ∈ C,p i)*jLabel p B v ε₁ ε₂
    canonicalMarkedSplit p hp hcop hg F V A Ψ
      (m*b0Label p B v ε₁ ε₂*d) r c d e k slots lists a W (primeProductNorm p V*X) =
      ∑ J ∈ slots.powerset, primeMark J lists a (A∪V) *
        finiteCanonicalMarkedRow p hp hcop hg F Ψ ((m*b0Label p B v ε₁ ε₂)*r)
          (c*e*∏ i ∈ V,p i) (d*e*k) (slots\J) lists a W X := by
  dsimp only
  let d := primeSubsetGenerator (fun i => Ideal.span {p i}) D
  let e := primeSubsetGenerator (fun i => Ideal.span {p i}) E
  let r := secondMaskQuotient p E G hEG
  let c := (∏ i ∈ C,p i)*jLabel p B v ε₁ ε₂
  have hd := actual_first_divisor_dvd_child p B C D V hCB hD v ε₁ ε₂ hv m r e
  have hk := actual_second_extracted_support_killed p B C G E V A hEG hA v ε₁ ε₂ hv m
  have hm : (m*b0Label p B v ε₁ ε₂*d)*r = ((m*b0Label p B v ε₁ ε₂)*r)*d := by ring
  have hX : primeProductNorm p V*X/primeProductNorm p V = X := by
    field_simp [(primeProductNorm_pos p hp V).ne']
  unfold canonicalMarkedSplit
  rw [show m*b0Label p B v ε₁ ε₂*primeSubsetGenerator (fun i => Ideal.span {p i}) D *
      secondMaskQuotient p E G hEG = ((m*b0Label p B v ε₁ ε₂)*r)*d from hm]
  rw [hX]
  apply Finset.sum_congr rfl
  intro J hJ
  rw [finiteCanonicalMarkedRow_drop_puncture p hp hcop hg F Ψ _ d _ _ hd]
  rw [finiteCanonicalMarkedRow_restore_lists p hp hcop hg F A Ψ _ _ _ (slots\J) lists a W X hk]

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.SecondCanonicalChild
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open InverseSecondFibers
open InverseInitialArithmetic (sourceIdeal sourceIdeal_gen)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

include hp

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem primaryGenerator_primeProduct
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1) (S : Finset ι) (v : ι → ℕ) :
    primaryGenerator (Ideal.span {primeProduct p S v}) = primeProduct p S v := by
  apply primaryGenerator_span _ (primeProduct_ne_zero p hp S v)
  unfold primeProduct
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    rw [Finset.prod_insert hi]
    have hpow : ConcretePrimeRowBridge.goodLambda^2 ∣ p i^v i-1 := by
      simpa only [one_pow] using (hpr i).trans (sub_dvd_pow_sub_pow (p i) 1 (v i))
    have he : p i^v i*(∏ j ∈ S,p j^v j)-1 =
        (p i^v i-1)*(∏ j ∈ S,p j^v j)+((∏ j ∈ S,p j^v j)-1) := by ring
    rw [he]
    exact dvd_add (dvd_mul_of_dvd_left hpow _) ih

omit [DecidableEq σ] in
theorem finiteCanonicalMarkedRow_mask_span (F : Finset ι) (Ψ : Eis →* ℂ)
    (m₁ m₂ f k : Eis) (he : Ideal.span {m₁}=Ideal.span {m₂})
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ) (W : ℝ → ℂ) (X : ℝ) :
    finiteCanonicalMarkedRow p hp hcop hg F Ψ m₁ f k slots lists a W X =
      finiteCanonicalMarkedRow p hp hcop hg F Ψ m₂ f k slots lists a W X :=
  fixedChildRow_congr_mask_span p hp hcop hg F Ψ he _ f k

theorem actual_second_puncture_span
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (hE : x.second.divisor ⊆ x.second.sourceCommon) (u v : Eisˣ) (m : Eis) :
    Ideal.span {((m*b0Label p x.cube.support
      (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)*
      secondExpansionQuotient p x.second)} =
    Ideal.span {actualSecondPuncture m (actualSecondChild p u v x).1} := by
  change Ideal.span {(m*b0Label p _ _ _ _)*secondExpansionQuotient p x.second} =
    Ideal.span {(m*primaryGenerator (Ideal.span {b0Label p _ _ _ _}))*
      primaryGenerator (sourceIdeal p (x.second.sourceCommon\x.second.divisor))}
  rw [show primaryGenerator (Ideal.span {b0Label p x.cube.support
      (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit}) =
      b0Label p x.cube.support (fun i => x.cube.leftExponent i+x.cube.rightExponent i)
        x.cube.leftBit x.cube.rightBit from primaryGenerator_primeProduct p hp hpr _ _,
    sourceIdeal_gen p hp hpr,secondExpansionQuotient_of_subset p x.second hE]
  simp only [←Ideal.span_singleton_mul_span_singleton,secondMaskQuotient_span,
    FiniteGaussPhase.span_finset_prod]

theorem actual_second_generator_sectors
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) :
    ∃ u v : Eisˣ,
      actualSecondRawLabel p x = (u:Eis)*primaryGenerator (actualSecondChild p u v x).2.1 ∧
      primeSubsetGenerator (fun i => Ideal.span {p i}) x.firstDivisor *
        primeSubsetGenerator (fun i => Ideal.span {p i}) x.second.divisor =
        (v:Eis)*(primaryGenerator (sourceIdeal p x.firstDivisor)*primaryGenerator (sourceIdeal p x.second.divisor)) := by
  let L := (markedSecondOriginal p x).J * sourceIdeal p x.firstCommon *
    sourceIdeal p x.second.divisor * sourceIdeal p x.second.overlap
  have hs (S : Finset ι) : Ideal.span {primeSubsetGenerator (fun i => Ideal.span {p i}) S} = sourceIdeal p S := by
    simp only [primeSubsetGenerator,ConcretePrimeRowBridge.span_idealGenerator,sourceIdeal]
    exact (FiniteGaussPhase.span_finset_prod S p).symm
  have hl : Ideal.span {actualSecondRawLabel p x} = L := by
    unfold actualSecondRawLabel L
    simp only [←Ideal.span_singleton_mul_span_singleton,hs,sourceIdeal,markedSecondOriginal,cubeSecondSource]
    ring
  have hgp (S : Finset ι) : primaryGenerator (sourceIdeal p S) ≠ 0 := by
    rw [sourceIdeal_gen p hp hpr]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)
  have hL : primaryGenerator L ≠ 0 := by
    dsimp only [L]
    rw [primaryGenerator_mul,primaryGenerator_mul,primaryGenerator_mul]
    apply mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ (hgp _)) (hgp _)) (hgp _)
    change primaryGenerator (Ideal.span {jLabel p _ _ _ _}) ≠ 0
    rw [show primaryGenerator (Ideal.span {jLabel p x.cube.support
      (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit}) =
      jLabel p x.cube.support (fun i => x.cube.leftExponent i+x.cube.rightExponent i)
        x.cube.leftBit x.cube.rightBit from primaryGenerator_primeProduct p hp hpr _ _]
    exact primeProduct_ne_zero p hp _ _
  obtain ⟨u,v,hu,hv⟩ := exists_second_generator_sectors (actualSecondRawLabel p x)
    (primeSubsetGenerator (fun i => Ideal.span {p i}) x.firstDivisor)
    (primeSubsetGenerator (fun i => Ideal.span {p i}) x.second.divisor)
    L (sourceIdeal p x.firstDivisor) (sourceIdeal p x.second.divisor)
    hl (hs _) (hs _) hL (hgp _) (hgp _)
  exact ⟨u,v,hu,hv⟩

theorem actual_second_canonical_child
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (hE : x.second.divisor ⊆ x.second.sourceCommon) :
    ∃ u v : Eisˣ, ∀ (F : Finset ι) (Ψ : Eis →* ℂ) (m k : Eis)
      (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ) (W : ℝ → ℂ) (X : ℝ),
    finiteCanonicalMarkedRow p hp hcop hg F Ψ
      ((m*b0Label p x.cube.support (fun i => x.cube.leftExponent i+x.cube.rightExponent i)
        x.cube.leftBit x.cube.rightBit)*secondExpansionQuotient p x.second)
      (actualSecondRawLabel p x)
      (primeSubsetGenerator (fun i => Ideal.span {p i}) x.firstDivisor *
        primeSubsetGenerator (fun i => Ideal.span {p i}) x.second.divisor * k)
      slots lists a W X =
    secondCanonicalPolynomial p hp hcop hg F (fun _ => Ψ) (actualSecondPuncture m)
      slots lists a (fun _ => W) X
      (actualSecondChild p u v {x with second := {x.second with frequency := k}}) := by
  obtain ⟨u,v,hu,hv⟩ := actual_second_generator_sectors p hp hpr x
  refine ⟨u,v,?_⟩
  intro F Ψ m k slots lists a W X
  rw [secondCanonical_generator_transport p hp hcop hg F Ψ _ _ _ _ _ _ _ _ u v hu hv]
  exact finiteCanonicalMarkedRow_mask_span p hp hcop hg F Ψ _ _ _ _
    (actual_second_puncture_span p hp hpr x hE u v m) slots lists a W X

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.SecondCanonicalSplit
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open InverseSecondFibers
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem actual_second_split_child_uniform
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (hCB : Disjoint x.firstCommon x.cube.support)
    (hD : x.firstDivisor ⊆ x.firstCommon∪x.cube.support)
    (hE : x.second.divisor ⊆ x.second.sourceCommon) :
    ∃ u v : Eisˣ, ∀ (F : Finset ι) (Ψ : Eis →* ℂ) (m k : Eis)
      (A : Finset ι), A ⊆ (x.cube.support∪x.firstCommon)∪x.second.sourceCommon →
      ∀ (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ) (W : ℝ → ℂ) (X : ℝ),
      let d := primeSubsetGenerator (fun i => Ideal.span {p i}) x.firstDivisor
      let e := primeSubsetGenerator (fun i => Ideal.span {p i}) x.second.divisor
      let c := (∏ i ∈ x.firstCommon,p i)*jLabel p x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit
      canonicalMarkedSplit p hp hcop hg F x.second.overlap A Ψ
        (m*b0Label p x.cube.support (fun i => x.cube.leftExponent i+x.cube.rightExponent i)
          x.cube.leftBit x.cube.rightBit*d)
        (secondExpansionQuotient p x.second) c d e k slots lists a W
        (primeProductNorm p x.second.overlap*X) =
      ∑ J ∈ slots.powerset, primeMark J lists a (A∪x.second.overlap) *
        secondCanonicalPolynomial p hp hcop hg F (fun _ => Ψ) (actualSecondPuncture m)
          (slots\J) lists a (fun _ => W) X
          (actualSecondChild p u v {x with second := {x.second with frequency := k}}) := by
  obtain ⟨u,v,hchild⟩ := actual_second_canonical_child p hp hcop hg hpr (σ:=σ) x hE
  refine ⟨u,v,?_⟩
  intro F Ψ m k A hA slots lists a W X
  dsimp only
  rw [secondExpansionQuotient_of_subset p x.second hE]
  rw [actual_second_split_fixed_family p hp hcop hg F x.cube.support x.firstCommon
    x.firstDivisor x.second.sourceCommon x.second.divisor x.second.overlap A hCB hD hE hA
    (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit
    x.cube.support_pos Ψ m k slots lists a W X]
  apply Finset.sum_congr rfl
  intro J hJ
  congr 1
  simpa only [actualSecondRawLabel,secondExpansionQuotient_of_subset p x.second hE] using
    hchild F Ψ m k (slots\J) lists a W X

theorem actual_second_separated_pair_canonical
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (hCB : Disjoint x.firstCommon x.cube.support)
    (hD : x.firstDivisor ⊆ x.firstCommon∪x.cube.support)
    (hE : x.second.divisor ⊆ x.second.sourceCommon) :
    ∃ u v : Eisˣ, ∀ (F : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
      (A₁ A₂ : Finset ι), A₁ ⊆ x.cube.support∪x.firstCommon → A₂ ⊆ x.cube.support∪x.firstCommon →
      ∀ (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
      (ω₁ ω₂ : ℝ → ℂ) (G₀ E₀ V₀ K₀ X₀ : ℝ) (t : JointLogSeparation.Frequency × (Fin 6 → ℝ)),
      let h := profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2
      let data := actualMarkedSecondProfileData p x Ψ m z A₁ A₂
      secondSeparatedPair p hp hcop hg F data slots₁ slots₂ lists₁ lists₂ a₁ a₂ ω₁ ω₂ G₀ E₀ V₀ K₀ X₀ t =
      secondOuterPhase h (secondRelativeLog (secondActualNorms p data ∅ ∅) G₀ E₀ V₀ K₀ X₀) *
        ∑ J₁ ∈ slots₁.powerset, ∑ J₂ ∈ slots₂.powerset,
          (star (primeMark J₁ lists₁ a₁ ((A₁∪x.second.sourceCommon)∪x.second.overlap)) *
            primeMark J₂ lists₂ a₂ ((A₂∪x.second.sourceCommon)∪x.second.overlap)) *
          star (secondCanonicalPolynomial p hp hcop hg F (fun _ => secondRayMinus Ψ z)
            (actualSecondPuncture m) (slots₁\J₁) lists₁ a₁ (fun _ => childLogTest ω₁ (-h 4)) X₀
            (actualSecondChild p u v x)) *
          secondCanonicalPolynomial p hp hcop hg F (fun _ => secondRayPlus Ψ z)
            (actualSecondPuncture m) (slots₂\J₂) lists₂ a₂ (fun _ => childLogTest ω₂ (h 5)) X₀
            (actualSecondChild p u v {x with second := {x.second with frequency := -x.second.frequency}}) := by
  obtain ⟨u,v,hsplit⟩ := actual_second_split_child_uniform p hp hcop hg hpr (σ:=σ) x hCB hD hE
  refine ⟨u,v,?_⟩
  intro F Ψ m z A₁ A₂ hA₁ hA₂ slots₁ slots₂ lists₁ lists₂ a₁ a₂ ω₁ ω₂ G₀ E₀ V₀ K₀ X₀ t
  dsimp only
  have hA (A : Finset ι) (ha : A ⊆ x.cube.support∪x.firstCommon) :
      A∪x.second.sourceCommon ⊆ (x.cube.support∪x.firstCommon)∪x.second.sourceCommon :=
    Finset.union_subset_union_left ha
  unfold secondSeparatedPair
  dsimp only [actualMarkedSecondProfileData,expansionProfileData]
  rw [hsplit F (secondRayMinus Ψ z) m x.second.frequency _ (hA A₁ hA₁),
    hsplit F (secondRayPlus Ψ z) m (-x.second.frequency) _ (hA A₂ hA₂)]
  simp only [star_sum,star_mul,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro J₁ hJ₁
  apply Finset.sum_congr rfl
  intro J₂ hJ₂
  ring

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.SecondMarkedEnergy
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open InverseSecondFibers
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem actualSecondChild_neg_frequency {Jo Jn : ℕ} (u v : Eisˣ) (x : MarkedSecondSource ι Jo Jn) :
    actualSecondChild p u v {x with second := {x.second with frequency := -x.second.frequency}} =
      ((actualSecondChild p u v x).1,(actualSecondChild p u v x).2.1,-(actualSecondChild p u v x).2.2) := by
  simp only [actualSecondChild,secondChild,originalSecondTuple,markedSecondOriginal,cubeSecondSource,
    secondUnitFrequency_neg,mul_neg]

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.SecondSectorAssembly
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open InverseSecondFibers
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

attribute [local instance] OAI.SevenEighths.InverseMoment.instFintypeUnitsO
theorem exists_second_uniform_sectors
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (hs : ActualSecondSourceConditions p source) :
    ∃ sector : MarkedSecondSource ι Jo 0 → Eisˣ × Eisˣ,
      ∀ x ∈ source, SecondPairCanonicalAt (σ:=σ) p hp hcop hg x (sector x).1 (sector x).2 := by
  have he (x : {x // x ∈ source}) :=
    actual_second_separated_pair_canonical p hp hcop hg hpr (σ:=σ) x.val
      (hs.common_disjoint x.val x.property) (hs.first_divisor x.val x.property)
      (hs.second_divisor x.val x.property)
  choose u v hu using he
  let sector := fun x => if hx : x ∈ source then (u ⟨x,hx⟩,v ⟨x,hx⟩) else (1,1)
  refine ⟨sector,?_⟩
  intro x hx
  simpa only [sector,dif_pos hx,SecondPairCanonicalAt] using hu ⟨x,hx⟩

omit [DecidableEq ι] in
theorem secondSourceSector_partition {Jo Jn : ℕ}
    (source : Finset (MarkedSecondSource ι Jo Jn))
    (sector : MarkedSecondSource ι Jo Jn → Eisˣ × Eisˣ) (H : MarkedSecondSource ι Jo Jn → ℂ) :
    ∑ x ∈ source,H x = ∑ uv : Eisˣ × Eisˣ,∑ x ∈ secondSourceSector source sector uv,H x :=
  (Finset.sum_fiberwise source sector H).symm

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.SecondModeCanonical
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open InverseSecondFibers JointLogSeparation
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

local instance instFintypeUnitsO_1_r3b2d56_1 : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units
theorem second_inherited_mode_canonical {Jo Jn : ℕ}
    (x : MarkedSecondSource ι Jo Jn) (u v : Eisˣ)
    (hx : SecondPairCanonicalAt (σ:=σ) p hp hcop hg x u v)
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (ω₁ ω₂ : ℝ → ℂ) (G E V B X : ℝ) (t : Frequency × (Fin 6 → ℝ)) :
    secondSeparatedPair p hp hcop hg pool (secondInheritedProfile p x Ψ m z)
      slots₁ slots₂ lists₁ lists₂ a₁ a₂ ω₁ ω₂ G E V B X t =
    ∑ J₁ ∈ slots₁.powerset,∑ J₂ ∈ slots₂.powerset,
      secondModeBranch p hp hcop hg x u v pool Ψ m z slots₁ slots₂ J₁ J₂ lists₁ lists₂ a₁ a₂
        ω₁ ω₂ G E V B X t := by
  have he := hx pool Ψ (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z ∅ ∅
    (Finset.empty_subset _) (Finset.empty_subset _) slots₁ slots₂ lists₁ lists₂ a₁ a₂ ω₁ ω₂ G E V B X t
  dsimp only at he
  have hq : (actualSecondChild p u v x).1.quotient = x.quotient := rfl
  simpa only [secondInheritedProfile,secondModeBranch,secondModeOuter,secondModeLeft,secondModeRight,
    secondCanonicalPolynomial,actualSecondInheritedPuncture,actualSecondChild_neg_frequency,
    Finset.empty_union,Finset.mul_sum,mul_assoc,hq] using he

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.SecondPhysicalRows
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open InverseInitialArithmetic (sourceIdeal sourceIdeal_gen)
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι] (p : ι → Eis)
  (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]

omit [DecidableEq ι] in
theorem actualSecondMultiplier_ne_zero {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) :
    actualSecondMultiplier p x ≠ 0 := by
  apply mul_ne_zero
  · exact primeSubsetGenerator_ne_zero _ _
  · exact primeSubsetGenerator_ne_zero _ _

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.SecondVaryingDensity
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open MeasureTheory FourierBridge JointLogSeparation ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem actualSecondVaryingFreshRows_normalized_density {κ : Type*}
    (source : Finset κ) (F : Finset ι) (x : κ → SecondProfileData ι) (w : κ → ℂ)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : κ → σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (W₁ W₂ ω₁ ω₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (Y G₀ E₀ V₀ K₀ X₀ : ℝ)
    (density : Frequency × (Fin 6 → ℝ) → ℂ) (hDensity : Integrable density) (normalization : ℂ)
    (he : ∀ j ∈ secondProfileIndices source F x,
      normalization * secondNormProfile (fun z => star (W₁ (z/(G₀*V₀*X₀))))
        (fun z => W₂ (z/(G₀*V₀*X₀))) Φ (fun _ _ => 1) Y (secondActualNorms p (x j.1) j.2.1 j.2.2) =
      ((E₀*V₀*X₀ : ℝ):ℂ)⁻¹ *
        (star (ω₁ (primeProductNorm p j.2.1/X₀)) * ω₂ (primeProductNorm p j.2.2/X₀)) *
        ∫ v : Frequency × (Fin 6 → ℝ), density v *
          pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope
            (secondRelativeLog (secondActualNorms p (x j.1) j.2.1 j.2.2) G₀ E₀ V₀ K₀ X₀) v.1 v.2) :
    normalization * (∑ j ∈ source, w j * actualSecondProfileRow p hp hcop hg F (x j)
      slots₁ slots₂ (lists₁ j) (lists₂ j) a₁ a₂ W₁ W₂ Φ Y (G₀*V₀*X₀)) =
      ((E₀*V₀*X₀ : ℝ):ℂ)⁻¹ * ∫ v : Frequency × (Fin 6 → ℝ),
        density v *
          ∑ j ∈ source, w j * secondSeparatedPair p hp hcop hg F (x j)
            slots₁ slots₂ (lists₁ j) (lists₂ j) a₁ a₂ ω₁ ω₂ G₀ E₀ V₀ K₀ X₀ v := by
  have hindexed : (∑ j∈source,w j*actualSecondProfileRow p hp hcop hg F (x j)
      slots₁ slots₂ (lists₁ j) (lists₂ j) a₁ a₂ W₁ W₂ Φ Y (G₀*V₀*X₀)) =
      ∑ j∈secondProfileIndices source F x,
        (w j.1*secondActualCoefficient p hp hcop hg (x j.1) slots₁ slots₂
          (lists₁ j.1) (lists₂ j.1) a₁ a₂ j.2.1 j.2.2)*
        secondNormProfile (fun z=>star (W₁ (z/(G₀*V₀*X₀))))
          (fun z=>W₂ (z/(G₀*V₀*X₀))) Φ (fun _ _=>1) Y
          (secondActualNorms p (x j.1) j.2.1 j.2.2) := by
    simp_rw [actualSecondProfileRow_eq_whole]
    simp only [secondProfileIndices,Finset.sum_sigma,Finset.sum_product,Finset.mul_sum,mul_assoc]
  rw [hindexed]
  have hc (v : Frequency × (Fin 6 → ℝ)) :
      (∑ j ∈ source, w j * secondSeparatedPair p hp hcop hg F (x j)
        slots₁ slots₂ (lists₁ j) (lists₂ j) a₁ a₂ ω₁ ω₂ G₀ E₀ V₀ K₀ X₀ v) =
      ∑ j ∈ secondProfileIndices source F x,
        ((w j.1 * secondActualCoefficient p hp hcop hg (x j.1)
          slots₁ slots₂ (lists₁ j.1) (lists₂ j.1) a₁ a₂ j.2.1 j.2.2) *
          (star (ω₁ (primeProductNorm p j.2.1/X₀)) * ω₂ (primeProductNorm p j.2.2/X₀))) *
          pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope
            (secondRelativeLog (secondActualNorms p (x j.1) j.2.1 j.2.2) G₀ E₀ V₀ K₀ X₀) v.1 v.2 := by
    simp_rw [← actual_second_full_mode_columns]
    simp only [secondProfileIndices,Finset.sum_sigma,Finset.sum_product,Finset.mul_sum,mul_assoc]
  simp_rw [hc]
  rw [← density_finite_sum _ density hDensity]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  calc
    _ = (w j.1 * secondActualCoefficient p hp hcop hg (x j.1)
        slots₁ slots₂ (lists₁ j.1) (lists₂ j.1) a₁ a₂ j.2.1 j.2.2) *
        (normalization * secondNormProfile (fun z => star (W₁ (z/(G₀*V₀*X₀))))
          (fun z => W₂ (z/(G₀*V₀*X₀))) Φ (fun _ _ => 1) Y
          (secondActualNorms p (x j.1) j.2.1 j.2.2)) := by ring
    _ = _ := by rw [he j hj]; ring

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.SecondProfileUniform
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge JointLogSeparation EisensteinSchwartzPoisson
open SevenEighths.InverseMoment
open SevenEighths.InverseInitialProfile
open SevenEighths.InverseAmbientProfileTower
namespace SevenEighths.InverseSecondProfileUniform

theorem fresh_physical_profile (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ, ℂ))
    (V : Fin 6 → ℝ → ℂ) (G₀ E₀ V₀ K₀ X₀ Y L : ℝ)
    (hG : 0 < G₀) (hE : 0 < E₀) (hV : 0 < V₀) (hK : 0 < K₀) (hX : 0 < X₀)
    (ω₁ ω₂ : ℝ → ℂ) (q : Fin 6 → ℝ) (hq : ∀ i, 0 < q i)
    (hω₁ : W₁ (q 0*q 2*q 4/(G₀*V₀*X₀)) ≠ 0 → ω₁ (q 4/X₀) = 1)
    (hω₂ : W₂ (q 0*q 2*q 5/(G₀*V₀*X₀)) ≠ 0 → ω₂ (q 5/X₀) = 1)
    (hcut : ω₁ (q 4/X₀) ≠ 0 → ω₂ (q 5/X₀) ≠ 0 →
      ∀ i, V i (secondRelativeLog q G₀ E₀ V₀ K₀ X₀ i) = 1) :
    (Real.exp (-6*L) : ℂ) * secondNormProfile
      (fun x => W₁ (x/(G₀*V₀*X₀))) (fun x => W₂ (x/(G₀*V₀*X₀)))
      Φ (fun _ _ => 1) Y q =
      ((E₀*V₀*X₀ : ℝ) : ℂ)⁻¹ * (ω₁ (q 4/X₀)*ω₂ (q 5/X₀)) *
        ((Real.exp (-6*L) : ℂ)*secondPoissonProfile W₁ W₂ Φ V
          (Y*K₀/(E₀*V₀^2*X₀^2)) (secondRelativeLog q G₀ E₀ V₀ K₀ X₀)) := by
  by_cases hw₁ : ω₁ (q 4/X₀) = 0
  · have hW : W₁ (q 0*q 2*q 4/(G₀*V₀*X₀)) = 0 := by
      by_contra hn
      exact zero_ne_one (hw₁.symm.trans (hω₁ hn))
    simp only [secondNormProfile,hW,hw₁,mul_zero,zero_mul,zero_div]
  by_cases hw₂ : ω₂ (q 5/X₀) = 0
  · have hW : W₂ (q 0*q 2*q 5/(G₀*V₀*X₀)) = 0 := by
      by_contra hn
      exact zero_ne_one (hw₂.symm.trans (hω₂ hn))
    simp only [secondNormProfile,hW,hw₂,mul_zero,zero_mul,zero_div]
  have hm : secondNormProfile (fun x => W₁ (x/(G₀*V₀*X₀)))
      (fun x => W₂ (x/(G₀*V₀*X₀))) Φ (fun _ _ => 1) Y q =
    (ω₁ (q 4/X₀)*ω₂ (q 5/X₀))*secondNormProfile (fun x => W₁ (x/(G₀*V₀*X₀)))
      (fun x => W₂ (x/(G₀*V₀*X₀))) Φ (fun _ _ => 1) Y q := by
    by_cases h1 : W₁ (q 0*q 2*q 4/(G₀*V₀*X₀)) = 0
    · simp only [secondNormProfile,h1,mul_zero,zero_mul,zero_div]
    by_cases h2 : W₂ (q 0*q 2*q 5/(G₀*V₀*X₀)) = 0
    · simp only [secondNormProfile,h2,mul_zero,zero_mul,zero_div]
    simp only [hω₁ h1,hω₂ h2,one_mul]
  rw [hm, secondNormProfile_nominal W₁ W₂ Φ G₀ E₀ V₀ K₀ X₀ Y hG hE hV hK hX q hq]
  change _*( _*(_*secondNormProfile W₁ W₂ Φ (fun _ _ => 1) _
    (secondRelativeNorm q G₀ E₀ V₀ K₀ X₀))) = _
  rw [secondNormProfile_eq_full_of_windows W₁ W₂ Φ V _ _
    (secondRelativeNorm_pos q hq G₀ E₀ V₀ K₀ X₀ hG hE hV hK hX) (hcut hw₁ hw₂)]
  ring_nf
  rfl

end SevenEighths.InverseSecondProfileUniform

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.SecondVaryingBalanced
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open MeasureTheory JointLogSeparation ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

variable {κ ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem actual_second_varying_balanced_source (source : Finset κ) (F : Finset ι)
    (x : κ → SecondProfileData ι) (w : κ → ℂ)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : κ → σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (W₁ W₂ ω₁ ω₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (V : Fin 6 → ℝ → ℂ)
    (G₀ E₀ V₀ K₀ X₀ Y L : ℝ)
    (hG : 0 < G₀) (hE : 0 < E₀) (hV : 0 < V₀) (hK : 0 < K₀) (hX : 0 < X₀)
    (density : Frequency × (Fin 6 → ℝ) → ℂ) (hDensity : Integrable density)
    (hsep : ∀ y : Fin 6 → ℝ,
      (Real.exp (-6*L):ℂ) * secondPoissonProfile (fun x => star (W₁ x)) W₂ Φ V
        (Y*K₀/(E₀*V₀^2*X₀^2)) y =
      ∫ t : Frequency × (Fin 6 → ℝ), density t *
        pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope y t.1 t.2)
    (hn : ∀ j ∈ source,(x j).divisor ≠ 0 ∧ (x j).frequency ≠ 0)
    (hω₁ : ∀ j ∈ source, ∀ N ∈ (F\(x j).overlap).powerset,
      W₁ (primeProductNorm p (x j).common*primeProductNorm p (x j).overlap*primeProductNorm p N/(G₀*V₀*X₀)) ≠ 0 →
        ω₁ (primeProductNorm p N/X₀) = 1)
    (hω₂ : ∀ j ∈ source, ∀ N ∈ (F\(x j).overlap).powerset,
      W₂ (primeProductNorm p (x j).common*primeProductNorm p (x j).overlap*primeProductNorm p N/(G₀*V₀*X₀)) ≠ 0 →
        ω₂ (primeProductNorm p N/X₀) = 1)
    (hcut : ∀ j ∈ secondProfileIndices source F x,
      ω₁ (primeProductNorm p j.2.1/X₀) ≠ 0 → ω₂ (primeProductNorm p j.2.2/X₀) ≠ 0 → ∀ i,
      V i (secondRelativeLog (secondActualNorms p (x j.1) j.2.1 j.2.2) G₀ E₀ V₀ K₀ X₀ i) = 1) :
    (Real.exp (-6*L):ℂ) * (∑ j ∈ source,w j * actualSecondProfileRow p hp hcop hg F (x j)
      slots₁ slots₂ (lists₁ j) (lists₂ j) a₁ a₂ W₁ W₂ Φ Y (G₀*V₀*X₀)) =
    ((E₀*V₀*X₀:ℝ):ℂ)⁻¹ * ∫ t : Frequency × (Fin 6 → ℝ),density t *
      ∑ j ∈ source,w j * secondSeparatedPair p hp hcop hg F (x j)
        slots₁ slots₂ (lists₁ j) (lists₂ j) a₁ a₂ ω₁ ω₂ G₀ E₀ V₀ K₀ X₀ t := by
  apply actualSecondVaryingFreshRows_normalized_density p hp hcop hg source F x w
    slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ ω₁ ω₂ Φ Y G₀ E₀ V₀ K₀ X₀ density hDensity
  intro j hj
  obtain ⟨hjS,hN,hM⟩ := (mem_secondProfileIndices source F x j).mp hj
  have h1 : star (W₁ (primeProductNorm p (x j.1).common*primeProductNorm p (x j.1).overlap*
      primeProductNorm p j.2.1/(G₀*V₀*X₀))) ≠ 0 → star (ω₁ (primeProductNorm p j.2.1/X₀)) = 1 := by
    intro hh
    rw [hω₁ j.1 hjS j.2.1 hN (star_ne_zero.mp hh),star_one]
  have h2 := hω₂ j.1 hjS j.2.2 hM
  have h3 : star (ω₁ (primeProductNorm p j.2.1/X₀)) ≠ 0 → ω₂ (primeProductNorm p j.2.2/X₀) ≠ 0 → ∀ i,
      V i (secondRelativeLog (secondActualNorms p (x j.1) j.2.1 j.2.2) G₀ E₀ V₀ K₀ X₀ i) = 1 :=
    fun ha hb => hcut j hj (star_ne_zero.mp ha) hb
  have he := InverseSecondProfileUniform.fresh_physical_profile
    (fun x => star (W₁ x)) W₂ Φ V G₀ E₀ V₀ K₀ X₀ Y L hG hE hV hK hX
    (fun x => star (ω₁ x)) ω₂ (secondActualNorms p (x j.1) j.2.1 j.2.2)
    (secondActualNorms_pos p hp (x j.1) (hn j.1 hjS).1 (hn j.1 hjS).2 j.2.1 j.2.2)
    (by simpa [secondActualNorms] using h1)
    (by simpa [secondActualNorms] using h2)
    (by simpa [secondActualNorms] using h3)
  rw [hsep] at he
  simpa [secondActualNorms] using he

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.SecondVaryingPhysical
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical ContDiff
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open JointLogSeparation MeasureTheory SchwartzMap
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe u₁ u₂
variable {ι : Type u₁} {σ : Type u₂} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

attribute [local instance] OAI.SevenEighths.InverseMoment.inverseSecondVaryingPhysicalUnits
theorem actual_second_varying_modes_common_sectors
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (hs : ActualSecondSourceConditions p source) :
    ∃ sector : MarkedSecondSource ι Jo 0 → Eisˣ × Eisˣ,
      ∀ (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
        (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : MarkedSecondSource ι Jo 0 → σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
        (ω₁ ω₂ : ℝ → ℂ) (G E V B X : ℝ) (t : Frequency × (Fin 6 → ℝ))
        (w : MarkedSecondSource ι Jo 0 → ℂ),
      (∑ x ∈ source,w x * secondSeparatedPair p hp hcop hg pool (secondInheritedProfile p x Ψ m z)
        slots₁ slots₂ (lists₁ x) (lists₂ x) a₁ a₂ ω₁ ω₂ G E V B X t) =
      ∑ uv : Eisˣ × Eisˣ, ∑ x ∈ secondSourceSector source sector uv, w x *
        ∑ J₁ ∈ slots₁.powerset,∑ J₂ ∈ slots₂.powerset,
          secondModeBranch p hp hcop hg x uv.1 uv.2 pool Ψ m z slots₁ slots₂ J₁ J₂ (lists₁ x) (lists₂ x) a₁ a₂
            ω₁ ω₂ G E V B X t := by
  obtain ⟨sector,hsector⟩ := exists_second_uniform_sectors p hp hcop hg hpr (σ:=σ) source hs
  refine ⟨sector,?_⟩
  intro pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂ ω₁ ω₂ G E V B X t w
  rw [secondSourceSector_partition source sector]
  apply Finset.sum_congr rfl
  intro uv huv
  apply Finset.sum_congr rfl
  intro x hx
  obtain ⟨hx,hxs⟩ := Finset.mem_filter.mp hx
  congr 1
  have hh := hsector x hx
  rw [hxs] at hh
  exact second_inherited_mode_canonical p hp hcop hg x uv.1 uv.2 hh
    pool Ψ m z slots₁ slots₂ (lists₁ x) (lists₂ x) a₁ a₂ ω₁ ω₂ G E V B X t

theorem actual_second_varying_balanced_profile_children_oai
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (hs : ActualSecondSourceConditions p source) :
    ∃ sector : MarkedSecondSource ι Jo 0 → Eisˣ × Eisˣ,
      ∀ (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
        (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : MarkedSecondSource ι Jo 0 → σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
        (W₁ W₂ ω₁ ω₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (G E V B X Y R L : ℝ)
        (U : Fin 6 → ℝ → ℂ) (density : Frequency × (Fin 6 → ℝ) → ℂ)
        (w : MarkedSecondSource ι Jo 0 → ℂ),
      0 < G → 0 < E → 0 < V → 0 < B → 0 < X → Integrable density →
      (∀ y : Fin 6 → ℝ,(Real.exp (-6*L):ℂ)*secondPoissonProfile (fun x => star (W₁ x)) W₂ Φ U
        (Y*B/(E*V^2*X^2)) y = ∫ t : Frequency × (Fin 6 → ℝ),density t*
          pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope y t.1 t.2) →
      (∀ x ∈ source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) R) →
      (∀ x ∈ source,∀ N ∈ (pool\x.second.overlap).powerset,
        W₁ (primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap*
          primeProductNorm p N/(G*V*X)) ≠ 0 → ω₁ (primeProductNorm p N/X) = 1) →
      (∀ x ∈ source,∀ N ∈ (pool\x.second.overlap).powerset,
        W₂ (primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap*
          primeProductNorm p N/(G*V*X)) ≠ 0 → ω₂ (primeProductNorm p N/X) = 1) →
      (∀ j ∈ secondProfileIndices source pool (fun x => secondInheritedProfile p x Ψ m z),
        ω₁ (primeProductNorm p j.2.1/X) ≠ 0 → ω₂ (primeProductNorm p j.2.2/X) ≠ 0 → ∀ i,
        U i (secondRelativeLog (secondActualNorms p (secondInheritedProfile p j.1 Ψ m z) j.2.1 j.2.2)
          G E V B X i) = 1) →
      (Real.exp (-6*L):ℂ) * ((Y : ℂ)*secondRayCoefficient z *
        (∑ x ∈ source,(w x*actualSecondSignedWeight p hp hcop hg Ψ
            (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x) *
          actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ m z)
            slots₁ slots₂ (lists₁ x) (lists₂ x) a₁ a₂ W₁ W₂ Φ Y (G*V*X))) =
      ((Y : ℂ)*secondRayCoefficient z*((E*V*X : ℝ):ℂ)⁻¹) *
        ∫ t : Frequency × (Fin 6 → ℝ),density t *
          ∑ uv : Eisˣ × Eisˣ,∑ x ∈ secondSourceSector source sector uv,
            (w x*actualSecondSignedWeight p hp hcop hg Ψ
              (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x) *
            ∑ J₁ ∈ slots₁.powerset,∑ J₂ ∈ slots₂.powerset,
              secondModeBranch p hp hcop hg x uv.1 uv.2 pool Ψ m z slots₁ slots₂ J₁ J₂ (lists₁ x) (lists₂ x) a₁ a₂
                ω₁ ω₂ G E V B X t := by
  obtain ⟨sector,hsector⟩ := actual_second_varying_modes_common_sectors p hp hcop hg hpr (σ:=σ) source hs
  refine ⟨sector,?_⟩
  intro pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ ω₁ ω₂ Φ G E V B X Y R L
    U density w hG hE hV hB hX hDensity hsep hrows hω₁ hω₂ hcut
  have hn : ∀ x ∈ source,(secondInheritedProfile p x Ψ m z).divisor ≠ 0 ∧
      (secondInheritedProfile p x Ψ m z).frequency ≠ 0 := by
    intro x hx
    refine ⟨primeSubsetGenerator_ne_zero _ _,?_⟩
    have hh := (mem_nonzeroChildFrequencyBall _ (actualSecondMultiplier_ne_zero p x) R _).mp (hrows x hx)
    intro he
    change x.second.frequency = 0 at he
    simp only [he,mul_zero,map_zero,norm_zero,zero_pow (by omega : 2 ≠ 0),lt_self_iff_false] at hh
    exact hh.1
  have he := actual_second_varying_balanced_source p hp hcop hg source pool
    (fun x : MarkedSecondSource ι Jo 0 => secondInheritedProfile p x Ψ m z)
    (fun x : MarkedSecondSource ι Jo 0 => w x*actualSecondSignedWeight p hp hcop hg Ψ
      (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x)
    slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ ω₁ ω₂ Φ U G E V B X Y L
    hG hE hV hB hX density hDensity hsep hn hω₁ hω₂ hcut
  calc
    _ = ((Y:ℂ)*secondRayCoefficient z) * ((Real.exp (-6*L):ℂ)*
        ∑ x ∈ source,(w x*actualSecondSignedWeight p hp hcop hg Ψ
            (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x) *
          actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ m z)
            slots₁ slots₂ (lists₁ x) (lists₂ x) a₁ a₂ W₁ W₂ Φ Y (G*V*X)) := by ring
    _ = _ := by
      rw [he]
      rw [←mul_assoc]
      apply congrArg (fun a : ℂ => ((Y:ℂ)*secondRayCoefficient z*((E*V*X:ℝ):ℂ)⁻¹)*a)
      apply integral_congr_ae
      filter_upwards with t
      apply congrArg (fun a : ℂ => density t*a)
      exact hsector pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂ ω₁ ω₂ G E V B X t _

end
end SevenEighths.InverseMoment

end OAI
end

theorem solution.{u₁, u₂} : type_of% @OAI.SevenEighths.InverseMoment.actual_second_varying_balanced_profile_children_oai.{u₁, u₂} := @OAI.SevenEighths.InverseMoment.actual_second_varying_balanced_profile_children_oai.{u₁, u₂}
