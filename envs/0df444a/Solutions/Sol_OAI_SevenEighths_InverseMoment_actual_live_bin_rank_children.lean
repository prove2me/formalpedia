-- Prove2me | solution 1 for OAI.SevenEighths.InverseMoment.actual_live_bin_rank_children
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T03:35:22.659783+00:00
-- url     : https://prove2.me/submissions/0f71e032-9d9b-408b-87b4-6c00f9af1e16

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B019
import Theorems.Thm_OAI_SevenEighths_InverseMomentFirstLabelCell_source_state_bounds

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Arithmetic.IdealMobius
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

namespace CompletedGauss

section

open ActualEisensteinCubic

open ActualEisensteinCubic

theorem norm_at_least_one (I : Ideal O) (hI : I ≠ 0) :
    (1 : ℝ) ≤ Ideal.absNorm I := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)

end

open ActualEisensteinCubic
open IdealMobiusDivisorSum (idealDivisors mem_idealDivisors sum_moebius_divisors)

end CompletedGauss

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

theorem multiplicity_decomposition (m : ℕ) (ε₁ ε₂ : Bool) (hm : 0 < m) :
    2 * b0Exponent m ε₁ ε₂ + 2 * bit (evenDouble m ε₁ ε₂) + bit (parity m) = m := by
  have hmod := Nat.mod_lt m (by decide : 0 < 2)
  have hdiv := Nat.mod_add_div m 2
  cases ε₁ <;> cases ε₂ <;> by_cases h : m % 2 = 1 <;>
    simp [b0Exponent, evenDouble, parity, bit, h] <;> omega

section Reassembly
variable {ι κ : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
  (hg : ∀ i, lambda ∉ P i) (S : Finset ι)

theorem cube_product_decomposition (p : κ → O) (B : Finset κ) (v : κ → ℕ)
    (ε₁ ε₂ : κ → Bool) (hv : ∀ j ∈ B, 0 < v j) :
    primeProduct p B v = b0Label p B v ε₁ ε₂ ^ 2 * j2Label p B v ε₁ ε₂ ^ 2 *
      squarefreeLabel p B v := by
  simp only [b0Label, j2Label, squarefreeLabel, primeProduct, ← Finset.prod_pow,
    ← Finset.prod_mul_distrib, ← pow_mul, ← pow_add]
  apply Finset.prod_congr rfl
  intro j hj
  congr 1
  have h := multiplicity_decomposition (v j) (ε₁ j) (ε₂ j) (hv j hj)
  omega

theorem jLabel_eq_squarefree_mul_j2 (p : κ → O) (B : Finset κ) (v : κ → ℕ)
    (ε₁ ε₂ : κ → Bool) :
    jLabel p B v ε₁ ε₂ = squarefreeLabel p B v * j2Label p B v ε₁ ε₂ := by
  simp only [jLabel, squarefreeLabel, j2Label, primeProduct, ← Finset.prod_mul_distrib,
    ← pow_add]
  apply Finset.prod_congr rfl
  intro j hj
  congr 1
  cases hp : parity (v j) <;> cases ε₁ j <;> cases ε₂ j <;>
    simp [bit, retained, evenDouble, hp]

theorem cube_pair_product_decomposition
    (p : κ → O) (B : Finset κ) (v₁ v₂ : κ → ℕ) (ε₁ ε₂ : κ → Bool)
    (hv : ∀ j ∈ B, 0 < v₁ j + v₂ j) :
    primeProduct p B v₁ * primeProduct p B v₂ =
      b0Label p B (fun j => v₁ j + v₂ j) ε₁ ε₂ ^ 2 *
      j2Label p B (fun j => v₁ j + v₂ j) ε₁ ε₂ ^ 2 *
      squarefreeLabel p B (fun j => v₁ j + v₂ j) := by
  rw [← cube_product_decomposition p B (fun j => v₁ j + v₂ j) ε₁ ε₂ hv]
  simp only [primeProduct, pow_add, Finset.prod_mul_distrib]

end Reassembly

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.ReflectionBrackets
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

open scoped BigOperators Classical SchwartzMap
namespace ActualEisensteinCubic
open ConcreteTraceCRT ConcretePrimeRowBridge ActualEisensteinCoordinates EisensteinSchwartzPoisson

theorem primeSubsetGenerator_norm_sq {ι : Type*} (P : ι → Ideal O) (E : Finset ι) :
    ‖eisEmbedding (primeSubsetGenerator P E)‖ ^ 2 = (Ideal.absNorm (∏ i ∈ E, P i) : ℝ) := by
  rw [eisEmbedding_norm_sq_eq_absNorm_span]
  exact congrArg (fun I : Ideal O => (Ideal.absNorm I : ℝ)) (span_idealGenerator _)

end ActualEisensteinCubic

open scoped BigOperators Classical

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
lemma primeProduct_add (B : Finset ι) (u v : ι → ℕ) :
    primeProduct p B (fun i => u i + v i) = primeProduct p B u * primeProduct p B v := by
  simp only [primeProduct, pow_add, Finset.prod_mul_distrib]

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.QuadraticSieve.PrincipalTruncation
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

open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic

section

open ActualEisensteinCubic

theorem mem_secondExpansionPool {ι : Type*} [DecidableEq ι] (F : Finset ι)
    (K : Finset ι → Finset ι → Finset O) (x : SecondExpansionData ι) :
    x ∈ secondExpansionPool F K ↔
      x.sourceCommon ⊆ F ∧ x.divisor ⊆ x.sourceCommon ∧ x.overlap ⊆ F ∧
        x.frequency ∈ K x.sourceCommon x.divisor := by
  simp only [secondExpansionPool, Finset.mem_biUnion, Finset.mem_powerset, Finset.mem_image]
  constructor
  · rintro ⟨G,hG,E,hE,V,hV,k,hk,hx⟩
    subst x
    exact ⟨hG,hE,hV,hk⟩
  · rintro ⟨hG,hE,hV,hk⟩
    exact ⟨x.sourceCommon,hG,x.divisor,hE,x.overlap,hV,x.frequency,hk,rfl⟩

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

end

open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))
  (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)

include hc

end SecondPassArithmetic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.QuadraticSieve.PrincipalDifference
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
namespace SecondPassArithmetic

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem primeProductNorm_eq_ideal_norm (S : Finset ι) :
    primeProductNorm p S = (Ideal.absNorm (∏ i ∈ S, Ideal.span {p i}) : ℝ) := by
  rw [primeProductNorm, ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span,
    FiniteGaussPhase.span_finset_prod]

include hp in
omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem primeProductNorm_ge_one (S : Finset ι) : 1 ≤ primeProductNorm p S :=
  by
    rw [primeProductNorm, ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (show Ideal.absNorm (Ideal.span {∏ i ∈ S, p i}) ≠ 0 by
      rw [ne_eq, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
      exact Finset.prod_ne_zero_iff.mpr (fun i hi => hp i))

include hp in
omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem primeProductNorm_mono {S T : Finset ι} (hST : S ⊆ T) :
    primeProductNorm p S ≤ primeProductNorm p T := by
  have hd : Disjoint S (T\S) := Finset.disjoint_sdiff
  have hu : S ∪ (T\S) = T := Finset.union_sdiff_of_subset hST
  rw [← hu, FirstPassCubeLabels.primeProductNorm_union p S (T\S) hd]
  exact le_mul_of_one_le_right (FirstPassCubeLabels.primeProductNorm_pos p hp S).le
    (primeProductNorm_ge_one p hp _)

end SecondPassArithmetic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.SupportNorms
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
open FirstCauchyArithmetic (supportMobius)
open FirstPassCubeLabels (columnLog primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem primeSubsetGenerator_norm_eq_productNorm (E : Finset ι) :
    ‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖ ^ 2 = primeProductNorm p E := by
  rw [primeSubsetGenerator_norm_sq, primeProductNorm_eq_ideal_norm]

end

open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog primeProductNorm b0Label jLabel)
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)
open RayFourExpansion (RayCharacter)

end SecondPassArithmetic

open scoped BigOperators Classical SchwartzMap

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.GreenIdentity
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
open FirstPassCubeLabels (primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

lemma normLogScale_pos (j : ℕ) : 0 < normLogScale j := Real.exp_pos _
lemma normLogScale_ge_one (j : ℕ) : 1 ≤ normLogScale j :=
  Real.one_le_exp (by positivity)

lemma normLogBin_scale_bounds (u : ℝ) (hu : 1 ≤ u) :
    normLogScale (normLogBin u) ≤ u ∧
      u ≤ normLogScale (normLogBin u) * Real.exp 1 := by
  have hu0 : 0 < u := by linarith
  constructor
  · have h := Real.exp_le_exp.mpr (Nat.floor_le (Real.log_nonneg hu))
    simpa only [Real.exp_log hu0, normLogScale, normLogBin] using h
  · have h := Real.exp_le_exp.mpr (Nat.lt_floor_add_one (Real.log u)).le
    simpa only [Real.exp_log hu0, Real.exp_add, normLogScale, normLogBin] using h

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]

lemma element_norm_ge_one (a : O) (ha : a ≠ 0) : 1 ≤ ‖eisEmbedding a‖^2 := by
  rw [eisEmbedding_norm_sq_eq_absNorm_span]
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (show Ideal.absNorm (Ideal.span {a}) ≠ 0 by
    rw [ne_eq, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact ha)

end

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]

end SecondPassArithmetic

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

lemma element_norm_le_of_dvd {a b : O} (hb : b ≠ 0) (h : a ∣ b) :
    ‖eisEmbedding a‖^2 ≤ ‖eisEmbedding b‖^2 := by
  obtain ⟨c,rfl⟩ := h
  have hc : c ≠ 0 := (mul_ne_zero_iff.mp hb).2
  rw [map_mul, norm_mul, mul_pow]
  exact le_mul_of_one_le_right (sq_nonneg _) (element_norm_ge_one c hc)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]

include hp in
omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
lemma primeProduct_ne_zero (B : Finset ι) (v : ι → ℕ) : primeProduct p B v ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun i _hi => pow_ne_zero _ (hp i))

include hp in
omit [∀ (i : ι), (span {p i}).IsMaximal] in
lemma squarefreeLabel_active_bound (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) :
    ‖eisEmbedding (squarefreeLabel p B v)‖^2 ≤ primeProductNorm p (cubeActiveSupport B v ε₁ ε₂) := by
  let S := B.filter (fun i => parity (v i))
  have he : squarefreeLabel p B v = ∏ i ∈ S, p i := by
    unfold squarefreeLabel primeProduct S
    rw [Finset.prod_filter]
    apply Finset.prod_congr rfl
    intro i hi
    cases hb : parity (v i) <;> simp [bit,hb]
  have hsub : S ⊆ cubeActiveSupport B v ε₁ ε₂ := by
    intro i hi
    obtain ⟨hi,hpi⟩ := Finset.mem_filter.mp hi
    apply Finset.mem_filter.mpr
    refine ⟨hi,?_⟩
    change parity (v i) = true at hpi
    rw [hpi]
    cases h1 : ε₁ i <;> cases h2 : ε₂ i <;> decide
  rw [he]
  exact primeProductNorm_mono p hp hsub

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
lemma jLabel_dvd_cube_product (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (hv : ∀ i ∈ B, 0 < v₁ i+v₂ i) :
    jLabel p B (fun i => v₁ i+v₂ i) ε₁ ε₂ ∣ primeProduct p B v₁ * primeProduct p B v₂ := by
  rw [← primeProduct_add]
  apply Finset.prod_dvd_prod_of_dvd
  intro i hi
  apply pow_dvd_pow
  dsimp only
  unfold bit
  split <;> have h := hv i hi <;> omega

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
lemma b0_square_dvd_cube_product (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (hv : ∀ i ∈ B, 0 < v₁ i+v₂ i) :
    b0Label p B (fun i => v₁ i+v₂ i) ε₁ ε₂ ^ 2 ∣ primeProduct p B v₁ * primeProduct p B v₂ := by
  rw [FirstPassCubeLabels.cube_pair_product_decomposition p B v₁ v₂ ε₁ ε₂ hv]
  exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
lemma b0_jLabel_square (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (hv : ∀ i ∈ B, 0 < v₁ i+v₂ i) :
    (b0Label p B (fun i => v₁ i+v₂ i) ε₁ ε₂ * jLabel p B (fun i => v₁ i+v₂ i) ε₁ ε₂)^2 =
      primeProduct p B v₁ * primeProduct p B v₂ * squarefreeLabel p B (fun i => v₁ i+v₂ i) := by
  rw [FirstPassCubeLabels.jLabel_eq_squarefree_mul_j2,
    FirstPassCubeLabels.cube_pair_product_decomposition p B v₁ v₂ ε₁ ε₂ hv]
  ring

include hp in

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem cube_label_norm_bounds (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (hv : ∀ i ∈ B, 0 < v₁ i+v₂ i) (B₀ : ℝ) (hB : 0 ≤ B₀)
    (hb₁ : ‖eisEmbedding (primeProduct p B v₁)‖^2 ≤ B₀)
    (hb₂ : ‖eisEmbedding (primeProduct p B v₂)‖^2 ≤ B₀) :
    let v := fun i => v₁ i+v₂ i
    ‖eisEmbedding (jLabel p B v ε₁ ε₂)‖^2 ≤ B₀^2 ∧
    ‖eisEmbedding (b0Label p B v ε₁ ε₂)‖^2 ≤ B₀ ∧
    ‖eisEmbedding (b0Label p B v ε₁ ε₂)‖^2 ≤
      B₀*‖eisEmbedding (∏ i ∈ cubeActiveSupport B v ε₁ ε₂,p i)‖ /
        ‖eisEmbedding (jLabel p B v ε₁ ε₂)‖^2 := by
  dsimp only
  have hbb : ‖eisEmbedding (primeProduct p B v₁ * primeProduct p B v₂)‖^2 ≤ B₀^2 := by
    rw [map_mul,norm_mul,mul_pow]
    simpa only [pow_two] using mul_le_mul hb₁ hb₂ (sq_nonneg _) hB
  have hbb0 := mul_ne_zero (primeProduct_ne_zero p hp B v₁) (primeProduct_ne_zero p hp B v₂)
  have hJ := (element_norm_le_of_dvd hbb0 (jLabel_dvd_cube_product p B v₁ v₂ ε₁ ε₂ hv)).trans hbb
  have hb0sq := (element_norm_le_of_dvd hbb0 (b0_square_dvd_cube_product p B v₁ v₂ ε₁ ε₂ hv)).trans hbb
  simp only [map_pow,norm_pow] at hb0sq
  have hb0 : ‖eisEmbedding (b0Label p B (fun i => v₁ i+v₂ i) ε₁ ε₂)‖^2 ≤ B₀ := by
    nlinarith [sq_nonneg ‖eisEmbedding (b0Label p B (fun i => v₁ i+v₂ i) ε₁ ε₂)‖]
  refine ⟨hJ,hb0,?_⟩
  have heq := congrArg (fun a : O => ‖eisEmbedding a‖^2) (b0_jLabel_square p B v₁ v₂ ε₁ ε₂ hv)
  simp only [map_pow,map_mul,norm_pow,norm_mul,mul_pow] at heq
  have hs := squarefreeLabel_active_bound p hp B (fun i => v₁ i+v₂ i) ε₁ ε₂
  have hNprod : ‖eisEmbedding (primeProduct p B v₁)‖^2 * ‖eisEmbedding (primeProduct p B v₂)‖^2 ≤ B₀^2 := by
    simpa only [map_mul,norm_mul,mul_pow] using hbb
  have hmul := mul_le_mul hNprod hs (sq_nonneg _) (sq_nonneg B₀)
  change _ ≤ B₀^2*‖eisEmbedding (∏ i ∈ cubeActiveSupport B (fun i => v₁ i+v₂ i) ε₁ ε₂,p i)‖^2 at hmul
  have hjpos : 0 < ‖eisEmbedding (jLabel p B (fun i => v₁ i+v₂ i) ε₁ ε₂)‖^2 := by
    exact zero_lt_one.trans_le (element_norm_ge_one _ (primeProduct_ne_zero p hp B _))
  apply (le_div_iff₀ hjpos).mpr
  apply (sq_le_sq₀ (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    (mul_nonneg hB (norm_nonneg _))).mp
  simp only [mul_pow]
  exact heq.trans_le hmul

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.ReopenedFibers
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
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

open scoped BigOperators Classical
namespace SecondPassArithmetic

section

open ActualEisensteinCubic FirstPassCubeLabels
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]

lemma mem_reopenedCubeFiber (v₁ v₂ : ι →₀ ℕ) (b : CubeCoordinates ι) :
    b ∈ reopenedCubeFiber v₁ v₂ ↔
      b.leftExponent=v₁ ∧ b.rightExponent=v₂ ∧ b.Admissible := by
  constructor
  · intro hb
    obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨h₂,h₁⟩ := Finset.mem_product.mp hA
    exact ⟨rfl,rfl,Finset.mem_powerset.mp h₁,Finset.mem_powerset.mp h₂⟩
  · rintro ⟨hl,hr,hb⟩
    apply Finset.mem_image.mpr
    refine ⟨(b.rightDivisor,b.leftDivisor),?_,?_⟩
    · apply Finset.mem_product.mpr
      have hs : b.support=v₁.support∪v₂.support := by rw [CubeCoordinates.support,hl,hr]
      exact ⟨Finset.mem_powerset.mpr (hs ▸ hb.2),Finset.mem_powerset.mpr (hs ▸ hb.1)⟩
    · exact CubeCoordinates.ext hl.symm hr.symm rfl rfl

lemma mem_reopenedCubeFamily (Q : Finset (ι →₀ ℕ)) (b : CubeCoordinates ι) :
    b ∈ reopenedCubeFamily Q ↔ b.leftExponent ∈ Q ∧ b.rightExponent ∈ Q ∧ b.Admissible := by
  constructor
  · intro hb
    obtain ⟨v,hv,hb⟩ := Finset.mem_biUnion.mp hb
    obtain ⟨hl,hr,ha⟩ := (mem_reopenedCubeFiber v.2 v.1 b).mp hb
    exact ⟨hl ▸ (Finset.mem_product.mp hv).2,hr ▸ (Finset.mem_product.mp hv).1,ha⟩
  · rintro ⟨hl,hr,ha⟩
    exact Finset.mem_biUnion.mpr ⟨(b.rightExponent,b.leftExponent),Finset.mem_product.mpr ⟨hr,hl⟩,
      (mem_reopenedCubeFiber _ _ b).mpr ⟨rfl,rfl,ha⟩⟩

lemma reopenedCubeFamily_admissible (Q : Finset (ι →₀ ℕ)) :
    ∀ b ∈ reopenedCubeFamily Q,b.Admissible :=
  fun b hb => ((mem_reopenedCubeFamily Q b).mp hb).2.2

omit [DecidableEq ι] in
lemma primeProduct_finsupp_support (p : ι → ActualEisensteinCubic.O) (B : Finset ι) (v : ι →₀ ℕ)
    (hv : v.support ⊆ B) : primeProduct p B v=primeProduct p v.support v := by
  unfold primeProduct
  symm
  apply Finset.prod_subset hv
  intro i hi hn
  have hv0 : v i=0 := by simpa only [Finsupp.mem_support_iff,not_not] using hn
  simp only [hv0,pow_zero]

lemma reopenedCubeFamily_cube_norms (p : ι → ActualEisensteinCubic.O) (Q : Finset (ι →₀ ℕ)) (B : ℝ)
    (hQ : ∀ v ∈ Q,‖eisEmbedding (primeProduct p v.support v)‖^2 ≤ B) :
    ∀ b ∈ reopenedCubeFamily Q,
      ‖eisEmbedding (primeProduct p b.support b.leftExponent)‖^2 ≤ B ∧
      ‖eisEmbedding (primeProduct p b.support b.rightExponent)‖^2 ≤ B := by
  intro b hb
  obtain ⟨hl,hr,ha⟩ := (mem_reopenedCubeFamily Q b).mp hb
  rw [primeProduct_finsupp_support p b.support b.leftExponent Finset.subset_union_left,
    primeProduct_finsupp_support p b.support b.rightExponent Finset.subset_union_right]
  exact ⟨hQ _ hl,hQ _ hr⟩

end

open ActualEisensteinCubic FirstPassCubeLabels
open ConcreteTraceCRT (eisEmbedding)
open ConcretePrimeRowBridge (idealGenerator)

end SecondPassArithmetic

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff SchwartzMap

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.RowCompletion.SupportBounds
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
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

open scoped BigOperators Classical
namespace CanonicalRowCompletion

open ActualEisensteinCubic
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open CompletedGauss hiding O

theorem cubeIdeal_ne_zero (F : Finset (Ideal ActualEisensteinCubic.O)) (v : primePool F →₀ ℕ) :
    cubeIdeal F v ≠ 0 := by
  unfold cubeIdeal
  exact Finset.prod_ne_zero_iff.mpr (fun i _=>pow_ne_zero _ (NeZero.ne i.val))

end CanonicalRowCompletion

open scoped BigOperators Classical
open MeasureTheory

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.CanonicalLogEnergy
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
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical

namespace CanonicalRowCompletion

open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O

theorem activeCubeLogBin_norms (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (b X : ℝ) (j : ℕ)
    (v : primePool (InitialMeanSquare.outsideSquarefreeIdeals S D) →₀ ℕ)
    (hv : v ∈ activeCubeLogBin S D b X j) :
    normLogScale j ≤ (Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v) : ℝ) ∧
    (Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v) : ℝ) ≤ Real.exp 1*normLogScale j := by
  have hj := (Finset.mem_filter.mp hv).2
  rw [← hj]
  have hh := normLogBin_scale_bounds
    (Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v) : ℝ)
    (norm_at_least_one _ (cubeIdeal_ne_zero _ v))
  exact ⟨hh.1,by simpa only [mul_comm,cubeLogIndex] using hh.2⟩

end CanonicalRowCompletion

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.CoordinateLaplacian
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
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

open scoped BigOperators Classical

open scoped BigOperators Classical
namespace CanonicalCoefficientClass

section
open ActualEisensteinCubic
open SecondPassArithmetic (rayMonoid conjugateRayMonoid rayMonoid_apply conjugateRayMonoid_apply
  FirstCoreIndex firstCoreTwist sideRayMonoid SecondRayIndex secondRayMinus secondRayPlus)
open RayFourExpansion (RayCharacter)

lemma rayMonoid_mul (χ η : RayCharacter) : rayMonoid (χ*η)=rayMonoid χ*rayMonoid η := by
  ext x
  simp only [rayMonoid_apply,RayFourExpansion.rayCharacter,MulChar.mul_apply,MonoidHom.mul_apply]

lemma conjugateRayMonoid_eq (χ : RayCharacter) : conjugateRayMonoid χ=rayMonoid (star χ) := by
  ext x
  simp only [conjugateRayMonoid_apply,rayMonoid_apply,RayFourExpansion.rayCharacter,MulChar.star_apply]

lemma IsBaseRayTwist.mul_ray {base Ψ : ActualEisensteinCubic.O→*ℂ} (hΨ : IsBaseRayTwist base Ψ) (χ : RayCharacter) :
    IsBaseRayTwist base (rayMonoid χ*Ψ) := by
  rcases hΨ with h|⟨η,h⟩
  · exact Or.inr ⟨χ,by rw [h]⟩
  · exact Or.inr ⟨χ*η,by rw [h,rayMonoid_mul,mul_assoc]⟩

lemma firstCoreTwist_single_ray (side : Bool) (χ : RayCharacter) (Ψ : ActualEisensteinCubic.O→*ℂ)
    (r : FirstCoreIndex) :
    firstCoreTwist side χ Ψ r =
      rayMonoid ((if side then star χ else χ)*FirstPassCubeLabels.coreRayCharacter side r.1 r.2.2)*Ψ := by
  rw [rayMonoid_mul]
  have hcore : FirstPassCubeLabels.coreRayTwist side r.1 r.2.2 =
      rayMonoid (FirstPassCubeLabels.coreRayCharacter side r.1 r.2.2) := rfl
  unfold firstCoreTwist sideRayMonoid
  rw [hcore]
  cases side <;> simp only [Bool.false_eq_true,ite_false,ite_true,conjugateRayMonoid_eq] <;> ac_rfl

lemma IsBaseRayTwist.firstCore {base Ψ : ActualEisensteinCubic.O→*ℂ} (hΨ : IsBaseRayTwist base Ψ)
    (side : Bool) (χ : RayCharacter) (r : FirstCoreIndex) :
    IsBaseRayTwist base (firstCoreTwist side χ Ψ r) := by
  rw [firstCoreTwist_single_ray]
  exact hΨ.mul_ray _

lemma secondRayMinus_single_ray (Ψ : ActualEisensteinCubic.O→*ℂ) (r : SecondRayIndex) :
    secondRayMinus Ψ r=rayMonoid (star r.2.2*star r.1.2)*Ψ := by
  rw [rayMonoid_mul]
  simp only [secondRayMinus,conjugateRayMonoid_eq,mul_assoc]

lemma secondRayPlus_single_ray (Ψ : ActualEisensteinCubic.O→*ℂ) (r : SecondRayIndex) :
    secondRayPlus Ψ r=rayMonoid (r.2.1*star r.1.1)*Ψ := by
  rw [rayMonoid_mul]
  simp only [secondRayPlus,conjugateRayMonoid_eq,mul_assoc]

lemma IsBaseRayTwist.secondMinus {base Ψ : ActualEisensteinCubic.O→*ℂ} (hΨ : IsBaseRayTwist base Ψ)
    (r : SecondRayIndex) : IsBaseRayTwist base (secondRayMinus Ψ r) := by
  rw [secondRayMinus_single_ray]
  exact hΨ.mul_ray _

lemma IsBaseRayTwist.secondPlus {base Ψ : ActualEisensteinCubic.O→*ℂ} (hΨ : IsBaseRayTwist base Ψ)
    (r : SecondRayIndex) : IsBaseRayTwist base (secondRayPlus Ψ r) := by
  rw [secondRayPlus_single_ray]
  exact hΨ.mul_ray _

end

open ActualEisensteinCubic
open ActualEisensteinCoordinates (eval coords eval_coords)
open ShortDraftLatticeCount (qNat qO_nonneg coords_eval)

end CanonicalCoefficientClass

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.RowCompletion.CubicReopening
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
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

open scoped BigOperators Classical
namespace CanonicalRowCompletion

section
open ActualEisensteinCubic
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open FirstPassCubeLabels hiding O

theorem cubeIdeal_eq_primeProduct_span (F : Finset (Ideal ActualEisensteinCubic.O))
    (hF : ∀I∈F,Admissible I) (v : primePool F→₀ℕ) :
    Ideal.span {primeProduct (poolPrimary F) v.support v}=cubeIdeal F v := by
  rw [primeProduct,FiniteGaussPhase.span_finset_prod]
  simp only [←Ideal.span_singleton_pow,poolPrimary_span F hF]
  unfold cubeIdeal
  apply Finset.prod_subset (Finset.subset_univ v.support)
  intro i hi hni
  rw [Finsupp.notMem_support_iff.mp hni,pow_zero]

theorem cubeIdeal_primeProduct_norm (F : Finset (Ideal ActualEisensteinCubic.O))
    (hF : ∀I∈F,Admissible I) (v : primePool F→₀ℕ) :
    ‖ConcreteTraceCRT.eisEmbedding (primeProduct (poolPrimary F) v.support v)‖^2=
      (Ideal.absNorm (cubeIdeal F v):ℝ) := by
  rw [eisEmbedding_norm_sq_eq_absNorm_span,cubeIdeal_eq_primeProduct_span F hF]

end

open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open CanonicalCubeSeparation JointLogSeparation
open FirstPassCubeLabels (columnLog)

end CanonicalRowCompletion

open scoped BigOperators Classical

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialArithmetic
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.InverseInitialArithmetic
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open MixedCrossSeparation (columnCoefficient)
open SevenEighths.InverseMoment SevenEighths.InverseInitialFibers
open CompletedGauss
local notation "O" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → O) (hp : ∀ i, p i≠0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, λ₀∉Ideal.span {p i})

include hp in
omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem sourceIdeal_ne_zero (S : Finset ι) : sourceIdeal p S≠0 :=
  Ideal.span_singleton_eq_bot.not.mpr (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i))

omit [DecidableEq ι] in
theorem source_prime_dvd (S : Finset ι) (i : ι) (hi : i∈S) :
    (sourcePrime p i).val∣sourceIdeal p S := by
  apply Ideal.dvd_iff_le.mpr
  apply Ideal.span_singleton_le_span_singleton.mpr
  exact Finset.dvd_prod_of_mem p hi

end SevenEighths.InverseInitialArithmetic

end

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

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.SlotAssignments
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
noncomputable section
variable {σ ι : Type*} [DecidableEq σ] [DecidableEq ι]

theorem indexedSlotAssignment_support (I : Finset σ) (L : σ → Finset ι)
    (A : Finset ι) (q : ∀ i ∈ I, ι) (hq : q ∈ I.pi (fun i => L i ∩ A))
    (j : Fin I.card) :
    indexedSlotAssignment I q j ∈ L ((I.equivFin).symm j).val ∩ A :=
  Finset.mem_pi.mp hq _ _

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.SecondAssignedSum
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
noncomputable section
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]

omit [DecidableEq ι] [DecidableEq σ] in
lemma indexedSlotAssignment_apply (I : Finset σ) (q : ∀ i ∈ I,ι) (i : σ) (hi : i ∈ I) :
    indexedSlotAssignment I q (I.equivFin ⟨i,hi⟩) = q i hi := by
  exact congrArg (fun j : I => q j.val j.property) ((I.equivFin).symm_apply_apply ⟨i,hi⟩)

omit [DecidableEq ι] [DecidableEq σ] in
@[simp] theorem assignedSecondCoefficient_attach {Jo : ℕ}
    (J₁ J₂ : Finset σ) (a₁ a₂ : σ → ι → ℂ)
    (x : MarkedSecondSource ι Jo 0) (q : (∀ i ∈ J₁,ι) × (∀ i ∈ J₂,ι)) :
    assignedSecondCoefficient J₁ J₂ a₁ a₂ (attachPairedSlots J₁ J₂ (x,q)) =
      pairedSlotWeight J₁ J₂ a₁ a₂ q := by
  simp only [assignedSecondCoefficient,attachPairedSlots,attachSecondSlots,
    pairedSlotAssignment,Fin.addCases_left,Fin.addCases_right,indexedSlotAssignment_apply,pairedSlotWeight]

theorem paired_assignment_filter (J₁ J₂ : Finset σ) (L₁ L₂ : σ → Finset ι) (A : Finset ι) :
    ((J₁.pi L₁) ×ˢ (J₂.pi L₂)).filter (fun q => ∀ j, pairedSlotAssignment J₁ J₂ q j ∈ A) =
      (J₁.pi (fun i => L₁ i∩A)) ×ˢ (J₂.pi (fun i => L₂ i∩A)) := by
  ext q
  constructor
  · intro hq
    obtain ⟨hmem,hs⟩ := Finset.mem_filter.mp hq
    obtain ⟨hq₁,hq₂⟩ := Finset.mem_product.mp hmem
    apply Finset.mem_product.mpr
    constructor
    · apply Finset.mem_pi.mpr
      intro i hi
      refine Finset.mem_inter.mpr ⟨Finset.mem_pi.mp hq₁ i hi,?_⟩
      simpa only [pairedSlotAssignment,Fin.addCases_left,Fin.addCases_right,indexedSlotAssignment_apply] using hs (Fin.castAdd J₂.card (J₁.equivFin ⟨i,hi⟩))
    · apply Finset.mem_pi.mpr
      intro i hi
      refine Finset.mem_inter.mpr ⟨Finset.mem_pi.mp hq₂ i hi,?_⟩
      simpa only [pairedSlotAssignment,Fin.addCases_left,Fin.addCases_right,indexedSlotAssignment_apply] using hs (Fin.natAdd J₁.card (J₂.equivFin ⟨i,hi⟩))
  · intro hq
    obtain ⟨hq₁,hq₂⟩ := Finset.mem_product.mp hq
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_,?_⟩,?_⟩
    · exact Finset.mem_pi.mpr (fun i hi => (Finset.mem_inter.mp (Finset.mem_pi.mp hq₁ i hi)).1)
    · exact Finset.mem_pi.mpr (fun i hi => (Finset.mem_inter.mp (Finset.mem_pi.mp hq₂ i hi)).1)
    · intro j
      refine Fin.addCases (fun k => ?_) (fun k => ?_) j
      · simpa only [pairedSlotAssignment,Fin.addCases_left] using
          (Finset.mem_inter.mp (indexedSlotAssignment_support J₁ L₁ _ q.1 hq₁ k)).2
      · simpa only [pairedSlotAssignment,Fin.addCases_right] using
          (Finset.mem_inter.mp (indexedSlotAssignment_support J₂ L₂ _ q.2 hq₂ k)).2

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.SecondPuncture
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open InverseInitialArithmetic (sourceIdeal sourceIdeal_gen sourceIdeal_ne_zero)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem radical_product_norm_le (I J B R : Ideal Eis) (hI : I ≠ 0) (hB : B ≠ 0)
    (hR : R ≠ 0) (hBJ : B ≤ J.radical) :
    (Ideal.absNorm (I*J*R).radical : ℝ) ≤
      (Ideal.absNorm I.radical : ℝ)*Ideal.absNorm B*Ideal.absNorm R := by
  have hi : I.radical ≠ 0 := by
    intro he
    apply hI
    exact le_antisymm (he ▸ Ideal.le_radical) bot_le
  have hle : I.radical*B*R ≤ (I*J*R).radical := by
    rw [Ideal.radical_mul,Ideal.radical_mul]
    refine le_inf (le_inf ?_ ?_) ?_
    · exact Ideal.mul_le_left.trans Ideal.mul_le_left
    · exact (Ideal.mul_le_left.trans Ideal.mul_le_right).trans hBJ
    · exact Ideal.mul_le_right.trans Ideal.le_radical
  have hb := Nat.le_of_dvd (Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
    (mul_ne_zero (mul_ne_zero hi hB) hR))) (Ideal.absNorm_dvd_absNorm_of_le hle)
  simpa only [map_mul,Nat.cast_mul] using (show (Ideal.absNorm (I*J*R).radical : ℝ) ≤
    Ideal.absNorm (I.radical*B*R) from by exact_mod_cast hb)

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.SecondSupportedEnergy
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open InverseSecondFibers SecondPassArithmetic
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem ActualSecondSourceConditions.mono {Jo Jn : ℕ}
    {S T : Finset (MarkedSecondSource ι Jo Jn)} (h : ActualSecondSourceConditions p S)
    (hTS : T ⊆ S) : ActualSecondSourceConditions p T where
  admissible x hx := h.admissible x (hTS hx)
  common_disjoint x hx := h.common_disjoint x (hTS hx)
  first_divisor x hx := h.first_divisor x (hTS hx)
  second_divisor x hx := h.second_divisor x (hTS hx)
  old_support x hx := h.old_support x (hTS hx)
  new_support x hx := h.new_support x (hTS hx)
  quotient_nonzero x hx := h.quotient_nonzero x (hTS hx)

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.SecondPunctureBudget
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι] (p : ι → Eis) (hp : ∀ i, p i ≠ 0)
  [∀ i, (Ideal.span {p i}).IsMaximal]

include hp in
omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem second_residual_norm_eq_div (E G : Finset ι) (hE : E ⊆ G) :
    primeProductNorm p (G\E) = primeProductNorm p G/primeProductNorm p E := by
  have he : primeProductNorm p G = primeProductNorm p E*primeProductNorm p (G\E) := by
    rw [←primeProductNorm_union p E (G\E) Finset.disjoint_sdiff,Finset.union_sdiff_of_subset hE]
  rw [he]
  field_simp [(primeProductNorm_pos p hp E).ne']

include hp in

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem second_residual_norm_power_bound (E G : Finset ι) (hE : E ⊆ G)
    (Z g theta eta : ℝ) (hZ : 0 < Z)
    (hg : primeProductNorm p G ≤ Z^(g+eta))
    (hd : Z^(theta-eta) ≤ primeProductNorm p E) :
    primeProductNorm p (G\E) ≤ Z^(g-theta+2*eta) := by
  rw [second_residual_norm_eq_div p hp E G hE]
  calc
    _ ≤ Z^(g+eta)/Z^(theta-eta) := div_le_div₀ (Real.rpow_pos_of_pos hZ _).le hg
      (Real.rpow_pos_of_pos hZ _) hd
    _ = Z^((g+eta)-(theta-eta)) := (Real.rpow_sub hZ _ _).symm
    _ = _ := by congr 1; ring

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.SecondTripleBounds
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι] (p : ι → Eis)
  (hp : ∀ i, p i ≠ 0)

include hp in

theorem actual_second_common_center
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (hE : x.second.divisor ⊆ x.second.sourceCommon)
    (Z g theta eta : ℝ) (hZ : 1 < Z)
    (hG : primeProductNorm p x.second.sourceCommon ≤ Z^(g+eta))
    (hD : Z^(theta-eta) ≤ primeProductNorm p x.second.divisor) :
    -2*eta ≤ g-theta := by
  have hh : Z^(theta-eta) ≤ Z^(g+eta) :=
    hD.trans ((primeProductNorm_mono p hp hE).trans hG)
  have hh' := (Real.rpow_le_rpow_left_iff hZ).mp hh
  linarith

variable [∀ i, (Ideal.span {p i}).IsMaximal]

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.Basic
namespace OAI

namespace SevenEighths.InverseMoment

theorem child_margins_sharp {F M Q Q' z c ell A t g theta V j delta eta : ℝ}
    (h : CanonicalMargins F M Q z c)
    (hA : 0 ≤ A) (ht : 0 ≤ t) (hV : 0 ≤ V) (hj : 0 ≤ j)
    (hgt : -2 * eta ≤ g - theta)
    (hQ : Q' ≤ Q + decrease ell A t g theta V + 4 * eta) :
    c + delta - 5 * eta ≤
      childF F ell A t g theta V j delta -
      childM M ell A t g theta V j eta - Q' - z ∧
    c + 4 * delta - 7 * eta ≤
      4 * childF F ell A t g theta V j delta -
      3 * childM M ell A t g theta V j eta - 6 * z := by
  obtain ⟨h₁, h₂⟩ := h
  unfold childF childM decrease at *
  constructor <;> linarith

theorem child_margins {F M Q Q' z c ell A t g theta V j delta eta : ℝ}
    (h : CanonicalMargins F M Q z c)
    (hA : 0 ≤ A) (ht : 0 ≤ t) (hV : 0 ≤ V) (hj : 0 ≤ j)
    (hgt : -2 * eta ≤ g - theta) (hdelta : 0 ≤ delta) (heta : 0 ≤ eta)
    (hQ : Q' ≤ Q + decrease ell A t g theta V + 4 * eta) :
    CanonicalMargins (childF F ell A t g theta V j delta)
      (childM M ell A t g theta V j eta) Q' z (c - 7 * eta) := by
  obtain ⟨h₁, h₂⟩ := child_margins_sharp (delta := delta) h hA ht hV hj hgt hQ
  constructor <;> linarith

end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.SecondSourceAttachment
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondFibers
open InverseInitialArithmetic (sourceIdeal)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]

omit [DecidableEq ι] in
theorem attachSecondExpansion_recover {Jo : ℕ} (x : MarkedSecondSource ι Jo 0) :
    attachSecondExpansion (secondParentOf x) x.second = x := by
  apply MarkedSecondSource.ext <;> try rfl
  funext i
  exact Fin.elim0 i

variable (p : ι → Eis) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.SecondParentAssembly
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondFibers
open InverseInitialArithmetic (sourceIdeal)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]

omit [DecidableEq ι] in
theorem mem_attachedSecondFamily {Jo : ℕ} (parents : Finset (SecondParentSource ι Jo))
    (source : SecondParentSource ι Jo → Finset (SecondExpansionData ι))
    (x : MarkedSecondSource ι Jo 0) :
    x∈attachedSecondFamily parents source ↔
      secondParentOf x∈parents ∧ x.second∈source (secondParentOf x) := by
  simp only [attachedSecondFamily,Finset.mem_biUnion,Finset.mem_image]
  constructor
  · rintro ⟨parent,hp,y,hy,rfl⟩
    exact ⟨hp,hy⟩
  · rintro ⟨hp,hx⟩
    exact ⟨secondParentOf x,hp,x.second,hx,attachSecondExpansion_recover x⟩

variable (p : ι → Eis) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem attached_family_conditions {Jo : ℕ} (parents : Finset (SecondParentSource ι Jo))
    (source : SecondParentSource ι Jo → Finset (SecondExpansionData ι))
    (ha : ∀ parent∈parents,parent.cube.Admissible)
    (hC : ∀ parent∈parents,Disjoint parent.firstCommon parent.cube.support)
    (hD : ∀ parent∈parents,parent.firstDivisor ⊆ parent.firstCommon∪parent.cube.support)
    (hE : ∀ parent∈parents,∀ x∈source parent,x.divisor ⊆ x.sourceCommon)
    (hold : ∀ parent∈parents,∀ i,(parent.oldAssigned i).val ∣
      sourceIdeal p parent.cube.support*sourceIdeal p parent.firstCommon*parent.quotient)
    (hq : ∀ parent∈parents,parent.quotient ≠ 0) :
    ActualSecondSourceConditions p (attachedSecondFamily parents source) := by
  have h (x : MarkedSecondSource ι Jo 0) (hx : x∈attachedSecondFamily parents source) :=
    (mem_attachedSecondFamily parents source x).mp hx
  constructor
  · intro x hx; exact ha (secondParentOf x) (h x hx).1
  · intro x hx; exact hC (secondParentOf x) (h x hx).1
  · intro x hx; exact hD (secondParentOf x) (h x hx).1
  · intro x hx; exact hE (secondParentOf x) (h x hx).1 x.second (h x hx).2
  · intro x hx i; exact hold (secondParentOf x) (h x hx).1 i
  · intro x hx i; exact Fin.elim0 i
  · intro x hx; exact hq (secondParentOf x) (h x hx).1

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.FirstPriorityParents
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseFirstPriorityParents
open ActualEisensteinCubic SecondPassArithmetic FirstPassCubeLabels FirstCauchyArithmetic
open InverseMoment InverseInitialArithmetic
local notation "O" => ActualEisensteinCubic.O

variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ] {Jo : ℕ}

variable (p : ι→O) [∀ i,(Ideal.span {p i}).IsMaximal]

theorem extracted_prime_dvd (x : Source ι Jo) (hx : x.cube.Admissible)
    (negative : Bool) (i : ι) (hi : i∈extractedSupport negative x) :
    (sourcePrime p i).val∣sourceIdeal p x.cube.support*sourceIdeal p x.firstCommon*
      sourceIdeal p x.quotientSupport := by
  obtain hi|hi := Finset.mem_union.mp hi
  · obtain hi|hi := Finset.mem_union.mp hi
    · have hb : i∈x.cube.support := by
        cases negative <;> simp only [Bool.false_eq_true,ite_false,ite_true] at hi
        · exact hx.1 hi
        · exact hx.2 hi
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (source_prime_dvd p _ i hb) _) _
    · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (source_prime_dvd p _ i hi) _) _
  · exact dvd_mul_of_dvd_right (source_prime_dvd p _ i hi) _

variable (hp : ∀ i,p i≠0) (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

end SevenEighths.InverseFirstPriorityParents

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.WholePriorityParents
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMomentWholePriorityParents
open ActualEisensteinCubic SecondPassArithmetic FirstPassCubeLabels FirstCauchyArithmetic
open InverseMoment InverseInitialArithmetic InverseFirstPriorityParents
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ] {Jo : ℕ}

variable (p : ι→O) [∀ i,(Ideal.span {p i}).IsMaximal]

lemma mem_wholeAssignmentSource (extra : Source ι Jo→Finset ι) (source : Finset (Source ι Jo)) (negative : Bool)
    (J : Finset σ) (lists : σ→Finset ι)
    (x : Source ι Jo) (q : (∀ i∈J,ι)×(∀ i∈J,ι)) :
    (x,q)∈wholeAssignmentSource extra source negative J lists ↔ x∈source ∧
      q∈(J.pi (fun i=>lists i∩wholeExtractedSupport extra negative x))×ˢ
        (J.pi (fun i=>lists i∩wholeExtractedSupport extra negative x)) := by
  rw [←paired_assignment_filter]
  simp only [wholeAssignmentSource,Finset.mem_filter,Finset.mem_product]
  tauto

theorem mem_wholeAssignedParents (extra : Source ι Jo→Finset ι) (source : Finset (Source ι Jo)) (negative : Bool)
    (J : Finset σ) (lists : σ→Finset ι) (y : SecondParentSource ι (Jo+(J.card+J.card))) :
    y∈wholeAssignedParents p extra source negative J lists ↔
      ∃ x∈source,∃ q∈(J.pi (fun i=>lists i∩wholeExtractedSupport extra negative x))×ˢ
        (J.pi (fun i=>lists i∩wholeExtractedSupport extra negative x)),attach p J (x,q)=y := by
  simp only [wholeAssignedParents,Finset.mem_image]
  constructor
  · rintro ⟨⟨x,q⟩,hq,he⟩
    exact ⟨x,(mem_wholeAssignmentSource extra source negative J lists x q).mp hq |>.1,
      q,(mem_wholeAssignmentSource extra source negative J lists x q).mp hq |>.2,he⟩
  · rintro ⟨x,hx,q,hq,he⟩
    exact ⟨(x,q),(mem_wholeAssignmentSource extra source negative J lists x q).mpr ⟨hx,hq⟩,he⟩

theorem whole_extracted_prime_dvd (extra : Source ι Jo→Finset ι)
    (x : Source ι Jo) (hx : x.cube.Admissible) (he : extra x⊆x.cube.support)
    (negative : Bool) (i : ι) (hi : i∈wholeExtractedSupport extra negative x) :
    (sourcePrime p i).val∣sourceIdeal p x.cube.support*sourceIdeal p x.firstCommon*
      sourceIdeal p x.quotientSupport := by
  obtain hi|hi := Finset.mem_union.mp hi
  · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (source_prime_dvd p _ i (he hi)) _) _
  · exact extracted_prime_dvd p x hx negative i hi

theorem whole_attach_old_support (extra : Source ι Jo→Finset ι)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (x : Source ι Jo) (hx : SourceValid p x) (he : extra x⊆x.cube.support)
    (q : (∀ i∈J,ι)×(∀ i∈J,ι))
    (hq : q∈(J.pi (fun i=>lists i∩wholeExtractedSupport extra negative x))×ˢ
      (J.pi (fun i=>lists i∩wholeExtractedSupport extra negative x))) :
    ∀ i,((attach p J (x,q)).oldAssigned i).val∣
      sourceIdeal p (attach p J (x,q)).cube.support*
        sourceIdeal p (attach p J (x,q)).firstCommon*(attach p J (x,q)).quotient := by
  have hh : ∀ i,pairedSlotAssignment J J q i∈wholeExtractedSupport extra negative x := by
    have hf : q∈((J.pi lists)×ˢ(J.pi lists)).filter
        (fun q=>∀ i,pairedSlotAssignment J J q i∈wholeExtractedSupport extra negative x) := by
      rwa [paired_assignment_filter]
    exact (Finset.mem_filter.mp hf).2
  intro i
  refine Fin.addCases (fun k=>?_) (fun k=>?_) i
  · simpa only [attach,appendParent,parent,Fin.addCases_left] using hx.old_support k
  · simpa only [attach,appendParent,parent,Fin.addCases_right] using
      whole_extracted_prime_dvd p extra x hx.admissible he negative _ (hh k)

theorem whole_assigned_family_conditions (hp : ∀ i,p i≠0)
    (extra : Source ι Jo→Finset ι)
    (source : Finset (Source ι Jo)) (hs : ∀ x∈source,SourceValid p x)
    (he : ∀ x∈source,extra x⊆x.cube.support)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (expansion : SecondParentSource ι (Jo+(J.card+J.card))→Finset (SecondExpansionData ι))
    (hE : ∀ y∈wholeAssignedParents p extra source negative J lists,
      ∀ x∈expansion y,x.divisor⊆x.sourceCommon) :
    ActualSecondSourceConditions p
      (attachedSecondFamily (wholeAssignedParents p extra source negative J lists) expansion) := by
  apply attached_family_conditions p _ _
  · intro y hy
    obtain ⟨x,hx,q,hq,rfl⟩ := (mem_wholeAssignedParents p extra source negative J lists y).mp hy
    exact (hs x hx).admissible
  · intro y hy
    obtain ⟨x,hx,q,hq,rfl⟩ := (mem_wholeAssignedParents p extra source negative J lists y).mp hy
    exact (hs x hx).common_disjoint
  · intro y hy
    obtain ⟨x,hx,q,hq,rfl⟩ := (mem_wholeAssignedParents p extra source negative J lists y).mp hy
    exact (hs x hx).first_divisor
  · exact hE
  · intro y hy
    obtain ⟨x,hx,q,hq,rfl⟩ := (mem_wholeAssignedParents p extra source negative J lists y).mp hy
    exact whole_attach_old_support p extra negative J lists x (hs x hx) (he x hx) q hq
  · intro y hy
    obtain ⟨x,hx,q,hq,rfl⟩ := (mem_wholeAssignedParents p extra source negative J lists y).mp hy
    exact sourceIdeal_ne_zero p hp x.quotientSupport

end SevenEighths.InverseMomentWholePriorityParents

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.SecondSourceBlocks
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
namespace SevenEighths.InverseSecondSourceBlocks
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseMoment
open InverseSecondFibers InversePrioritySecondSource
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O
variable {ι σ κ : Type*} [DecidableEq ι] [DecidableEq σ] [DecidableEq κ]

omit [DecidableEq ι] in
theorem outerNorms_ge_one (p : ι → O) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) (hk : x.second.frequency ≠ 0) :
    ∀ i,1 ≤ outerNorms p x i := by
  intro i
  fin_cases i
  · exact primeProductNorm_ge_one p hp _
  · exact primeProductNorm_ge_one p hp _
  · exact primeProductNorm_ge_one p hp _
  · exact element_norm_ge_one _ hk

theorem dyadScale_pos (n : ℕ) : 0 < dyadScale n := by unfold dyadScale; positivity

theorem dyadIndex_bounds (r : ℝ) (hr : 1 ≤ r) :
    dyadScale (dyadIndex r) ≤ r ∧ r < 2*dyadScale (dyadIndex r) := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hlog : 0 ≤ Real.logb 2 r := Real.logb_nonneg (by norm_num) hr
  constructor
  · have h := (Real.le_logb_iff_rpow_le (by norm_num : (1:ℝ)<2) hr0).mp (Nat.floor_le hlog)
    simpa only [dyadScale,dyadIndex,Real.rpow_natCast] using h
  · have h := (Real.logb_lt_iff_lt_rpow (by norm_num : (1:ℝ)<2) hr0).mp
      (Nat.lt_floor_add_one (Real.logb 2 r))
    have ht : r < (2:ℝ)^(dyadIndex r+1) := by
      rw [←Real.rpow_natCast]
      simpa only [Nat.cast_add,Nat.cast_one,dyadIndex] using h
    simpa only [dyadScale,pow_succ,mul_comm] using ht

omit [DecidableEq ι] in
theorem cell_subset (p : ι → O) {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (d : BlockIndex) : cell p source d ⊆ source := Finset.filter_subset _ _

omit [DecidableEq ι] in
theorem cell_ratios (p : ι → O) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal] {Jo Jn : ℕ}
    (source : Finset (MarkedSecondSource ι Jo Jn)) (hk : ∀ x∈source,x.second.frequency ≠ 0)
    (d : BlockIndex) (x : MarkedSecondSource ι Jo Jn) (hx : x∈cell p source d) (i : Fin 4) :
    1 ≤ outerNorms p x i / dyadScale (d i) ∧ outerNorms p x i / dyadScale (d i) < 2 := by
  obtain ⟨hxs,he⟩ := (mem_cell p source d x).mp hx
  have hb := dyadIndex_bounds _ (outerNorms_ge_one p hp x (hk x hxs) i)
  have hi : dyadIndex (outerNorms p x i) = d i := congrFun he i
  rw [hi] at hb
  exact ⟨(le_div_iff₀ (dyadScale_pos _)).mpr (by simpa using hb.1),
    (div_lt_iff₀ (dyadScale_pos _)).mpr hb.2⟩

end SevenEighths.InverseSecondSourceBlocks

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.SecondCellPhysical
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseSecondSourceBlocks InverseSecondPrincipalCaller InverseSecondProfileUniform
open FourierBridge CompletedHeight SecondPassIntegration
local notation "O" => ActualEisensteinCubic.O

theorem second_cell_column_scale (Z X:ℝ) (d:BlockIndex) (hZ:1<Z) (hX:0<X) :
    Z^(secondCellColumnExponent Z X d)=X/(scales d 0*scales d 2) := by
  exact Real.rpow_logb (by linarith) (ne_of_gt hZ)
    (div_pos hX (mul_pos (dyadScale_pos _) (dyadScale_pos _)))

end SevenEighths.InverseMoment

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.SecondCellParameters
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseSecondSourceBlocks InverseInitialArithmetic
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

theorem second_cell_scale_rpow (Z:ℝ) (d:BlockIndex) (i:Fin 4) (hZ:1<Z):
    Z^(secondCellExponent Z d i)=scales d i :=
  Real.rpow_logb (by linarith) (ne_of_gt hZ) (dyadScale_pos _)

theorem second_cell_formal_column (Z r A B t:ℝ) (d:BlockIndex) (hZ:1<Z):
    secondCellColumnExponent Z (Z^(r-A-B-t)) d=
      secondFormalColumn r A B t (secondCellExponent Z d 0) (secondCellExponent Z d 2) := by
  have hz:0<Z:=zero_lt_one.trans hZ
  apply (Real.rpow_right_inj hz (ne_of_gt hZ)).mp
  rw [second_cell_column_scale Z _ d hZ (Real.rpow_pos_of_pos hz _)]
  rw [←second_cell_scale_rpow Z d 0 hZ,←second_cell_scale_rpow Z d 2 hZ,
    ←Real.rpow_add hz,←Real.rpow_sub hz]
  congr 1
  unfold secondFormalColumn
  ring

theorem actual_second_child_label_norm {ι:Type*} [DecidableEq ι]
    (p:ι→O) [∀i,(Ideal.span {p i}).IsMaximal]
    {Jo Jn:ℕ} (x:MarkedSecondSource ι Jo Jn) (u v:Oˣ):
    (Ideal.absNorm (actualSecondChild p u v x).2.1:ℝ)=
      ‖eisEmbedding (jLabel p x.cube.support
        (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2*
      primeProductNorm p x.firstCommon*primeProductNorm p x.second.divisor*
      primeProductNorm p x.second.overlap := by
  have hn(S:Finset ι):(Ideal.absNorm (sourceIdeal p S):ℝ)=primeProductNorm p S:=by
    simpa only [sourceIdeal,primeProductNorm,map_prod] using
      (eisEmbedding_norm_sq_eq_absNorm_span (∏i∈S,p i)).symm
  change (Ideal.absNorm (Ideal.span {jLabel p x.cube.support
      (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit} *
      sourceIdeal p x.firstCommon * sourceIdeal p x.second.divisor * sourceIdeal p x.second.overlap):ℝ)=_
  simp only [map_mul,Nat.cast_mul,hn,←eisEmbedding_norm_sq_eq_absNorm_span]

theorem actual_cell_child_label_bound {ι:Type*} [DecidableEq ι]
    (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    {Jo Jn:ℕ} (source:Finset (MarkedSecondSource ι Jo Jn))
    (hk:∀x∈source,x.second.frequency≠0) (d:BlockIndex)
    (x:MarkedSecondSource ι Jo Jn) (hx:x∈cell p source d) (u v:Oˣ):
    (Ideal.absNorm (actualSecondChild p u v x).2.1:ℝ)≤
      4*‖eisEmbedding (jLabel p x.cube.support
        (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2*
      primeProductNorm p x.firstCommon*scales d 1*scales d 2 := by
  have hE:= (cell_ratios p hp source hk d x hx 1).2.le
  have hV:= (cell_ratios p hp source hk d x hx 2).2.le
  have he:primeProductNorm p x.second.divisor≤2*scales d 1:=
    (div_le_iff₀ (dyadScale_pos _)).mp hE
  have hv:primeProductNorm p x.second.overlap≤2*scales d 2:=
    (div_le_iff₀ (dyadScale_pos _)).mp hV
  rw [actual_second_child_label_norm]
  calc
    _ ≤ ‖eisEmbedding (jLabel p x.cube.support
        (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2*
      primeProductNorm p x.firstCommon*(2*scales d 1)*(2*scales d 2) := by
      have hc0 := (primeProductNorm_pos p hp x.firstCommon).le
      have hv0 := (primeProductNorm_pos p hp x.second.overlap).le
      have hs0 := (dyadScale_pos (d 1)).le
      gcongr
    _ = _ := by ring

theorem actual_cell_child_label_power {ι:Type*} [DecidableEq ι]
    (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    {Jo Jn:ℕ} (source:Finset (MarkedSecondSource ι Jo Jn))
    (hk:∀x∈source,x.second.frequency≠0) (d:BlockIndex)
    (x:MarkedSecondSource ι Jo Jn) (hx:x∈cell p source d) (u v:Oˣ)
    (Z B j eta:ℝ) (hZ:1<Z) (hbin:2≤Z^eta)
    (hC:primeProductNorm p x.firstCommon≤Z^(B+eta))
    (hJ:‖eisEmbedding (jLabel p x.cube.support
        (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2≤Z^(j+eta)) :
    (Ideal.absNorm (actualSecondChild p u v x).2.1:ℝ)≤
      Z^(secondFormalLabel B (secondCellExponent Z d 1) (secondCellExponent Z d 2) j+4*eta) := by
  have hz:0<Z:=zero_lt_one.trans hZ
  have hfour:(4:ℝ)≤Z^(2*eta):=by
    have hh:=mul_le_mul hbin hbin (by norm_num) (Real.rpow_nonneg hz.le _)
    norm_num only [←Real.rpow_add hz,show eta+eta=2*eta by ring] at hh
    exact hh
  apply (actual_cell_child_label_bound p hp source hk d x hx u v).trans
  calc
    _≤Z^(2*eta)*Z^(j+eta)*Z^(B+eta)*scales d 1*scales d 2:=by
      have hc0:0≤primeProductNorm p x.firstCommon:=(primeProductNorm_pos p hp _).le
      have hs1:0≤ scales d 1:=(dyadScale_pos _).le
      have hs2:0≤ scales d 2:=(dyadScale_pos _).le
      gcongr
    _= _:=by
      rw [←second_cell_scale_rpow Z d 1 hZ,←second_cell_scale_rpow Z d 2 hZ,
        ←Real.rpow_add hz,←Real.rpow_add hz,←Real.rpow_add hz,←Real.rpow_add hz]
      congr 1
      unfold secondFormalLabel
      ring

end SevenEighths.InverseMoment

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.SecondAdmissible
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open InverseInitialArithmetic (sourceIdeal sourceIdeal_gen)
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι] (p : ι → Eis)
  (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]

include hp in
theorem actual_second_inherited_puncture_ne_zero
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) (ht : x.quotient ≠ 0)
    (u v : Eisˣ) (m : Eis) (hm : m ≠ 0) :
    actualSecondInheritedPuncture m (actualSecondChild p u v x).1 ≠ 0 := by
  change ((m*ConcretePrimeRowBridge.idealGenerator x.quotient)*
    primaryGenerator (Ideal.span {b0Label p x.cube.support
      (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit}))*
    primaryGenerator (sourceIdeal p (x.second.sourceCommon\x.second.divisor)) ≠ 0
  rw [show primaryGenerator (Ideal.span {b0Label p x.cube.support
      (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit}) =
      b0Label p x.cube.support (fun i => x.cube.leftExponent i+x.cube.rightExponent i)
        x.cube.leftBit x.cube.rightBit from primaryGenerator_primeProduct p hp hpr _ _,
    sourceIdeal_gen p hp hpr]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hm (ConcretePrimeRowBridge.idealGenerator_ne_zero _ ht))
    (primeProduct_ne_zero p hp _ _)) (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i))

lemma radicalGenerator_ne_zero (a : Eis) (ha : a ≠ 0) :
    ConcretePrimeRowBridge.idealGenerator (Ideal.span {a}).radical ≠ 0 := by
  apply ConcretePrimeRowBridge.idealGenerator_ne_zero
  intro hz
  apply Ideal.span_singleton_eq_bot.not.mpr ha
  apply le_antisymm _ bot_le
  exact (Ideal.le_radical : (Ideal.span {a} : Ideal Eis) ≤ (Ideal.span {a}).radical).trans (le_of_eq hz)

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.SecondSharpPuncture
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open InverseInitialArithmetic (sourceIdeal sourceIdeal_gen sourceIdeal_ne_zero)
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι] (p : ι → Eis) (hp : ∀ i, p i ≠ 0)
  [∀ i, (Ideal.span {p i}).IsMaximal]

include hp in

theorem actual_second_radical_puncture_q0_norm
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (hE : x.second.divisor ⊆ x.second.sourceCommon) (u v : Eisˣ) (m : Eis) (hm : m ≠ 0) :
    ‖ConcreteTraceCRT.eisEmbedding (actualSecondRadicalPuncture m (actualSecondChild p u v x).1)‖^2 ≤
      (Ideal.absNorm (Ideal.span {m} : Ideal Eis).radical : ℝ) *
        (Ideal.absNorm (actualSecondChild p u v x).1.q0 : ℝ) * primeProductNorm p (x.second.sourceCommon\x.second.divisor) := by
  have hspan : Ideal.span {actualSecondPuncture m (actualSecondChild p u v x).1} =
      (Ideal.span {m} : Ideal Eis) *
      Ideal.span {b0Label p x.cube.support (fun i => x.cube.leftExponent i+x.cube.rightExponent i)
        x.cube.leftBit x.cube.rightBit} * sourceIdeal p (x.second.sourceCommon\x.second.divisor) := by
    rw [←actual_second_puncture_span p hp hpr x hE u v m]
    simp only [←Ideal.span_singleton_mul_span_singleton,secondExpansionQuotient_of_subset p x.second hE,
      secondMaskQuotient_span,sourceIdeal,FiniteGaussPhase.span_finset_prod]
  rw [eisEmbedding_norm_sq_eq_absNorm_span]
  simp only [actualSecondRadicalPuncture,ConcretePrimeRowBridge.span_idealGenerator,hspan]
  have hn (S : Finset ι) : (Ideal.absNorm (sourceIdeal p S) : ℝ)=primeProductNorm p S := by
    simpa only [sourceIdeal,primeProductNorm,map_prod] using
      (eisEmbedding_norm_sq_eq_absNorm_span (∏ i ∈ S,p i)).symm
  rw [←hn (x.second.sourceCommon\x.second.divisor)]
  exact radical_product_norm_le _ _ _ _ (Ideal.span_singleton_eq_bot.not.mpr hm)
    (Ideal.span_singleton_eq_bot.not.mpr (primeProduct_ne_zero p hp _ _))
    (sourceIdeal_ne_zero p hp _) Ideal.le_radical

include hp in

theorem actual_second_inherited_puncture_q0_norm
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (hE : x.second.divisor ⊆ x.second.sourceCommon) (ht : x.quotient ≠ 0)
    (u v : Eisˣ) (m : Eis) (hm : m ≠ 0) :
    ‖ConcreteTraceCRT.eisEmbedding (actualSecondInheritedRadicalPuncture m (actualSecondChild p u v x).1)‖^2 ≤
      (Ideal.absNorm (Ideal.span {m} : Ideal Eis).radical : ℝ) * Ideal.absNorm x.quotient *
        (Ideal.absNorm (actualSecondChild p u v x).1.q0 : ℝ) * primeProductNorm p (x.second.sourceCommon\x.second.divisor) := by
  have hm' := mul_ne_zero hm (ConcretePrimeRowBridge.idealGenerator_ne_zero x.quotient ht)
  have hb := actual_second_radical_puncture_q0_norm p hp hpr x hE u v
    (m*ConcretePrimeRowBridge.idealGenerator x.quotient) hm'
  change ‖ConcreteTraceCRT.eisEmbedding (actualSecondRadicalPuncture
    (m*ConcretePrimeRowBridge.idealGenerator x.quotient) (actualSecondChild p u v x).1)‖^2 ≤ _
  apply hb.trans
  have ho : (Ideal.absNorm (Ideal.span {m*ConcretePrimeRowBridge.idealGenerator x.quotient}).radical : ℝ) ≤
      (Ideal.absNorm (Ideal.span {m} : Ideal Eis).radical : ℝ)*Ideal.absNorm x.quotient := by
    rw [←Ideal.span_singleton_mul_span_singleton,ConcretePrimeRowBridge.span_idealGenerator]
    simpa only [mul_one,map_one,Nat.cast_one] using radical_product_norm_le (Ideal.span {m}) 1 1 x.quotient
      (Ideal.span_singleton_eq_bot.not.mpr hm) one_ne_zero ht Ideal.le_radical
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right ho (Nat.cast_nonneg _)) (primeProductNorm_pos p hp _).le

include hp in

theorem actual_second_q0_cube_bound
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) (u v : Eisˣ)
    (B : ℝ) (hB : 0 ≤ B)
    (h1 : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (h2 : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B) :
    (Ideal.absNorm (actualSecondChild p u v x).1.q0 : ℝ) ≤ B := by
  change (Ideal.absNorm (Ideal.span {b0Label p x.cube.support
    (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit}) : ℝ) ≤ B
  rw [←eisEmbedding_norm_sq_eq_absNorm_span]
  exact (cube_label_norm_bounds p hp _ _ _ _ _ x.cube.support_pos B hB h1 h2).2.1

include hp in
theorem actual_second_puncture_power_from_cubes
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (hE : x.second.divisor ⊆ x.second.sourceCommon) (ht : x.quotient ≠ 0)
    (u v : Eisˣ) (m : Eis) (hm : m ≠ 0)
    (Z Q ell t g theta eta : ℝ) (hZ : 0 < Z)
    (hQ : (Ideal.absNorm (Ideal.span {m} : Ideal Eis).radical : ℝ) ≤ Z^Q)
    (h1 : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ Z^(ell+eta))
    (h2 : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ Z^(ell+eta))
    (hT : (Ideal.absNorm x.quotient : ℝ) ≤ Z^(t+eta))
    (hG : primeProductNorm p x.second.sourceCommon ≤ Z^(g+eta))
    (hD : Z^(theta-eta) ≤ primeProductNorm p x.second.divisor) :
    ‖eisEmbedding (actualSecondInheritedRadicalPuncture m (actualSecondChild p u v x).1)‖^2 ≤
      Z^(Q+ell+t+g-theta+4*eta) := by
  have hr := second_residual_norm_power_bound p hp _ _ hE Z g theta eta hZ hG hD
  have hb := actual_second_q0_cube_bound p hp x u v _ (Real.rpow_pos_of_pos hZ _).le h1 h2
  apply (actual_second_inherited_puncture_q0_norm p hp hpr x hE ht u v m hm).trans
  calc
    _ ≤ (Z^Q*Z^(t+eta))*Z^(ell+eta)*Z^(g-theta+2*eta) := by
      have hr0 := (primeProductNorm_pos p hp (x.second.sourceCommon\x.second.divisor)).le
      gcongr
    _ = Z^((Q+(t+eta))+(ell+eta)+(g-theta+2*eta)) := by
      rw [←Real.rpow_add hZ,←Real.rpow_add hZ,←Real.rpow_add hZ]
    _ = _ := by congr 1; ring

include hp in
theorem actual_second_puncture_width_from_cubes
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (hE : x.second.divisor ⊆ x.second.sourceCommon) (ht : x.quotient ≠ 0)
    (u v : Eisˣ) (m : Eis) (hm : m ≠ 0)
    (Z Q ell t g theta eta : ℝ) (hZ : 1 < Z)
    (hQ : (Ideal.absNorm (Ideal.span {m} : Ideal Eis).radical : ℝ) ≤ Z^Q)
    (h1 : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ Z^(ell+eta))
    (h2 : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ Z^(ell+eta))
    (hT : (Ideal.absNorm x.quotient : ℝ) ≤ Z^(t+eta))
    (hG : primeProductNorm p x.second.sourceCommon ≤ Z^(g+eta))
    (hD : Z^(theta-eta) ≤ primeProductNorm p x.second.divisor) :
    actualSecondPunctureWidth Z m (actualSecondChild p u v x).1 ≤ Q+ell+t+g-theta+4*eta := by
  have hp0 := actual_second_inherited_puncture_ne_zero p hp hpr x ht u v m hm
  have hr0 := radicalGenerator_ne_zero _ hp0
  change actualSecondInheritedRadicalPuncture m (actualSecondChild p u v x).1 ≠ 0 at hr0
  apply (Real.logb_le_iff_le_rpow hZ (sq_pos_of_pos
    (norm_pos_iff.mpr (ConcreteTraceCRT.eisEmbedding_ne_zero hr0)))).mpr
  exact actual_second_puncture_power_from_cubes p hp hpr x hE ht u v m hm
    Z Q ell t g theta eta (zero_lt_one.trans hZ) hQ h1 h2 hT hG hD

include hp in

theorem actual_second_child_margins_from_cubes
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (hE : x.second.divisor ⊆ x.second.sourceCommon) (ht0 : x.quotient ≠ 0)
    (u v : Eisˣ) (m : Eis) (hm : m ≠ 0)
    (Z F M Q z c ell A t g theta V j delta eta : ℝ) (hZ : 1 < Z)
    (hparent : CanonicalMargins F M Q z c)
    (hA : 0 ≤ A) (ht : 0 ≤ t) (hV : 0 ≤ V) (hj : 0 ≤ j) (hdelta : 0 ≤ delta) (heta : 0 ≤ eta)
    (hQ : (Ideal.absNorm (Ideal.span {m} : Ideal Eis).radical : ℝ) ≤ Z^Q)
    (h1 : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ Z^(ell+eta))
    (h2 : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ Z^(ell+eta))
    (hT : (Ideal.absNorm x.quotient : ℝ) ≤ Z^(t+eta))
    (hG : primeProductNorm p x.second.sourceCommon ≤ Z^(g+eta))
    (hD : Z^(theta-eta) ≤ primeProductNorm p x.second.divisor) :
    CanonicalMargins (childF F ell A t g theta V j delta)
      (childM M ell A t g theta V j eta)
      (actualSecondPunctureWidth Z m (actualSecondChild p u v x).1) z (c-7*eta) := by
  apply child_margins hparent hA ht hV hj
    (actual_second_common_center p hp x hE Z g theta eta hZ hG hD) hdelta heta
  have hwidth := actual_second_puncture_width_from_cubes p hp hpr x hE ht0 u v m hm
    Z Q ell t g theta eta hZ hQ h1 h2 hT hG hD
  unfold decrease
  linarith

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.ActualChildState
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondSourceBlocks
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

lemma actual_cell_total_transition (Z r ell V A B t j eta : ℝ) (d : BlockIndex) (hZ : 1<Z) :
    actualCellTotalExponent Z (Z^(r-A-B-t)) B j eta d=
      childF (r+3*ell+V) ell A t (secondCellExponent Z d 0) (secondCellExponent Z d 1) V j
        (actualCellClipping Z (Z^(r-A-B-t)) d+4*eta) := by
  unfold actualCellTotalExponent actualCellLabelExponent actualCellClipping
  rw [second_cell_formal_column Z r A B t d hZ]
  unfold childF decrease secondFormalColumn secondFormalLabel
  ring

variable {ι : Type*} [DecidableEq ι] (p : ι→O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
include hp

omit [DecidableEq ι] in
theorem actual_cell_norm_centers {Jo Jn : ℕ}
    (source : Finset (MarkedSecondSource ι Jo Jn)) (hk : ∀x∈source,x.second.frequency≠0)
    (d : BlockIndex) (x : MarkedSecondSource ι Jo Jn) (hx : x∈cell p source d)
    (Z eta : ℝ) (hZ : 1<Z) (heta : 0≤eta) (hbin : 2≤Z^eta) (i : Fin 4) :
    Z^(secondCellExponent Z d i-eta)≤outerNorms p x i ∧
      outerNorms p x i≤Z^(secondCellExponent Z d i+eta) := by
  have hr := cell_ratios p hp source hk d x hx i
  have hz : 0<Z := zero_lt_one.trans hZ
  have hlo := (le_div_iff₀ (dyadScale_pos (d i))).mp hr.1
  have hhi := (div_le_iff₀ (dyadScale_pos (d i))).mp hr.2.le
  constructor
  · apply (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith : secondCellExponent Z d i-eta≤ secondCellExponent Z d i)).trans
    simpa only [second_cell_scale_rpow Z d i hZ,one_mul,scales] using hlo
  · calc
      _ ≤ 2*scales d i := hhi
      _ ≤ Z^eta*scales d i := mul_le_mul_of_nonneg_right hbin (dyadScale_pos _).le
      _ = _ := by rw [←second_cell_scale_rpow Z d i hZ,←Real.rpow_add hz];congr 1;ring

theorem actual_cell_child_margins
    (hpr : ∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (hs : ActualSecondSourceConditions p source) (hk : ∀x∈source,x.second.frequency≠0)
    (d : BlockIndex) (x : MarkedSecondSource ι Jo Jn) (hx : x∈cell p source d)
    (u v : Oˣ) (m : O) (hm : m≠0)
    (Z r ell V M Q z c A B t j eta : ℝ) (hZ : 1<Z)
    (hparent : CanonicalMargins (r+3*ell+V) M Q z c)
    (hA : 0≤A) (ht : 0≤t) (hV : 0≤V) (hj : 0≤j) (heta : 0≤eta) (hbin : 2≤Z^eta)
    (hQ : (Ideal.absNorm (Ideal.span {m}:Ideal O).radical:ℝ)≤Z^Q)
    (h1 : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Z^(ell+eta))
    (h2 : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Z^(ell+eta))
    (hT : (Ideal.absNorm x.quotient:ℝ)≤Z^(t+eta)) :
    CanonicalMargins (actualCellTotalExponent Z (Z^(r-A-B-t)) B j eta d)
      (childM M ell A t (secondCellExponent Z d 0) (secondCellExponent Z d 1) V j eta)
      (actualSecondPunctureWidth Z m (actualSecondChild p u v x).1) z (c-7*eta) := by
  have hxs := cell_subset p source d hx
  have hG := (actual_cell_norm_centers p hp source hk d x hx Z eta hZ heta hbin 0).2
  have hD := (actual_cell_norm_centers p hp source hk d x hx Z eta hZ heta hbin 1).1
  rw [actual_cell_total_transition Z r ell V A B t j eta d hZ]
  apply actual_second_child_margins_from_cubes p hp hpr x (hs.second_divisor x hxs)
    (hs.quotient_nonzero x hxs) u v m hm Z (r+3*ell+V) M Q z c ell A t
    (secondCellExponent Z d 0) (secondCellExponent Z d 1) V j _ eta hZ hparent hA ht hV hj
    (by unfold actualCellClipping;have := le_max_right 0 (secondCellColumnExponent Z (Z^(r-A-B-t)) d);linarith)
    heta hQ h1 h2 hT
  · simpa only [outerNorms,Matrix.cons_val_zero] using hG
  · simpa only [outerNorms,Matrix.cons_val_one,Matrix.cons_val_zero] using hD

end SevenEighths.InverseMoment
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.ActualChildStateLabels
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondSourceBlocks
open InverseSecondFibers CompletedGauss
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι] (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]

lemma actual_cell_labels_cover {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (d : BlockIndex) (x : MarkedSecondSource ι Jo Jn) (hx : x∈cell p source d) :
    (actualSecondChild p 1 1 x).2.1∈actualCellLabels p source d :=
  Finset.mem_image.mpr ⟨x,hx,rfl⟩

theorem actual_cell_labels_bound (hp : ∀i,p i≠0) {Jo Jn : ℕ}
    (source : Finset (MarkedSecondSource ι Jo Jn)) (hk : ∀x∈source,x.second.frequency≠0)
    (d : BlockIndex) (Z B j eta : ℝ) (hZ : 1<Z) (hbin : 2≤Z^eta)
    (hC : ∀x∈source,primeProductNorm p x.firstCommon≤Z^(B+eta))
    (hJ : ∀x∈source,‖eisEmbedding (jLabel p x.cube.support
      (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2≤Z^(j+eta)) :
    ∀I∈actualCellLabels p source d,(Ideal.absNorm I:ℝ)≤Z^(actualCellLabelExponent Z B j eta d) := by
  intro I hI
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hI
  exact actual_cell_child_label_power p hp source hk d x hx 1 1 Z B j eta hZ hbin
    (hC x (cell_subset p source d hx)) (hJ x (cell_subset p source d hx))

theorem actual_cell_squarefree_labels (hp : ∀i,p i≠0) {Jo Jn : ℕ}
    (source : Finset (MarkedSecondSource ι Jo Jn)) (hk : ∀x∈source,x.second.frequency≠0)
    (d : BlockIndex) (Z B j eta : ℝ) (hZ : 1<Z) (hbin : 2≤Z^eta)
    (hC : ∀x∈source,primeProductNorm p x.firstCommon≤Z^(B+eta))
    (hJ : ∀x∈source,‖eisEmbedding (jLabel p x.cube.support
      (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2≤Z^(j+eta)) :
    ∀I∈(actualCellLabels p source d).filter Squarefree,
      Squarefree I ∧ I≠0 ∧ (Ideal.absNorm I:ℝ)≤Z^(actualCellLabelExponent Z B j eta d) := by
  intro I hI
  have hi := Finset.mem_filter.mp hI
  exact ⟨hi.2,hi.2.ne_zero,actual_cell_labels_bound p hp source hk d Z B j eta hZ hbin hC hJ I hi.1⟩

end SevenEighths.InverseMoment
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.ActualChildStateSupport
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondSourceBlocks
open InverseSecondFibers CompletedGauss
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι] (p : ι→O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
include hp

theorem actual_cell_triple_puncture_nonzero
    (hpr : ∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (hs : ActualSecondSourceConditions p source) (d : BlockIndex) (m : O) (hm : m≠0)
    (γ : OuterTriple) (hγ : γ∈actualSecondTriples p 1 1 (cell p source d)) :
    actualSecondInheritedRadicalPuncture m γ≠0 := by
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hγ
  exact radicalGenerator_ne_zero _ (actual_second_inherited_puncture_ne_zero p hp hpr x
    (hs.quotient_nonzero x (cell_subset p source d hx)) 1 1 m hm)

end SevenEighths.InverseMoment
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.ActualChildStateTriples
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondSourceBlocks
open InverseSecondFibers CompletedGauss
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι] (p : ι→O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
include hp

theorem actual_cell_triple_margins
    (hpr : ∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (hs : ActualSecondSourceConditions p source) (hk : ∀x∈source,x.second.frequency≠0)
    (d : BlockIndex) (m : O) (hm : m≠0)
    (Z r ell V M Q z c A B t j eta : ℝ) (hZ : 1<Z)
    (hparent : CanonicalMargins (r+3*ell+V) M Q z c)
    (hA : 0≤A) (ht : 0≤t) (hV : 0≤V) (hj : 0≤j) (heta : 0≤eta) (hbin : 2≤Z^eta)
    (hQ : (Ideal.absNorm (Ideal.span {m}:Ideal O).radical:ℝ)≤Z^Q)
    (h1 : ∀x∈source,‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Z^(ell+eta))
    (h2 : ∀x∈source,‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Z^(ell+eta))
    (hT : ∀x∈source,(Ideal.absNorm x.quotient:ℝ)≤Z^(t+eta))
    (γ : OuterTriple) (hγ : γ∈actualSecondTriples p 1 1 (cell p source d)) :
    actualSecondInheritedRadicalPuncture m γ≠0 ∧
    0≤actualSecondPunctureWidth Z m γ ∧
    ‖eisEmbedding (actualSecondInheritedRadicalPuncture m γ)‖^2=Z^(actualSecondPunctureWidth Z m γ) ∧
    CanonicalMargins (actualCellTotalExponent Z (Z^(r-A-B-t)) B j eta d)
      (childM M ell A t (secondCellExponent Z d 0) (secondCellExponent Z d 1) V j eta)
      (actualSecondPunctureWidth Z m γ) z (c-7*eta) := by
  have hn := actual_cell_triple_puncture_nonzero p hp hpr source hs d m hm γ hγ
  refine ⟨hn,?_,?_,?_⟩
  · exact Real.logb_nonneg hZ (EisensteinSchwartzPoisson.one_le_eisenstein_norm_sq _ hn)
  · exact (Real.rpow_logb (zero_lt_one.trans hZ) (ne_of_gt hZ)
      (sq_pos_of_pos (norm_pos_iff.mpr (ConcreteTraceCRT.eisEmbedding_ne_zero hn)))).symm
  · obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hγ
    have hxs := cell_subset p source d hx
    exact actual_cell_child_margins p hp hpr source hs hk d x hx 1 1 m hm
      Z r ell V M Q z c A B t j eta hZ hparent hA ht hV hj heta hbin hQ
      (h1 x hxs) (h2 x hxs) (hT x hxs)

end SevenEighths.InverseMoment
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.FirstGlobalSourceIndex
namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]

lemma mem_firstOriginalOuter (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : FirstOriginalOuter ι) :
    k∈firstOriginalOuter pool Q ↔ k.1∈reopenedCubeFamily Q ∧ k.2.1∈(pool\k.1.support).powerset ∧
      k.2.2∈(k.2.1∪cubePrincipalSupport k.1.support k.1.leftExponent k.1.rightExponent k.1.leftBit k.1.rightBit).powerset := by
  simp [firstOriginalOuter]

variable (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.WholePriorityRetainedSource
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseWholePriorityRetainedSource
open ActualEisensteinCubic SecondPassArithmetic FirstPassCubeLabels FirstCauchyArithmetic
open InverseMoment InverseInitialArithmetic InverseFirstPriorityParents InversePrioritySecondSource
open InverseMomentWholePriorityParents InverseMomentWholePriorityPhysical
open InverseWholePriorityValidSource RayFourExpansion InversePrincipalEnergy InverseSecondPrincipalCaller
local notation "O" => ActualEisensteinCubic.O
variable {ι σ κ : Type*} [DecidableEq ι] [DecidableEq σ] [DecidableEq κ]
variable {Jo : ℕ} (p : ι→O) [∀ i,(Ideal.span {p i}).IsMaximal]

omit [∀ i,(Ideal.span {p i}).IsMaximal] in
theorem mem_unifiedSource (pool : Finset ι) (parents : Finset (SecondParentSource ι Jo))
    (R : SecondParentSource ι Jo→Finset ι→Finset ι→ℝ) (x : MarkedSecondSource ι Jo 0) :
    x∈unifiedSource p pool parents R ↔ secondParentOf x∈parents ∧
      x.second.sourceCommon⊆pool ∧ x.second.divisor⊆x.second.sourceCommon ∧
      x.second.overlap⊆pool ∧ x.second.frequency∈nonzeroChildFrequencyBall
        (actualSecondMultiplier p x) (R (secondParentOf x) x.second.sourceCommon x.second.divisor) := by
  rw [unifiedSource,mem_attachedSecondFamily,mem_secondExpansionPool]
  rfl

omit [∀ i,(Ideal.span {p i}).IsMaximal] in
theorem unified_frequency_ne_zero (pool : Finset ι) (parents : Finset (SecondParentSource ι Jo))
    (R : SecondParentSource ι Jo→Finset ι→Finset ι→ℝ) (x : MarkedSecondSource ι Jo 0)
    (hx : x∈unifiedSource p pool parents R) : x.second.frequency≠0 :=
  (Finset.mem_erase.mp ((mem_unifiedSource p pool parents R x).mp hx).2.2.2.2).1

theorem unified_conditions (hp : ∀ i,p i≠0)
    (extra : CubeCoordinates ι→Finset ι) (source : Finset (Source ι Jo))
    (hs : ∀ x∈source,SourceValid p x) (he : ∀ x∈source,extra x.cube⊆x.cube.support)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (pool : Finset ι)
    (R : SecondParentSource ι (Jo+(J.card+J.card))→Finset ι→Finset ι→ℝ) :
    ActualSecondSourceConditions p (unifiedSource p pool
      (wholeAssignedParents p (fun x=>extra x.cube) source negative J lists) R) := by
  apply whole_assigned_family_conditions p hp (fun x=>extra x.cube) source hs he negative J lists
  intro y hy x hx
  exact ((mem_secondExpansionPool _ _ x).mp hx).2.1

variable (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

end SevenEighths.InverseWholePriorityRetainedSource

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.FirstGlobalParents
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.InverseFirstGlobalParents
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open FirstCauchyArithmetic RayFourExpansion InverseMoment
open InverseFirstPriorityParents InverseMomentWholePriorityParents
open InverseWholePriorityValidSource InversePrioritySecondSource
open InverseInitialArithmetic (sourceIdeal)
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]

theorem mem_originalParentSource (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (selector : FirstOriginalOuter ι→Finset ι→ℂ) (x : Source ι 0) :
    x∈originalParentSource pool Q selector ↔
      ∃k∈firstOriginalOuter pool Q,∃D∈pool.powerset,
        selector k D≠0 ∧ fillFirstQuotient (ofOriginal k) D=x := by
  simp only [originalParentSource,globalParentSource,Finset.mem_biUnion,
    originalOuterSource,Finset.mem_image,Finset.mem_filter]
  constructor
  · rintro ⟨y,⟨k,hk,rfl⟩,D,⟨hD,hs⟩,he⟩
    exact ⟨k,hk,D,hD,by simpa using hs,he⟩
  · rintro ⟨k,hk,D,hD,hs,he⟩
    exact ⟨ofOriginal k,⟨k,hk,rfl⟩,D,⟨hD,by simpa using hs⟩,he⟩

theorem original_fill_valid (p : ι→O) (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (k : FirstOriginalOuter ι) (hk : k∈firstOriginalOuter pool Q) (D : Finset ι) :
    SourceValid p (fillFirstQuotient (ofOriginal k) D) := by
  obtain ⟨hb,hC,hE⟩:=(mem_firstOriginalOuter pool Q k).mp hk
  refine ⟨reopenedCubeFamily_admissible Q k.1 hb,?_,?_,?_⟩
  · exact Finset.disjoint_left.mpr (fun i hi hiB=>
      (Finset.mem_sdiff.mp (Finset.mem_powerset.mp hC hi)).2 hiB)
  · exact (Finset.mem_powerset.mp hE).trans
      (Finset.union_subset_union_right (Finset.filter_subset _ _))
  · exact fun i=>Fin.elim0 i

variable (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]

variable (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

end SevenEighths.InverseFirstGlobalParents

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.FirstGlobalCaps
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.InverseFirstGlobalCaps
open InverseMoment InverseFirstGlobalParents InverseFirstPriorityParents
open InverseMomentWholePriorityParents InverseMomentFirstChildWindows
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic FirstCauchyArithmetic
open InverseSecondSourceBlocks (dyadIndex dyadScale dyadScale_pos dyadIndex_bounds)
open ConcreteTraceCRT (eisEmbedding)
open InverseInitialArithmetic (sourceIdeal)
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]

theorem mem_parentCell (p : ι→O) (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (selector : FirstOriginalOuter ι→Finset ι→ℂ) (k : SourceIndex) (l : ℕ)
    (x : Source ι 0) : x∈parentCell p pool Q selector k l ↔
    ∃o∈outerCell p pool Q k,∃D∈pool.powerset,
      commonSelector p (selector o) l D≠0 ∧ fillFirstQuotient (ofOriginal o) D=x := by
  simp only [parentCell,outerCell,Finset.mem_filter,mem_originalParentSource]
  constructor
  · rintro ⟨⟨o,ho,D,hD,hs,rfl⟩,hg⟩
    exact ⟨o,⟨ho,by simpa using hg⟩,D,hD,hs,rfl⟩
  · rintro ⟨o,⟨ho,hg⟩,D,hD,hs,rfl⟩
    exact ⟨⟨o,ho,D,hD,hs,rfl⟩,by simpa using hg⟩

variable (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]

include hp in
omit [∀i,(Ideal.span {p i}).IsMaximal] in
lemma outerNorms_ge_one (x : FirstOriginalOuter ι) : ∀i,1≤outerNorms p x i := by
  intro i
  fin_cases i
  · exact EisensteinSchwartzPoisson.one_le_eisenstein_norm_sq _ (primeProduct_ne_zero p hp _ _)
  · exact EisensteinSchwartzPoisson.one_le_eisenstein_norm_sq _ (primeProduct_ne_zero p hp _ _)
  · exact primeProductNorm_ge_one p hp _
  · change 1≤‖eisEmbedding (primeSubsetGenerator (fun i=>Ideal.span {p i}) x.2.2)‖^2
    rw [primeSubsetGenerator_norm_eq_productNorm]
    exact primeProductNorm_ge_one p hp _
  · exact primeProductNorm_ge_one p hp _

include hp in
omit [∀i,(Ideal.span {p i}).IsMaximal] in
lemma outerGate_dyads (k : SourceIndex) (x : FirstOriginalOuter ι) (hx : outerGate p k x) :
    ∀i : Fin 5,dyadScale (k i.castSucc)≤outerNorms p x i ∧
      outerNorms p x i≤2*dyadScale (k i.castSucc) := by
  intro i
  have h:=dyadIndex_bounds _ (outerNorms_ge_one p hp x i)
  rw [hx i] at h
  exact ⟨h.1,h.2.le⟩

include hp in
omit [∀i,(Ideal.span {p i}).IsMaximal] in
lemma live_common_dyads (selector : Finset ι→ℂ) (l : ℕ) (D : Finset ι)
    (hlive : commonSelector p selector l D≠0) :
    dyadScale l≤primeProductNorm p D ∧ primeProductNorm p D≤2*dyadScale l := by
  have he : dyadIndex (primeProductNorm p D)=l := by
    by_contra h
    exact hlive (by simp [commonSelector,h])
  have h:=dyadIndex_bounds _ (primeProductNorm_ge_one p hp D)
  rw [he] at h
  exact ⟨h.1,h.2.le⟩

omit [DecidableEq ι] [∀i,(Ideal.span {p i}).IsMaximal] in
lemma sourceIdeal_norm (D : Finset ι) : (Ideal.absNorm (sourceIdeal p D):ℝ)=primeProductNorm p D := by
  simp only [sourceIdeal,←eisEmbedding_norm_sq_eq_absNorm_span,primeProductNorm]

omit [∀i,(Ideal.span {p i}).IsMaximal] in

theorem parentCell_cube_bounds (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (selector : FirstOriginalOuter ι→Finset ι→ℂ) (k : SourceIndex) (l : ℕ)
    (Z ell eta : ℝ)
    (hQ : ∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta))
    (x : Source ι 0) (hx : x∈parentCell p pool Q selector k l) :
    ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Z^(ell+eta) ∧
    ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Z^(ell+eta) := by
  obtain ⟨o,ho,D,hD,hs,rfl⟩:=(mem_parentCell p pool Q selector k l x).mp hx
  exact reopenedCubeFamily_cube_norms p Q _ hQ o.1
    ((mem_firstOriginalOuter pool Q o).mp (Finset.mem_filter.mp ho).1).1

lemma rpow_dyadicExponent (Z : ℝ) (hZ : 1<Z) (n : ℕ) :
    Z^dyadicExponent Z n=dyadScale n :=
  Real.rpow_logb (by linarith) (by linarith) (dyadScale_pos n)

lemma dyad_power_bounds (Z eta q : ℝ) (hZ : 1<Z) (h2 : 2≤Z^eta) (n : ℕ)
    (hq : dyadScale n≤q ∧ q≤2*dyadScale n) :
    Z^dyadicExponent Z n≤q ∧ q≤Z^(dyadicExponent Z n+eta) := by
  rw [Real.rpow_add (by linarith),rpow_dyadicExponent Z hZ]
  refine ⟨hq.1,hq.2.trans ?_⟩
  nlinarith [dyadScale_pos n]

include hp in
omit [∀i,(Ideal.span {p i}).IsMaximal] in
theorem parentCell_norm_bounds (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (selector : FirstOriginalOuter ι→Finset ι→ℂ) (k : SourceIndex) (l : ℕ)
    (Z eta : ℝ) (hZ : 1<Z) (h2 : 2≤Z^eta)
    (x : Source ι 0) (hx : x∈parentCell p pool Q selector k l) :
    (∀i : Fin 5,Z^dyadicExponent Z (k i.castSucc)≤outerNorms p (toOriginal x) i ∧
      outerNorms p (toOriginal x) i≤Z^(dyadicExponent Z (k i.castSucc)+eta)) ∧
    (Ideal.absNorm (parent p x).quotient:ℝ)=primeProductNorm p x.quotientSupport ∧
    Z^dyadicExponent Z l≤(Ideal.absNorm (parent p x).quotient:ℝ) ∧
    (Ideal.absNorm (parent p x).quotient:ℝ)≤Z^(dyadicExponent Z l+eta) := by
  obtain ⟨o,ho,D,hD,hs,rfl⟩:=(mem_parentCell p pool Q selector k l x).mp hx
  have hg := outerGate_dyads p hp k o (Finset.mem_filter.mp ho).2
  have hd := live_common_dyads p hp (selector o) l D hs
  simp only [toOriginal_fill,toOriginal_ofOriginal]
  refine ⟨fun i=>dyad_power_bounds Z eta _ hZ h2 _ (hg i),sourceIdeal_norm p D,?_⟩
  change Z^dyadicExponent Z l≤(Ideal.absNorm (sourceIdeal p D):ℝ) ∧
    (Ideal.absNorm (sourceIdeal p D):ℝ)≤Z^(dyadicExponent Z l+eta)
  rw [sourceIdeal_norm]
  exact dyad_power_bounds Z eta _ hZ h2 l hd

include hp in
omit [∀i,(Ideal.span {p i}).IsMaximal] in
theorem parentCell_ideal_bounds (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (selector : FirstOriginalOuter ι→Finset ι→ℂ) (k : SourceIndex) (l : ℕ)
    (Z eta : ℝ) (hZ : 1<Z) (h2 : 2≤Z^eta)
    (x : Source ι 0) (hx : x∈parentCell p pool Q selector k l) :
    (Z^dyadicExponent Z (k 2)≤primeProductNorm p x.firstCommon ∧
      primeProductNorm p x.firstCommon≤Z^(dyadicExponent Z (k 2)+eta)) ∧
    (Z^dyadicExponent Z (k 3)≤(Ideal.absNorm (sourceIdeal p x.firstDivisor):ℝ) ∧
      (Ideal.absNorm (sourceIdeal p x.firstDivisor):ℝ)≤Z^(dyadicExponent Z (k 3)+eta)) ∧
    (Z^dyadicExponent Z (k 4)≤(Ideal.absNorm (sourceIdeal p (cubeActiveSupport x.cube.support
      (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)):ℝ) ∧
      (Ideal.absNorm (sourceIdeal p (cubeActiveSupport x.cube.support
        (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)):ℝ)
        ≤Z^(dyadicExponent Z (k 4)+eta)) := by
  have h:=(parentCell_norm_bounds p hp pool Q selector k l Z eta hZ h2 x hx).1
  refine ⟨h 2,?_,?_⟩
  · simpa [sourceIdeal_norm,outerNorms,toOriginal,primeSubsetGenerator_norm_eq_productNorm] using h 3
  · simpa [sourceIdeal_norm,outerNorms,toOriginal] using h 4

include hp in
omit [∀i,(Ideal.span {p i}).IsMaximal] in
theorem labelParentCell_bounds (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (selector : FirstOriginalOuter ι→Finset ι→ℂ) (k : SourceIndex) (l j : ℕ)
    (Z eta : ℝ) (hZ : 1<Z) (h2 : 2≤Z^eta)
    (x : Source ι 0) (hx : x∈labelParentCell p pool Q selector k l j) :
    x∈parentCell p pool Q selector k l ∧
    Z^dyadicExponent Z j≤jNorm p (toOriginal x) ∧
      jNorm p (toOriginal x)≤Z^(dyadicExponent Z j+eta) := by
  obtain ⟨hm,hj⟩:=Finset.mem_filter.mp hx
  have hn : 1≤jNorm p (toOriginal x) :=
    EisensteinSchwartzPoisson.one_le_eisenstein_norm_sq _ (primeProduct_ne_zero p hp _ _)
  have hd:=dyadIndex_bounds _ hn
  rw [hj] at hd
  exact ⟨hm,dyad_power_bounds Z eta _ hZ h2 j ⟨hd.1,hd.2.le⟩⟩

end SevenEighths.InverseFirstGlobalCaps

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.GlobalRetainedGates
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMomentGlobalRetainedGates
open InverseMoment InverseFirstPriorityParents InverseMomentWholePriorityParents
open InverseWholePriorityRetainedSource InversePrioritySecondSource InverseInitialArithmetic
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondSourceBlocks
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ] {Jo : ℕ}
variable (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]

lemma original_parent_witness
    (extra : CubeCoordinates ι→Finset ι) (original : Finset (Source ι Jo))
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (pool : Finset ι)
    (cutoff : Finset ι→Finset ι→ℝ)
    (x : MarkedSecondSource ι (Jo+(J.card+J.card)) 0)
    (hx : x∈retainedSource p extra original negative J lists pool cutoff) :
    ∃y∈original,forgetAppended (Jo:=Jo) (secondParentOf x)=parent p y := by
  have hp := ((mem_unifiedSource p pool _ (fun _=>cutoff) x).mp hx).1
  obtain ⟨y,hy,q,hq,he⟩ := (mem_wholeAssignedParents p (fun x=>extra x.cube) original negative J lists _).mp hp
  exact ⟨y,hy,by simpa only [forget_attach] using congrArg (forgetAppended (Jo:=Jo)) he.symm⟩

lemma original_coordinates
    (extra : CubeCoordinates ι→Finset ι) (original : Finset (Source ι Jo))
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (pool : Finset ι)
    (cutoff : Finset ι→Finset ι→ℝ)
    (x : MarkedSecondSource ι (Jo+(J.card+J.card)) 0)
    (hx : x∈retainedSource p extra original negative J lists pool cutoff) :
    ∃y∈original,x.cube=y.cube ∧ x.firstCommon=y.firstCommon ∧
      x.firstDivisor=y.firstDivisor ∧ x.quotient=sourceIdeal p y.quotientSupport ∧
      (∀i:Fin Jo,x.oldAssigned (Fin.castAdd (J.card+J.card) i)=y.oldAssigned i) := by
  obtain ⟨y,hy,he⟩ := original_parent_witness p extra original negative J lists pool cutoff x hx
  exact ⟨y,hy,congrArg SecondParentSource.cube he,congrArg SecondParentSource.firstCommon he,
    congrArg SecondParentSource.firstDivisor he,congrArg SecondParentSource.quotient he,
    fun i=>congrArg (fun z=>z.oldAssigned i) he⟩

lemma retained_conditions (hp : ∀i,p i≠0)
    (extra : CubeCoordinates ι→Finset ι) (original : Finset (Source ι Jo))
    (hvalid : ∀x∈original,SourceValid p x) (hextra : ∀x∈original,extra x.cube⊆x.cube.support)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (pool : Finset ι)
    (cutoff : Finset ι→Finset ι→ℝ) :
    ActualSecondSourceConditions p (retainedSource p extra original negative J lists pool cutoff) :=
  unified_conditions p hp extra original hvalid hextra negative J lists pool (fun _=>cutoff)

end SevenEighths.InverseMomentGlobalRetainedGates
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.GlobalRetainedGatesGeometry
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMomentGlobalRetainedGates
open InverseMoment InverseFirstPriorityParents InverseMomentWholePriorityParents
open InverseWholePriorityRetainedSource InversePrioritySecondSource InverseInitialArithmetic
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondSourceBlocks
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
variable (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]

omit hp [∀i,(Ideal.span {p i}).IsMaximal] in
omit [DecidableEq ι] in
lemma geometrySource_subset {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn)) (b X : ℝ) :
    geometrySource p source b X⊆source := Finset.filter_subset _ _

end SevenEighths.InverseMomentGlobalRetainedGates
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.GlobalRetainedGatesRadius
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMomentGlobalRetainedGates
open InverseMoment InverseFirstPriorityParents InverseMomentWholePriorityParents
open InverseWholePriorityRetainedSource InversePrioritySecondSource InverseInitialArithmetic
open InverseSecondUniformCutoff
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondSourceBlocks
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ] {Jo : ℕ}
variable (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]

lemma supported_subset (extra : CubeCoordinates ι→Finset ι) (original : Finset (Source ι Jo))
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (pool : Finset ι)
    (cutoff : Finset ι→Finset ι→ℝ) (b X : ℝ) :
    supportedRetainedSource p extra original negative J lists pool cutoff b X⊆
      retainedSource p extra original negative J lists pool cutoff := geometrySource_subset p _ b X

lemma supported_conditions (hp : ∀i,p i≠0)
    (extra : CubeCoordinates ι→Finset ι) (original : Finset (Source ι Jo))
    (hvalid : ∀x∈original,SourceValid p x) (hextra : ∀x∈original,extra x.cube⊆x.cube.support)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (pool : Finset ι)
    (cutoff : Finset ι→Finset ι→ℝ) (b X : ℝ) :
    ActualSecondSourceConditions p (supportedRetainedSource p extra original negative J lists pool cutoff b X) :=
  ActualSecondSourceConditions.mono p (retained_conditions p hp extra original hvalid hextra negative J lists pool cutoff)
    (supported_subset p extra original negative J lists pool cutoff b X)

lemma supported_frequency_ne_zero
    (extra : CubeCoordinates ι→Finset ι) (original : Finset (Source ι Jo))
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (pool : Finset ι)
    (cutoff : Finset ι→Finset ι→ℝ) (b X : ℝ) :
    ∀x∈supportedRetainedSource p extra original negative J lists pool cutoff b X,x.second.frequency≠0 := by
  intro x hx
  exact unified_frequency_ne_zero p pool _ (fun _=>cutoff) x
    (supported_subset p extra original negative J lists pool cutoff b X hx)

end SevenEighths.InverseMomentGlobalRetainedGates
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.GlobalRetainedGatesChildren
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMomentGlobalRetainedGates
open InverseMoment InverseFirstPriorityParents InverseMomentWholePriorityParents
open InverseWholePriorityRetainedSource InversePrioritySecondSource InverseInitialArithmetic
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondSourceBlocks
open InverseSecondFibers CompletedGauss
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ] {Jo : ℕ}
variable (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]

lemma supported_original_property
    (extra : CubeCoordinates ι→Finset ι) (original : Finset (Source ι Jo))
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (pool : Finset ι)
    (cutoff : Finset ι→Finset ι→ℝ) (b X : ℝ)
    (F : CubeCoordinates ι→Finset ι→Finset ι→Ideal O→Prop)
    (hF : ∀y∈original,F y.cube y.firstCommon y.firstDivisor (sourceIdeal p y.quotientSupport)) :
    ∀x∈supportedRetainedSource p extra original negative J lists pool cutoff b X,
      F x.cube x.firstCommon x.firstDivisor x.quotient := by
  intro x hx
  obtain ⟨y,hy,hb,hc,hd,hq,ho⟩ := original_coordinates p extra original negative J lists pool cutoff x
    (supported_subset p extra original negative J lists pool cutoff b X hx)
  rw [hb,hc,hd,hq]
  exact hF y hy

theorem supported_label_gates (hp : ∀i,p i≠0)
    (extra : CubeCoordinates ι→Finset ι) (original : Finset (Source ι Jo))
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (pool : Finset ι)
    (cutoff : Finset ι→Finset ι→ℝ) (b X Z B j eta : ℝ) (hZ : 1<Z) (hbin : 2≤Z^eta)
    (hC : ∀y∈original,primeProductNorm p y.firstCommon≤Z^(B+eta))
    (hJ : ∀y∈original,‖eisEmbedding (jLabel p y.cube.support
      (fun i=>y.cube.leftExponent i+y.cube.rightExponent i) y.cube.leftBit y.cube.rightBit)‖^2≤Z^(j+eta)) :
    let source := supportedRetainedSource p extra original negative J lists pool cutoff b X
    (∀d,∀x∈cell p source d,(actualSecondChild p 1 1 x).2.1∈actualCellLabels p source d) ∧
    (∀d,∀I∈(actualCellLabels p source d).filter Squarefree,
      Squarefree I ∧ I≠0 ∧ (Ideal.absNorm I:ℝ)≤Z^(actualCellLabelExponent Z B j eta d)) := by
  intro source
  have hc := supported_original_property p extra original negative J lists pool cutoff b X
    (fun _ C _ _=>primeProductNorm p C≤Z^(B+eta)) hC
  have hj := supported_original_property p extra original negative J lists pool cutoff b X
    (fun q _ _ _=>‖eisEmbedding (jLabel p q.support
      (fun i=>q.leftExponent i+q.rightExponent i) q.leftBit q.rightBit)‖^2≤Z^(j+eta)) hJ
  exact ⟨fun d x hx=>actual_cell_labels_cover p source d x hx,
    fun d=>actual_cell_squarefree_labels p hp source
      (supported_frequency_ne_zero p extra original negative J lists pool cutoff b X) d Z B j eta hZ hbin hc hj⟩

theorem supported_child_margins (hp : ∀i,p i≠0)
    (hpr : ∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (extra : CubeCoordinates ι→Finset ι) (original : Finset (Source ι Jo))
    (hvalid : ∀x∈original,SourceValid p x) (hextra : ∀x∈original,extra x.cube⊆x.cube.support)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (pool : Finset ι)
    (cutoff : Finset ι→Finset ι→ℝ) (b : ℝ) (m : O) (hm : m≠0)
    (Z r ell V M Q z c A B t j eta : ℝ) (hZ : 1<Z)
    (hparent : CanonicalMargins (r+3*ell+V) M Q z c)
    (hA : 0≤A) (ht : 0≤t) (hV : 0≤V) (hj : 0≤j) (heta : 0≤eta) (hbin : 2≤Z^eta)
    (hQ : (Ideal.absNorm (Ideal.span {m}:Ideal O).radical:ℝ)≤Z^Q)
    (h1 : ∀y∈original,‖eisEmbedding (primeProduct p y.cube.support y.cube.leftExponent)‖^2≤Z^(ell+eta))
    (h2 : ∀y∈original,‖eisEmbedding (primeProduct p y.cube.support y.cube.rightExponent)‖^2≤Z^(ell+eta))
    (hT : ∀y∈original,primeProductNorm p y.quotientSupport≤Z^(t+eta)) :
    let source := supportedRetainedSource p extra original negative J lists pool cutoff b (Z^(r-A-B-t))
    ∀d,∀γ∈actualSecondTriples p 1 1 (cell p source d),
      actualSecondInheritedRadicalPuncture m γ≠0 ∧ 0≤actualSecondPunctureWidth Z m γ ∧
      ‖eisEmbedding (actualSecondInheritedRadicalPuncture m γ)‖^2=Z^(actualSecondPunctureWidth Z m γ) ∧
      CanonicalMargins (actualCellTotalExponent Z (Z^(r-A-B-t)) B j eta d)
        (childM M ell A t (secondCellExponent Z d 0) (secondCellExponent Z d 1) V j eta)
        (actualSecondPunctureWidth Z m γ) z (c-7*eta) := by
  intro source d γ hγ
  have hs := supported_conditions p hp extra original hvalid hextra negative J lists pool cutoff b (Z^(r-A-B-t))
  have hk := supported_frequency_ne_zero p extra original negative J lists pool cutoff b (Z^(r-A-B-t))
  have hb₁ := supported_original_property p extra original negative J lists pool cutoff b (Z^(r-A-B-t))
    (fun q _ _ _=>‖eisEmbedding (primeProduct p q.support q.leftExponent)‖^2≤Z^(ell+eta)) h1
  have hb₂ := supported_original_property p extra original negative J lists pool cutoff b (Z^(r-A-B-t))
    (fun q _ _ _=>‖eisEmbedding (primeProduct p q.support q.rightExponent)‖^2≤Z^(ell+eta)) h2
  have hq := supported_original_property p extra original negative J lists pool cutoff b (Z^(r-A-B-t))
    (fun _ _ _ I=>(Ideal.absNorm I:ℝ)≤Z^(t+eta)) (by
      intro y hy
      simpa only [sourceIdeal,←eisEmbedding_norm_sq_eq_absNorm_span,primeProductNorm] using hT y hy)
  exact actual_cell_triple_margins p hp hpr source hs hk d m hm
    Z r ell V M Q z c A B t j eta hZ hparent hA ht hV hj heta hbin hQ hb₁ hb₂ hq γ hγ

end SevenEighths.InverseMomentGlobalRetainedGates
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.FirstLabelCellStepGates
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMomentFirstLabelCell
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstChildWindows InverseFirstPriorityParents InverseFirstGlobalParents
open InverseMomentGlobalRetainedGates InverseInitialArithmetic InverseSecondSourceBlocks
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
variable (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]

lemma extra_subset (negative : Bool) (c : CubeCoordinates ι) : extra negative c⊆c.support := by
  cases negative
  · exact Finset.subset_union_left
  · exact Finset.subset_union_right

lemma dyadic_exponent_nonneg (Z : ℝ) (hZ : 1<Z) (n : ℕ) :
    0≤InverseFirstGlobalCaps.dyadicExponent Z n :=
  Real.logb_nonneg hZ (by unfold dyadScale;exact one_le_pow₀ (by norm_num : (1:ℝ)≤2))

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
lemma label_parent_valid (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (k : SourceIndex) (l j : ℕ) :
    ∀y∈InverseFirstGlobalCaps.labelParentCell p pool Q (fun _ _=>1) k l j,SourceValid p y := by
  intro y hy
  obtain ⟨o,ho,D,hD,hs,rfl⟩ := (InverseFirstGlobalCaps.mem_parentCell p pool Q (fun _ _=>1) k l y).mp
    (Finset.mem_filter.mp hy).1
  exact original_fill_valid p pool Q o (Finset.mem_filter.mp ho).1 D

include hp in
omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem label_parent_bounds (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (k : SourceIndex) (l j : ℕ) (Z ell eta : ℝ) (hZ : 1<Z) (heta : 0≤eta) (hbin : 2≤Z^eta)
    (hQ : ∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta)) :
    ∀y∈InverseFirstGlobalCaps.labelParentCell p pool Q (fun _ _=>1) k l j,
      ‖eisEmbedding (primeProduct p y.cube.support y.cube.leftExponent)‖^2≤Z^(ell+eta) ∧
      ‖eisEmbedding (primeProduct p y.cube.support y.cube.rightExponent)‖^2≤Z^(ell+eta) ∧
      primeProductNorm p (cubeActiveSupport y.cube.support
        (fun i=>y.cube.leftExponent i+y.cube.rightExponent i) y.cube.leftBit y.cube.rightBit)
        ≤Z^(InverseFirstGlobalCaps.dyadicExponent Z (k 4)+eta) ∧
      primeProductNorm p y.firstCommon≤Z^(InverseFirstGlobalCaps.dyadicExponent Z (k 2)+eta) ∧
      primeProductNorm p y.quotientSupport≤Z^(InverseFirstGlobalCaps.dyadicExponent Z l+eta) ∧
      Z^(InverseFirstGlobalCaps.dyadicExponent Z j-eta)≤InverseFirstGlobalCaps.jNorm p (toOriginal y) ∧
      InverseFirstGlobalCaps.jNorm p (toOriginal y)≤Z^(InverseFirstGlobalCaps.dyadicExponent Z j+eta) ∧
      primeProductNorm p y.firstDivisor≤Z^(InverseFirstGlobalCaps.dyadicExponent Z (k 3)+eta) := by
  intro y hy
  have hparent := (Finset.mem_filter.mp hy).1
  have hc := InverseFirstGlobalCaps.parentCell_cube_bounds p pool Q (fun _ _=>1) k l Z ell eta hQ y hparent
  have hn := InverseFirstGlobalCaps.parentCell_norm_bounds p hp pool Q (fun _ _=>1) k l Z eta hZ hbin y hparent
  have hi := InverseFirstGlobalCaps.parentCell_ideal_bounds p hp pool Q (fun _ _=>1) k l Z eta hZ hbin y hparent
  have hj := InverseFirstGlobalCaps.labelParentCell_bounds p hp pool Q (fun _ _=>1) k l j Z eta hZ hbin y hy
  refine ⟨hc.1,hc.2,?_,hi.1.2,?_,?_,hj.2.2,?_⟩
  · simpa only [InverseFirstGlobalCaps.sourceIdeal_norm] using hi.2.2.2
  · simpa only [hn.2.1] using hn.2.2.2
  · exact (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)).trans hj.2.1
  · simpa only [InverseFirstGlobalCaps.sourceIdeal_norm] using hi.2.1.2

end SevenEighths.InverseMomentFirstLabelCell
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.FirstLabelCellStepChildren
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMomentFirstLabelCell
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstChildWindows InverseFirstPriorityParents InverseFirstGlobalParents
open InverseMomentGlobalRetainedGates InverseInitialArithmetic InverseSecondSourceBlocks
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
variable (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]

include hp in
theorem source_labels (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l j : ℕ)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (Z M r ell V eta tau window b : ℝ)
    (hZ : 1<Z) (heta : 0≤eta) (hbin : 2≤Z^eta)
    (hQ : ∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta)) :
    let S := source p pool Q k l j negative J lists Z M r ell V eta tau window b
    (∀d,∀x∈cell p S d,(actualSecondChild p 1 1 x).2.1∈actualCellLabels p S d) ∧
    (∀d,∀I∈(actualCellLabels p S d).filter Squarefree,
      Squarefree I ∧ I≠0 ∧ (Ideal.absNorm I:ℝ)≤
        Z^(actualCellLabelExponent Z (exponent Z (k 2)) (exponent Z j) eta d)) := by
  intro S
  have hb := label_parent_bounds p hp pool Q k l j Z ell eta hZ heta hbin hQ
  exact supported_label_gates p hp _ _ negative J lists pool _ b (columnScale Z r k l negative)
    Z (exponent Z (k 2)) (exponent Z j) eta hZ hbin
    (fun y hy=>(hb y hy).2.2.2.1) (fun y hy=>(hb y hy).2.2.2.2.2.2.1)

include hp in
theorem source_child_margins
    (hpr : ∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l j : ℕ)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (Z M r ell V eta tau window b : ℝ)
    (m : O) (hm : m≠0) (Qwidth z c : ℝ)
    (hZ : 1<Z) (heta : 0≤eta) (hbin : 2≤Z^eta) (hV : 0≤V)
    (hparent : CanonicalMargins (r+3*ell+V) M Qwidth z c)
    (hpuncture : (Ideal.absNorm (Ideal.span {m}:Ideal O).radical:ℝ)≤Z^Qwidth)
    (hQ : ∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta)) :
    let S := source p pool Q k l j negative J lists Z M r ell V eta tau window b
    ∀d,∀γ∈actualSecondTriples p 1 1 (cell p S d),
      actualSecondInheritedRadicalPuncture m γ≠0 ∧ 0≤actualSecondPunctureWidth Z m γ ∧
      ‖eisEmbedding (actualSecondInheritedRadicalPuncture m γ)‖^2=Z^(actualSecondPunctureWidth Z m γ) ∧
      CanonicalMargins (actualCellTotalExponent Z (columnScale Z r k l negative)
        (exponent Z (k 2)) (exponent Z j) eta d)
        (childM M ell (columnA Z k negative) (exponent Z l) (secondCellExponent Z d 0)
          (secondCellExponent Z d 1) V (exponent Z j) eta)
        (actualSecondPunctureWidth Z m γ) z (c-7*eta) := by
  intro S
  have hb := label_parent_bounds p hp pool Q k l j Z ell eta hZ heta hbin hQ
  exact supported_child_margins p hp hpr _ _ (label_parent_valid p pool Q k l j)
    (fun y hy=>extra_subset negative y.cube) negative J lists pool _ b m hm
    Z r ell V M Qwidth z c (columnA Z k negative) (exponent Z (k 2)) (exponent Z l) (exponent Z j) eta
    hZ hparent (dyadic_exponent_nonneg Z hZ _) (dyadic_exponent_nonneg Z hZ _) hV
    (dyadic_exponent_nonneg Z hZ _) heta hbin hpuncture
    (fun y hy=>(hb y hy).1) (fun y hy=>(hb y hy).2.1) (fun y hy=>(hb y hy).2.2.2.2.1)

end SevenEighths.InverseMomentFirstLabelCell
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.CanonicalChildSupport
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CanonicalQuadraticSieve
open InverseInitialArithmetic InverseSecondSourceBlocks InverseSecondFibers
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[DecidableEq ι](p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
variable (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
variable (hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)

include hp hg hc in
omit [DecidableEq ι] in
lemma canonical_source_prime_supported (i:ι):Supported (Ideal.span {p i}) :=by
  have hn:(Ideal.span {p i}:Ideal O)≠0:=Ideal.span_singleton_eq_bot.not.mpr (hp i)
  refine ⟨hn,?_⟩
  intro P hP
  obtain ⟨hprime,hle⟩:=(Ideal.mem_normalizedFactors_iff hn).mp hP
  have he:Ideal.span {p i}=P:=(inferInstance:(Ideal.span {p i}:Ideal O).IsMaximal).eq_of_le hprime.ne_top hle
  subst P
  exact ⟨hg i,hc i⟩

lemma canonical_supported_prod {α:Type*}(S:Finset α)(f:α→Ideal O)
    (hf:∀i∈S,Supported (f i)):Supported (∏i∈S,f i) :=by
  classical
  induction S using Finset.induction_on with
  | empty =>
    change Supported (1:Ideal O)
    refine ⟨one_ne_zero,?_⟩
    intro P hP
    rw [UniqueFactorizationMonoid.normalizedFactors_one] at hP
    exact (Multiset.notMem_zero P hP).elim
  | @insert i S hi ih =>
    rw [Finset.prod_insert hi,supported_mul_iff]
    exact ⟨hf i (Finset.mem_insert_self _ _),ih (fun j hj=>hf j (Finset.mem_insert_of_mem hj))⟩

include hp hg hc in
omit [DecidableEq ι] in
lemma canonical_source_ideal_supported (S:Finset ι):Supported (sourceIdeal p S) :=by
  rw [sourceIdeal,FiniteGaussPhase.span_finset_prod]
  exact canonical_supported_prod S (fun i=>Ideal.span {p i}) (fun i _=>canonical_source_prime_supported p hp hg hc i)

include hp hg hc in
omit [DecidableEq ι] in
lemma canonical_prime_product_supported (S:Finset ι)(v:ι→ℕ):Supported (Ideal.span {primeProduct p S v}) :=by
  rw [primeProduct,FiniteGaussPhase.span_finset_prod]
  apply canonical_supported_prod
  intro i hi
  rw [←Ideal.span_singleton_pow]
  exact supported_pow (canonical_source_prime_supported p hp hg hc i) _

include hp hg hc in
lemma actual_second_label_supported {Jo Jn:ℕ}(x:MarkedSecondSource ι Jo Jn):
    Supported (actualSecondChild p 1 1 x).2.1 :=by
  change Supported ((Ideal.span {jLabel p x.cube.support
    (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit})*
    sourceIdeal p x.firstCommon*sourceIdeal p x.second.divisor*sourceIdeal p x.second.overlap)
  simp only [supported_mul_iff]
  exact ⟨⟨⟨canonical_prime_product_supported p hp hg hc _ _,canonical_source_ideal_supported p hp hg hc _⟩,
    canonical_source_ideal_supported p hp hg hc _⟩,canonical_source_ideal_supported p hp hg hc _⟩

include hp hg hc in
theorem actual_cell_labels_supported {Jo Jn:ℕ}(S:Finset (MarkedSecondSource ι Jo Jn))(d:BlockIndex):
    ∀I∈actualCellLabels p S d,Supported I :=by
  intro I hI
  obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp hI
  exact actual_second_label_supported p hp hg hc x

include hp hg hc in
theorem actual_cell_labels_admissible {Jo Jn:ℕ}(S:Finset (MarkedSecondSource ι Jo Jn))(d:BlockIndex):
    ∀I∈(actualCellLabels p S d).filter Squarefree,CanonicalQuadraticSieve.Admissible I :=by
  intro I hI
  obtain ⟨hm,hs⟩:=Finset.mem_filter.mp hI
  have hh:=actual_cell_labels_supported p hp hg hc S d I hm
  exact ⟨hh.1,hs,hh.2⟩

end SevenEighths.InverseMoment

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.CanonicalLongSource
namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap ContDiff
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion ConcretePrimeRowBridge
open CanonicalCubeSeparation CanonicalQuadraticSieve FirstPassCubeLabels SecondPassArithmetic
open JointLogSeparation FourierBridge CompletedHeight
local notation "O"=>ActualEisensteinCubic.O

theorem long_cube_progress
    (S:Finset (Ideal O))(D:ℕ)
    (Q:Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→₀ℕ))
    (Z cutoff V ell:ℝ)(hZ:1<Z)
    (hne:(progressingCubes S D (Z^(cutoff-V)) Q).Nonempty)
    (hupper:∀v∈Q,(Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v):ℝ)≤
      Real.exp 1*Z^ell) :
    cutoff-1/Real.log Z≤ell+V := by
  obtain ⟨v,hv⟩:=hne
  obtain ⟨hv,hlower⟩:=Finset.mem_filter.mp hv
  have hz:0<Z:=zero_lt_one.trans hZ
  have he:=Real.log_le_log (Real.rpow_pos_of_pos hz _) (hlower.trans (hupper v hv))
  rw [Real.log_rpow hz,Real.log_mul (Real.exp_pos _).ne' (Real.rpow_pos_of_pos hz _).ne',
    Real.log_exp,Real.log_rpow hz] at he
  have hlog:=Real.log_pos hZ
  have hd: (cutoff-ell-V)*Real.log Z≤1:=by nlinarith
  have hh:cutoff-ell-V≤1/Real.log Z:=(le_div_iff₀ hlog).mpr hd
  linarith

theorem long_cube_progress_with_slack
    (S:Finset (Ideal O))(D:ℕ)
    (Q:Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→₀ℕ))
    (Z cutoff V ell eta:ℝ)(hZ:1<Z)(hlog:1≤eta*Real.log Z)
    (hne:(progressingCubes S D (Z^(cutoff-V)) Q).Nonempty)
    (hupper:∀v∈Q,(Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v):ℝ)≤
      Real.exp 1*Z^ell) :
    cutoff-eta≤ell+V := by
  have h:=long_cube_progress S D Q Z cutoff V ell hZ hne hupper
  have hh:1/Real.log Z≤eta:=(div_le_iff₀ (Real.log_pos hZ)).mpr (by simpa only [mul_comm] using hlog)
  linarith

end SevenEighths.InverseMoment

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.CanonicalLongGeometry
namespace OAI

noncomputable section

open scoped BigOperators Classical
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion ConcretePrimeRowBridge
open CanonicalQuadraticSieve CanonicalCubeSeparation FirstPassCubeLabels SecondPassArithmetic
local notation "O"=>ActualEisensteinCubic.O

theorem actualCubeLength_power (Z:ℝ)(hZ:1<Z)(j:ℕ) :
    Z^(actualCubeLength Z j)=normLogScale j :=
  Real.rpow_logb (zero_lt_one.trans hZ) (ne_of_gt hZ) (normLogScale_pos j)

theorem actual_long_bin_geometry
    (S:Finset (Ideal O))(D:ℕ)(hbad:fixedBadPrimes⊆S)
    (b Z N V cutoff eta L:ℝ)(j:ℕ)(hZ:1<Z)(hL:1≤L)(heta:eta≤1)
    (hV:0≤V)(hparent:N+V≤L)(hb:b≤Z^eta)(hlog:1≤eta*Real.log Z)
    (hne:(progressingCubes S D (Z^(cutoff-V)) (activeCubeLogBin S D b (Z^N) j)).Nonempty) :
    let ell:=actualCubeLength Z j;
    let r:=N-3*ell;
    let F:=InitialMeanSquare.outsideSquarefreeIdeals S D;
    let Q:=progressingCubes S D (Z^(cutoff-V)) (activeCubeLogBin S D b (Z^N) j);
    0≤ell ∧ -eta≤ r ∧ r≤L ∧ ell≤L ∧ r+3*ell+V≤L ∧ cutoff-eta≤ell+V ∧
      ∀v∈Q,Z^ell≤‖ConcreteTraceCRT.eisEmbedding (primeProduct (poolPrimary F) v.support v)‖^2 ∧
        ‖ConcreteTraceCRT.eisEmbedding (primeProduct (poolPrimary F) v.support v)‖^2≤Real.exp 1*Z^ell := by
  dsimp only
  have hz:0<Z:=zero_lt_one.trans hZ
  have hp:Z^(actualCubeLength Z j)=normLogScale j:=actualCubeLength_power Z hZ j
  have hel:0≤actualCubeLength Z j:=Real.logb_nonneg hZ (normLogScale_ge_one j)
  have hnorm (v:primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→₀ℕ)
      (hv:v∈activeCubeLogBin S D b (Z^N) j) :
      Z^(actualCubeLength Z j)≤(Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v):ℝ) ∧
      (Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v):ℝ)≤Real.exp 1*Z^(actualCubeLength Z j) := by
    rw [hp]
    exact activeCubeLogBin_norms S D b (Z^N) j v hv
  obtain ⟨v,hv⟩:=hne
  have hvbin: v∈activeCubeLogBin S D b (Z^N) j := (Finset.mem_filter.mp hv).1
  have hactive:= (Finset.mem_filter.mp hvbin).1
  have hcube:(Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v):ℝ)^3≤b*Z^N :=
    (Finset.mem_filter.mp hactive).2
  have hsc:(Z^(actualCubeLength Z j))^3≤Z^(N+eta) := by
    calc
      _≤(Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v):ℝ)^3 :=
        pow_le_pow_left₀ (Real.rpow_nonneg hz.le _) (hnorm v hvbin).1 3
      _≤b*Z^N:=hcube
      _≤Z^eta*Z^N:=mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg hz.le _)
      _=Z^(N+eta):=by rw [Real.rpow_add hz];ring
  rw [←Real.rpow_mul_natCast hz.le] at hsc
  have hscale:actualCubeLength Z j*3≤N+eta := (Real.rpow_le_rpow_left_iff hZ).mp hsc
  have hprogress:=long_cube_progress_with_slack S D (activeCubeLogBin S D b (Z^N) j)
    Z cutoff V (actualCubeLength Z j) eta hZ hlog ⟨v,hv⟩ (fun v hv=>(hnorm v hv).2)
  refine ⟨hel,by linarith,by linarith,by linarith,by linarith,hprogress,?_⟩
  intro u hu
  rw [cubeIdeal_primeProduct_norm _ (InitialMeanSquare.outsideSquarefree_admissible S D hbad)]
  exact hnorm u (Finset.mem_filter.mp hu).1

end SevenEighths.InverseMoment

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.CanonicalRankMoments
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CanonicalQuadraticSieve
open InverseInitialClippedColumns InverseSecondFibers InverseSecondSourceBlocks
open CanonicalCoefficientClass InverseMomentFirstLabelCell InverseMomentFirstChildWindows InverseFirstGlobalCaps
local notation "O"=>ActualEisensteinCubic.O
variable {ι σ:Type}[DecidableEq ι][DecidableEq σ]
variable (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
variable (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
variable (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

include hp in
theorem canonical_rank_moments_children
    (hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool:Finset ι)(Q:Finset (ι→₀ℕ))(k:SourceIndex)(l j:ℕ)(negative:Bool)
    (base Ψ:O→*ℂ)(hΨ:IsBaseRayTwist base Ψ)(m:O)(hm:m≠0)
    (slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)(ω₁ ω₂:𝓢(ℝ,ℂ))
    (Z M r ell V eta tau window b cutoff Qwidth z c eps A:ℝ)(K degree:ℕ)
    (hZ:1<Z)(heta:0≤eta)(hbin:2≤Z^eta)(hell:0≤ell)(hV:0≤V)
    (hb:1≤b)(hbt:b≤Z^(6*eta))(hwindow:Real.exp window≤Z^(4*eta))
    (_hd:0<cutoff)(hterminal:cutoff≤ell+V)(hsmall:eta≤ cutoff/16)
    (hparent:CanonicalMargins (r+3*ell+V) M Qwidth z c)
    (hpuncture:(Ideal.absNorm (Ideal.span {m}:Ideal O).radical:ℝ)≤Z^Qwidth)
    (hQ:∀v∈Q,‖ConcreteTraceCRT.eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta))
    (h₁:CanonicalRankMoments p hp hcop hg pool base slots lists a ω₁ Z (M-3*cutoff/2) (r+3*ell+V+15*eta) z (c-7*eta) eps A K degree)
    (h₂:CanonicalRankMoments p hp hcop hg pool base slots lists a ω₂ Z (M-3*cutoff/2) (r+3*ell+V+15*eta) z (c-7*eta) eps A K degree):
    ChildBounds p hp hcop hg pool Q k l j negative Ψ m slots lists a ω₁ ω₂
      Z M r ell V eta tau window b eps A K degree :=by
  intro ray core assigned hass
  let S:=source p pool Q k l j negative assigned lists Z M r ell V eta tau window b
  let Ψ₀:=firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core
  have hbase:IsBaseRayTwist base Ψ₀:=hΨ.firstCore _ _ _
  have hstate:=source_state_bounds p hp pool Q k l j negative assigned lists Z M r ell V eta tau window b cutoff
    hZ heta hbin hell hV hb hbt hwindow hterminal hsmall hQ
  have hmargin:=source_child_margins p hp hpr pool Q k l j negative assigned lists Z M r ell V eta tau window b
    m hm Qwidth z c hZ heta hbin hV hparent hpuncture hQ
  have hlabels:=source_labels p hp pool Q k l j negative assigned lists Z M r ell V eta tau window b hZ heta hbin hQ
  constructor
  · intro zz d hdcell s J hJ γ hγ
    have st:=hstate d hdcell
    have mg:=hmargin d γ hγ
    apply h₁ (secondRayMinus Ψ₀ zz) (hbase.secondMinus zz) (actualSecondInheritedRadicalPuncture m γ) mg.1
      (max 0 (secondCellColumnExponent Z (columnScale Z r k l negative) d))
      (actualCellLabelExponent Z (exponent Z (k 2)) (exponent Z j) eta d)
      (actualCellRowExponent Z M ell (columnA Z k negative) (exponent Z l) V (exponent Z j) eta d)
      (actualSecondPunctureWidth Z m γ) st.1 st.2.1 st.2.2.2.1 mg.2.1 (by linarith [st.2.2.2.2]) st.2.2.1 mg.2.2.2 mg.2.2.1
      ((slots\assigned)\J) (Finset.sdiff_subset.trans Finset.sdiff_subset)
      ((actualCellLabels p S d).filter Squarefree) ?_ s
    intro I hI
    exact ⟨actual_cell_labels_admissible p hp hg hc S d I hI,(hlabels.2 d I hI).2.2⟩
  · intro zz d hdcell s J hJ γ hγ
    have st:=hstate d hdcell
    have mg:=hmargin d γ hγ
    apply h₂ (secondRayPlus Ψ₀ zz) (hbase.secondPlus zz) (actualSecondInheritedRadicalPuncture m γ) mg.1
      (max 0 (secondCellColumnExponent Z (columnScale Z r k l negative) d))
      (actualCellLabelExponent Z (exponent Z (k 2)) (exponent Z j) eta d)
      (actualCellRowExponent Z M ell (columnA Z k negative) (exponent Z l) V (exponent Z j) eta d)
      (actualSecondPunctureWidth Z m γ) st.1 st.2.1 st.2.2.2.1 mg.2.1 (by linarith [st.2.2.2.2]) st.2.2.1 mg.2.2.2 mg.2.2.1
      ((slots\assigned)\J) (Finset.sdiff_subset.trans Finset.sdiff_subset)
      ((actualCellLabels p S d).filter Squarefree) ?_ s
    intro I hI
    exact ⟨actual_cell_labels_admissible p hp hg hc S d I hI,(hlabels.2 d I hI).2.2⟩

end SevenEighths.InverseMoment

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.CanonicalRankMonotone
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic CanonicalQuadraticSieve InverseInitialClippedColumns
local notation "O"=>ActualEisensteinCubic.O
variable {ι σ:Type}[DecidableEq ι][DecidableEq σ]
variable (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
variable (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
variable (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

omit [DecidableEq σ] in
theorem canonical_rank_restrict (pool:Finset ι)(base:O→*ℂ)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (W:𝓢(ℝ,ℂ))(Z M₁ M₂ F₁ F₂ z c₁ c₂ eps A:ℝ)(K degree:ℕ)
    (hM:M₁≤M₂)(hF:F₁≤F₂)(hc:c₂≤ c₁)
    (h:CanonicalRankMoments p hp hcop hg pool base slots lists a W Z M₂ F₂ z c₂ eps A K degree):
    CanonicalRankMoments p hp hcop hg pool base slots lists a W Z M₁ F₁ z c₁ eps A K degree :=by
  intro Ψ hΨ m hm N V M Qwidth hN hV hM0 hQ hMc hFc hmargin hnorm ss hss labels hlabels s
  have hmarg:CanonicalMargins (N+V) M Qwidth z c₂:=by
    unfold CanonicalMargins at *
    constructor <;> linarith [hmargin.1,hmargin.2]
  exact h Ψ hΨ m hm N V M Qwidth hN hV hM0 hQ (hMc.trans hM) (hFc.trans hF) hmarg hnorm ss hss labels hlabels s

end SevenEighths.InverseMoment

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.CanonicalRankCapChildren
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CanonicalQuadraticSieve
open InverseMomentFirstLabelCell InverseMomentFirstChildWindows InverseFirstGlobalCaps
local notation "O"=>ActualEisensteinCubic.O
variable {ι σ:Type}[DecidableEq ι][DecidableEq σ]
variable (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
variable (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
variable (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem canonical_rank_cap_children
    (hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool:Finset ι)(Q:Finset (ι→₀ℕ))(k:SourceIndex)(l j:ℕ)(negative:Bool)
    (base Ψ:O→*ℂ)(hΨ:CanonicalCoefficientClass.IsBaseRayTwist base Ψ)(m:O)(hm:m≠0)
    (slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)(ω₁ ω₂:𝓢(ℝ,ℂ))
    (Z M r ell V eta tau window b cutoff Qwidth z c eps A Mnext Fnext cnext:ℝ)(K degree:ℕ)
    (hZ:1<Z)(heta:0≤eta)(hbin:2≤Z^eta)(hell:0≤ell)(hV:0≤V)
    (hb:1≤b)(hbt:b≤Z^(6*eta))(hwindow:Real.exp window≤Z^(4*eta))
    (hd:0<cutoff)(hterminal:cutoff≤ell+V)(hsmall:eta≤ cutoff/16)
    (hparent:CanonicalMargins (r+3*ell+V) M Qwidth z c)
    (hpuncture:(Ideal.absNorm (Ideal.span {m}:Ideal O).radical:ℝ)≤Z^Qwidth)
    (hQ:∀v∈Q,‖ConcreteTraceCRT.eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta))
    (hMc:M-3*cutoff/2≤Mnext)(hFc:r+3*ell+V+15*eta≤Fnext)(hcc:cnext≤ c-7*eta)
    (h₁:CanonicalRankMoments p hp hcop hg pool base slots lists a ω₁ Z Mnext Fnext z cnext eps A K degree)
    (h₂:CanonicalRankMoments p hp hcop hg pool base slots lists a ω₂ Z Mnext Fnext z cnext eps A K degree):
    ChildBounds p hp hcop hg pool Q k l j negative Ψ m slots lists a ω₁ ω₂
      Z M r ell V eta tau window b eps A K degree :=by
  exact canonical_rank_moments_children p hp hcop hg hc hpr pool Q k l j negative base Ψ hΨ m hm
    slots lists a ω₁ ω₂ Z M r ell V eta tau window b cutoff Qwidth z c eps A K degree
    hZ heta hbin hell hV hb hbt hwindow hd hterminal hsmall hparent hpuncture hQ
    (canonical_rank_restrict p hp hcop hg pool base slots lists a ω₁ Z _ _ _ _ z _ _ eps A K degree hMc hFc hcc h₁)
    (canonical_rank_restrict p hp hcop hg pool base slots lists a ω₂ Z _ _ _ _ z _ _ eps A K degree hMc hFc hcc h₂)

end SevenEighths.InverseMoment

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.CanonicalLiveBinRank
namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge CanonicalQuadraticSieve
open CanonicalRowCompletion FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstLabelCell InverseMomentFirstChildWindows
local notation "O"=>ActualEisensteinCubic.O

theorem actual_live_bin_rank_children_oai
    (S:Finset (Ideal O))(D:ℕ)(hbad:fixedBadPrimes⊆S)
    (Z N V M cutoff eta L b window bW Qwidth z c eps A Mnext Fnext cnext tau:ℝ)
    (j:ℕ)(hZ:1<Z)(hL:1≤L)(heta:0≤eta)(heta1:eta≤1)
    (hcut:0<cutoff)(hsmall:eta≤ cutoff/32)(hV:0≤V)(hparentcap:N+V≤L)
    (hbW:bW≤Z^eta)(hlog:1≤eta*Real.log Z)(hexp:Real.exp 1≤Z^eta)
    (hbin:2≤Z^eta)(hb:1≤b)(hbt:b≤Z^(6*eta))(hwindow:Real.exp window≤Z^(4*eta))
    (hne:(progressingCubes S D (Z^(cutoff-V)) (activeCubeLogBin S D bW (Z^N) j)).Nonempty)
    (base Ψ:O→*ℂ)(hΨ:CanonicalCoefficientClass.IsBaseRayTwist base Ψ)(m:O)(hm:m≠0)
    (hparent:CanonicalMargins (N+V) M Qwidth z c)
    (hpuncture:(Ideal.absNorm (Ideal.span {m}:Ideal O).radical:ℝ)≤Z^Qwidth)
    (hMc:M-3*(cutoff/2)/2≤Mnext)(hFc:N+V+15*eta≤Fnext)(hcc:cnext≤ c-7*eta)
    {σ:Type}[DecidableEq σ](slots:Finset σ)
    (lists:σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
    (a:σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ)
    (ω₁ ω₂:𝓢(ℝ,ℂ))(K degree:ℕ):
    let F:=InitialMeanSquare.outsideSquarefreeIdeals S D;
    let hF:=InitialMeanSquare.outsideSquarefree_admissible S D hbad;
    letI:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hF i];infer_instance;
    CanonicalRankMoments (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
      (poolPrimary_good F hF) Finset.univ base slots lists a ω₁ Z Mnext Fnext z cnext eps A K degree →
    CanonicalRankMoments (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
      (poolPrimary_good F hF) Finset.univ base slots lists a ω₂ Z Mnext Fnext z cnext eps A K degree →
    ∀k:SourceIndex,∀l jj:ℕ,∀negative:Bool,
      ChildBounds (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
        (poolPrimary_good F hF) Finset.univ
        (progressingCubes S D (Z^(cutoff-V)) (activeCubeLogBin S D bW (Z^N) j))
        k l jj negative Ψ m slots lists a ω₁ ω₂
        Z M (N-3*actualCubeLength Z j) (actualCubeLength Z j) V eta tau window b eps A K degree :=by
  dsimp only
  intro h₁ h₂ k l jj negative
  let F:=InitialMeanSquare.outsideSquarefreeIdeals S D
  have hF:=InitialMeanSquare.outsideSquarefree_admissible S D hbad
  let:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hF i];infer_instance
  obtain ⟨hel,hr,hrL,helL,hFL,hgap,hqn⟩:=actual_long_bin_geometry S D hbad bW Z N V cutoff eta L j
    hZ hL heta1 hV hparentcap hbW hlog hne
  have hs:(N-3*actualCubeLength Z j)+3*actualCubeLength Z j+V=N+V:=by ring
  apply canonical_rank_cap_children (poolPrimary F) (poolPrimary_ne_zero F hF)
    (poolPrimary_coprime F hF) (poolPrimary_good F hF) (poolPrimary_odd F hF)
    (fun i=>(primaryPrime_spec i.val (poolPrimary_ne_zero F hF i)).2.2.2)
    Finset.univ _ k l jj negative base Ψ hΨ m hm slots lists a ω₁ ω₂
    Z M _ _ V eta tau window b (cutoff/2) Qwidth z c eps A Mnext Fnext cnext K degree
    hZ heta hbin hel hV hb hbt hwindow (by linarith) (by linarith) (by linarith)
    (by simpa only [hs] using hparent) hpuncture ?_ hMc (by simpa only [hs] using hFc) hcc h₁ h₂
  intro v hv
  apply (hqn v hv).2.trans
  calc
    _≤Z^eta*Z^(actualCubeLength Z j):=mul_le_mul_of_nonneg_right hexp (Real.rpow_nonneg (by linarith) _)
    _=Z^(actualCubeLength Z j+eta):=by rw [Real.rpow_add (by linarith : 0<Z)];ring

end SevenEighths.InverseMoment

end

end OAI
end

theorem solution : type_of% @OAI.SevenEighths.InverseMoment.actual_live_bin_rank_children_oai := @OAI.SevenEighths.InverseMoment.actual_live_bin_rank_children_oai
