-- Prove2me | solution 1 for OAI.SevenEighths.InverseMomentFirstLabelCell.source_step_arithmetic
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T03:32:58.907979+00:00
-- url     : https://prove2.me/submissions/8753c23f-fad1-407f-90be-d06397710575

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIHecke78B019

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

lemma nonzeroChildFrequencyBall_empty (a : Eis) (ha : a ≠ 0) (R : ℝ) (hR : R < 1) :
    nonzeroChildFrequencyBall a R = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro k hk
  have hm := (mem_nonzeroChildFrequencyBall a ha R k).mp hk
  have hk0 : k ≠ 0 := by intro hk; simp [hk] at hm
  exact (not_le_of_gt hR) ((EisensteinSchwartzPoisson.one_le_eisenstein_norm_sq
    (a*k) (mul_ne_zero ha hk0)).trans hm.2)

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

omit [DecidableEq ι] in
theorem actual_second_row_radius_one
    {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn)) (R : ℝ)
    (hsource : source.Nonempty)
    (hrows : ∀ x ∈ source,
      x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) R) : 1 ≤ R := by
  obtain ⟨x,hx⟩ := hsource
  by_contra hR
  have he := nonzeroChildFrequencyBall_empty _ (actualSecondMultiplier_ne_zero p x) R (lt_of_not_ge hR)
  simpa [he] using hrows x hx

end
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
theorem mem_keys_iff (p : ι → O) {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (d : BlockIndex) : d ∈ keys p source ↔ (cell p source d).Nonempty := by
  simp only [keys,Finset.mem_image,Finset.nonempty_iff_ne_empty]
  constructor
  · rintro ⟨x,hx,he⟩
    exact Finset.nonempty_iff_ne_empty.mp ⟨x,(mem_cell p source d x).mpr ⟨hx,he⟩⟩
  · intro h
    obtain ⟨x,hx⟩ := Finset.nonempty_iff_ne_empty.mpr h
    exact ⟨x,(mem_cell p source d x).mp hx⟩

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.SecondCellParameters
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseSecondSourceBlocks InverseInitialArithmetic
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

theorem secondCellExponent_nonneg (Z:ℝ) (d:BlockIndex) (i:Fin 4) (hZ:1<Z):
    0≤ secondCellExponent Z d i := by
  apply Real.logb_nonneg hZ
  exact one_le_pow₀ (by norm_num : (1:ℝ)≤2)

theorem second_cell_scale_rpow (Z:ℝ) (d:BlockIndex) (i:Fin 4) (hZ:1<Z):
    Z^(secondCellExponent Z d i)=scales d i :=
  Real.rpow_logb (by linarith) (ne_of_gt hZ) (dyadScale_pos _)

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.ActualChildState
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondSourceBlocks
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.ActualChildStateRadius
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondSourceBlocks
open InverseSecondFibers CompletedGauss
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

theorem actual_cell_radius_nonnegative_on_keys {ι : Type*} [DecidableEq ι]
    (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]
    {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (Z M ell A t V j eta : ℝ) (hZ : 1<Z)
    (hrows : ∀d,∀x∈cell p source d,x.second.frequency∈nonzeroChildFrequencyBall (actualSecondMultiplier p x)
      (actualCellRowRadius Z M ell A t V j eta d)) :
    ∀d∈keys p source,0≤actualCellRowExponent Z M ell A t V j eta d := by
  intro d hd
  obtain ⟨x,hx⟩ := (mem_keys_iff p source d).mp hd
  have hr := actual_second_row_radius_one p (cell p source d)
    (actualCellRowRadius Z M ell A t V j eta d) ⟨x,hx⟩ (hrows d)
  exact (Real.rpow_le_rpow_left_iff hZ).mp (by simpa only [Real.rpow_zero,actualCellRowRadius] using hr)

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.SecondUniformCutoff
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
namespace SevenEighths.InverseSecondUniformCutoff
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseMoment InverseSecondSourceBlocks InverseSecondFibers CompletedGauss
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

theorem uniform_radius_bound {ι : Type*} [DecidableEq ι]
    (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (G E : Finset ι) (Z delta theta g s Hc eta tau L : ℝ)
    (hZ : 0<Z) (hL0 : 0≤L)
    (hE : primeProductNorm p E≤Z^(theta+eta))
    (hG : Z^(g-eta)≤primeProductNorm p G) (hL : L≤Z^(s+4*eta)) :
    uniformSecondRadius p Z delta eta G E L (Z^(Hc+12*eta+tau)) (Z^tau)≤
      Z^(2*(s-g)-Hc+delta+2*theta+eta) := by
  have hratio : primeProductNorm p E/primeProductNorm p G≤Z^(theta-g+2*eta) := by
    calc
      _≤Z^(theta+eta)/Z^(g-eta):=div_le_div₀
        (Real.rpow_pos_of_pos hZ _).le hE (Real.rpow_pos_of_pos hZ _) hG
      _= _:=by rw [←Real.rpow_sub hZ];congr 1;ring
  have hratio0 : 0≤primeProductNorm p E/primeProductNorm p G :=
    div_nonneg (primeProductNorm_pos p hp E).le (primeProductNorm_pos p hp G).le
  have hsq (x : ℝ) : (Z^x)^2=Z^(2*x) := by
    rw [pow_two,←Real.rpow_add hZ]
    congr 1
    ring
  calc
    _≤Z^(delta+eta)*(Z^(theta-g+2*eta))^2*(Z^(s+4*eta))^2*Z^tau/Z^(Hc+12*eta+tau):=by
      unfold uniformSecondRadius
      gcongr
    _= _:=by
      rw [hsq,hsq,←Real.rpow_add hZ,←Real.rpow_add hZ,←Real.rpow_add hZ,←Real.rpow_sub hZ]
      congr 1
      ring

theorem uniform_radius_childM {ι : Type*} [DecidableEq ι]
    (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (G E : Finset ι) (Z M r ell V delta A B j t g theta eta tau L : ℝ)
    (hZ : 0<Z) (hL0 : 0≤L)
    (hE : primeProductNorm p E≤Z^(theta+eta))
    (hG : Z^(g-eta)≤primeProductNorm p G) (hL : L≤Z^(r-A-B-t+4*eta)) :
    uniformSecondRadius p Z delta eta G E L
      (Z^(firstPhysicalHeight M r ell V delta B j+12*eta+tau)) (Z^tau)≤
      Z^(childM M ell A t g theta V j eta) := by
  have hb:=uniform_radius_bound p hp G E Z delta theta g (r-A-B-t)
    (firstPhysicalHeight M r ell V delta B j) eta tau L hZ hL0 hE hG hL
  convert (preTransparency := .instances) hb using 1
  congr 1
  unfold childM decrease firstPhysicalHeight
  ring

theorem actual_cell_uniform_source_gates {ι : Type*} [DecidableEq ι]
    (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (Z M r ell V delta A B j t eta tau L : ℝ) (hZ : 1<Z)
    (heta : 0≤eta) (hbin : 2≤Z^eta) (hL0 : 0≤L)
    (hL : L≤Z^(r-A-B-t+4*eta))
    (hgate : ∀x∈source,x.second.frequency∈nonzeroChildFrequencyBall (actualSecondMultiplier p x)
      (uniformSecondRadius p Z delta eta x.second.sourceCommon x.second.divisor L
        (Z^(firstPhysicalHeight M r ell V delta B j+12*eta+tau)) (Z^tau))) :
    ∀d,∀x∈cell p source d,x.second.frequency∈nonzeroChildFrequencyBall (actualSecondMultiplier p x)
      (actualCellRowRadius Z M ell A t V j eta d) := by
  have hk : ∀x∈source,x.second.frequency≠0 := fun x hx=>(Finset.mem_erase.mp (hgate x hx)).1
  intro d x hx
  have hxs:=cell_subset p source d hx
  have hE:=(actual_cell_norm_centers p hp source hk d x hx Z eta hZ heta hbin 1).2
  have hG:=(actual_cell_norm_centers p hp source hk d x hx Z eta hZ heta hbin 0).1
  have hr:=uniform_radius_childM p hp x.second.sourceCommon x.second.divisor
    Z M r ell V delta A B j t (secondCellExponent Z d 0) (secondCellExponent Z d 1) eta tau L
    (zero_lt_one.trans hZ) hL0 (by simpa [outerNorms] using hE) (by simpa [outerNorms] using hG) hL
  have hb:=(mem_nonzeroChildFrequencyBall _ (actualSecondMultiplier_ne_zero p x) _ _).mp (hgate x hxs)
  exact (mem_nonzeroChildFrequencyBall _ (actualSecondMultiplier_ne_zero p x) _ _).mpr ⟨hb.1,hb.2.trans hr⟩

end SevenEighths.InverseSecondUniformCutoff
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

lemma original_numeric_gates (extra : CubeCoordinates ι→Finset ι)
    (original : Finset (Source ι Jo)) (negative : Bool) (J : Finset σ)
    (lists : σ→Finset ι) (pool : Finset ι) (cutoff : Finset ι→Finset ι→ℝ)
    (B A C Q JL JU D : ℝ)
    (hB₁ : ∀y∈original,‖eisEmbedding (primeProduct p y.cube.support y.cube.leftExponent)‖^2≤B)
    (hB₂ : ∀y∈original,‖eisEmbedding (primeProduct p y.cube.support y.cube.rightExponent)‖^2≤B)
    (hA : ∀y∈original,primeProductNorm p (cubeActiveSupport y.cube.support
      (fun i=>y.cube.leftExponent i+y.cube.rightExponent i) y.cube.leftBit y.cube.rightBit)≤A)
    (hC : ∀y∈original,primeProductNorm p y.firstCommon≤C)
    (hQ : ∀y∈original,primeProductNorm p y.quotientSupport≤Q)
    (hJ : ∀y∈original,JL≤‖eisEmbedding (jLabel p y.cube.support
      (fun i=>y.cube.leftExponent i+y.cube.rightExponent i) y.cube.leftBit y.cube.rightBit)‖^2 ∧
      ‖eisEmbedding (jLabel p y.cube.support (fun i=>y.cube.leftExponent i+y.cube.rightExponent i)
        y.cube.leftBit y.cube.rightBit)‖^2≤JU)
    (hD : ∀y∈original,primeProductNorm p y.firstDivisor≤D) :
    ∀x∈retainedSource p extra original negative J lists pool cutoff,
      ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤B ∧
      ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤B ∧
      primeProductNorm p (cubeActiveSupport x.cube.support (fun i=>x.cube.leftExponent i+x.cube.rightExponent i)
        x.cube.leftBit x.cube.rightBit)≤A ∧ primeProductNorm p x.firstCommon≤C ∧
      (Ideal.absNorm x.quotient:ℝ)≤Q ∧
      JL≤‖eisEmbedding (jLabel p x.cube.support (fun i=>x.cube.leftExponent i+x.cube.rightExponent i)
        x.cube.leftBit x.cube.rightBit)‖^2 ∧
      ‖eisEmbedding (jLabel p x.cube.support (fun i=>x.cube.leftExponent i+x.cube.rightExponent i)
        x.cube.leftBit x.cube.rightBit)‖^2≤JU ∧
      primeProductNorm p x.firstDivisor≤D := by
  intro x hx
  obtain ⟨y,hy,hb,hc,hd,hq,ho⟩ := original_coordinates p extra original negative J lists pool cutoff x hx
  rw [hb,hc,hd,hq]
  refine ⟨hB₁ y hy,hB₂ y hy,hA y hy,hC y hy,?_,(hJ y hy).1,(hJ y hy).2,hD y hy⟩
  simpa only [sourceIdeal,←eisEmbedding_norm_sq_eq_absNorm_span,primeProductNorm] using hQ y hy

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

omit hp [∀i,(Ideal.span {p i}).IsMaximal] in
omit [DecidableEq ι] in
lemma geometrySource_gate {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn)) (b X : ℝ) :
    ∀x∈geometrySource p source b X,
      primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap≤b*X :=
  fun _x hx=>(Finset.mem_filter.mp hx).2

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

lemma supported_uniform_frequency_gate
    (extra : CubeCoordinates ι→Finset ι) (original : Finset (Source ι Jo))
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (pool : Finset ι)
    (Z delta eta L Y tau b X : ℝ) :
    ∀x∈supportedRetainedSource p extra original negative J lists pool
      (fun G E=>uniformSecondRadius p Z delta eta G E L Y (Z^tau)) b X,
      x.second.frequency∈nonzeroChildFrequencyBall (actualSecondMultiplier p x)
        (uniformSecondRadius p Z delta eta x.second.sourceCommon x.second.divisor L Y (Z^tau)) := by
  intro x hx
  exact ((mem_unifiedSource p pool _ _ x).mp
    (supported_subset p extra original negative J lists pool _ b X hx)).2.2.2.2

theorem supported_cell_row_gates (hp : ∀i,p i≠0)
    (extra : CubeCoordinates ι→Finset ι) (original : Finset (Source ι Jo))
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (pool : Finset ι)
    (Z M r ell V delta A B j t eta tau L b X : ℝ)
    (hZ : 1<Z) (heta : 0≤eta) (hbin : 2≤Z^eta) (hL0 : 0≤L)
    (hL : L≤Z^(r-A-B-t+4*eta)) :
    let source := supportedRetainedSource p extra original negative J lists pool
      (fun G E=>uniformSecondRadius p Z delta eta G E L
        (Z^(firstPhysicalHeight M r ell V delta B j+12*eta+tau)) (Z^tau)) b X
    (∀x∈source,x.second.frequency∈nonzeroChildFrequencyBall (actualSecondMultiplier p x)
      (actualCellRowRadius Z M ell A t V j eta (index p x))) ∧
    (∀d∈keys p source,0≤actualCellRowExponent Z M ell A t V j eta d) := by
  intro source
  have hgates := actual_cell_uniform_source_gates p hp source Z M r ell V delta A B j t eta tau L
    hZ heta hbin hL0 hL (supported_uniform_frequency_gate p extra original negative J lists pool Z delta eta L _ tau b X)
  refine ⟨?_,actual_cell_radius_nonnegative_on_keys p source Z M ell A t V j eta hZ hgates⟩
  intro x hx
  exact hgates (index p x) x (Finset.mem_filter.mpr ⟨hx,rfl⟩)

end SevenEighths.InverseMomentGlobalRetainedGates
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.GlobalRetainedGatesCaps
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
variable (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]

include hp in
omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
lemma uniform_radius_cap (G E : Finset ι) (hEG : E⊆G)
    (Z delta eta L Y tau Lcol LY : ℝ) (hZ : 0<Z) (hL : 0≤L) (hY : 0<Y)
    (hLc : L≤Z^Lcol) (hYi : Y⁻¹≤Z^LY) :
    uniformSecondRadius p Z delta eta G E L Y (Z^tau)≤
      Z^(delta+eta+2*Lcol+tau+LY) := by
  have hr : primeProductNorm p E/primeProductNorm p G≤1 :=
    (div_le_one (primeProductNorm_pos p hp G)).mpr (primeProductNorm_mono p hp hEG)
  have hr0 : 0≤primeProductNorm p E/primeProductNorm p G := by
    exact div_nonneg (primeProductNorm_pos p hp E).le (primeProductNorm_pos p hp G).le
  have hs : (primeProductNorm p E/primeProductNorm p G)^2≤1 := pow_le_one₀ hr0 hr
  unfold uniformSecondRadius
  rw [div_eq_mul_inv]
  calc
    _ ≤ Z^(delta+eta)*1*(Z^Lcol)^2*Z^tau*Z^LY := by gcongr
    _ = _ := by
      rw [mul_one,←Real.rpow_mul_natCast hZ.le]
      repeat rw [←Real.rpow_add hZ]
      congr 1
      norm_num
      ring

lemma bare_frequency_norm_le (a k : O) (ha : a≠0) :
    ‖eisEmbedding k‖^2≤‖eisEmbedding (a*k)‖^2 := by
  have hh := element_norm_ge_one a ha
  rw [map_mul,norm_mul,mul_pow]
  exact le_mul_of_one_le_left (sq_nonneg _) hh

include hp in

theorem supported_outer_caps
    (extra : CubeCoordinates ι→Finset ι) (original : Finset (Source ι Jo))
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (pool : Finset ι)
    (Z delta eta L Y tau b X Lcol LY Lcap : ℝ)
    (hZ : 1≤Z) (hL : 0≤L) (hY : 0<Y) (hLc : L≤Z^Lcol) (hYi : Y⁻¹≤Z^LY)
    (hgeom : b*X≤Z^Lcap) (hphysical : delta+eta+2*Lcol+tau+LY≤Lcap) :
    ∀x∈supportedRetainedSource p extra original negative J lists pool
      (fun G E=>uniformSecondRadius p Z delta eta G E L Y (Z^tau)) b X,
      ∀i,outerNorms p x i≤Z^Lcap := by
  intro x hx i
  have hret := supported_subset p extra original negative J lists pool _ b X hx
  have hm := (mem_unifiedSource p pool _ _ x).mp hret
  have hg : primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap≤Z^Lcap :=
    (geometrySource_gate p _ b X x hx).trans hgeom
  have hG : primeProductNorm p x.second.sourceCommon≤Z^Lcap :=
    (le_mul_of_one_le_right (primeProductNorm_pos p hp _).le (primeProductNorm_ge_one p hp _)).trans hg
  have hV : primeProductNorm p x.second.overlap≤Z^Lcap :=
    (le_mul_of_one_le_left (primeProductNorm_pos p hp _).le (primeProductNorm_ge_one p hp _)).trans hg
  fin_cases i
  · exact hG
  · exact (primeProductNorm_mono p hp hm.2.2.1).trans hG
  · exact hV
  · have hb := (mem_nonzeroChildFrequencyBall _ (actualSecondMultiplier_ne_zero p x) _ _).mp hm.2.2.2.2
    exact (bare_frequency_norm_le _ _ (actualSecondMultiplier_ne_zero p x)).trans
      (hb.2.trans ((uniform_radius_cap p hp _ _ hm.2.2.1 Z delta eta L Y tau Lcol LY
        (zero_lt_one.trans_le hZ) hL hY hLc hYi).trans
        (Real.rpow_le_rpow_of_exponent_le hZ hphysical)))

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

end SevenEighths.InverseMomentGlobalRetainedGates
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.GlobalRetainedGatesBudget
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMomentGlobalRetainedGates
open InverseMoment InverseInitialArithmetic InverseSecondSourceBlocks
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
local notation "O" => ActualEisensteinCubic.O

 theorem source_cell_exponent_cap {ι : Type*} [DecidableEq ι]
    (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (hk : ∀x∈source,x.second.frequency≠0) (Z Lcap : ℝ) (hZ : 1<Z)
    (hnorm : ∀x∈source,∀i,outerNorms p x i≤Z^Lcap)
    (d : BlockIndex) (hd : d∈keys p source) (i : Fin 4) :
    secondCellExponent Z d i≤Lcap := by
  obtain ⟨x,hx⟩ := (mem_keys_iff p source d).mp hd
  have hs : scales d i≤outerNorms p x i := by
    simpa only [one_mul,scales] using (le_div_iff₀ (dyadScale_pos _)).mp (cell_ratios p hp source hk d x hx i).1
  apply (Real.rpow_le_rpow_left_iff hZ).mp
  rw [second_cell_scale_rpow Z d i hZ]
  exact hs.trans (hnorm x (cell_subset p source d hx) i)

theorem source_cell_mass_gate {ι : Type*} [DecidableEq ι]
    (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (hk : ∀x∈source,x.second.frequency≠0)
    (Z Lcap ell Ractive j t eta eps pi : ℝ) (hZ : 1<Z) (hj : 0≤j) (heps : 0≤eps)
    (hnorm : ∀x∈source,∀i,outerNorms p x i≤Z^Lcap)
    (hbudget : eps*(ell+Ractive/2+t+Lcap+11*eta/2)≤pi) :
    ∀d∈keys p source,eps*(secondCount ell Ractive j t
      (secondCellExponent Z d 0) (secondCellExponent Z d 1)+11*eta/2)≤pi := by
  intro d hd
  have hg := source_cell_exponent_cap p hp source hk Z Lcap hZ hnorm d hd 0
  have htheta := secondCellExponent_nonneg Z d 1 hZ
  apply le_trans (mul_le_mul_of_nonneg_left (show
    secondCount ell Ractive j t (secondCellExponent Z d 0) (secondCellExponent Z d 1)+11*eta/2≤
      ell+Ractive/2+t+Lcap+11*eta/2 by unfold secondCount; linarith) heps) hbudget

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

include hp in

theorem retained_label_numeric (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (k : SourceIndex) (l j : ℕ) (Z ell eta : ℝ) (hZ : 1<Z) (heta : 0≤eta) (hbin : 2≤Z^eta)
    (hQ : ∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta))
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (cutoff : Finset ι→Finset ι→ℝ) (b X : ℝ) :
    let source := supportedRetainedSource p (extra negative)
      (InverseFirstGlobalCaps.labelParentCell p pool Q (fun _ _=>1) k l j) negative J lists pool cutoff b X
    ∀x∈source,
      ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Z^(ell+eta) ∧
      ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Z^(ell+eta) ∧
      primeProductNorm p (cubeActiveSupport x.cube.support
        (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)
        ≤Z^(InverseFirstGlobalCaps.dyadicExponent Z (k 4)+eta) ∧
      primeProductNorm p x.firstCommon≤Z^(InverseFirstGlobalCaps.dyadicExponent Z (k 2)+eta) ∧
      (Ideal.absNorm x.quotient:ℝ)≤Z^(InverseFirstGlobalCaps.dyadicExponent Z l+eta) ∧
      Z^(InverseFirstGlobalCaps.dyadicExponent Z j-eta)≤
        ‖eisEmbedding (jLabel p x.cube.support (fun i=>x.cube.leftExponent i+x.cube.rightExponent i)
          x.cube.leftBit x.cube.rightBit)‖^2 ∧
      ‖eisEmbedding (jLabel p x.cube.support (fun i=>x.cube.leftExponent i+x.cube.rightExponent i)
        x.cube.leftBit x.cube.rightBit)‖^2≤Z^(InverseFirstGlobalCaps.dyadicExponent Z j+eta) ∧
      primeProductNorm p x.firstDivisor≤Z^(InverseFirstGlobalCaps.dyadicExponent Z (k 3)+eta) := by
  intro source x hx
  have h := label_parent_bounds p hp pool Q k l j Z ell eta hZ heta hbin hQ
  exact original_numeric_gates p (extra negative) _ negative J lists pool cutoff _ _ _ _ _ _ _
    (fun y hy=>(h y hy).1) (fun y hy=>(h y hy).2.1) (fun y hy=>(h y hy).2.2.1)
    (fun y hy=>(h y hy).2.2.2.1) (fun y hy=>(h y hy).2.2.2.2.1)
    (fun y hy=>⟨(h y hy).2.2.2.2.2.1,(h y hy).2.2.2.2.2.2.1⟩)
    (fun y hy=>(h y hy).2.2.2.2.2.2.2) x (supported_subset p _ _ negative J lists pool cutoff b X hx)

end SevenEighths.InverseMomentFirstLabelCell
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.FirstLabelCellStepSource
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMomentFirstLabelCell
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstChildWindows InverseFirstPriorityParents InverseFirstGlobalParents
open InverseMomentGlobalRetainedGates InverseInitialArithmetic InverseSecondSourceBlocks
open InverseSecondUniformCutoff
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]

variable (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]

include hp in
theorem source_valid (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l j : ℕ)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (Z M r ell V eta tau window b : ℝ) :
    ActualSecondSourceConditions p (source p pool Q k l j negative J lists Z M r ell V eta tau window b) :=
  supported_conditions p hp _ _ (label_parent_valid p pool Q k l j) (fun y _hy=>extra_subset negative y.cube)
    negative J lists pool _ b _

lemma source_frequency_ne_zero (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l j : ℕ)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (Z M r ell V eta tau window b : ℝ) :
    ∀x∈source p pool Q k l j negative J lists Z M r ell V eta tau window b,x.second.frequency≠0 :=
  supported_frequency_ne_zero p _ _ negative J lists pool _ b _

lemma source_geometry (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l j : ℕ)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (Z M r ell V eta tau window b : ℝ) :
    ∀x∈source p pool Q k l j negative J lists Z M r ell V eta tau window b,
      primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap≤b*columnScale Z r k l negative :=
  geometrySource_gate p _ b _

include hp in
theorem source_row_gates (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l j : ℕ)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (Z M r ell V eta tau window b : ℝ)
    (hZ : 1<Z) (heta : 0≤eta) (hbin : 2≤Z^eta) (hwindow : Real.exp window≤Z^(4*eta)) :
    let S := source p pool Q k l j negative J lists Z M r ell V eta tau window b
    (∀x∈S,x.second.frequency∈nonzeroChildFrequencyBall (actualSecondMultiplier p x)
      (actualCellRowRadius Z M ell (columnA Z k negative) (exponent Z l) V (exponent Z j) eta (index p x))) ∧
    (∀d∈keys p S,0≤actualCellRowExponent Z M ell (columnA Z k negative) (exponent Z l) V (exponent Z j) eta d) := by
  intro S
  have hz : 0<Z := zero_lt_one.trans hZ
  have hc : columnScale Z r k l negative*Real.exp window≤
      Z^(r-columnA Z k negative-exponent Z (k 2)-exponent Z l+4*eta) := by
    unfold columnScale
    rw [Real.rpow_add hz]
    exact mul_le_mul_of_nonneg_left hwindow (Real.rpow_nonneg hz.le _)
  exact supported_cell_row_gates p hp _ _ negative J lists pool Z M r ell V (exponent Z (k 3))
    (columnA Z k negative) (exponent Z (k 2)) (exponent Z j) (exponent Z l) eta tau
    (columnScale Z r k l negative*Real.exp window) b (columnScale Z r k l negative)
    hZ heta hbin (by unfold columnScale;positivity) hc

include hp in
theorem source_outer_caps (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l j : ℕ)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (Z M r ell V eta tau window b Lcol LY Lcap : ℝ)
    (hZ : 1<Z)
    (hcol : columnScale Z r k l negative*Real.exp window≤Z^Lcol)
    (hYi : (firstCellRadius Z M r ell V eta tau k j)⁻¹≤Z^LY)
    (hgeom : b*columnScale Z r k l negative≤Z^Lcap)
    (hphysical : exponent Z (k 3)+eta+2*Lcol+tau+LY≤Lcap) :
    ∀x∈source p pool Q k l j negative J lists Z M r ell V eta tau window b,
      ∀i,outerNorms p x i≤Z^Lcap := by
  exact supported_outer_caps p hp _ _ negative J lists pool Z (exponent Z (k 3)) eta
    (columnScale Z r k l negative*Real.exp window) (firstCellRadius Z M r ell V eta tau k j)
    tau b (columnScale Z r k l negative) Lcol LY Lcap hZ.le
    (by unfold columnScale;positivity) (by unfold firstCellRadius;exact Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)
    hcol hYi hgeom hphysical

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
theorem source_mass_gate (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l j : ℕ)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (Z M r ell V eta tau window b Lcol LY Lcap eps pi : ℝ)
    (hZ : 1<Z) (heps : 0≤eps)
    (hcol : columnScale Z r k l negative*Real.exp window≤Z^Lcol)
    (hYi : (firstCellRadius Z M r ell V eta tau k j)⁻¹≤Z^LY)
    (hgeom : b*columnScale Z r k l negative≤Z^Lcap)
    (hphysical : exponent Z (k 3)+eta+2*Lcol+tau+LY≤Lcap)
    (hbudget : eps*(ell+exponent Z (k 4)/2+exponent Z l+Lcap+11*eta/2)≤pi) :
    let S := source p pool Q k l j negative J lists Z M r ell V eta tau window b
    ∀d∈keys p S,eps*(secondCount ell (exponent Z (k 4)) (exponent Z j) (exponent Z l)
      (secondCellExponent Z d 0) (secondCellExponent Z d 1)+11*eta/2)≤pi := by
  intro S
  exact source_cell_mass_gate p hp S (source_frequency_ne_zero p pool Q k l j negative J lists Z M r ell V eta tau window b)
    Z Lcap ell (exponent Z (k 4)) (exponent Z j) (exponent Z l) eta eps pi hZ
    (dyadic_exponent_nonneg Z hZ _) heps
    (source_outer_caps p hp pool Q k l j negative J lists Z M r ell V eta tau window b Lcol LY Lcap
      hZ hcol hYi hgeom hphysical) hbudget

end SevenEighths.InverseMomentFirstLabelCell
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.FirstLabelCellStepData
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
theorem source_step_arithmetic_oai (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l j : ℕ)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (Z M r ell V eta tau window b Lcol LY Lcap eps pi : ℝ)
    (hZ : 1<Z) (heta : 0≤eta) (hbin : 2≤Z^eta) (heps : 0≤eps)
    (hwindow : Real.exp window≤Z^(4*eta))
    (hQ : ∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta))
    (hcol : columnScale Z r k l negative*Real.exp window≤Z^Lcol)
    (hYi : (firstCellRadius Z M r ell V eta tau k j)⁻¹≤Z^LY)
    (hgeom : b*columnScale Z r k l negative≤Z^Lcap)
    (hphysical : exponent Z (k 3)+eta+2*Lcol+tau+LY≤Lcap)
    (hbudget : eps*(ell+exponent Z (k 4)/2+exponent Z l+Lcap+11*eta/2)≤pi) :
    let S := source p pool Q k l j negative J lists Z M r ell V eta tau window b
    ActualSecondSourceConditions p S ∧
    (∀x∈S,x.second.frequency≠0) ∧
    (∀x∈S,x.second.frequency∈nonzeroChildFrequencyBall (actualSecondMultiplier p x)
      (actualCellRowRadius Z M ell (columnA Z k negative) (exponent Z l) V (exponent Z j) eta (index p x))) ∧
    (∀d∈keys p S,0≤actualCellRowExponent Z M ell (columnA Z k negative) (exponent Z l) V (exponent Z j) eta d) ∧
    (∀x∈S,
      ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Z^(ell+eta) ∧
      ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Z^(ell+eta) ∧
      primeProductNorm p (cubeActiveSupport x.cube.support
        (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)
        ≤Z^(exponent Z (k 4)+eta) ∧
      primeProductNorm p x.firstCommon≤Z^(exponent Z (k 2)+eta) ∧
      (Ideal.absNorm x.quotient:ℝ)≤Z^(exponent Z l+eta) ∧
      Z^(exponent Z j-eta)≤
        ‖eisEmbedding (jLabel p x.cube.support (fun i=>x.cube.leftExponent i+x.cube.rightExponent i)
          x.cube.leftBit x.cube.rightBit)‖^2 ∧
      ‖eisEmbedding (jLabel p x.cube.support (fun i=>x.cube.leftExponent i+x.cube.rightExponent i)
        x.cube.leftBit x.cube.rightBit)‖^2≤Z^(exponent Z j+eta) ∧
      primeProductNorm p x.firstDivisor≤Z^(exponent Z (k 3)+eta)) ∧
    (∀d,∀x∈cell p S d,(actualSecondChild p 1 1 x).2.1∈actualCellLabels p S d) ∧
    (∀d,∀I∈(actualCellLabels p S d).filter Squarefree,
      Squarefree I ∧ I≠0 ∧ (Ideal.absNorm I:ℝ)≤Z^(actualCellLabelExponent Z (exponent Z (k 2)) (exponent Z j) eta d)) ∧
    (∀x∈S,∀i,outerNorms p x i≤Z^Lcap) ∧
    (∀x∈S,primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap≤b*columnScale Z r k l negative) ∧
    (∀d∈keys p S,eps*(secondCount ell (exponent Z (k 4)) (exponent Z j) (exponent Z l)
      (secondCellExponent Z d 0) (secondCellExponent Z d 1)+11*eta/2)≤pi) := by
  intro S
  have hr := source_row_gates p hp pool Q k l j negative J lists Z M r ell V eta tau window b hZ heta hbin hwindow
  have hl := source_labels p hp pool Q k l j negative J lists Z M r ell V eta tau window b hZ heta hbin hQ
  exact ⟨source_valid p hp pool Q k l j negative J lists Z M r ell V eta tau window b,
    source_frequency_ne_zero p pool Q k l j negative J lists Z M r ell V eta tau window b,
    hr.1,hr.2,
    retained_label_numeric p hp pool Q k l j Z ell eta hZ heta hbin hQ negative J lists _ b _,
    hl.1,hl.2,
    source_outer_caps p hp pool Q k l j negative J lists Z M r ell V eta tau window b Lcol LY Lcap
      hZ hcol hYi hgeom hphysical,
    source_geometry p pool Q k l j negative J lists Z M r ell V eta tau window b,
    source_mass_gate p hp pool Q k l j negative J lists Z M r ell V eta tau window b Lcol LY Lcap eps pi
      hZ heps hcol hYi hgeom hphysical hbudget⟩

end SevenEighths.InverseMomentFirstLabelCell
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.SevenEighths.InverseMomentFirstLabelCell.source_step_arithmetic_oai.{u_1, u_2} := @OAI.SevenEighths.InverseMomentFirstLabelCell.source_step_arithmetic_oai.{u_1, u_2}
