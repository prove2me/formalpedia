-- Prove2me | solution 1 for OAI.SevenEighths.InverseMoment.original_dyadic_retained_budget
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T03:43:59.953152+00:00
-- url     : https://prove2.me/submissions/50cc7b21-a2ed-4210-be06-ab5b581d8d28

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIHecke78B019
import Theorems.Thm_OAI_SevenEighths_InverseMomentFirstOriginalProfile_original_refined_cell_physical_budget

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

lemma span_dvd_of_element_dvd {a b : O} (h : a ∣ b) :
    (Ideal.span {a} : Ideal O) ∣ Ideal.span {b} := by
  obtain ⟨c, rfl⟩ := h
  exact ⟨Ideal.span {c}, (Ideal.span_singleton_mul_span_singleton a c).symm⟩

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.CubeSource
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open InverseSecondFibers
open InverseInitialArithmetic (sourceIdeal sourceIdeal_gen sourcePrime )
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι] (p : ι → Eis)
  [∀ i, (Ideal.span {p i}).IsMaximal]

omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
lemma cubeRadical_span_dvd_product (B : Finset ι) (v : ι → ℕ)
    (hv : ∀ i ∈ B, 0 < v i) :
    sourceIdeal p B ∣ Ideal.span {primeProduct p B v} := by
  apply span_dvd_of_element_dvd
  change (∏ i ∈ B,p i) ∣ primeProduct p B v
  unfold primeProduct
  apply Finset.prod_dvd_prod_of_dvd
  intro i hi
  exact dvd_pow_self _ (Nat.ne_of_gt (hv i hi))

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.FirstPhysicalCutoff
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "O" => ActualEisensteinCubic.O

lemma firstPhysicalMultiplier_ne_zero {ι : Type*} (p : ι→O) (hp : ∀ i,p i≠0)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    (S : Finset ι) (v₁ v₂ : ι→ℕ) (ε₁ ε₂ : ι→Bool) (f : Ideal O) (hf : f≠0) :
    firstPhysicalMultiplier p S v₁ v₂ ε₁ ε₂ f≠0 :=
  mul_ne_zero (pow_ne_zero _ (ConcretePrimeRowBridge.idealGenerator_ne_zero f hf))
    (primeProduct_ne_zero p hp _ _)

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.FirstWholeMarkedColumns
namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
local notation "O" => ActualEisensteinCubic.O

theorem primeProductNorm_union_le_mul {ι : Type*} [DecidableEq ι]
    (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal] (A U : Finset ι) :
    primeProductNorm p (A∪U)≤primeProductNorm p A*primeProductNorm p U := by
  have he : A∪U=A∪(U\A) := by ext i;simp only [Finset.mem_union,Finset.mem_sdiff];tauto
  rw [he,primeProductNorm_union p A (U\A) Finset.disjoint_sdiff]
  exact mul_le_mul_of_nonneg_left (primeProductNorm_mono p hp Finset.sdiff_subset)
    (primeProductNorm_pos p hp A).le

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.CubeSupportNorm
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseInitialArithmetic
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι] (p : ι→O) (hp : ∀ i,p i≠0)

include hp in
theorem cube_whole_support_norm (b : CubeCoordinates ι) :
    primeProductNorm p b.support≤
      ‖eisEmbedding (primeProduct p b.support b.leftExponent)‖^2*
      ‖eisEmbedding (primeProduct p b.support b.rightExponent)‖^2 := by
  have hd := cubeRadical_span_dvd_product p b.support
    (fun i=>b.leftExponent i+b.rightExponent i) b.support_pos
  have hne : (Ideal.span {primeProduct p b.support (fun i=>b.leftExponent i+b.rightExponent i)}:Ideal O)≠0 :=
    Ideal.span_singleton_eq_bot.not.mpr (primeProduct_ne_zero p hp _ _)
  have hn := Nat.le_of_dvd (Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hne))
    (Ideal.absNorm_dvd_absNorm_of_le (Ideal.dvd_iff_le.mp hd))
  have he : (Ideal.absNorm (sourceIdeal p b.support):ℝ)=primeProductNorm p b.support := by
    simpa only [sourceIdeal,primeProductNorm,map_prod] using
      (eisEmbedding_norm_sq_eq_absNorm_span (∏i∈b.support,p i)).symm
  have hh : primeProductNorm p b.support≤
      ‖eisEmbedding (primeProduct p b.support (fun i=>b.leftExponent i+b.rightExponent i))‖^2 := by
    rw [eisEmbedding_norm_sq_eq_absNorm_span,←he]
    exact_mod_cast hn
  simpa only [primeProduct_add,map_mul,norm_mul,mul_pow] using hh

include hp in
theorem cube_whole_support_dyad (b : CubeCoordinates ι) (B : ℝ) (hB : 0≤B)
    (hl : ‖eisEmbedding (primeProduct p b.support b.leftExponent)‖^2≤B)
    (hr : ‖eisEmbedding (primeProduct p b.support b.rightExponent)‖^2≤B) :
    primeProductNorm p b.support≤B^2 :=
  (cube_whole_support_norm p hp b).trans ((mul_le_mul hl hr (sq_nonneg _) hB).trans_eq (pow_two B).symm)

end SevenEighths.InverseMoment

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.FirstRetainedFamily
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
noncomputable section
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]

theorem mem_firstRetainedSource (p : ι→O) (labels : Finset (Ideal O)) (b : CubeCoordinates ι) (Y : ℝ)
    (x : Ideal O×O) :
    x∈firstRetainedSource p labels b Y ↔ x.1∈labels ∧ x.2∈nonzeroChildFrequencyBall
      (firstPhysicalMultiplier p b.support b.leftExponent b.rightExponent b.leftBit b.rightBit x.1) Y := by
  rcases x with ⟨f,h⟩
  simp [firstRetainedSource]

variable (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

end
end SevenEighths.InverseMoment

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

end SevenEighths.InverseSecondSourceBlocks

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.FirstChildWindowsCells
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMomentFirstChildWindows
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels
open InverseSecondSourceBlocks (dyadIndex dyadScale dyadScale_pos dyadIndex_bounds)
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

lemma rawScales_pos (k : SourceIndex) (l : ℕ) (T₁ T₂ : ℝ) (h₁ : 0<T₁) (h₂ : 0<T₂) :
    ∀i,0< rawScales k l T₁ T₂ i := by
  intro i
  fin_cases i <;> first | exact dyadScale_pos _ | exact h₁ | exact h₂

lemma sourceNorms_ge_one {κ : Type*} (A₁ A₂ C R : κ→ℝ) (d h : κ→O) (x : κ)
    (hA₁ : 1≤A₁ x) (hA₂ : 1≤A₂ x) (hC : 1≤C x) (hR : 1≤R x)
    (hd : d x≠0) (hh : h x≠0) : ∀i,1≤ sourceNorms A₁ A₂ C R d h x i := by
  intro i
  fin_cases i
  · exact hA₁
  · exact hA₂
  · exact hC
  · exact EisensteinSchwartzPoisson.one_le_eisenstein_norm_sq _ hd
  · exact hR
  · exact EisensteinSchwartzPoisson.one_le_eisenstein_norm_sq _ hh

end SevenEighths.InverseMomentFirstChildWindows
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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.PriorityProfile
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseSecondPrincipalCaller InverseSecondProfileUniform
open FourierBridge CompletedHeight SecondPassIntegration
local notation "O" => ActualEisensteinCubic.O

theorem priorityLogWindow_support (om:𝓢(ℝ,ℂ)) (a b:ℝ) (ha:0<a)
    (hs:Function.support om⊆Set.Icc a b) (negative:Bool) :
    Function.support (priorityLogWindow om a b ha hs negative)⊆
      Set.Icc (-(|Real.log a|+|Real.log b|)) (|Real.log a|+|Real.log b|) := by
  intro y hy
  have hn:om (Real.exp y)≠0:=by
    cases negative <;> simpa only [priorityLogWindow,Bool.false_eq_true,ite_true,ite_false,
      conjugateProfile_apply,CubicReflectionKernel.logSchwartz_apply,Function.mem_support,star_ne_zero] using hy
  have hh:=hs hn
  have hlo:=Real.log_le_log ha hh.1
  have hhi:=Real.log_le_log (Real.exp_pos y) hh.2
  rw [Real.log_exp] at hlo hhi
  constructor
  · linarith [neg_abs_le (Real.log a),abs_nonneg (Real.log b)]
  · linarith [le_abs_self (Real.log b),abs_nonneg (Real.log a)]

end SevenEighths.InverseMoment

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.FirstOriginalProfileData
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMomentFirstOriginalProfile
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
open CompletedHeight FourierBridge
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
variable (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]

include hp in
theorem original_source_positive (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (labels : Finset (Ideal O)) (Y : ℝ) :
    ∀x∈firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun k=>k.1) Y,
      0<leftNorm p x ∧ 0< rightNorm p x ∧ 0<commonNorm p x ∧ 0<activeNorm p x ∧
      divisorElement p x.1≠0 ∧ x.2.2≠0 := by
  intro x hx
  have hm := (Finset.mem_sigma.mp hx).2
  have hk := ((mem_firstRetainedSource p labels x.1.1 Y x.2).mp hm).2
  refine ⟨?_,?_,primeProductNorm_pos p hp _,primeProductNorm_pos p hp _,?_,(Finset.mem_erase.mp hk).1⟩
  · exact sq_pos_of_pos (norm_pos_iff.mpr (ConcreteTraceCRT.eisEmbedding_ne_zero
      (primeProduct_ne_zero p hp _ _)))
  · exact sq_pos_of_pos (norm_pos_iff.mpr (ConcreteTraceCRT.eisEmbedding_ne_zero
      (primeProduct_ne_zero p hp _ _)))
  · exact primeSubsetGenerator_ne_zero _ _

include hp in
theorem original_source_norms_ge_one (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (labels : Finset (Ideal O)) (Y : ℝ) :
    ∀x∈firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun k=>k.1) Y,
      ∀i,1≤InverseMomentFirstChildWindows.sourceNorms (leftNorm p) (rightNorm p) (commonNorm p)
        (activeNorm p) (fun x=>divisorElement p x.1) (fun x=>x.2.2) x i := by
  intro x hx
  have hh := original_source_positive p hp pool Q labels Y x hx
  apply InverseMomentFirstChildWindows.sourceNorms_ge_one
  · exact element_norm_ge_one _ (primeProduct_ne_zero p hp _ _)
  · exact element_norm_ge_one _ (primeProduct_ne_zero p hp _ _)
  · exact primeProductNorm_ge_one p hp _
  · exact primeProductNorm_ge_one p hp _
  · exact hh.2.2.2.2.1
  · exact hh.2.2.2.2.2

theorem actual_old_profile (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a)
    (hs : Function.support om⊆Set.Icc a b) (theta x : ℝ) (hx : 0<x) :
    InverseMomentFirstProfileUniform.positiveSource (priorityLogWindow om a b ha hs false) 1 theta x=
      normTwistedSource om theta x ∧
    InverseMomentFirstProfileUniform.positiveSource (priorityLogWindow om a b ha hs true) 1 (-theta) x=
      star (normTwistedSource om theta x) := by
  constructor
  · simp [InverseMomentFirstProfileUniform.positiveSource,priorityLogWindow,
      CubicReflectionKernel.logSchwartz_apply,Real.exp_log hx,normTwistedSource]
  · simp [InverseMomentFirstProfileUniform.positiveSource,priorityLogWindow,
      SecondPassIntegration.conjugateProfile_apply,CubicReflectionKernel.logSchwartz_apply,
      Real.exp_log hx,normTwistedSource,SecondPassIntegration.logPhase_conjugate]

end SevenEighths.InverseMomentFirstOriginalProfile
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.FirstOriginalProfileIdentity
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMomentFirstOriginalProfile
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open CompletedHeight FourierBridge
open InverseMomentFirstProfileUniform
local notation "O" => ActualEisensteinCubic.O
variable {ι κ : Type*} [DecidableEq ι]
variable (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
variable (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

include hp in
lemma physical_rows_congr_positive (F : Finset ι) (selector C₁ C₂ : Finset ι→ℂ)
    (W₁ W₂ V₁ V₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (A₁ A₂ C R K : ℝ) (d h : O)
    (hA₁ : 0<A₁) (hA₂ : 0<A₂) (hC : 0<C)
    (h₁ : ∀x,0<x→W₁ x=V₁ x) (h₂ : ∀x,0<x→W₂ x=V₂ x) :
    firstBlockedPhysicalRows p hg F selector C₁ C₂ W₁ W₂ Φ A₁ A₂ C R K d h=
      firstBlockedPhysicalRows p hg F selector C₁ C₂ V₁ V₂ Φ A₁ A₂ C R K d h := by
  unfold firstBlockedPhysicalRows
  apply Finset.sum_congr rfl
  intro j hj
  have he₁ := h₁ (A₁*C*primeProductNorm p j.2.1*primeProductNorm p j.2.2.1)
    (mul_pos (mul_pos (mul_pos hA₁ hC) (primeProductNorm_pos p hp _)) (primeProductNorm_pos p hp _))
  have he₂ := h₂ (A₂*C*primeProductNorm p j.2.1*primeProductNorm p j.2.2.2)
    (mul_pos (mul_pos (mul_pos hA₂ hC) (primeProductNorm_pos p hp _)) (primeProductNorm_pos p hp _))
  simp [firstNormProfile,firstCommonNorms,he₁,he₂]

include hp in
lemma physical_family_congr_positive (S : Finset κ) (F : Finset ι)
    (selector C₁ C₂ : κ→Finset ι→ℂ) (w : κ→ℂ)
    (W₁ W₂ V₁ V₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (A₁ A₂ C R : κ→ℝ) (K : ℝ)
    (d h : κ→O) (s : Fin 9→ℝ) (hs : ∀i,0<s i)
    (hpos : ∀x∈S,0<A₁ x ∧ 0<A₂ x ∧ 0<C x)
    (h₁ : ∀x,0<x→W₁ x=V₁ x) (h₂ : ∀x,0<x→W₂ x=V₂ x) :
    firstFamilyPhysicalRows p hg S F selector C₁ C₂ w W₁ W₂ Φ A₁ A₂ C R K d h s=
      firstFamilyPhysicalRows p hg S F selector C₁ C₂ w V₁ V₂ Φ A₁ A₂ C R K d h s := by
  unfold firstFamilyPhysicalRows
  apply Finset.sum_congr rfl
  intro x hx
  congr 1
  exact physical_rows_congr_positive p hp hg F (selector x) (C₁ x) (C₂ x) _ _ _ _ Φ
    (A₁ x) (A₂ x) (C x) (R x) K (d x) (h x) (hpos x hx).1 (hpos x hx).2.1 (hpos x hx).2.2
    (fun y hy=>h₁ _ (div_pos hy (mul_pos (mul_pos (mul_pos (hs 0) (hs 2)) (hs 5)) (hs 7))))
    (fun y hy=>h₂ _ (div_pos hy (mul_pos (mul_pos (mul_pos (hs 1) (hs 2)) (hs 5)) (hs 8))))

include hp in

theorem original_family_profiles (S : Finset κ) (F : Finset ι)
    (selector C₁ C₂ : κ→Finset ι→ℂ) (w : κ→ℂ)
    (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a) (hsom : Function.support om⊆Set.Icc a b)
    (Φ : 𝓢(ℝ,ℂ)) (A₁ A₂ C R : κ→ℝ) (K X theta : ℝ)
    (d h : κ→O) (s : Fin 9→ℝ) (hs : ∀i,0<s i)
    (hpos : ∀x∈S,0<A₁ x ∧ 0<A₂ x ∧ 0<C x)
    (hX : 0<X) (hleft : s 0*s 2*s 5*s 7=X) (hright : s 1*s 2*s 5*s 8=X) :
    firstFamilyPhysicalRows p hg S F selector C₁ C₂ w
      (fun y=>star (normTwistedSource om theta ((s 0*s 2*s 5*s 7)*y/X)))
      (fun y=>normTwistedSource om theta ((s 1*s 2*s 5*s 8)*y/X)) Φ A₁ A₂ C R K d h s=
    firstFamilyPhysicalRows p hg S F selector C₁ C₂ w
      (positiveSource (priorityLogWindow om a b ha hsom true) 1 (-theta))
      (positiveSource (priorityLogWindow om a b ha hsom false) 1 theta) Φ A₁ A₂ C R K d h s := by
  apply physical_family_congr_positive p hp hg S F selector C₁ C₂ w _ _ _ _ Φ A₁ A₂ C R K d h s hs hpos
  · intro y hy
    rw [hleft,mul_div_cancel_left₀ y (ne_of_gt hX)]
    exact (actual_old_profile om a b ha hsom theta y hy).2.symm
  · intro y hy
    rw [hright,mul_div_cancel_left₀ y (ne_of_gt hX)]
    exact (actual_old_profile om a b ha hsom theta y hy).1.symm

end SevenEighths.InverseMomentFirstOriginalProfile
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.FirstOriginalProfileAssembly
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMomentFirstOriginalProfile
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstChildWindows CompletedHeight
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
variable (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
variable (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
variable (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem original_retained_sum (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (labels : Finset (Ideal O)) (β : Ideal O→(ι→₀ℕ)→ℂ) (Ψ : O→*ℂ) (m : O)
    (mark : (ι→₀ℕ)→Finset ι→ℂ) (W : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (K Y : ℝ)
    (R : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ) (s : Fin 9→ℝ) (hs : ∀i,0<s i) :
    originalRetainedFamily p hp hcop hg pool Q labels β Ψ m mark W Φ K Y R s=
      ∑x∈firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) Y,
        ∑j∈firstCommonIndices pool,sourceSummand p hp hcop hg β R Ψ m mark W Φ K x j := by
  have hleft : s 0*s 2*s 5*s 7≠0 := ne_of_gt (mul_pos (mul_pos (mul_pos (hs 0) (hs 2)) (hs 5)) (hs 7))
  have hright : s 1*s 2*s 5*s 8≠0 := ne_of_gt (mul_pos (mul_pos (mul_pos (hs 1) (hs 2)) (hs 5)) (hs 8))
  simp only [originalRetainedFamily,firstFamilyPhysicalRows,firstBlockedPhysicalRows,
    Finset.mul_sum,sourceSummand,weight,coefficient,leftNorm,rightNorm,commonNorm,activeNorm,divisorElement,
    Bool.false_eq_true,ite_true,ite_false,one_mul]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro j hj
  simp only [firstNormProfile,mul_div_cancel₀ _ hleft,mul_div_cancel₀ _ hright]
  ring

end SevenEighths.InverseMomentFirstOriginalProfile
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.FirstLiveCaps
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMomentFirstLiveCaps
open InverseMoment InverseMomentFirstOriginalProfile ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
local notation "O"=>ActualEisensteinCubic.O

lemma factor_four_bound (a b c d L:ℝ)(ha:1≤a)(hb:1≤b)(hc:1≤ c)(hd:1≤d)
    (h:a*b*c*d≤L): a≤L ∧ b≤L ∧ c≤L ∧ d≤L:=by
  have ha0:0≤a:=zero_le_one.trans ha
  have hb0:0≤b:=zero_le_one.trans hb
  have hc0:0≤ c:=zero_le_one.trans hc
  have hd0:0≤d:=zero_le_one.trans hd
  have hab:1≤a*b:=ha.trans (le_mul_of_one_le_right ha0 hb)
  have habc:1≤a*b*c:=hab.trans (le_mul_of_one_le_right (mul_nonneg ha0 hb0) hc)
  have habd:1≤a*b*d:=hab.trans (le_mul_of_one_le_right (mul_nonneg ha0 hb0) hd)
  have ha':a≤a*b*c*d:=by
    calc
      a≤a*b:=le_mul_of_one_le_right ha0 hb
      _≤a*b*c:=le_mul_of_one_le_right (mul_nonneg ha0 hb0) hc
      _≤a*b*c*d:=le_mul_of_one_le_right (mul_nonneg (mul_nonneg ha0 hb0) hc0) hd
  have hb':b≤a*b*c*d:=by
    calc
      b≤a*b:=le_mul_of_one_le_left hb0 ha
      _≤a*b*c:=le_mul_of_one_le_right (mul_nonneg ha0 hb0) hc
      _≤a*b*c*d:=le_mul_of_one_le_right (mul_nonneg (mul_nonneg ha0 hb0) hc0) hd
  have hc':c≤a*b*c*d:=by
    calc
      c≤a*b*c:=le_mul_of_one_le_left hc0 hab
      _≤a*b*c*d:=le_mul_of_one_le_right (mul_nonneg (mul_nonneg ha0 hb0) hc0) hd
  exact ⟨ha'.trans h,hb'.trans h,hc'.trans h,(le_mul_of_one_le_left hd0 habc).trans h⟩

theorem first_profile_live_factors (W:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(K L:ℝ)(q:Fin 9→ℝ)
    (hq:∀i,1≤q i)(hW:∀x,W x≠0→x≤L)
    (hn:firstNormProfile (fun y=>star (W y)) W Φ (fun _ _=>1) K q≠0):
    q 0≤L ∧ q 1≤L ∧ q 2≤L ∧ q 5≤L:=by
  have h₁:W (q 0*q 2*q 5*q 7)≠0:=by
    intro h
    apply hn
    simp [firstNormProfile,h]
  have h₂:W (q 1*q 2*q 5*q 8)≠0:=by
    intro h
    apply hn
    simp [firstNormProfile,h]
  have hb₁:=factor_four_bound (q 0) (q 2) (q 5) (q 7) L (hq _) (hq _) (hq _) (hq _) (hW _ h₁)
  have hb₂:=factor_four_bound (q 1) (q 2) (q 5) (q 8) L (hq _) (hq _) (hq _) (hq _) (hW _ h₂)
  exact ⟨hb₁.1,hb₂.1,hb₁.2.1,hb₁.2.2.1⟩

variable {ι:Type*}[DecidableEq ι]
    (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem original_live_profile_caps
    (pool:Finset ι)(Q:Finset (ι→₀ℕ))(labels:Finset (Ideal O))(Y:ℝ)
    (β:Ideal O→(ι→₀ℕ)→ℂ)(cutoff:CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (Ψ:O→*ℂ)(m:O)(mark:(ι→₀ℕ)→Finset ι→ℂ)(W:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(K L:ℝ)
    (hW:∀y,W y≠0→y≤L)(x:OriginalIndex ι)
    (hx:x∈firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun o=>o.1) Y)
    (j:FirstCommonIndex ι)
    (hn:sourceSummand p hp hcop hg β cutoff Ψ m mark W Φ K x j≠0):
    leftNorm p x≤L ∧ rightNorm p x≤L ∧ commonNorm p x≤L ∧ primeProductNorm p j.2.1≤L:=by
  have hq:∀i,1≤firstCommonNorms p (leftNorm p x) (rightNorm p x) (commonNorm p x) (activeNorm p x)
      (divisorElement p x.1) x.2.2 j i:=by
    have hs:=original_source_norms_ge_one p hp pool Q labels Y x hx
    intro i
    fin_cases i
    · exact hs 0
    · exact hs 1
    · exact hs 2
    · exact hs 3
    · exact hs 4
    · exact primeProductNorm_ge_one p hp _
    · exact hs 5
    · exact primeProductNorm_ge_one p hp _
    · exact primeProductNorm_ge_one p hp _
  have hprof:firstNormProfile (fun y=>star (W y)) W Φ (fun _ _=>1) K
      (firstCommonNorms p (leftNorm p x) (rightNorm p x) (commonNorm p x) (activeNorm p x)
        (divisorElement p x.1) x.2.2 j)≠0:=by
    intro hz
    exact hn (by unfold sourceSummand;rw [hz,mul_zero])
  exact first_profile_live_factors W Φ K L _ hq hW hprof

end SevenEighths.InverseMomentFirstLiveCaps

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

lemma originalNorms_outer (p : ι→O) (x : Σ _ : FirstOriginalOuter ι,Ideal O×O)
    (i : Fin 5) : originalNorms p x i.castSucc=outerNorms p x.1 i := by
  fin_cases i <;> rfl

theorem sourceCell_outer (p : ι→O) (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (labels : Finset (Ideal O)) (Y : ℝ) (k : SourceIndex)
    (x : Σ _ : FirstOriginalOuter ι,Ideal O×O)
    (hx : x∈sourceCell (originalNorms p)
      (firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun o=>o.1) Y) k) :
    x.1∈outerCell p pool Q k := by
  obtain ⟨hs,hk⟩:=Finset.mem_filter.mp hx
  refine Finset.mem_filter.mpr ⟨(Finset.mem_sigma.mp hs).1,?_⟩
  intro i
  simpa only [sourceIndex,originalNorms_outer] using congrFun hk i.castSucc

variable (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]

lemma rpow_dyadicExponent (Z : ℝ) (hZ : 1<Z) (n : ℕ) :
    Z^dyadicExponent Z n=dyadScale n :=
  Real.rpow_logb (by linarith) (by linarith) (dyadScale_pos n)

lemma dyad_power_bounds (Z eta q : ℝ) (hZ : 1<Z) (h2 : 2≤Z^eta) (n : ℕ)
    (hq : dyadScale n≤q ∧ q≤2*dyadScale n) :
    Z^dyadicExponent Z n≤q ∧ q≤Z^(dyadicExponent Z n+eta) := by
  rw [Real.rpow_add (by linarith),rpow_dyadicExponent Z hZ]
  refine ⟨hq.1,hq.2.trans ?_⟩
  nlinarith [dyadScale_pos n]

end SevenEighths.InverseFirstGlobalCaps

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.FirstLiveNorms
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMomentFirstLiveCaps
open InverseMoment InverseMomentFirstOriginalProfile ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[DecidableEq ι]
    (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem original_live_norm_caps
    (pool:Finset ι)(Q:Finset (ι→₀ℕ))(labels:Finset (Ideal O))(Y:ℝ)
    (β:Ideal O→(ι→₀ℕ)→ℂ)(cutoff:CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (Ψ:O→*ℂ)(m:O)(mark:(ι→₀ℕ)→Finset ι→ℂ)(W:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(K L B:ℝ)
    (hB:0≤B)(hQ:∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤B)
    (hlabels:∀I∈labels,I≠0)(hW:∀y,W y≠0→y≤L)(x:OriginalIndex ι)
    (hx:x∈firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun o=>o.1) Y)
    (j:FirstCommonIndex ι)
    (hn:sourceSummand p hp hcop hg β cutoff Ψ m mark W Φ K x j≠0):
    (∀i:Fin 6,originalNorms p x i≤(![L,L,L,L*B^2,B^2,Y]:Fin 6→ℝ) i) ∧
      primeProductNorm p j.2.1≤L ∧ InverseFirstGlobalCaps.jNorm p x.1≤B^2:=by
  obtain ⟨ha₁,ha₂,hcommon,hquot⟩:=original_live_profile_caps p hp hcop hg pool Q labels Y β cutoff Ψ m mark W Φ K L hW x hx j hn
  obtain ⟨ho,hfreq⟩:=Finset.mem_sigma.mp hx
  obtain ⟨hb,hC,hD⟩:=(mem_firstOriginalOuter pool Q x.1).mp ho
  obtain ⟨hf,hrow⟩:=(mem_firstRetainedSource p labels x.1.1 Y x.2).mp hfreq
  have hcube:=reopenedCubeFamily_cube_norms p Q B hQ x.1.1 hb
  have hsup:=cube_whole_support_dyad p hp x.1.1 B hB hcube.1 hcube.2
  have hdiv:primeProductNorm p x.1.2.2≤L*B^2:=by
    calc
      _≤primeProductNorm p (x.1.2.1∪cubePrincipalSupport x.1.1.support x.1.1.leftExponent
          x.1.1.rightExponent x.1.1.leftBit x.1.1.rightBit):=
        primeProductNorm_mono p hp (Finset.mem_powerset.mp hD)
      _≤primeProductNorm p x.1.2.1*primeProductNorm p x.1.1.support:=by
        apply (primeProductNorm_union_le_mul p hp _ _).trans
        exact mul_le_mul_of_nonneg_left (primeProductNorm_mono p hp (Finset.filter_subset _ _))
          (primeProductNorm_pos p hp _).le
      _≤L*B^2:=mul_le_mul hcommon hsup (primeProductNorm_pos p hp _).le
        ((primeProductNorm_pos p hp _).le.trans hcommon)
  have hactive:activeNorm p x≤B^2:=
    (primeProductNorm_mono p hp (Finset.filter_subset _ _)).trans hsup
  have hE:=firstPhysicalMultiplier_ne_zero p hp x.1.1.support x.1.1.leftExponent x.1.1.rightExponent
    x.1.1.leftBit x.1.1.rightBit x.2.1 (hlabels _ hf)
  have hh0:x.2.2≠0:=(Finset.mem_erase.mp hrow).1
  have hh:=((mem_nonzeroChildFrequencyBall _ hE Y x.2.2).mp hrow).2
  have hfreqnorm:‖eisEmbedding x.2.2‖^2≤Y:=
    (element_norm_le_of_dvd (mul_ne_zero hE hh0) (dvd_mul_left x.2.2 _)).trans hh
  have hj:InverseFirstGlobalCaps.jNorm p x.1≤B^2:=by
    have hd:=jLabel_dvd_cube_product p x.1.1.support x.1.1.leftExponent x.1.1.rightExponent
      x.1.1.leftBit x.1.1.rightBit x.1.1.support_pos
    have hnorm:=element_norm_le_of_dvd
      (mul_ne_zero (primeProduct_ne_zero p hp _ _) (primeProduct_ne_zero p hp _ _)) hd
    simp only [map_mul,norm_mul,mul_pow] at hnorm
    exact hnorm.trans ((mul_le_mul hcube.1 hcube.2 (sq_nonneg _) hB).trans_eq (pow_two B).symm)
  refine ⟨?_,hquot,hj⟩
  intro i
  fin_cases i
  · exact ha₁
  · exact ha₂
  · exact hcommon
  · simpa [originalNorms,InverseMomentFirstChildWindows.sourceNorms,divisorElement,
      primeSubsetGenerator_norm_eq_productNorm] using hdiv
  · exact hactive
  · exact hfreqnorm

end SevenEighths.InverseMomentFirstLiveCaps

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.FirstDyadicRadius
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseFirstGlobalCaps
open InverseSecondSourceBlocks
open ConcreteTraceCRT (eisEmbedding)
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[DecidableEq ι]

theorem first_dyadic_bounds (Z eta x:ℝ)(hZ:1<Z)(hbin:2≤Z^eta)(hx:1≤x):
    0≤firstDyadicExponent Z x ∧ Z^firstDyadicExponent Z x≤x ∧ x≤Z^(firstDyadicExponent Z x+eta):=by
  have hd:=dyadIndex_bounds x hx
  have he:=dyad_power_bounds Z eta x hZ hbin (dyadIndex x) ⟨hd.1,hd.2.le⟩
  refine ⟨?_,he⟩
  apply (Real.rpow_le_rpow_left_iff hZ).mp
  rw [Real.rpow_zero,firstDyadicExponent,rpow_dyadicExponent Z hZ]
  exact one_le_pow₀ (by norm_num : (1:ℝ)≤2)

theorem first_dyadic_radius_global_cap
    (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
    (b:CubeCoordinates ι)(C D:Finset ι)
    (hD:D⊆C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit)
    (Z M r ell V eta tau Fmax:ℝ)(hZ:1<Z)(hbin:2≤Z^eta)(hM:0≤M)
    (hF:r+3*ell+V≤Fmax)
    (h₁:‖eisEmbedding (primeProduct p b.support b.leftExponent)‖^2≤Z^(ell+eta))
    (h₂:‖eisEmbedding (primeProduct p b.support b.rightExponent)‖^2≤Z^(ell+eta)):
    firstDyadicRadius p b C D Z M r ell V eta tau≤Z^(2*Fmax+15*eta+tau):=by
  have hz:0<Z:=zero_lt_one.trans hZ
  have hC:=first_dyadic_bounds Z eta (primeProductNorm p C) hZ hbin (primeProductNorm_ge_one p hp C)
  have hd:=first_dyadic_bounds Z eta (primeProductNorm p D) hZ hbin (primeProductNorm_ge_one p hp D)
  have hj:=first_dyadic_bounds Z eta (‖eisEmbedding (jLabel p b.support
    (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit)‖^2) hZ hbin
    (EisensteinSchwartzPoisson.one_le_eisenstein_norm_sq _ (primeProduct_ne_zero p hp _ _))
  have hs:=cube_whole_support_dyad p hp b (Z^(ell+eta)) (Real.rpow_nonneg hz.le _) h₁ h₂
  have hn:primeProductNorm p D≤Z^(firstDyadicExponent Z (primeProductNorm p C)+2*ell+3*eta):=by
    calc
      _≤primeProductNorm p (C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit):=
        primeProductNorm_mono p hp hD
      _≤primeProductNorm p C*primeProductNorm p b.support:=
        (primeProductNorm_union_le_mul p hp _ _).trans
          (mul_le_mul_of_nonneg_left (primeProductNorm_mono p hp (Finset.filter_subset _ _)) (primeProductNorm_pos p hp _).le)
      _≤Z^(firstDyadicExponent Z (primeProductNorm p C)+eta)*(Z^(ell+eta))^2:=
        mul_le_mul hC.2.2 hs (primeProductNorm_pos p hp _).le (Real.rpow_nonneg hz.le _)
      _=_:=by
        rw [←Real.rpow_natCast,←Real.rpow_mul hz.le,←Real.rpow_add hz]
        congr 1
        norm_num
        ring
  have hde:= (Real.rpow_le_rpow_left_iff hZ).mp (hd.2.1.trans hn)
  unfold firstDyadicRadius firstPhysicalHeight
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  linarith [hC.1,hj.1]

end SevenEighths.InverseMoment

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.FirstOriginalProfileParents
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMomentFirstOriginalProfile
open InverseMoment InverseMomentFirstChildWindows ActualEisensteinCubic
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι] (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
lemma originalNorms_eq_caps : originalNorms p=InverseFirstGlobalCaps.originalNorms p := by
  funext x i
  fin_cases i <;> rfl

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
lemma originalOuterCell_eq_caps (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) :
    originalOuterCell p pool Q k=InverseFirstGlobalCaps.outerCell p pool Q k := by
  unfold originalOuterCell InverseFirstGlobalCaps.outerCell InverseFirstGlobalCaps.outerGate
  ext x
  simp only [Finset.mem_filter,originalNorms_eq_caps,InverseFirstGlobalCaps.originalNorms_outer]

end SevenEighths.InverseMomentFirstOriginalProfile
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.FirstOriginalProfileLiveSource
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMomentFirstOriginalProfile
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstChildWindows
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
variable (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
lemma refinedSource_subset (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (labels : Finset (Ideal O))
    (β : Ideal O→(ι→₀ℕ)→ℂ) (cutoff : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (Y : ℝ) (k : SourceIndex) (gate : FirstOriginalOuter ι→Prop) :
    refinedSource p pool Q labels β cutoff Y k gate⊆sourceCell (originalNorms p)
      (firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) Y) k :=
  Finset.filter_subset _ _

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
lemma refinedOuter_label (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (j : ℕ) :
    refinedOuter p pool Q k (labelGate p j)=
      (InverseFirstGlobalCaps.outerCell p pool Q k).filter
        (fun x=>InverseSecondSourceBlocks.dyadIndex (InverseFirstGlobalCaps.jNorm p x)=j) := by
  rw [refinedOuter,originalOuterCell_eq_caps]
  ext x
  simp [labelGate]

end SevenEighths.InverseMomentFirstOriginalProfile
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.FirstDyadicCell
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseFirstGlobalCaps InverseSecondSourceBlocks InverseMomentFirstChildWindows
open InverseMomentFirstOriginalProfile
open ConcreteTraceCRT (eisEmbedding)
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[DecidableEq ι]
variable (p:ι→O)

theorem first_dyadic_radius_cell (pool:Finset ι)(Q:Finset (ι→₀ℕ))
    (k:SourceIndex)(j:ℕ)(x:FirstOriginalOuter ι)
    (hx:x∈refinedOuter p pool Q k (labelGate p j))
    (Z M r ell V eta tau:ℝ):
    firstDyadicRadius p x.1 x.2.1 x.2.2 Z M r ell V eta tau=
      firstCellRadius Z M r ell V eta tau k j:=by
  rw [refinedOuter_label] at hx
  obtain ⟨hx,hj⟩:=Finset.mem_filter.mp hx
  have hg:outerGate p k x:=(Finset.mem_filter.mp hx).2
  have hC:=hg 2
  have hD:=hg 3
  change dyadIndex (primeProductNorm p x.2.1)=k 2 at hC
  change dyadIndex (‖eisEmbedding (primeSubsetGenerator (fun i=>Ideal.span {p i}) x.2.2)‖^2)=k 3 at hD
  rw [primeSubsetGenerator_norm_eq_productNorm] at hD
  unfold firstDyadicRadius firstCellRadius firstDyadicExponent
  rw [hD,hC]
  change dyadIndex (‖eisEmbedding (jLabel p x.1.support
    (fun i=>x.1.leftExponent i+x.1.rightExponent i) x.1.leftBit x.1.rightBit)‖^2)=j at hj
  rw [hj]

theorem first_dyadic_refined_cutoff (pool:Finset ι)(Q:Finset (ι→₀ℕ))
    (k:SourceIndex)(j:ℕ)(Z M r ell V eta tau:ℝ):
    ∀x∈refinedOuter p pool Q k (labelGate p j),∀_I:Ideal O,
      firstDyadicRadius p x.1 x.2.1 x.2.2 Z M r ell V eta tau≤
        firstCellRadius Z M r ell V eta tau k j:=by
  intro x hx I
  exact (first_dyadic_radius_cell p pool Q k j x hx Z M r ell V eta tau).le

end SevenEighths.InverseMoment

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.FirstOriginalProfileLivePartition
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMomentFirstOriginalProfile
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstChildWindows InverseSecondSourceBlocks
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
variable (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
lemma sum_live_joint_cells (S : Finset (OriginalIndex ι)) (pool : Finset ι)
    (term : OriginalIndex ι→FirstCommonIndex ι→ℂ) :
    (∑x∈S,∑j∈firstCommonIndices pool,term x j)=
      ∑k∈liveJointKeys p S pool term,∑x∈S,∑j∈firstCommonIndices pool,
        if jointKey p x j=k then term x j else 0 := by
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hz : term x j=0
  · simp [hz]
  · have hk : jointKey p x j∈liveJointKeys p S pool term :=
      Finset.mem_image.mpr ⟨(x,j),Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx,hj⟩,hz⟩,rfl⟩
    simp [hk]

lemma sourceSummand_zero_of_weight (hp : ∀i,p i≠0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (β : Ideal O→(ι→₀ℕ)→ℂ) (cutoff : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (Ψ : O→*ℂ) (m : O) (mark : (ι→₀ℕ)→Finset ι→ℂ) (W : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ)
    (x : OriginalIndex ι) (j : FirstCommonIndex ι) (hx : firstOriginalWeight p β cutoff x.1 x.2=0) :
    sourceSummand p hp hcop hg β cutoff Ψ m mark W Φ K x j=0 := by
  simp [sourceSummand,weight,retainedCubeWeight,hx]

lemma joint_cell_eq_refined (hp : ∀i,p i≠0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (labels : Finset (Ideal O))
    (β : Ideal O→(ι→₀ℕ)→ℂ) (cutoff : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (Ψ : O→*ℂ) (m : O) (mark : (ι→₀ℕ)→Finset ι→ℂ) (W : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (K Y : ℝ)
    (k : JointKey) :
    let S := firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) Y
    let term := sourceSummand p hp hcop hg β cutoff Ψ m mark W Φ K
    (∑x∈S,∑j∈firstCommonIndices pool,if jointKey p x j=k then term x j else 0)=
      ∑x∈refinedSource p pool Q labels β cutoff Y k.1 (labelGate p k.2.2),
        ∑j∈firstCommonIndices pool,commonSelector p (fun _=>1) k.2.1 j.2.1*term x j := by
  intro S term
  simp only [refinedSource,sourceCell,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hw : firstOriginalWeight p β cutoff x.1 x.2=0
  · have ht : ∀j,term x j=0 := fun j=>sourceSummand_zero_of_weight p hp hcop hg β cutoff Ψ m mark W Φ K x j hw
    simp [ht,hw]
  · by_cases hs : sourceIndex (originalNorms p) x=k.1
    · by_cases hj : dyadIndex (InverseFirstGlobalCaps.jNorm p x.1)=k.2.2
      · simp [jointKey,hs,hj,labelGate,hw,Prod.ext_iff,commonSelector,ite_mul]
      · simp [jointKey,hs,hj,labelGate,Prod.ext_iff]
    · simp [jointKey,hs,Prod.ext_iff]

theorem original_retained_joint_partition (hp : ∀i,p i≠0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (labels : Finset (Ideal O))
    (β : Ideal O→(ι→₀ℕ)→ℂ) (cutoff : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (Ψ : O→*ℂ) (m : O) (mark : (ι→₀ℕ)→Finset ι→ℂ) (W : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (K Y : ℝ)
    (s : Fin 9→ℝ) (hs : ∀i,0<s i) :
    let S := firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) Y
    let term := sourceSummand p hp hcop hg β cutoff Ψ m mark W Φ K
    originalRetainedFamily p hp hcop hg pool Q labels β Ψ m mark W Φ K Y cutoff s=
      ∑k∈liveJointKeys p S pool term,
        ∑x∈refinedSource p pool Q labels β cutoff Y k.1 (labelGate p k.2.2),
          ∑j∈firstCommonIndices pool,commonSelector p (fun _=>1) k.2.1 j.2.1*term x j := by
  intro S term
  rw [original_retained_sum p hp hcop hg pool Q labels β Ψ m mark W Φ K Y cutoff s hs,
    sum_live_joint_cells p S pool term]
  apply Finset.sum_congr rfl
  intro k hk
  exact joint_cell_eq_refined p hp hcop hg pool Q labels β cutoff Ψ m mark W Φ K Y k

end SevenEighths.InverseMomentFirstOriginalProfile
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.FirstDyadicLiveRadius
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseFirstGlobalCaps InverseSecondSourceBlocks InverseMomentFirstChildWindows
open InverseMomentFirstOriginalProfile
open ConcreteTraceCRT (eisEmbedding)
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[DecidableEq ι]
variable (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]

include hp in
theorem first_dyadic_original_cap (pool:Finset ι)(Q:Finset (ι→₀ℕ))
    (Z M r ell V eta tau Fmax:ℝ)(hZ:1<Z)(hbin:2≤Z^eta)(hM:0≤M)
    (hF:r+3*ell+V≤Fmax)
    (hQ:∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta)):
    ∀x∈firstOriginalOuter pool Q,firstDyadicRadius p x.1 x.2.1 x.2.2 Z M r ell V eta tau≤Z^(2*Fmax+15*eta+tau):=by
  intro x hx
  have hm:=(mem_firstOriginalOuter pool Q x).mp hx
  have hb:=reopenedCubeFamily_cube_norms p Q _ hQ x.1 hm.1
  exact first_dyadic_radius_global_cap p hp x.1 x.2.1 x.2.2 (Finset.mem_powerset.mp hm.2.2)
    Z M r ell V eta tau Fmax hZ hbin hM hF hb.1 hb.2

include hp in
theorem first_live_cell_radius_cap (pool:Finset ι)(Q:Finset (ι→₀ℕ))
    (labels:Finset (Ideal O))(Y:ℝ)(term:OriginalIndex ι→FirstCommonIndex ι→ℂ)
    (Z M r ell V eta tau Fmax:ℝ)(hZ:1<Z)(hbin:2≤Z^eta)(hM:0≤M)
    (hF:r+3*ell+V≤Fmax)
    (hQ:∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta))
    (k:JointKey)(hk:k∈liveJointKeys p
      (firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) Y) pool term):
    firstCellRadius Z M r ell V eta tau k.1 k.2.2≤Z^(2*Fmax+15*eta+tau):=by
  obtain ⟨⟨x,j⟩,hx,rfl⟩:=Finset.mem_image.mp hk
  have hm:=Finset.mem_product.mp (Finset.mem_filter.mp hx).1
  have ho: x.1∈firstOriginalOuter pool Q:=(Finset.mem_sigma.mp hm.1).1
  have href:x.1∈refinedOuter p pool Q (sourceIndex (InverseMomentFirstOriginalProfile.originalNorms p) x)
      (labelGate p (dyadIndex (InverseFirstGlobalCaps.jNorm p x.1))):=by
    rw [refinedOuter_label]
    apply Finset.mem_filter.mpr
    refine ⟨?_,rfl⟩
    apply InverseFirstGlobalCaps.sourceCell_outer p pool Q labels Y
    exact Finset.mem_filter.mpr ⟨hm.1,rfl⟩
  change firstCellRadius Z M r ell V eta tau (sourceIndex (InverseMomentFirstOriginalProfile.originalNorms p) x)
    (dyadIndex (InverseFirstGlobalCaps.jNorm p x.1))≤_
  rw [←first_dyadic_radius_cell p pool Q _ _ x.1 href]
  exact first_dyadic_original_cap p hp pool Q Z M r ell V eta tau Fmax hZ hbin hM hF hQ x.1 ho

end SevenEighths.InverseMoment

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.FirstOriginalProfileLiveCount
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMomentFirstOriginalProfile
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels InverseMomentFirstChildWindows InverseSecondSourceBlocks
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
variable (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem liveJointKeys_card (S : Finset (OriginalIndex ι)) (pool : Finset ι)
    (term : OriginalIndex ι→FirstCommonIndex ι→ℂ) (B : ℕ)
    (hcap : ∀x∈S,∀j∈firstCommonIndices pool,term x j≠0→
      (∀i,sourceIndex (originalNorms p) x i≤B) ∧
      dyadIndex (primeProductNorm p j.2.1)≤B ∧
      dyadIndex (InverseFirstGlobalCaps.jNorm p x.1)≤B) :
    (liveJointKeys p S pool term).card≤(B+1)^8 := by
  let box := (Fintype.piFinset (fun _ : Fin 6=>Finset.range (B+1))) ×ˢ
    (Finset.range (B+1) ×ˢ Finset.range (B+1))
  have hsub : liveJointKeys p S pool term⊆box := by
    intro k hk
    obtain ⟨⟨x,j⟩,hm,rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨hm,hn⟩ := Finset.mem_filter.mp hm
    obtain ⟨hx,hj⟩ := Finset.mem_product.mp hm
    obtain ⟨h₁,h₂,h₃⟩ := hcap x hx j hj hn
    exact Finset.mem_product.mpr ⟨Fintype.mem_piFinset.mpr
      (fun i=>Finset.mem_range.mpr (Nat.lt_succ_of_le (h₁ i))),
      Finset.mem_product.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le h₂),
        Finset.mem_range.mpr (Nat.lt_succ_of_le h₃)⟩⟩
  have hc : box.card=(B+1)^8 := by
    simp only [box,Finset.card_product,Fintype.card_piFinset,Finset.card_range,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
    ring
  exact hc ▸ Finset.card_le_card hsub

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem liveJointKeys_card_of_norm_cap (S : Finset (OriginalIndex ι)) (pool : Finset ι)
    (term : OriginalIndex ι→FirstCommonIndex ι→ℂ) (R : ℝ)
    (hcap : ∀x∈S,∀j∈firstCommonIndices pool,term x j≠0→
      (∀i,0<originalNorms p x i ∧ originalNorms p x i≤R) ∧
      (0<primeProductNorm p j.2.1 ∧ primeProductNorm p j.2.1≤R) ∧
      (0<InverseFirstGlobalCaps.jNorm p x.1 ∧ InverseFirstGlobalCaps.jNorm p x.1≤R)) :
    (liveJointKeys p S pool term).card≤(dyadIndex R+1)^8 := by
  apply liveJointKeys_card
  intro x hx j hj hn
  obtain ⟨h₁,h₂,h₃⟩ := hcap x hx j hj hn
  have hm : ∀a : ℝ,0<a→a≤R→dyadIndex a≤dyadIndex R := fun a ha haR=>
    Nat.floor_mono (Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2) ha haR)
  exact ⟨fun i=>hm _ (h₁ i).1 (h₁ i).2,hm _ h₂.1 h₂.2,hm _ h₃.1 h₃.2⟩

end SevenEighths.InverseMomentFirstOriginalProfile
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.FirstOriginalProfileLiveIdentity
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMomentFirstOriginalProfile
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstChildWindows InverseMomentFirstProfileUniform CompletedHeight
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
variable (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
variable (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
variable (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem original_refined_cell_profile_identity (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (labels : Finset (Ideal O)) (β : Ideal O→(ι→₀ℕ)→ℂ)
    (cutoff : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (Ψ : O→*ℂ) (m : O) (mark : (ι→₀ℕ)→Finset ι→ℂ)
    (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a) (hsom : Function.support om⊆Set.Icc a b)
    (Φ : 𝓢(ℝ,ℂ)) (K Y X theta : ℝ) (hX : 0<X)
    (k : SourceIndex) (l : ℕ) (gate : FirstOriginalOuter ι→Prop) (s : Fin 9→ℝ) (hs : ∀i,0<s i)
    (hleft : s 0*s 2*s 5*s 7=X) (hright : s 1*s 2*s 5*s 8=X) :
    let source := refinedSource p pool Q labels β cutoff Y k gate
    (∑x∈source,∑j∈firstCommonIndices pool,commonSelector p (fun _=>1) l j.2.1*
      sourceSummand p hp hcop hg β cutoff Ψ m mark
        (fun y=>normTwistedSource om theta (y/X)) Φ K x j)=
    refinedCellRows p hp hcop hg pool Q labels β cutoff Ψ m mark k l gate
      (positiveSource (priorityLogWindow om a b ha hsom true) 1 (-theta))
      (positiveSource (priorityLogWindow om a b ha hsom false) 1 theta) Φ K Y s := by
  intro source
  let W₁ := fun y=>star (normTwistedSource om theta ((s 0*s 2*s 5*s 7)*y/X))
  let W₂ := fun y=>normTwistedSource om theta ((s 1*s 2*s 5*s 8)*y/X)
  have he := original_family_profiles p hp hg source pool (fun _=>commonSelector p (fun _=>1) l)
    (coefficient p hp hcop hg Ψ m mark true) (coefficient p hp hcop hg Ψ m mark false)
    (weight p hp hcop hg β cutoff Ψ m) om a b ha hsom Φ
    (leftNorm p) (rightNorm p) (commonNorm p) (activeNorm p) K X theta
    (fun x=>divisorElement p x.1) (fun x=>x.2.2) s hs
    (by intro x hx;have hh:=original_source_positive p hp pool Q labels Y x (Finset.mem_filter.mp (refinedSource_subset p pool Q labels β cutoff Y k gate hx)).1
        exact ⟨hh.1,hh.2.1,hh.2.2.1⟩) hX hleft hright
  change _=firstFamilyPhysicalRows p hg source pool _ _ _ _ _ _ Φ _ _ _ _ K _ _ s
  rw [←he]
  have hl : s 0*s 2*s 5*s 7≠0 := hleft.trans_ne (ne_of_gt hX)
  have hr : s 1*s 2*s 5*s 8≠0 := hright.trans_ne (ne_of_gt hX)
  simp only [firstFamilyPhysicalRows,firstBlockedPhysicalRows,sourceSummand,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro j hj
  simp only [firstNormProfile,mul_div_cancel₀ _ hl,mul_div_cancel₀ _ hr]
  ring

end SevenEighths.InverseMomentFirstOriginalProfile
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.FirstOriginalProfileScales
namespace OAI

noncomputable section
namespace SevenEighths.InverseMomentFirstOriginalProfile
open InverseMoment InverseMomentFirstChildWindows InverseSecondSourceBlocks

lemma physicalScales_pos (X : ℝ) (hX : 0<X) (k : SourceIndex) (l : ℕ) :
    ∀i,0<physicalScales X k l i := by
  apply rawScales_pos
  · exact div_pos hX (mul_pos (mul_pos (dyadScale_pos _) (dyadScale_pos _)) (dyadScale_pos _))
  · exact div_pos hX (mul_pos (mul_pos (dyadScale_pos _) (dyadScale_pos _)) (dyadScale_pos _))

lemma physicalScales_products (X : ℝ) (k : SourceIndex) (l : ℕ) :
    physicalScales X k l 0*physicalScales X k l 2*physicalScales X k l 5*physicalScales X k l 7=X ∧
    physicalScales X k l 1*physicalScales X k l 2*physicalScales X k l 5*physicalScales X k l 8=X := by
  constructor
  · change (dyadScale (k 0)*dyadScale (k 2)*dyadScale l)*(X/(dyadScale (k 0)*dyadScale (k 2)*dyadScale l))=X
    exact mul_div_cancel₀ X (ne_of_gt (mul_pos (mul_pos (dyadScale_pos _) (dyadScale_pos _)) (dyadScale_pos _)))
  · change (dyadScale (k 1)*dyadScale (k 2)*dyadScale l)*(X/(dyadScale (k 1)*dyadScale (k 2)*dyadScale l))=X
    exact mul_div_cancel₀ X (ne_of_gt (mul_pos (mul_pos (dyadScale_pos _) (dyadScale_pos _)) (dyadScale_pos _)))

theorem physicalScales_rpow (Z r : ℝ) (hZ : 1<Z) (k : SourceIndex) (l : ℕ) :
    physicalScales (Z^r) k l=fun i=>Z^(![Real.logb Z (dyadScale (k 0)),
      Real.logb Z (dyadScale (k 1)),Real.logb Z (dyadScale (k 2)),
      Real.logb Z (dyadScale (k 3)),Real.logb Z (dyadScale (k 4)),Real.logb Z (dyadScale l),
      Real.logb Z (dyadScale (k 5)),
      r-Real.logb Z (dyadScale (k 0))-Real.logb Z (dyadScale (k 2))-Real.logb Z (dyadScale l),
      r-Real.logb Z (dyadScale (k 1))-Real.logb Z (dyadScale (k 2))-Real.logb Z (dyadScale l)] i) := by
  have hz : 0<Z := zero_lt_one.trans hZ
  have he (n : ℕ) : Z^(Real.logb Z (dyadScale n))=dyadScale n :=
    Real.rpow_logb hz (ne_of_gt hZ) (dyadScale_pos n)
  funext i
  fin_cases i <;> simp [physicalScales,rawScales,he,Real.rpow_sub hz,div_div]

end SevenEighths.InverseMomentFirstOriginalProfile
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.FirstOriginalProfileLiveAggregate
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMomentFirstOriginalProfile
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstChildWindows InverseMomentFirstProfileUniform CompletedHeight
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
variable (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
variable (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
variable (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem original_retained_joint_profile_bound (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (labels : Finset (Ideal O)) (β : Ideal O→(ι→₀ℕ)→ℂ)
    (cutoff : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (Ψ : O→*ℂ) (m : O) (mark : (ι→₀ℕ)→Finset ι→ℂ)
    (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a) (hsom : Function.support om⊆Set.Icc a b)
    (Φ : 𝓢(ℝ,ℂ)) (K Y X theta : ℝ) (hX : 0<X)
    (reference : Fin 9→ℝ) (href : ∀i,0< reference i) :
    let source := firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) Y
    let W := fun y=>normTwistedSource om theta (y/X)
    let term := sourceSummand p hp hcop hg β cutoff Ψ m mark W Φ K
    ‖originalRetainedFamily p hp hcop hg pool Q labels β Ψ m mark W Φ K Y cutoff reference‖≤
      ∑k∈liveJointKeys p source pool term,
        ‖refinedCellRows p hp hcop hg pool Q labels β cutoff Ψ m mark k.1 k.2.1 (labelGate p k.2.2)
          (positiveSource (priorityLogWindow om a b ha hsom true) 1 (-theta))
          (positiveSource (priorityLogWindow om a b ha hsom false) 1 theta) Φ K Y (physicalScales X k.1 k.2.1)‖ := by
  intro source W term
  rw [original_retained_joint_partition p hp hcop hg pool Q labels β cutoff Ψ m mark W Φ K Y reference href]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro k hk
  have hp₁ := (physicalScales_products X k.1 k.2.1).1
  have hp₂ := (physicalScales_products X k.1 k.2.1).2
  rw [original_refined_cell_profile_identity p hp hcop hg pool Q labels β cutoff Ψ m mark om a b ha hsom
    Φ K Y X theta hX k.1 k.2.1 (labelGate p k.2.2) (physicalScales X k.1 k.2.1) (physicalScales_pos X hX k.1 k.2.1) hp₁ hp₂]

end SevenEighths.InverseMomentFirstOriginalProfile
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.FirstDyadicRetainedEnergy
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseFirstGlobalCaps InverseSecondSourceBlocks InverseMomentFirstChildWindows
open InverseMomentFirstOriginalProfile InverseMomentFirstProfileUniform
open InverseAmbientProfileTower JointLogSeparation FourierBridge CompletedHeight
open ConcreteTraceCRT (eisEmbedding)
local notation "O"=>ActualEisensteinCubic.O

theorem original_dyadic_retained_energy
    (om Φ:𝓢(ℝ,ℂ))(a b:ℝ)(ha:0<a)(hs:Function.support om⊆Set.Icc a b):
    ∃(omega₁ omega₂:𝓢(ℝ,ℂ))(lo hi:ℝ),0<lo ∧ lo≤hi ∧
      HasCompactSupport (omega₁:ℝ→ℂ) ∧ HasCompactSupport (omega₂:ℝ→ℂ) ∧
      tsupport (omega₁:ℝ→ℂ)⊆Set.Icc lo hi ∧ tsupport (omega₂:ℝ→ℂ)⊆Set.Icc lo hi ∧
    ∀eps:ℝ,0<eps→∀J:ℕ,∃C:ℝ,0≤C ∧
    ∀{ι:Type}[DecidableEq ι](p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (_hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
      (pool:Finset ι)(Q:Finset (ι→₀ℕ))(labels:Finset (Ideal O))
      (β:Ideal O→(ι→₀ℕ)→ℂ)(Ψ:O→*ℂ)(m:O)(mark:(ι→₀ℕ)→Finset ι→ℂ)
      (Z M r ell V eta tau Fmax Γ K theta Benergy:ℝ)
      (_hZ:1<Z)(_hbin:2≤Z^eta)(_hM:0≤M)(_hF:r+3*ell+V≤Fmax)
      (_hQ:∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta))
      (_hΨ:∀u,‖Ψ u‖≤1)(_hΓ:0≤Γ)(_hK:0<K)(_hB:0≤Benergy)
      (_hsf:∀I∈labels,Squarefree I)(_hn:∀I∈labels,I≠0)(_hβ:∀I∈labels,∀v∈Q,‖β I v‖≤Γ),
      let Y:=Z^(2*Fmax+15*eta+tau);
      let cutoff:=fun (q:CubeCoordinates ι) (C:Finset ι) (_I:Ideal O) (D:Finset ι)=>firstDyadicRadius p q C D Z M r ell V eta tau;
      let W:=fun y=>normTwistedSource om theta (y/Z^r);
      let source:=firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) Y;
      let keys:=liveJointKeys p source pool (sourceSummand p hp hcop hg β cutoff Ψ m mark W Φ K);
      (∀k∈keys,∀z:Frequency×(Fin 9→ℝ),
        (Z^(firstKappa M r ell V (dyadicExponent Z (k.1 3)) (dyadicExponent Z (k.1 0))
          (dyadicExponent Z (k.1 2)) (dyadicExponent Z (k.1 4)))*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
        refinedChildEnergy p hp hg hinj pool Q k.1 k.2.1 (labelGate p k.2.2) true Ψ m mark omega₁
          ((physicalScales (Z^r) k.1 k.2.1) 7)
          (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 7)
          (firstCellRadius Z M r ell V eta tau k.1 k.2.2)≤Benergy*(tripleHeight J z.1*coordinateHeight J z.2))→
      (∀k∈keys,∀z:Frequency×(Fin 9→ℝ),
        (Z^(firstKappa M r ell V (dyadicExponent Z (k.1 3)) (dyadicExponent Z (k.1 1))
          (dyadicExponent Z (k.1 2)) (dyadicExponent Z (k.1 4)))*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
        refinedChildEnergy p hp hg hinj pool Q k.1 k.2.1 (labelGate p k.2.2) false Ψ m mark omega₂
          ((physicalScales (Z^r) k.1 k.2.1) 8)
          (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 8)
          (firstCellRadius Z M r ell V eta tau k.1 k.2.2)≤Benergy*(tripleHeight J z.1*coordinateHeight J z.2))→
      (Z^(-r-2*ell-V)*Z^M)*‖originalRetainedFamily p hp hcop hg pool Q labels β Ψ m mark W Φ K Y cutoff (fun _=>1)‖≤
        C*Γ^2*Benergy*(1+‖theta‖)^(2*InverseClippingProfiles.momentOrder J)*
          Z^((2*Fmax+15*eta+tau)*eps)*(keys.card:ℝ):=by
  let g₁:=priorityLogWindow om a b ha hs true
  let g₂:=priorityLogWindow om a b ha hs false
  let M₀:=|Real.log a|+|Real.log b|
  have hm:0≤M₀:=by dsimp [M₀];positivity
  obtain ⟨w₁,w₂,lo,hi,hlo,hlh,hw₁,hw₂,hs₁,hs₂,he⟩:=original_refined_cell_physical_budget
    g₁ g₂ Φ M₀ M₀ hm hm (priorityLogWindow_support om a b ha hs true) (priorityLogWindow_support om a b ha hs false)
  refine ⟨w₁,w₂,lo,hi,hlo,hlh,hw₁,hw₂,hs₁,hs₂,?_⟩
  intro eps heps J
  obtain ⟨Cp,Kp,hCp,hKp,hcell⟩:=he eps heps 0 J
  refine ⟨Cp*Kp,mul_nonneg hCp hKp.le,?_⟩
  intro ι _ p hp _ hg hinj hcop hc hpr pool Q labels β Ψ m mark Z M r ell V eta tau Fmax Γ K theta Benergy
    hZ hbin hM hF hQ hΨ hΓ hK hB hsf hn hβ Y cutoff W source keys hleft hright
  have hz:0<Z:=zero_lt_one.trans hZ
  have hsum:=original_retained_joint_profile_bound p hp hcop hg pool Q labels β cutoff Ψ m mark
    om a b ha hs Φ K Y (Z^r) theta (Real.rpow_pos_of_pos hz _) (fun _=>1) (by intro i;norm_num)
  have hnrm:0≤Z^(-r-2*ell-V)*Z^M:=mul_nonneg (Real.rpow_nonneg hz.le _) (Real.rpow_nonneg hz.le _)
  apply (mul_le_mul_of_nonneg_left hsum hnrm).trans
  rw [Finset.mul_sum]
  have hpoint:∀k∈keys,
      (Z^(-r-2*ell-V)*Z^M)*‖refinedCellRows p hp hcop hg pool Q labels β cutoff Ψ m mark k.1 k.2.1 (labelGate p k.2.2)
        (positiveSource g₁ 1 (-theta)) (positiveSource g₂ 1 theta) Φ K Y (physicalScales (Z^r) k.1 k.2.1)‖≤
      (Cp*Kp)*Γ^2*Benergy*(1+‖theta‖)^(2*InverseClippingProfiles.momentOrder J)*Z^((2*Fmax+15*eta+tau)*eps):=by
    intro k hk
    let T₁:=(physicalScales (Z^r) k.1 k.2.1) 7
    let T₂:=(physicalScales (Z^r) k.1 k.2.1) 8
    have hT₁:0<T₁:=physicalScales_pos _ (Real.rpow_pos_of_pos hz _) _ _ 7
    have hT₂:0<T₂:=physicalScales_pos _ (Real.rpow_pos_of_pos hz _) _ _ 8
    have hY:0<firstCellRadius Z M r ell V eta tau k.1 k.2.2:=Real.rpow_pos_of_pos hz _
    have hl:=hleft k hk
    have hr:=hright k hk
    have heta:0≤eta:=by
      apply (Real.rpow_le_rpow_left_iff hZ).mp
      rw [Real.rpow_zero]
      linarith
    have hL:0≤eta*Real.log Z:=mul_nonneg heta (Real.log_nonneg hZ.le)
    have he' := hcell p hp hg hinj hcop hc hpr pool Q labels β cutoff Ψ m mark Γ Y
      (firstCellRadius Z M r ell V eta tau k.1 k.2.2) hΨ hΓ hY hsf hn hβ k.1 k.2.1 (labelGate p k.2.2)
      (fun x hx I _=>first_dyadic_refined_cutoff p pool Q k.1 k.2.2 Z M r ell V eta tau x hx I)
      T₁ T₂ K theta (eta*Real.log Z) hT₁ hT₂ hK hL Benergy Z M r ell V (dyadicExponent Z (k.1 3))
      (dyadicExponent Z (k.1 0)) (dyadicExponent Z (k.1 1)) (dyadicExponent Z (k.1 2))
      (dyadicExponent Z (k.1 4)) (dyadicExponent Z k.2.1) (dyadicExponent Z (k.1 5)) eta
      hB hz (physicalScales_rpow Z r hZ k.1 k.2.1) rfl hl hr
    have hrad:=first_live_cell_radius_cap p hp pool Q labels Y _ Z M r ell V eta tau Fmax hZ hbin hM hF hQ k hk
    have hpow:=Real.rpow_le_rpow hY.le hrad heps.le
    rw [←Real.rpow_mul hz.le] at hpow
    simp only [pow_zero,div_one,norm_neg] at he'
    calc
      _≤(Γ^2*Kp*(firstCellRadius Z M r ell V eta tau k.1 k.2.2)^eps*Benergy)*
          (Cp*((1+‖theta‖)^InverseClippingProfiles.momentOrder J*(1+‖theta‖)^InverseClippingProfiles.momentOrder J)):=he'
      _≤(Γ^2*Kp*Z^((2*Fmax+15*eta+tau)*eps)*Benergy)*
          (Cp*((1+‖theta‖)^InverseClippingProfiles.momentOrder J*(1+‖theta‖)^InverseClippingProfiles.momentOrder J)):=by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by positivity)) hB
      _=_:=by rw [show 2*InverseClippingProfiles.momentOrder J=InverseClippingProfiles.momentOrder J+InverseClippingProfiles.momentOrder J by omega,pow_add];ring
  calc
    _≤∑_k∈keys,(Cp*Kp)*Γ^2*Benergy*(1+‖theta‖)^(2*InverseClippingProfiles.momentOrder J)*Z^((2*Fmax+15*eta+tau)*eps):=
      Finset.sum_le_sum hpoint
    _=_:=by simp [mul_comm]

end SevenEighths.InverseMoment

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.FirstOriginalProfileLiveSupport
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMomentFirstOriginalProfile
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstChildWindows InverseSecondSourceBlocks
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
variable (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
variable (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
variable (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem original_live_joint_card (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (labels : Finset (Ideal O)) (Y : ℝ) (β : Ideal O→(ι→₀ℕ)→ℂ)
    (cutoff : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (Ψ : O→*ℂ) (m : O) (mark : (ι→₀ℕ)→Finset ι→ℂ) (W : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (K L B : ℝ)
    (hB : 0≤B) (hQ : ∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤B)
    (hlabels : ∀I∈labels,I≠0) (hW : ∀y,W y≠0→y≤L) :
    (liveJointKeys p
      (firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) Y) pool
      (sourceSummand p hp hcop hg β cutoff Ψ m mark W Φ K)).card≤
        (dyadIndex (liveNormCap L B Y)+1)^8 := by
  apply liveJointKeys_card_of_norm_cap
  intro x hx j hj hn
  obtain ⟨h₁,h₂,h₃⟩ := InverseMomentFirstLiveCaps.original_live_norm_caps p hp hcop hg
    pool Q labels Y β cutoff Ψ m mark W Φ K L B hB hQ hlabels hW x hx j hn
  have hc : ∀i : Fin 6,(![L,L,L,L*B^2,B^2,Y] : Fin 6→ℝ) i≤liveNormCap L B Y := by
    intro i
    fin_cases i <;> simp [liveNormCap,le_max_iff]
  refine ⟨fun i=>⟨lt_of_lt_of_le zero_lt_one (original_source_norms_ge_one p hp pool Q labels Y x hx i),(h₁ i).trans (hc i)⟩,?_,?_⟩
  · exact ⟨primeProductNorm_pos p hp _,h₂.trans (le_max_of_le_right (le_max_left _ _))⟩
  · refine ⟨lt_of_lt_of_le zero_lt_one (element_norm_ge_one _ (primeProduct_ne_zero p hp _ _)),?_⟩
    exact h₃.trans (le_max_of_le_right (le_max_of_le_right (le_max_right _ _)))

theorem original_twisted_live_joint_card (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (labels : Finset (Ideal O)) (Y : ℝ) (β : Ideal O→(ι→₀ℕ)→ℂ)
    (cutoff : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (Ψ : O→*ℂ) (m : O) (mark : (ι→₀ℕ)→Finset ι→ℂ) (W : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (K b B X theta : ℝ)
    (hX : 0<X) (hB : 0≤B) (hQ : ∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤B)
    (hlabels : ∀I∈labels,I≠0) (hW : ∀y,W y≠0→y≤b) :
    (liveJointKeys p
      (firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) Y) pool
      (sourceSummand p hp hcop hg β cutoff Ψ m mark
        (fun y=>CompletedHeight.normTwistedSource W theta (y/X)) Φ K)).card≤
        (dyadIndex (liveNormCap (b*X) B Y)+1)^8 := by
  apply original_live_joint_card p hp hcop hg pool Q labels Y β cutoff Ψ m mark _ Φ K (b*X) B hB hQ hlabels
  intro y hy
  have hwy : W (y/X)≠0 := by
    intro hz
    exact hy (by simp [CompletedHeight.normTwistedSource,hz])
  exact (div_le_iff₀ hX).mp (hW _ hwy)

end SevenEighths.InverseMomentFirstOriginalProfile
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.FirstLiveCountBudget
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMomentFirstOriginalProfile
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstChildWindows InverseSecondSourceBlocks
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

lemma liveNormCap_power_bound (b Lcap Z r ell F eta tau : ℝ)
    (_hb : 0 ≤ b) (hcap : 0 ≤ Lcap) (hZ : 2 ≤ Z)
    (hr : r ≤ Lcap) (hell : ell ≤ Lcap) (hF : 0 ≤ F) (hFcap : F ≤ Lcap)
    (heta : 0 ≤ eta) (heta1 : eta ≤ 1) (htau : 0 ≤ tau) (htau1 : tau ≤ 1) :
    1 ≤ liveNormCap (b*Z^r) (Z^(ell+eta)) (Z^(2*F+15*eta+tau)) ∧
    liveNormCap (b*Z^r) (Z^(ell+eta)) (Z^(2*F+15*eta+tau)) ≤
      max 1 b * Z^(3*Lcap+16) := by
  have hz : 0<Z := by linarith
  have hz1 : 1 ≤ Z := by linarith
  have hb1 : 1 ≤ max 1 b := le_max_left _ _
  have hbmax : b ≤ max 1 b := le_max_right _ _
  have hpow (a : ℝ) (ha : a ≤ 3*Lcap+16) : Z^a ≤ max 1 b*Z^(3*Lcap+16) :=
    (Real.rpow_le_rpow_of_exponent_le hz1 ha).trans (le_mul_of_one_le_left (Real.rpow_nonneg hz.le _) hb1)
  have hsq : (Z^(ell+eta))^2=Z^(2*(ell+eta)) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hz.le]
    congr 1
    ring
  refine ⟨(Real.one_le_rpow hz1 (by linarith : 0 ≤ 2*F+15*eta+tau)).trans (le_max_left _ _),?_⟩
  unfold liveNormCap
  apply max_le (hpow _ (by linarith))
  apply max_le
  · exact mul_le_mul hbmax (Real.rpow_le_rpow_of_exponent_le hz1 (by linarith))
      (Real.rpow_nonneg hz.le _) (by linarith)
  apply max_le
  · rw [hsq,mul_assoc,←Real.rpow_add hz]
    exact mul_le_mul hbmax (Real.rpow_le_rpow_of_exponent_le hz1 (by linarith))
      (Real.rpow_nonneg hz.le _) (by linarith)
  · rw [hsq]
    exact hpow _ (by linarith)

lemma dyadIndex_power_log_bound (b A : ℝ) (hb : 1 ≤ b) (hA : 0 ≤ A) :
    ∃ C : ℝ,0<C ∧ ∀ Z R : ℝ,2 ≤ Z → 1 ≤ R → R ≤ b*Z^A →
      ((dyadIndex R+1:ℕ):ℝ)^8 ≤ C*(1+Real.log Z)^8 := by
  let c := 1+Real.log b/Real.log 2+A/Real.log 2
  have hl2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hcb : 0 ≤ Real.log b/Real.log 2 := div_nonneg (Real.log_nonneg hb) hl2.le
  have hcA : 0 ≤ A/Real.log 2 := div_nonneg hA hl2.le
  have hc : 0<c := by dsimp [c];linarith
  refine ⟨c^8,pow_pos hc _,?_⟩
  intro Z R hZ hR hbound
  have hz : 0<Z := by linarith
  have hr : 0<R := by linarith
  have hb0 : 0<b := by linarith
  have hlz : 0 ≤ Real.log Z := Real.log_nonneg (by linarith)
  have hf := Nat.floor_le (Real.logb_nonneg (by norm_num : (1:ℝ)<2) hR)
  have hl := Real.log_le_log hr hbound
  rw [Real.log_mul (ne_of_gt hb0) (ne_of_gt (Real.rpow_pos_of_pos hz _)),Real.log_rpow hz] at hl
  have hstep : ((dyadIndex R+1:ℕ):ℝ) ≤ c*(1+Real.log Z) := by
    simp only [Nat.cast_add,Nat.cast_one,dyadIndex,Real.logb] at *
    have hd := div_le_div_of_nonneg_right hl hl2.le
    have hmul : 0 ≤ (Real.log b/Real.log 2)*Real.log Z := mul_nonneg hcb hlz
    dsimp [c]
    have he : (Real.log b+A*Real.log Z)/Real.log 2=Real.log b/Real.log 2+(A/Real.log 2)*Real.log Z := by ring
    rw [he] at hd
    nlinarith
  calc
    _ ≤ (c*(1+Real.log Z))^8 := pow_le_pow_left₀ (by positivity) hstep 8
    _= _ := by rw [mul_pow]

theorem live_joint_scalar_log_budget (b Lcap : ℝ) (hb : 0 ≤ b) (hcap : 0 ≤ Lcap) :
    ∃ C : ℝ,0<C ∧ ∀ Z r ell F eta tau : ℝ,2 ≤ Z → r ≤ Lcap → ell ≤ Lcap →
      0 ≤ F → F ≤ Lcap → 0 ≤ eta → eta ≤ 1 → 0 ≤ tau → tau ≤ 1 →
      ((dyadIndex (liveNormCap (b*Z^r) (Z^(ell+eta)) (Z^(2*F+15*eta+tau)))+1:ℕ):ℝ)^8 ≤
        C*(1+Real.log Z)^8 := by
  obtain ⟨C,hC,hcount⟩ := dyadIndex_power_log_bound (max 1 b) (3*Lcap+16) (le_max_left _ _) (by linarith)
  refine ⟨C,hC,?_⟩
  intro Z r ell F eta tau hZ hr hell hF hFcap heta heta1 htau htau1
  have hc := liveNormCap_power_bound b Lcap Z r ell F eta tau hb hcap hZ hr hell hF hFcap heta heta1 htau htau1
  exact hcount Z _ hZ hc.1 hc.2

lemma log_eighth_small_power (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ Z : ℝ,1 ≤ Z → (1+Real.log Z)^8 ≤ C*Z^ε := by
  let δ := ε/8
  have hd : 0<δ := by dsimp [δ];positivity
  refine ⟨(1+1/δ)^8,by positivity,?_⟩
  intro Z hZ
  have hz : 0<Z := by linarith
  have h1 := Real.one_le_rpow hZ hd.le
  have hl := Real.log_le_rpow_div hz.le hd
  have hb : 1+Real.log Z ≤ (1+1/δ)*Z^δ := by
    calc
      _ ≤ Z^δ+Z^δ/δ := add_le_add h1 hl
      _=_ := by ring
  calc
    _ ≤ ((1+1/δ)*Z^δ)^8 := pow_le_pow_left₀ (by linarith [Real.log_nonneg hZ]) hb 8
    _=(1+1/δ)^8*Z^ε := by
      have he : (Z^δ)^8=Z^ε := by
        rw [←Real.rpow_natCast,←Real.rpow_mul hz.le]
        congr 1
        dsimp [δ]
        ring
      rw [mul_pow,he]

theorem live_joint_scalar_small_power (b Lcap ε : ℝ) (hb : 0 ≤ b) (hcap : 0 ≤ Lcap) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ Z r ell F eta tau : ℝ,2 ≤ Z → r ≤ Lcap → ell ≤ Lcap →
      0 ≤ F → F ≤ Lcap → 0 ≤ eta → eta ≤ 1 → 0 ≤ tau → tau ≤ 1 →
      ((dyadIndex (liveNormCap (b*Z^r) (Z^(ell+eta)) (Z^(2*F+15*eta+tau)))+1:ℕ):ℝ)^8 ≤ C*Z^ε := by
  obtain ⟨C₁,hC₁,h₁⟩ := live_joint_scalar_log_budget b Lcap hb hcap
  obtain ⟨C₂,hC₂,h₂⟩ := log_eighth_small_power ε hε
  refine ⟨C₁*C₂,mul_pos hC₁ hC₂,?_⟩
  intro Z r ell F eta tau hZ hr hell hF hFcap heta heta1 htau htau1
  exact (h₁ Z r ell F eta tau hZ hr hell hF hFcap heta heta1 htau htau1).trans
    ((mul_le_mul_of_nonneg_left (h₂ Z (by linarith)) hC₁.le).trans_eq (mul_assoc _ _ _).symm)

theorem original_live_joint_small_power (b Lcap ε : ℝ) (hb : 0 ≤ b) (hcap : 0 ≤ Lcap) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀{ι : Type*}[DecidableEq ι](p : ι → O)(hp : ∀i,p i≠0)
      [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (pool : Finset ι)(Q : Finset (ι→₀ℕ))(labels : Finset (Ideal O))
      (β : Ideal O → (ι→₀ℕ) → ℂ)(cutoff : CubeCoordinates ι → Finset ι → Ideal O → Finset ι → ℝ)
      (Ψ : O→*ℂ)(m : O)(mark : (ι→₀ℕ) → Finset ι → ℂ)(W : ℝ → ℂ)(Φ : 𝓢(ℝ,ℂ))
      (K Z r ell F eta tau theta : ℝ),
      2 ≤ Z → r ≤ Lcap → ell ≤ Lcap → 0 ≤ F → F ≤ Lcap → 0 ≤ eta → eta ≤ 1 → 0 ≤ tau → tau ≤ 1 →
      (∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2 ≤ Z^(ell+eta)) →
      (∀I∈labels,I≠0) → (∀y,W y≠0 → y ≤ b) →
      ((liveJointKeys p
        (firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1)
          (Z^(2*F+15*eta+tau))) pool
        (sourceSummand p hp hcop hg β cutoff Ψ m mark
          (fun y=>CompletedHeight.normTwistedSource W theta (y/Z^r)) Φ K)).card:ℝ) ≤ C*Z^ε := by
  obtain ⟨C,hC,hcount⟩ := live_joint_scalar_small_power b Lcap ε hb hcap hε
  refine ⟨C,hC,?_⟩
  intro ι _ p hp _ hcop hg pool Q labels β cutoff Ψ m mark W Φ K Z r ell F eta tau theta
    hZ hr hell hF hFcap heta heta1 htau htau1 hQ hlabels hW
  have hz : 0<Z := by linarith
  have he := original_twisted_live_joint_card p hp hcop hg pool Q labels (Z^(2*F+15*eta+tau))
    β cutoff Ψ m mark W Φ K b (Z^(ell+eta)) (Z^r) theta
    (Real.rpow_pos_of_pos hz _) (Real.rpow_nonneg hz.le _) hQ hlabels hW
  have he' : ((liveJointKeys p
        (firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1)
          (Z^(2*F+15*eta+tau))) pool
        (sourceSummand p hp hcop hg β cutoff Ψ m mark
          (fun y=>CompletedHeight.normTwistedSource W theta (y/Z^r)) Φ K)).card:ℝ) ≤
      (((dyadIndex (liveNormCap (b*Z^r) (Z^(ell+eta)) (Z^(2*F+15*eta+tau))))+1:ℕ):ℝ)^8 := by exact_mod_cast he
  exact he'.trans (hcount Z r ell F eta tau hZ hr hell hF hFcap heta heta1 htau htau1)

end SevenEighths.InverseMomentFirstOriginalProfile
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.FirstDyadicRetainedBudget
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseFirstGlobalCaps InverseSecondSourceBlocks InverseMomentFirstChildWindows
open InverseMomentFirstOriginalProfile InverseMomentFirstProfileUniform
open InverseAmbientProfileTower JointLogSeparation FourierBridge CompletedHeight
open ConcreteTraceCRT (eisEmbedding)
local notation "O"=>ActualEisensteinCubic.O

theorem original_dyadic_retained_budget_oai
    (om Φ:𝓢(ℝ,ℂ))(a b:ℝ)(ha:0<a)(hs:Function.support om⊆Set.Icc a b) (Lcap:ℝ)(hcap:0≤Lcap)(hb:0≤b):
    ∃(omega₁ omega₂:𝓢(ℝ,ℂ))(lo hi:ℝ),0<lo ∧ lo≤hi ∧
      HasCompactSupport (omega₁:ℝ→ℂ) ∧ HasCompactSupport (omega₂:ℝ→ℂ) ∧
      tsupport (omega₁:ℝ→ℂ)⊆Set.Icc lo hi ∧ tsupport (omega₂:ℝ→ℂ)⊆Set.Icc lo hi ∧
    ∀eps:ℝ,0<eps→∀J:ℕ,∃C:ℝ,0≤C ∧
    ∀{ι:Type}[DecidableEq ι](p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (_hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
      (pool:Finset ι)(Q:Finset (ι→₀ℕ))(labels:Finset (Ideal O))
      (β:Ideal O→(ι→₀ℕ)→ℂ)(Ψ:O→*ℂ)(m:O)(mark:(ι→₀ℕ)→Finset ι→ℂ)
      (Z M r ell V eta tau Fmax Γ K theta Benergy:ℝ)
      (_hZ:2≤Z)(_hbin:2≤Z^eta)(_hM:0≤M)(_hF:r+3*ell+V≤Fmax)
      (_hQ:∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta))
      (_hrcap:r≤Lcap)(_hellcap:ell≤Lcap)(_hF0:0≤Fmax)(_hFcap:Fmax≤Lcap)
      (_heta:0≤eta)(_heta1:eta≤1)(_htau:0≤tau)(_htau1:tau≤1)
      (_hΨ:∀u,‖Ψ u‖≤1)(_hΓ:0≤Γ)(_hK:0<K)(_hB:0≤Benergy)
      (_hsf:∀I∈labels,Squarefree I)(_hn:∀I∈labels,I≠0)(_hβ:∀I∈labels,∀v∈Q,‖β I v‖≤Γ),
      let Y:=Z^(2*Fmax+15*eta+tau);
      let cutoff:=fun (q:CubeCoordinates ι) (C:Finset ι) (_I:Ideal O) (D:Finset ι)=>firstDyadicRadius p q C D Z M r ell V eta tau;
      let W:=fun y=>normTwistedSource om theta (y/Z^r);
      let source:=firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) Y;
      let keys:=liveJointKeys p source pool (sourceSummand p hp hcop hg β cutoff Ψ m mark W Φ K);
      (∀k∈keys,∀z:Frequency×(Fin 9→ℝ),
        (Z^(firstKappa M r ell V (dyadicExponent Z (k.1 3)) (dyadicExponent Z (k.1 0))
          (dyadicExponent Z (k.1 2)) (dyadicExponent Z (k.1 4)))*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
        refinedChildEnergy p hp hg hinj pool Q k.1 k.2.1 (labelGate p k.2.2) true Ψ m mark omega₁
          ((physicalScales (Z^r) k.1 k.2.1) 7)
          (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 7)
          (firstCellRadius Z M r ell V eta tau k.1 k.2.2)≤Benergy*(tripleHeight J z.1*coordinateHeight J z.2))→
      (∀k∈keys,∀z:Frequency×(Fin 9→ℝ),
        (Z^(firstKappa M r ell V (dyadicExponent Z (k.1 3)) (dyadicExponent Z (k.1 1))
          (dyadicExponent Z (k.1 2)) (dyadicExponent Z (k.1 4)))*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
        refinedChildEnergy p hp hg hinj pool Q k.1 k.2.1 (labelGate p k.2.2) false Ψ m mark omega₂
          ((physicalScales (Z^r) k.1 k.2.1) 8)
          (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 8)
          (firstCellRadius Z M r ell V eta tau k.1 k.2.2)≤Benergy*(tripleHeight J z.1*coordinateHeight J z.2))→
      (Z^(-r-2*ell-V)*Z^M)*‖originalRetainedFamily p hp hcop hg pool Q labels β Ψ m mark W Φ K Y cutoff (fun _=>1)‖≤
        C*Γ^2*Benergy*(1+‖theta‖)^(2*InverseClippingProfiles.momentOrder J)*
          Z^((2*Fmax+15*eta+tau)*eps+eps) :=by
  obtain ⟨w₁,w₂,lo,hi,hlo,hlh,hw₁,hw₂,hs₁,hs₂,he⟩:=original_dyadic_retained_energy om Φ a b ha hs
  refine ⟨w₁,w₂,lo,hi,hlo,hlh,hw₁,hw₂,hs₁,hs₂,?_⟩
  intro eps heps J
  obtain ⟨C,hC,henergy⟩:=he eps heps J
  obtain ⟨Cc,hCc,hcount⟩:=original_live_joint_small_power b Lcap eps hb hcap heps
  refine ⟨C*Cc,mul_nonneg hC hCc.le,?_⟩
  intro ι _ p hp _ hg hinj hcop hc hpr pool Q labels β Ψ m mark Z M r ell V eta tau Fmax Γ K theta Benergy
    hZ hbin hM hF hQ hrcap hellcap hF0 hFcap heta heta1 htau htau1 hΨ hΓ hK hB hsf hn hβ
    Y cutoff W source keys hleft hright
  have hz:0<Z:=by linarith
  have hZ1:1<Z:=by linarith
  have he':=henergy p hp hg hinj hcop hc hpr pool Q labels β Ψ m mark Z M r ell V eta tau Fmax Γ K theta Benergy
    hZ1 hbin hM hF hQ hΨ hΓ hK hB hsf hn hβ hleft hright
  have hnkey:=hcount p hp hcop hg pool Q labels β cutoff Ψ m mark om Φ K Z r ell Fmax eta tau theta
    hZ hrcap hellcap hF0 hFcap heta heta1 htau htau1 hQ hn (fun y hy=>(hs hy).2)
  apply he'.trans
  calc
    _≤C*Γ^2*Benergy*(1+‖theta‖)^(2*InverseClippingProfiles.momentOrder J)*
        Z^((2*Fmax+15*eta+tau)*eps)*(Cc*Z^eps):=
      mul_le_mul_of_nonneg_left hnkey (by positivity)
    _=_:=by rw [Real.rpow_add hz];ring

end SevenEighths.InverseMoment

end

end OAI
end

theorem solution : type_of% @OAI.SevenEighths.InverseMoment.original_dyadic_retained_budget_oai := @OAI.SevenEighths.InverseMoment.original_dyadic_retained_budget_oai
