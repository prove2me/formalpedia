-- Prove2me | solution 1 for OAI.SevenEighths.DetectorDictionaryInverseRawReference.raw_reference_moment
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T05:25:10.484647+00:00
-- url     : https://prove2.me/submissions/af03dca0-4333-463d-bff3-0cac422a58b7

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B024
import Theorems.Thm_OAI_SevenEighths_DetectorDictionaryInverseRawInitialEnergy_raw_rows_le_initial
import Theorems.Thm_OAI_SevenEighths_DetectorDictionaryInverseRawInputBound_raw_input_bound

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.QuadraticTrace
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

section

theorem finiteSquarefreeRow_one
    {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i) (S : Finset ι) :
    finiteSquarefreeRow P hgood S 1 = 1 := by
  classical
  unfold finiteSquarefreeRow
  apply Finset.prod_eq_one
  intro i hi
  simp

open EisensteinEmbedding ConcreteTraceCRT Complex

end

end ActualEisensteinCubic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.RayCharacters
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

namespace FirstCauchyArithmetic

open ActualEisensteinCubic ConcretePrimeRowBridge

theorem family_prime_dvd_product_iff {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) (S : Finset ι) (i : ι) :
    P i ∣ ∏ j ∈ S, P j ↔ i ∈ S := by
  constructor
  · intro h
    obtain ⟨j, hj, hd⟩ := ((family_prime P i).dvd_finsetProd_iff P).mp h
    have he : P i = P j := associated_iff_eq.mp
      ((family_prime P i).associated_of_dvd (family_prime P j) hd)
    exact hinj he ▸ hj
  · exact fun hi => Finset.dvd_prod_of_mem P hi

theorem family_product_injective {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) : Function.Injective (fun S : Finset ι => ∏ i ∈ S, P i) := by
  intro S T h
  change (∏ i ∈ S, P i) = (∏ i ∈ T, P i) at h
  ext i
  rw [← family_prime_dvd_product_iff P hinj S i, h, family_prime_dvd_product_iff P hinj T i]

end FirstCauchyArithmetic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.QuadraticSieve.IdealQuotients
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
namespace CanonicalQuadraticSieve

section
open ConcretePrimeRowBridge ActualEisensteinCubic CompletedGauss ConcreteTraceCRT

theorem primaryGenerator_admissible (I : Ideal O) (hI : Admissible I) : primaryGenerator I ≠ 0 :=
  PrimaryIdealUnitReindex.primaryGenerator_ne_zero_of_good_factors I hI.1
    (fun P hP => (hI.2.2 P hP).1)

end

open ActualEisensteinCubic CompletedGauss

end CanonicalQuadraticSieve

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.MeanSquare.SourceTransfer
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

open scoped BigOperators Classical SchwartzMap ContDiff

open scoped BigOperators Classical
namespace InitialMeanSquare
open ActualEisensteinCubic ConcretePrimeRowBridge CanonicalQuadraticSieve
open CompletedGauss FirstCauchyArithmetic ShortDraftHeckeBridge

lemma pool_support_product (F : Finset (Ideal O)) (S : Finset (primePool F)) :
    idealSupport F (∏i∈S,i.val)=S := by
  have hp (i : primePool F) : Prime i.val :=
    Ideal.prime_of_isPrime (NeZero.ne i.val) inferInstance
  have hn : (∏i∈S,i.val)≠(0:Ideal O) :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => (hp i).ne_zero)
  ext i
  rw [mem_idealSupport_iff,UniqueFactorizationMonoid.mem_normalizedFactors_iff hn]
  simp only [family_prime_dvd_product_iff _ Subtype.val_injective S i,hp,true_and]

theorem sum_selected_ideals (F : Finset (Ideal O)) (hF : ∀I∈F,Squarefree I)
    (a : Ideal O→ℂ) :
    (∑I∈F,a I)=∑S∈(Finset.univ:Finset (primePool F)).powerset,
      if (∏i∈S,i.val)∈F then a (∏i∈S,i.val) else 0 := by
  rw [←Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun S _ => ∏i∈S,i.val)
  · intro S hS
    exact (Finset.mem_filter.mp hS).2
  · intro S hS T hT he
    exact family_product_injective (fun i:primePool F => i.val) Subtype.val_injective he
  · intro I hI
    refine ⟨idealSupport F I,?_,idealSupport_product_eq F hI (hF I hI)⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr (Finset.subset_univ _),?_⟩
    rwa [idealSupport_product_eq F hI (hF I hI)]
  · intro S hS
    rfl

end InitialMeanSquare

open scoped BigOperators Classical SchwartzMap FourierTransform
open MeasureTheory

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.MeanSquare.InputEnergy
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

open scoped BigOperators Classical SchwartzMap ContDiff
namespace InitialMeanSquare
open ActualEisensteinCubic ConcretePrimeRowBridge CanonicalQuadraticSieve
open FirstPassCubeLabels (primeProductNorm columnLog)

theorem poolProduct_admissible (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I)
    (S : Finset (primePool F)) : Admissible (∏ i ∈ S,i.val) := by
  have hp (i : primePool F) : Prime i.val :=
    Ideal.prime_of_isPrime (NeZero.ne i.val) inferInstance
  have hn : (∏ i ∈ S,i.val) ≠ (0 : Ideal O) :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => (hp i).ne_zero)
  refine ⟨hn, ?_, ?_⟩
  · apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro i hi j hj hij
      exact (Ideal.isCoprime_of_isMaximal (fun he => hij (Subtype.ext he))).isRelPrime
    · intro i hi
      exact (hp i).squarefree
  · intro P hP
    obtain ⟨hprime, hdiv⟩ := (UniqueFactorizationMonoid.mem_normalizedFactors_iff hn).mp hP
    obtain ⟨i, hi, hPi⟩ := (hprime.dvd_finsetProd_iff (fun i : primePool F => i.val)).mp hdiv
    have he : P=i.val := (prime_dvd_prime_iff_eq hprime (hp i)).mp hPi
    rw [he]
    exact ⟨poolGood F hF i, poolOdd F hF i⟩

theorem poolPrimary_norm (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I)
    (S : Finset (primePool F)) :
    primeProductNorm (poolPrimary F) S = (Ideal.absNorm (∏ i ∈ S,i.val) : ℝ) := by
  rw [primeProductNorm, eisEmbedding_norm_sq_eq_absNorm_span, FiniteGaussPhase.span_finset_prod]
  congr 2
  apply Finset.prod_congr rfl
  intro i hi
  exact poolPrimary_span F hF i

end InitialMeanSquare

open scoped BigOperators Classical SchwartzMap

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Cusp.StaticReflectionPhases
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

open scoped Classical BigOperators

namespace CanonicalRowCompletion
open ActualEisensteinCubic CanonicalQuadraticSieve CanonicalCoefficientClass
local notation "Eis" => ActualEisensteinCubic.O

lemma reflectionConductor_ne_zero (q:ℕ) (hq:q≠0) : reflectionConductor q≠0 := by
  unfold reflectionConductor
  exact_mod_cast Nat.mul_ne_zero (by decide : 2592≠0) hq

lemma reflectionConductor_prime_mem (q:ℕ) (hq:q≠0) (P:Ideal Eis)
    (hP:Prime P) (hd:P∣Ideal.span {reflectionConductor q}) :
    P∈reflectionExcludedPrimes q := by
  apply Finset.mem_union_right
  apply Multiset.mem_toFinset.mpr
  apply (Ideal.mem_normalizedFactors_iff (Ideal.span_singleton_eq_bot.not.mpr
    (reflectionConductor_ne_zero q hq))).mpr
  exact ⟨Ideal.isPrime_of_prime hP,Ideal.dvd_iff_le.mp hd⟩

end CanonicalRowCompletion

open scoped BigOperators Classical

open scoped BigOperators Classical MatrixGroups Matrix

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

theorem initial_input_row (F : Finset ι) (Ψ : O →* ℂ) (j : O)
    (H : Finset ι→ℂ) (z : O) :
    inputConjugateRow p hg F Ψ j 1 1 H z =
      FirstCauchyArithmetic.supportConjugateSum (fun i=>Ideal.span {p i}) hg F
        (fun S=>Ψ (∏ i∈S,p i)*rowCoprimeMask (fun i=>Ideal.span {p i}) S j*H S) z := by
  unfold inputConjugateRow
  congr 1
  funext S
  have hone := ActualEisensteinCubic.finiteSquarefreeRow_one (fun i=>Ideal.span {p i}) hg S
  simp only [secondInputCoefficient,hone,one_pow,mul_one]

end SevenEighths.InverseInitialArithmetic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.Counting
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentCounting
open CenteredMomentPrimary
open QuadraticInitialBound

theorem norm_tsum_ideal_ball (f : Ideal O → ℂ) (H M : ℝ)
    (hH : 0 ≤ H) (hM : 0 ≤ M) (hzero : f ⊥ = 0)
    (hbound : ∀ I, ‖f I‖ ≤ M)
    (hsupport : ∀ I, f I ≠ 0 → (Ideal.absNorm I : ℝ) ≤ H) :
    ‖∑' I : Ideal O, f I‖ ≤ 128 * M * H := by
  classical
  have hfinite : (Function.support f).Finite := by
    apply (Ideal.finite_setOfPred_absNorm_le (S := O) (Nat.ceil H)).subset
    intro I hI
    exact_mod_cast (hsupport I hI).trans (Nat.le_ceil H)
  let S := hfinite.toFinset
  have hmem (I : Ideal O) : I ∈ S ↔ f I ≠ 0 := hfinite.mem_toFinset
  have htsum : (∑' I : Ideal O, f I) = ∑ I ∈ S, f I := by
    exact tsum_eq_sum (fun I hI => not_ne_iff.mp (mt (hmem I).mpr hI))
  rw [htsum]
  by_cases hS : S.Nonempty
  · obtain ⟨I, hI⟩ := hS
    have hI0 : I ≠ ⊥ := by intro h; exact (hmem I).mp hI (h ▸ hzero)
    have hn : 1 ≤ (Ideal.absNorm I : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr
        (fun hz => hI0 (Ideal.absNorm_eq_zero_iff.mp hz))
    have hH1 : 1 ≤ H := hn.trans (hsupport I ((hmem I).mp hI))
    have hcount := DescentFiberCost.finite_ideal_count_real S H hH1
      (fun J hJ hz => (hmem J).mp hJ (hz ▸ hzero))
      (fun J hJ => hsupport J ((hmem J).mp hJ))
    calc
      _ ≤ ∑ I ∈ S, ‖f I‖ := norm_sum_le _ _
      _ ≤ ∑ _I ∈ S, M := Finset.sum_le_sum (fun I _ => hbound I)
      _ = (S.card : ℝ) * M := by simp
      _ ≤ (128 * H) * M := mul_le_mul_of_nonneg_right hcount hM
      _ = _ := by ring
  · rw [Finset.not_nonempty_iff_eq_empty.mp hS]
    simp only [Finset.sum_empty, norm_zero]
    positivity

end SevenEighths.CenteredMomentCounting
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.Dyadic
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open MeasureTheory Set
namespace SevenEighths.HeckeDyadic
open HeckeFamily

theorem coefficient_norm_le (χ : Character) (inverse : Bool) (I : Ideal O) :
    ‖coefficient χ inverse I‖ ≤ 1 := by
  cases inverse
  · exact idealCoeff_norm_le_one χ I
  · change ‖(UniqueFactorizationMonoid.moebius I : ℂ)*idealCoeff χ I‖ ≤ 1
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (CubicEisenstein.norm_ideal_moebius_le_one I)).trans
      (idealCoeff_norm_le_one χ I)

end SevenEighths.HeckeDyadic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialPoissonBridge
namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap ContDiff
namespace SevenEighths.InverseInitialPoissonBridge
open ActualEisensteinCubic CanonicalQuadraticSieve CanonicalRowCompletion
open ConcretePrimeRowBridge ConcreteTraceCRT EisensteinSchwartzPoisson
open UniqueFactorizationMonoid InverseInitialOverlap
local notation "Eis" => ActualEisensteinCubic.O

theorem idealRowHom_eq_idealSexticRow
    (F : Finset (Ideal Eis)) (hF : ∀ I ∈ F, Admissible I)
    {I : Ideal Eis} (hI : I ∈ F) (u : Eis) :
    idealRowHom u I = idealSexticRow F (pool_positive F hF) (pool_good F hF) I u := by
  let : ∀ q : primePool F, q.val.IsMaximal := primePool_maximal F (pool_positive F hF)
  conv_lhs => rw [← idealSupport_product_eq F hI (hF I hI).2.1]
  rw [map_prod]
  change (∏ q ∈ idealSupport F I, idealRowHom u q.val) =
    ∏ q ∈ idealSupport F I, CompletedGauss.actualSextic q.val (primePool_good F (pool_good F hF) q)
      (Ideal.Quotient.mk q.val u)
  apply Finset.prod_congr rfl
  intro q hq
  exact idealRowHom_prime u q.val (primePool_good F (pool_good F hF) q)

theorem heckeIdealCharacter_apply (η : Ideal Eis →* ℂ) (u : Eis) (I : Ideal Eis) :
    heckeIdealCharacter η u I = η I * idealRowHom u I := rfl

end SevenEighths.InverseInitialPoissonBridge

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialRayAttachment
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseInitialRayAttachment
open ActualEisensteinCubic ConcretePrimeRowBridge CanonicalQuadraticSieve
open CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid
open FirstCauchyArithmetic SecondPassArithmetic ConcreteTraceCRT EisensteinSchwartzPoisson
open InverseInitialOverlap InverseInitialPoissonBridge InverseInitialKernelBridge
open InverseInitialArithmetic InverseInitialProfile
local notation "O" => ActualEisensteinCubic.O

theorem elementCharacter_product {ι : Type*} (η : Ideal O →* ℂ)
    (p : ι → O) (A : Finset ι) :
    elementCharacter η (∏ i ∈ A,p i) = η (∏ i ∈ A,Ideal.span {p i}) := by
  change η (Ideal.span {∏ i ∈ A,p i}) = _
  rw [FiniteGaussPhase.span_finset_prod]

theorem selected_mask (F : Finset (Ideal O)) (j : Ideal O) (hj : Admissible j)
    (A : Finset (primePool F)) (hcop : IsCoprime (∏ i ∈ A,i.val) j) :
    rowCoprimeMask (fun i : primePool F => i.val) A (primaryGenerator j)=1 := by
  have hspan := (primaryGenerator_spec j (primaryGenerator_admissible j hj)).1
  unfold rowCoprimeMask
  split_ifs with h
  · obtain ⟨i,hi,hm⟩ := h
    have hd : i.val ∣ ∏ k ∈ A,k.val := Finset.dvd_prod_of_mem _ hi
    have hjd : i.val ∣ j := by
      rw [Ideal.dvd_iff_le,←hspan]
      exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hm)
    have hp : Prime i.val := Ideal.prime_of_isPrime (NeZero.ne i.val) inferInstance
    exact False.elim (hp.not_isUnit (hcop.isRelPrime hd hjd))
  · rfl

theorem selected_conjugate_row (F : Finset (Ideal O))
    (hF : ∀ I ∈ F,Admissible I) (j : Ideal O) (hj : Admissible j)
    (hcop : ∀ I ∈ F,IsCoprime I j) (η : Ideal O →* ℂ) (H : Ideal O → ℂ) (u : O) :
    let : ∀ i : primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i => by rw [poolPrimary_span F hF i]; infer_instance
    (∑ I ∈ F,(moebius I : ℂ)*η I*H I*star (idealRowHom u I)) =
      inputConjugateRow (poolPrimary F) (poolPrimary_good F hF) Finset.univ
        (elementCharacter η) (primaryGenerator j) 1 1
        (fun A => if (∏ i ∈ A,i.val)∈F then H (∏ i ∈ A,i.val) else 0) u := by
  let : ∀ i : primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i => by rw [poolPrimary_span F hF i]; infer_instance
  have he : (fun i : primePool F => Ideal.span {poolPrimary F i}) =
      (fun i : primePool F => i.val) := funext (poolPrimary_span F hF)
  dsimp only
  rw [InitialMeanSquare.sum_selected_ideals F (fun I hI => (hF I hI).2.1)]
  erw [initial_input_row]
  unfold supportConjugateSum
  apply Finset.sum_congr rfl
  intro A hA
  dsimp only
  rw [elementCharacter_product]
  simp only [he]
  by_cases hAF : (∏ i ∈ A,i.val)∈F
  · simp only [hAF,ite_true]
    rw [selected_mask F j hj A (hcop _ hAF),mul_one]
    rw [idealRowHom_eq_idealSexticRow F hF hAF]
    simp only [supportMobius,idealSexticRow,InitialMeanSquare.pool_support_product]
    ring
  · simp only [hAF,ite_false,mul_zero,zero_mul]

end SevenEighths.InverseInitialRayAttachment

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialConjugateEnergy
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseInitialConjugateEnergy
open ActualEisensteinCubic CanonicalRowCompletion CanonicalQuadraticSieve
open ConcretePrimeRowBridge CompletedGauss ConcreteTraceCRT
open InverseInitialOverlap InverseInitialPoissonBridge InverseInitialRayAttachment
open UniqueFactorizationMonoid IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O

theorem radialWeight_nonneg (Φ : 𝓢(ℝ,ℂ)) (hΦ : ∀ x : ℝ,0≤x → 0≤(Φ x).re)
    {Y : ℝ} (hY : 0<Y) (u : O) : 0≤ radialWeight Φ Y u :=
  hΦ _ (div_nonneg (sq_nonneg _) hY.le)

theorem smoothedEnergy_nonneg (Φ : 𝓢(ℝ,ℂ)) (hΦ : ∀ x : ℝ,0≤x → 0≤(Φ x).re)
    {Y : ℝ} (hY : 0<Y) (f : O → ℂ) : 0≤ smoothedEnergy Φ Y f :=
  tsum_nonneg (fun u => mul_nonneg (radialWeight_nonneg Φ hΦ hY u) (sq_nonneg _))

theorem real_smoothed_sum_eq (Φ : 𝓢(ℝ,ℂ))
    (hΦ : ∀ x : ℝ,0≤x → (Φ x).im=0) {Y : ℝ} (hY : 0<Y) (f : O → ℂ) :
    (∑' u : O,Φ (‖eisEmbedding u‖^2/Y)*(‖f u‖^2 : ℝ)) =
      (smoothedEnergy Φ Y f : ℂ) := by
  unfold smoothedEnergy
  rw [Complex.ofReal_tsum]
  apply tsum_congr
  intro u
  have he : Φ (‖eisEmbedding u‖^2/Y) = (radialWeight Φ Y u : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using hΦ _ (div_nonneg (sq_nonneg _) hY.le)
  rw [he,Complex.ofReal_mul]

end SevenEighths.InverseInitialConjugateEnergy

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.ComparisonReflection
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentComparisonReflection
open HeckeFamily HeckePrimitive ActualEisensteinCubic ConcreteTraceCRT
open EisensteinSchwartzPoisson ConcretePrimeRowBridge GaussGeneratorTransport
local notation "O" => HeckeFamily.O
local notation "NI" => UnrestrictedIdealReindex.NonzeroIdeal

lemma inverse_half_power (X : ℝ) (hX : 0≤X) :
    (X:ℂ)^(-(1/2:ℂ))=(Real.sqrt X:ℂ)⁻¹ := by
  rw [Complex.cpow_neg]
  congr 1
  rw [Real.sqrt_eq_rpow]
  simpa only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] using (Complex.ofReal_cpow hX (1/2)).symm

end SevenEighths.CenteredMomentComparisonReflection

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.OriginalReflectionErrorMass
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentOriginalReflectionErrorMass
open HeckeFamily HeckeDyadic HeckePrimeAnnular HeckePrimeRay
open CenteredMomentCounting CenteredMomentComparisonReflection
open QuadraticInitialBound ConcreteTraceCRT
local notation "O" => HeckeFamily.O

lemma annularWeight_zero_norm (W : ℝ→ℂ) (D freq : ℝ) (hD : 0<D)
    (I : Ideal O) (hI : I≠0) :
    ‖annularWeight W D 0 freq I‖=‖W ((I.absNorm:ℝ)/D)‖ := by
  have hn : 0<(I.absNorm:ℝ):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  rw [annularWeight,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (div_pos hn hD)]
  simp only [Complex.neg_re,shift_re,neg_zero,Real.rpow_zero,mul_one]

lemma normalized_linear_bound (D c : ℝ) (hD : 0<D) (v : ℂ)
    (hv : ‖v‖≤ c*D) : ‖(D:ℂ)^(-(1/2:ℂ))*v‖≤ c*Real.sqrt D := by
  rw [inverse_half_power D hD.le,norm_mul,norm_inv,Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg D)]
  have hs:Real.sqrt D≠0:=(Real.sqrt_pos.mpr hD).ne'
  have hd:D/Real.sqrt D=Real.sqrt D:=by
    apply (div_eq_iff hs).mpr
    simpa only [pow_two] using (Real.sq_sqrt hD.le).symm
  calc
    _ ≤ (Real.sqrt D)⁻¹*(c*D):=mul_le_mul_of_nonneg_left hv (inv_nonneg.mpr (Real.sqrt_nonneg D))
    _ = c*(D/Real.sqrt D):=by ring
    _ = _:=by rw [hd]

lemma compact_norm_bound (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) (hW : Continuous W) :
    ∃B:ℝ,0<B ∧ ∀x,‖W x‖≤B := by
  obtain ⟨B,hB,hbound⟩:=fixed_profile_norm_bound W hW a b 0 0 ha
  refine ⟨B,hB,?_⟩
  intro x
  by_cases hx:W x=0
  · simpa only [hx,norm_zero] using hB.le
  · simpa using hbound 0 (by simp) x (hs hx)

end SevenEighths.CenteredMomentOriginalReflectionErrorMass

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Dictionary.InverseRawCompact
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.DetectorDictionaryInverseRawCompact
open HeckeFamily HeckeDyadic HeckeInverseAmplification InverseMoment FourierBridge HeckePrimeAnnular
open CenteredMomentOriginalReflectionErrorMass CenteredMomentCounting
open ActualEisensteinCubic ConcreteTraceCRT

local notation "O" => HeckeFamily.O

lemma inverse_polynomial_all_ideals (χ : Character) (W : ℝ→ℂ) (D freq : ℝ) :
    polynomial χ true W D 0 freq =
      (D:ℂ)^(-(1/2:ℂ))*∑'I:Ideal O,coefficient χ true I*annularWeight W D 0 freq I := by
  unfold polynomial
  congr 1
  have he : (∑'I:HeckeDyadic.NonzeroIdeal,coefficient χ true I.val*annularWeight W D 0 freq I.val)=
      ∑'I:Ideal O,coefficient χ true I*annularWeight W D 0 freq I := by
    apply tsum_subtype_eq_of_support_subset (s:={I:Ideal O|I≠0})
      (f:=fun I:Ideal O=>coefficient χ true I*annularWeight W D 0 freq I)
    intro I hI hz
    subst I
    exact hI (by simp only [coefficient_zero,zero_mul])
  simpa only [summand,HeckeDyadic.norm,annularWeight,mul_assoc] using he

theorem inverse_polynomial_bound (χ : Character) (W : ℝ→ℂ) (b B D freq : ℝ)
    (hB : 0≤B) (hD : 0<D) (hW : ∀x,‖W x‖≤B)
    (hs : Function.support W⊆Set.Iic b) :
    ‖polynomial χ true W D 0 freq‖≤(128*max 1 b*B)*Real.sqrt D := by
  rw [inverse_polynomial_all_ideals]
  apply normalized_linear_bound D _ hD
  have hh:=norm_tsum_ideal_ball (fun I:Ideal O=>coefficient χ true I*annularWeight W D 0 freq I)
    (max 1 b*D) B (by positivity) hB (by
      change coefficient χ true (0:Ideal O)*_ = 0
      rw [coefficient_zero,zero_mul])
    (by
      intro I
      by_cases hI:I=0
      · subst I
        simpa only [coefficient_zero,zero_mul,norm_zero] using hB
      rw [norm_mul,annularWeight_zero_norm W D freq hD I hI]
      exact (mul_le_mul (coefficient_norm_le χ true I) (hW _) (norm_nonneg _) zero_le_one).trans_eq
        (one_mul B))
    (by
      intro I hne
      have hw : W ((I.absNorm:ℝ)/D)≠0 := by
        intro hz
        exact hne (by simp only [annularWeight,hz,zero_mul,mul_zero])
      exact ((div_le_iff₀ hD).mp (hs hw)).trans
        (mul_le_mul_of_nonneg_right (le_max_right 1 b) hD.le))
  convert (preTransparency := .instances) hh using 1; ring

lemma childLogTest_norm (W : ℝ→ℂ) (s x : ℝ) :
    ‖childLogTest W s x‖=‖W x‖ := by
  simp only [childLogTest,norm_mul,logPhase_norm,mul_one]

theorem inverse_reference_bound (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) :
    ∃A:ℝ,0<A ∧ ∀(χ:Character) (s D:ℝ),0<D →
      ‖polynomial χ true (childLogTest W s) D 0 0‖≤A*Real.sqrt D := by
  obtain ⟨B,hB,hbound⟩:=compact_norm_bound W a b ha hs W.continuous
  refine ⟨128*max 1 b*B,by positivity,?_⟩
  intro χ s D hD
  apply inverse_polynomial_bound χ (childLogTest W s) b B D 0 hB.le hD
  · intro x
    simpa only [childLogTest_norm] using hbound x
  · intro x hx
    have hw : W x≠0 := by
      intro hz
      exact hx (by simp only [childLogTest,hz,zero_mul])
    exact (hs hw).2

theorem nonzero_element_rows_card (rows : Finset NonzeroElement) (H : ℝ) (hH : 1≤H)
    (hrows : ∀v∈rows,((Ideal.span {v.val}).absNorm:ℝ)≤H) :
    (rows.card:ℝ)≤128*H := by
  have hh:=DescentFiberCost.finite_element_count_real (rows.image Subtype.val) H hH (by
    intro z hz
    obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hz
    rw [eisEmbedding_norm_sq_eq_absNorm_span]
    exact hrows v hv)
  rw [Finset.card_image_of_injective _ Subtype.val_injective] at hh
  exact hh

theorem reference_energy_linear (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) :
    ∃K:ℝ,0<K ∧ ∀(χ:NonzeroElement→Character) (rows:Finset NonzeroElement)
      (s H D:ℝ),1≤H → 0<D →
      (∀v∈rows,((Ideal.span {v.val}).absNorm:ℝ)≤H) →
      (∑v∈rows,‖polynomial (χ v) true (childLogTest W s) D 0 0‖^2)≤K*H*D := by
  obtain ⟨A,hA,hbound⟩:=inverse_reference_bound W a b ha hs
  refine ⟨128*A^2,by positivity,?_⟩
  intro χ rows s H D hH hD hrows
  calc
    _≤∑v∈rows,A^2*D := by
      apply Finset.sum_le_sum
      intro v _
      have hh:=pow_le_pow_left₀ (norm_nonneg _) (hbound (χ v) s D hD) 2
      simpa only [mul_pow,Real.sq_sqrt hD.le] using hh
    _=(rows.card:ℝ)*(A^2*D) := by simp
    _≤(128*H)*(A^2*D) := mul_le_mul_of_nonneg_right
      (nonzero_element_rows_card rows H hH hrows) (by positivity)
    _=(128*A^2)*H*D := by ring

lemma scale_le_rows (c H D : ℝ) (hc : 0≤ c) (hH : 1≤H)
    (_hD : 0<D) (hDH : D^(1+c)≤H) : D≤H := by
  by_cases hD1:D≤1
  · exact hD1.trans hH
  · have hd : 1≤D := le_of_not_ge hD1
    calc
      D=D^(1:ℝ) := (Real.rpow_one D).symm
      _≤D^(1+c) := Real.rpow_le_rpow_of_exponent_le hd (by linarith)
      _≤H := hDH

lemma raw_majorant_ge_linear (C C0 H D κ s : ℝ) (J : ℕ)
    (hC : 0≤C) (hC0 : 0≤C0) (hH : 1≤H) (hκ : 0≤κ) :
    C0*H≤((C+C0)*(1+‖s‖)^(2*J))*H*(H*max 1 D)^κ := by
  have ht : 1≤(1+‖s‖)^(2*J) := one_le_pow₀ (by linarith [norm_nonneg s])
  have hb : 1≤H*max 1 D := hH.trans
    (le_mul_of_one_le_right (by positivity) (le_max_left _ _))
  have hp : 1≤(H*max 1 D)^κ := Real.one_le_rpow hb hκ
  calc
    C0*H≤(C+C0)*H := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _≤((C+C0)*(1+‖s‖)^(2*J))*H := mul_le_mul_of_nonneg_right
      (le_mul_of_one_le_right (by positivity) ht) (by positivity)
    _≤_ := le_mul_of_one_le_right (by positivity) hp

theorem rawMoment_of_large_rows_ge_one (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) (H0 : ℝ) (hH0 : 1≤H0) :
    ∃C0:ℝ,0<C0 ∧ ∀(data:RowData) (c κ C:ℝ) (J:ℕ),
      0≤ c → 0≤κ → 0≤C →
      (∀(s H D:ℝ),H0≤H → 1≤D → D^(1+c)≤H →
        ∀rows:Finset NonzeroElement,
          (∀v∈rows,((Ideal.span {v.val}).absNorm:ℝ)≤H) →
          (∑v∈rows,‖polynomial (data.character v) true (childLogTest W s) D 0 0‖^2)≤
            (C*(1+‖s‖)^(2*J))*H*(H*max 1 D)^κ) →
      ∀s:ℝ,RawMoment data (childLogTest W s) c κ ((C+C0)*(1+‖s‖)^(2*J)) := by
  obtain ⟨K,hK,hbound⟩:=reference_energy_linear W a b ha hs
  refine ⟨K*H0,by positivity,?_⟩
  intro data c κ C J hc hκ hC hlarge s H D hH hD hDH rows hrows
  have hsmall (hDH0:D≤H0) :
      (∑v∈rows,‖polynomial (data.character v) true (childLogTest W s) D 0 0‖^2)≤
        ((C+K*H0)*(1+‖s‖)^(2*J))*H*(H*max 1 D)^κ := by
    calc
      _≤K*H*D := hbound data.character rows s H D hH hD hrows
      _≤K*H*H0 := mul_le_mul_of_nonneg_left hDH0 (by positivity)
      _=(K*H0)*H := by ring
      _≤_ := raw_majorant_ge_linear C (K*H0) H D κ s J hC (by positivity) hH hκ
  by_cases hHH0:H≤H0
  · exact hsmall ((scale_le_rows c H D hc hH hD hDH).trans hHH0)
  by_cases hD1:D≤1
  · exact hsmall (hD1.trans hH0)
  · apply (hlarge s H D (le_of_not_ge hHH0) (le_of_not_ge hD1) hDH rows hrows).trans
    gcongr
    exact le_add_of_nonneg_right (by positivity)

end SevenEighths.DetectorDictionaryInverseRawCompact

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Dictionary.InverseRawGeometry
namespace OAI

noncomputable section
namespace SevenEighths.DetectorDictionaryInverseRawGeometry
open InverseMoment InverseInitialCanonicalState

theorem capacityGap_pos (c : ℝ) (hc : 0<c) : 0<capacityGap c :=
  div_pos hc (by linarith)

theorem capacityGap_lt_one (c : ℝ) (hc : 0<c) : capacityGap c<1 := by
  apply (div_lt_one (by linarith : 0<1+c)).mpr
  linarith

theorem raw_log_capacity (H D c : ℝ) (hH : 1<H) (hD : 1≤D) (hc : 0<c)
    (hcap : D^(1+c)≤H) :
    0≤Real.logb H D ∧ Real.logb H D≤1-capacityGap c ∧
    2*Real.logb H D≤3-capacityGap c ∧ H^(Real.logb H D)=D := by
  have hHp : 0<H:=zero_lt_one.trans hH
  have hDp : 0<D:=zero_lt_one.trans_le hD
  have hlogH : 0<Real.log H:=Real.log_pos hH
  have hh:=Real.log_le_log (Real.rpow_pos_of_pos hDp (1+c)) hcap
  rw [Real.log_rpow hDp] at hh
  have hr : Real.logb H D≤1/(1+c) := by
    unfold Real.logb
    apply (le_div_iff₀ (by linarith : 0<1+c)).mpr
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hlogH).mpr
    simpa only [mul_div_assoc,mul_comm,mul_left_comm,one_mul] using hh
  have he : 1/(1+c)=1-capacityGap c := by
    unfold capacityGap
    field_simp
    ring
  have hg:=(capacityGap_pos c hc).le
  exact ⟨div_nonneg (Real.log_nonneg hD) hlogH.le,hr.trans_eq he,
    by linarith [hr.trans_eq he],Real.rpow_logb hHp (ne_of_gt hH) hDp⟩

theorem raw_fixed_reserves (c κ : ℝ) (hc : 0<c) (hκ : 0<κ) :
    ∃η τ π ε : ℝ,0<η ∧ 0<τ ∧ 0<π ∧ 0<ε ∧
      η≤1 ∧ η≤ capacityGap c/200 ∧ τ≤ capacityGap c/200 ∧
      40*η+π+ε≤κ := by
  let η:=min (capacityGap c/200) (min (κ/100) (1/100))
  have hg:=capacityGap_pos c hc
  have hη : 0<η:=lt_min (by positivity)
    (lt_min (by positivity) (by norm_num))
  have hηg : η≤ capacityGap c/200:=min_le_left _ _
  have hηκ : η≤κ/100:=(min_le_right _ _).trans (min_le_left _ _)
  have hη1 : η≤1/100:=(min_le_right _ _).trans (min_le_right _ _)
  refine ⟨η,η,κ/4,κ/4,hη,hη,by positivity,by positivity,by linarith,hηg,hηg,?_⟩
  linarith

theorem raw_output_budget (H D κ e : ℝ) (hH : 1≤H) (hκ : 0≤κ) (he : e≤κ) :
    H^(1+e)≤H*(H*max 1 D)^κ := by
  have hHp : 0<H:=zero_lt_one.trans_le hH
  rw [Real.rpow_add hHp,Real.rpow_one]
  apply mul_le_mul_of_nonneg_left _ hHp.le
  calc
    H^e≤H^κ:=Real.rpow_le_rpow_of_exponent_le hH he
    _≤(H*max 1 D)^κ:=Real.rpow_le_rpow hHp.le (by nlinarith [le_max_left 1 D]) hκ

end SevenEighths.DetectorDictionaryInverseRawGeometry

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialExcludedPolynomial
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.InverseInitialExcludedPolynomial
open HeckeFamily HeckeDyadic HeckeDetectorDyadicBridge
open InverseInitialExcludedSource IdealMobiusDivisorSum UniqueFactorizationMonoid
local notation "O"=>HeckeFamily.O

theorem prime_product_squarefree (S:Finset (Ideal O))(hS:∀P∈S,Prime P):
    Squarefree (∏P∈S,P) := by
  have hz:(∏P∈S,P)≠0:=Finset.prod_ne_zero_iff.mpr (fun P hP=>(hS P hP).ne_zero)
  apply (squarefree_iff_nodup_normalizedFactors hz).mpr
  have he:normalizedFactors (∏P∈S,P)=S.val:=by
    simpa using normalizedFactors_prod_of_prime (m:=S.val) (fun P hP=>hS P hP)
  rw [he]
  exact S.nodup

end SevenEighths.InverseInitialExcludedPolynomial

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialExcludedPeriod
namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.InverseInitialExcludedPeriod
open ActualEisensteinCubic CanonicalRowCompletion CanonicalQuadraticSieve
open CanonicalCoefficientClass ConcretePrimeRowBridge IdealMobiusDivisorSum
open UniqueFactorizationMonoid HeckeFamily
local notation "O" => ActualEisensteinCubic.O

theorem deletedPeriod_ne_zero (q:ℕ)(hq:q≠0):deletedPeriod q≠0 := by
  unfold deletedPeriod
  exact mul_ne_zero (by norm_num) (pow_ne_zero _ hq)

theorem fixed_bad_divides_reflection (q:ℕ)(P:Ideal O)(hP:P∈fixedBadPrimes):
    P∣Ideal.span {reflectionConductor q} := by
  change P∈({Ideal.span {goodLambda},Ideal.span {(2:O)}}:Finset (Ideal O)) at hP
  rcases Finset.mem_insert.mp hP with rfl|hP
  · apply Ideal.dvd_iff_le.mpr
    apply Ideal.span_singleton_le_span_singleton.mpr
    have h3:goodLambda∣(3:O):=CubicEisenstein.halfPrimary_lambda_dvd_three
    apply h3.trans
    refine ⟨(864*q:ℕ),?_⟩
    unfold reflectionConductor
    push_cast
    ring
  · rw [Finset.mem_singleton.mp hP]
    apply Ideal.dvd_iff_le.mpr
    apply Ideal.span_singleton_le_span_singleton.mpr
    refine ⟨(1296*q:ℕ),?_⟩
    unfold reflectionConductor
    push_cast
    ring

theorem excluded_mem_iff (q:ℕ)(hq:q≠0)(P:Ideal O):
    P∈reflectionExcludedPrimes q ↔ Prime P ∧ P∣Ideal.span {reflectionConductor q} := by
  constructor
  · intro hP
    refine ⟨reflectionExcludedPrimes_prime q P hP,?_⟩
    rcases Finset.mem_union.mp hP with hb|hp
    · exact fixed_bad_divides_reflection q P hb
    · exact dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hp)
  · rintro ⟨hp,hd⟩
    exact reflectionConductor_prime_mem q hq P hp hd

theorem excluded_product_divides_reflection (q:ℕ)(hq:q≠0):
    (∏P∈reflectionExcludedPrimes q,P)∣Ideal.span {reflectionConductor q} := by
  apply support_product_dvd (Ideal.span_singleton_eq_bot.not.mpr (reflectionConductor_ne_zero q hq))
  intro P hP
  apply Multiset.mem_toFinset.mpr
  apply (Ideal.mem_normalizedFactors_iff
    (Ideal.span_singleton_eq_bot.not.mpr (reflectionConductor_ne_zero q hq))).mpr
  obtain ⟨hp,hd⟩:= (excluded_mem_iff q hq P).mp hP
  exact ⟨Ideal.isPrime_of_prime hp,Ideal.dvd_iff_le.mp hd⟩

theorem deleted_reflection_ideal (q:ℕ):
    Ideal.span {reflectionConductor (deletedPeriod q)}=
      (Ideal.span {reflectionConductor q}:Ideal O)^2 := by
  rw [Ideal.span_singleton_pow]
  congr 1
  unfold reflectionConductor deletedPeriod
  push_cast
  ring_nf

theorem deleted_excluded_eq (q:ℕ)(hq:q≠0):
    reflectionExcludedPrimes (deletedPeriod q)=reflectionExcludedPrimes q := by
  ext P
  rw [excluded_mem_iff _ (deletedPeriod_ne_zero q hq),excluded_mem_iff q hq,
    deleted_reflection_ideal]
  constructor
  · rintro ⟨hp,hd⟩
    exact ⟨hp,hp.dvd_of_dvd_pow hd⟩
  · rintro ⟨hp,hd⟩
    exact ⟨hp,hd.trans (dvd_pow_self _ (by decide:2≠0))⟩

theorem deleted_period_ideal (q:ℕ):
    (Ideal.span {(deletedPeriod q:O)}:Ideal O)=
      Ideal.span {(q:O)}*Ideal.span {reflectionConductor q} := by
  rw [Ideal.span_singleton_mul_span_singleton]
  congr 1
  unfold deletedPeriod reflectionConductor
  push_cast
  ring_nf

theorem deleted_period_le_modulus (χ:Character)(q:ℕ)(hq:q≠0)
    (hperiod:Ideal.span {(q:O)}≤χ.modulus):
    Ideal.span {(deletedPeriod q:O)}≤
      (χ.excludePrimes (reflectionExcludedPrimes q) (reflectionExcludedPrimes_prime q)).modulus := by
  change Ideal.span {(deletedPeriod q:O)}≤χ.modulus*(∏P∈reflectionExcludedPrimes q,P)
  rw [deleted_period_ideal]
  exact Ideal.mul_mono hperiod (Ideal.dvd_iff_le.mp (excluded_product_divides_reflection q hq))

theorem deleted_element_period (χ:Character)(q:ℕ)(hq:q≠0)
    (hperiod:Ideal.span {(q:O)}≤χ.modulus):
    FactorsModulo (fixedBaseConductor (deletedPeriod q))
      (HeckeRowClosure.elementHom
        (χ.excludePrimes (reflectionExcludedPrimes q) (reflectionExcludedPrimes_prime q))) := by
  intro x y hxy
  apply HeckeRowClosure.elementHom_periodic
  exact deleted_period_le_modulus χ q hq hperiod (Ideal.mul_le_left hxy)

theorem deleted_base_gates (χ:Character)(q:ℕ)(hq:q≠0)
    (hperiod:Ideal.span {(q:O)}≤χ.modulus):
    deletedPeriod q≠0 ∧ reflectionExcludedPrimes (deletedPeriod q)=reflectionExcludedPrimes q ∧
    (∀x,‖HeckeRowClosure.elementHom
      (χ.excludePrimes (reflectionExcludedPrimes q) (reflectionExcludedPrimes_prime q)) x‖≤1) ∧
    FactorsModulo (fixedBaseConductor (deletedPeriod q))
      (HeckeRowClosure.elementHom
        (χ.excludePrimes (reflectionExcludedPrimes q) (reflectionExcludedPrimes_prime q))) := by
  exact ⟨deletedPeriod_ne_zero q hq,deleted_excluded_eq q hq,
    HeckeRowClosure.elementHom_norm _,deleted_element_period χ q hq hperiod⟩

end SevenEighths.InverseInitialExcludedPeriod

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialExcludedElement
namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.InverseInitialExcludedPeriod
open ActualEisensteinCubic CanonicalRowCompletion CanonicalQuadraticSieve
open CanonicalCoefficientClass HeckeFamily InverseInitialRayAttachment
local notation "O"=>ActualEisensteinCubic.O

theorem elementCharacter_eq_elementHom (χ:Character)(hproper:χ.modulus≠⊤):
    elementCharacter (idealCoeff χ).toMonoidHom=HeckeRowClosure.elementHom χ := by
  let:Nontrivial (O⧸χ.modulus):=Ideal.Quotient.nontrivial_iff.mpr hproper
  ext z
  change idealCoeff χ (Ideal.span {z})=elementCoeff χ z
  by_cases hz:z=0
  · subst z
    simp only [Ideal.span_singleton_zero,←Ideal.zero_eq_bot,
      elementCoeff,map_zero,MulChar.map_zero]
  · exact idealCoeff_span χ hz

theorem deleted_modulus_proper (χ:Character)(q:ℕ):
    (χ.excludePrimes (reflectionExcludedPrimes q) (reflectionExcludedPrimes_prime q)).modulus≠⊤ := by
  have htwo:(Ideal.span {(2:O)}:Ideal O)∈reflectionExcludedPrimes q:=
    reflectionExcludedPrimes_bad q (by simp [fixedBadPrimes])
  have hle:(χ.excludePrimes (reflectionExcludedPrimes q) (reflectionExcludedPrimes_prime q)).modulus≤
      Ideal.span {(2:O)}:=by
    change χ.modulus*(∏P∈reflectionExcludedPrimes q,P)≤Ideal.span {(2:O)}
    exact Ideal.mul_le_right.trans (Ideal.dvd_iff_le.mp (Finset.dvd_prod_of_mem (fun P=>P) htwo))
  intro he
  exact twoIdeal_maximal.ne_top (top_le_iff.mp (he ▸ hle))

theorem deleted_physical_element_eq (χ:Character)(q:ℕ):
    elementCharacter (idealCoeff
      (χ.excludePrimes (reflectionExcludedPrimes q) (reflectionExcludedPrimes_prime q))).toMonoidHom=
      HeckeRowClosure.elementHom
        (χ.excludePrimes (reflectionExcludedPrimes q) (reflectionExcludedPrimes_prime q)) :=
  elementCharacter_eq_elementHom _ (deleted_modulus_proper χ q)

theorem deleted_physical_base_gates (χ:Character)(q:ℕ)(hq:q≠0)
    (hperiod:Ideal.span {(q:O)}≤χ.modulus):
    deletedPeriod q≠0 ∧ reflectionExcludedPrimes (deletedPeriod q)=reflectionExcludedPrimes q ∧
    (∀x,‖elementCharacter (idealCoeff
      (χ.excludePrimes (reflectionExcludedPrimes q) (reflectionExcludedPrimes_prime q))).toMonoidHom x‖≤1) ∧
    FactorsModulo (fixedBaseConductor (deletedPeriod q))
      (elementCharacter (idealCoeff
        (χ.excludePrimes (reflectionExcludedPrimes q) (reflectionExcludedPrimes_prime q))).toMonoidHom) := by
  rw [deleted_physical_element_eq]
  exact deleted_base_gates χ q hq hperiod

end SevenEighths.InverseInitialExcludedPeriod

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Dictionary.InverseRawInitialGates
namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap Topology
open Filter
namespace SevenEighths.DetectorDictionaryInverseRawInitialGates
open HeckeFamily HeckeDyadic HeckeInverseAmplification InverseInitialDetectorSource
open InverseInitialRawDictionary InverseInitialRayAttachment InverseInitialExcludedPeriod
open InverseInitialExcludedPool InverseInitialExcludedPolynomial
open CanonicalRowCompletion CanonicalCoefficientClass CanonicalQuadraticSieve ConcreteTraceCRT
open ConcretePrimeRowBridge UniqueFactorizationMonoid IdealMobiusDivisorSum
open DetectorDictionaryInverseRawGeometry
local notation "O"=>HeckeFamily.O

theorem basePeriod_ne_zero (data:RowData):basePeriod data≠0:=Nat.ne_of_gt (Character.period_pos _)

theorem basePeriod_le (data:RowData):Ideal.span {(basePeriod data:O)}≤(baseCharacter data).modulus:=
  Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (Character.period_mem _))

theorem raw_base_gates (data:RowData):
    deletedPeriod (basePeriod data)≠0 ∧
    reflectionExcludedPrimes (deletedPeriod (basePeriod data))=excluded data ∧
    (∀x,‖elementCharacter (idealCoeff (deletedBase data)).toMonoidHom x‖≤1) ∧
    FactorsModulo (fixedBaseConductor (deletedPeriod (basePeriod data)))
      (elementCharacter (idealCoeff (deletedBase data)).toMonoidHom):=
  deleted_physical_base_gates (baseCharacter data) (basePeriod data)
    (basePeriod_ne_zero data) (basePeriod_le data)

theorem completeCutoff_tree (H b Btree cap:ℝ):
    Btree*H^(cap+1)≤(completeCutoff H b Btree cap:ℝ):=
  (le_max_left _ _).trans (Nat.le_ceil _)

theorem completeCutoff_columns (H b Btree cap D n:ℝ)(hb:0≤b)(hD:0≤D)
    (hDH:D≤H)(hn:1≤n):b*(D/n)≤(completeCutoff H b Btree cap:ℝ):=by
  have hn0:0<n:=zero_lt_one.trans_le hn
  have hdn:D/n≤D:=(div_le_iff₀ hn0).mpr (le_mul_of_one_le_right hD hn)
  exact (mul_le_mul_of_nonneg_left (hdn.trans hDH) hb).trans
    ((le_max_right _ _).trans (Nat.le_ceil _))

theorem excluded_divisor_norm (data:RowData)(j:Ideal O)
    (hj:j∈idealDivisors (∏P∈excluded data,P)):
    1≤(j.absNorm:ℝ) ∧ (j.absNorm:ℝ)≤((∏P∈excluded data,P).absNorm:ℝ):=by
  have hP:Squarefree (∏P∈excluded data,P):=
    prime_product_squarefree _ (reflectionExcludedPrimes_prime (basePeriod data))
  have hd: j∣∏P∈excluded data,P:=(mem_idealDivisors hP.ne_zero).mp hj
  have hj0:=ne_zero_of_dvd_ne_zero hP.ne_zero hd
  constructor
  · exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hj0)
  · exact_mod_cast Nat.le_of_dvd
      (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hP.ne_zero)) (map_dvd Ideal.absNorm hd)

theorem shifted_raw_geometry_eventually (data:RowData)(c eta:ℝ)(hc:0<c)(heta:0<eta):
    ∀ᶠH:ℝ in atTop,1<H ∧ ∀D:ℝ,1≤D→D^(1+c)≤H→
      ∀j∈idealDivisors (∏P∈excluded data,P),
      let r:=Real.logb H (D/(j.absNorm:ℝ));
      -eta≤ r ∧ r≤1-capacityGap c ∧ 2*r≤3-capacityGap c ∧
      H^r=D/(j.absNorm:ℝ) ∧ r+7*eta≤1+7*eta ∧ D≤H:=by
  have ht:∀ᶠH:ℝ in atTop,((∏P∈excluded data,P).absNorm:ℝ)≤H^eta:=
    (tendsto_rpow_atTop heta).eventually (eventually_ge_atTop _)
  filter_upwards [eventually_gt_atTop (1:ℝ),ht] with H hH ht
  refine ⟨hH,?_⟩
  intro D hD hcap j hj r
  obtain ⟨hn,hnB⟩:=excluded_divisor_norm data j hj
  have hH0:0<H:=zero_lt_one.trans hH
  have hD0:0<D:=zero_lt_one.trans_le hD
  have hn0:0<(j.absNorm:ℝ):=zero_lt_one.trans_le hn
  obtain ⟨hr0,hr1,hr2,hex⟩:=raw_log_capacity H D c hH hD hc hcap
  have hr:r=Real.logb H D-Real.logb H (j.absNorm:ℝ):=
    Real.logb_div hD0.ne' hn0.ne'
  have hnlog:0≤Real.logb H (j.absNorm:ℝ):=
    div_nonneg (Real.log_nonneg hn) (Real.log_pos hH).le
  have hneta:Real.logb H (j.absNorm:ℝ)≤eta:=by
    exact (Real.logb_le_iff_le_rpow hH hn0).mpr (hnB.trans ht)
  have hrlo:-eta≤ r:=by rw [hr];linarith
  have hrup:r≤1-capacityGap c:=by rw [hr];linarith
  refine ⟨hrlo,hrup,by rw [hr];linarith,
    Real.rpow_logb hH0 hH.ne' (div_pos hD0 hn0),?_,?_⟩
  · linarith [(capacityGap_pos c hc).le]
  · calc
      D=H^(Real.logb H D):=hex.symm
      _≤H^1:=Real.rpow_le_rpow_of_exponent_le hH.le (by linarith [(capacityGap_pos c hc).le])
      _=H:=Real.rpow_one _

end SevenEighths.DetectorDictionaryInverseRawInitialGates

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Dictionary.InverseRawConjugateGates
namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.DetectorDictionaryInverseRawConjugateGates
open CanonicalRowCompletion
open HeckeFamily HeckeDyadic HeckeInverseAmplification InverseInitialConjugateEnergy
open InverseInitialRayAttachment InverseInitialExcludedPeriod CanonicalCoefficientClass
open DetectorDictionaryInverseRawInitialGates InverseInitialExcludedPool
open InverseMoment InverseInitialProfile
local notation "O"=>HeckeFamily.O

theorem conjugate_element_apply (η:Ideal O→*ℂ)(x:O):
    elementCharacter (conjugateIdealCharacter η) x=star (elementCharacter η x):=rfl

theorem conjugate_element_factors (η:Ideal O→*ℂ)(Q:Ideal O)
    (h:FactorsModulo Q (elementCharacter η)):
    FactorsModulo Q (elementCharacter (conjugateIdealCharacter η)):=by
  intro x y hxy
  exact congrArg star (h x y hxy)

theorem conjugate_element_norm (η:Ideal O→*ℂ)(x:O):
    ‖elementCharacter (conjugateIdealCharacter η) x‖=‖elementCharacter η x‖:=by
  rw [conjugate_element_apply,norm_star]

theorem raw_conjugate_base_gates (data:RowData):
    deletedPeriod (basePeriod data)≠0 ∧
    reflectionExcludedPrimes (deletedPeriod (basePeriod data))=excluded data ∧
    (∀x,‖elementCharacter (conjugateIdealCharacter
      (idealCoeff (deletedBase data)).toMonoidHom) x‖≤1) ∧
    FactorsModulo (fixedBaseConductor (deletedPeriod (basePeriod data)))
      (elementCharacter (conjugateIdealCharacter (idealCoeff (deletedBase data)).toMonoidHom)):=by
  obtain ⟨hq,he,hn,hp⟩:=raw_base_gates data
  refine ⟨hq,he,?_,conjugate_element_factors _ _ hp⟩
  intro x
  rw [conjugate_element_norm]
  exact hn x

theorem childLogTest_conjugate (W:ℝ→ℂ)(θ:ℝ):
    (fun x=>star (childLogTest W θ x))=childLogTest (fun x=>star (W x)) (-θ):=by
  funext x
  simp only [childLogTest,star_mul,SecondPassIntegration.logPhase_conjugate]
  ring

end SevenEighths.DetectorDictionaryInverseRawConjugateGates

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialExcludedForcing
namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve ConcretePrimeRowBridge
open FirstCauchyArithmetic SecondPassArithmetic UniqueFactorizationMonoid
namespace SevenEighths.InverseInitialExcludedForcing
open InverseInitialOverlap InverseInitialPoissonBridge InverseInitialKernelBridge
open InverseInitialRayAttachment InverseInitialArithmetic
open InverseInitialEnergyCallerWindow
open InverseInitialExcludedPool
open InverseInitialCommonTuples
local notation "O"=>ActualEisensteinCubic.O

theorem pool_product_outside (F E:Finset (Ideal O))(hE:∀Q∈E,Prime Q)
    (hF:∀I∈F,outside E I)(A:Finset (primePool F)):
    outside E (∏i∈A,i.val) := by
  intro Q hQ hd
  obtain ⟨i,hi,hQi⟩:=((hE Q hQ).dvd_finsetProd_iff (fun i:primePool F=>i.val)).mp hd
  obtain ⟨I,hIF,hfactor⟩:=mem_primePool_iff.mp i.property
  exact hF I hIF Q hQ (hQi.trans (dvd_of_mem_normalizedFactors hfactor))

variable {κ:Type*}

end SevenEighths.InverseInitialExcludedForcing

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Dictionary.InverseRawInput
namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.DetectorDictionaryInverseRawInput
open CompletedGauss
open ActualEisensteinCubic CanonicalRowCompletion CanonicalQuadraticSieve ConcretePrimeRowBridge
open ConcreteTraceCRT FirstCauchyArithmetic SecondPassArithmetic IdealMobiusDivisorSum
open InverseInitialArithmetic InverseInitialRayAttachment InverseInitialConjugateEnergy
open InverseInitialPoissonBridge InverseInitialExcludedForcing InverseInitialExcludedPool
open UniqueFactorizationMonoid
local notation "O"=>HeckeFamily.O

private theorem admissible_one : Admissible (1:Ideal O):=by
  refine ⟨one_ne_zero,squarefree_one,?_⟩
  simp only [normalizedFactors_one,Multiset.notMem_zero,false_implies,forall_const]

theorem input_generator_one (F:Finset (Ideal O))(hF:∀I∈F,Admissible I)
    (η:O→*ℂ)(H:Finset (primePool F)→ℂ)(u:O):
    letI:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance;
    inputConjugateRow (poolPrimary F) (poolPrimary_good F hF) Finset.univ η
      (primaryGenerator (1:Ideal O)) 1 1 H u=
    inputConjugateRow (poolPrimary F) (poolPrimary_good F hF) Finset.univ η 1 1 1 H u:=by
  let:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  rw [initial_input_row (poolPrimary F) (poolPrimary_good F hF),
    initial_input_row (poolPrimary F) (poolPrimary_good F hF)]
  unfold supportConjugateSum
  apply Finset.sum_congr rfl
  intro A hA
  have he:(fun i:primePool F=>Ideal.span {poolPrimary F i})=(fun i=>i.val):=
    funext (poolPrimary_span F hF)
  have hm:rowCoprimeMask (fun i:primePool F=>Ideal.span {poolPrimary F i}) A
      (primaryGenerator (1:Ideal O))=1:=by
    rw [he]
    exact selected_mask F 1 admissible_one A isCoprime_one_right
  have ho:rowCoprimeMask (fun i:primePool F=>Ideal.span {poolPrimary F i}) A 1=1:=by
    simp [rowCoprimeMask,Ideal.IsPrime.one_notMem]
  simp only [hm,ho]

theorem complete_pool_selector (E:Finset (Ideal O))(hE:∀P∈E,Prime P)
    (Dpool:ℕ)(hbad:fixedBadPrimes⊆E)(W:ℝ→ℂ)(b Z r:ℝ)
    (hZ:0<Z)(hW:∀x,W x≠0→x≤b)(hbudget:b*Z^r≤(Dpool:ℝ)):
    let F:=InitialMeanSquare.outsideSquarefreeIdeals E Dpool;
    ∀A:Finset (primePool F),
      (if (∏i∈A,i.val)∈F then W (((∏i∈A,i.val).absNorm:ℝ)/Z^r) else 0)=
        W (((∏i∈A,i.val).absNorm:ℝ)/Z^r):=by
  intro F A
  by_cases hw:W (((∏i∈A,i.val).absNorm:ℝ)/Z^r)=0
  · simp only [hw,ite_self]
  have hF:=InitialMeanSquare.outsideSquarefree_admissible E Dpool hbad
  have hprod:=InitialMeanSquare.poolProduct_admissible F hF A
  have hout:outside E (∏i∈A,i.val):=
    pool_product_outside F E hE
      (fun I hI=>(mem_outsideIdealsUpTo.mp (Finset.mem_filter.mp hI).1).2.2) A
  have hN:((∏i∈A,i.val).absNorm:ℝ)≤(Dpool:ℝ):=
    ((div_le_iff₀ (Real.rpow_pos_of_pos hZ r)).mp (hW _ hw)).trans hbudget
  have hmem:(∏i∈A,i.val)∈F:=by
    apply Finset.mem_filter.mpr
    refine ⟨mem_outsideIdealsUpTo.mpr ⟨?_,?_,hout⟩,hprod.2.1⟩
    · exact Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hprod.1)
    · exact_mod_cast hN
  exact if_pos hmem

theorem original_complete_star_input
    (E:Finset (Ideal O))(hE:∀P∈E,Prime P)(Dpool:ℕ)(hbad:fixedBadPrimes⊆E)
    (η:Ideal O→*ℂ)(W:ℝ→ℂ)(b Z r:ℝ)(hZ:0<Z)
    (hW:∀x,W x≠0→x≤b)(hbudget:b*Z^r≤(Dpool:ℝ))(u:O):
    let F:=InitialMeanSquare.outsideSquarefreeIdeals E Dpool;
    let hF:=InitialMeanSquare.outsideSquarefree_admissible E Dpool hbad;
    letI:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance;
    star (originalTotalPolynomial F 1 η (fun _=>1) W Z r 0 u)=
      ((Z^(-r/2):ℝ):ℂ)*inputConjugateRow (poolPrimary F) (poolPrimary_good F hF)
        Finset.univ (elementCharacter (conjugateIdealCharacter η)) 1 1 1
        (initialTest (poolPrimary F) (fun _=>1) (fun x=>star (W x)) Z r) u:=by
  intro F hF
  let:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  have he:=selected_conjugate_row F hF 1 admissible_one (fun _ _=>isCoprime_one_right)
    (conjugateIdealCharacter η) (fun I=>star (W ((I.absNorm:ℝ)/Z^r))) u
  dsimp only at he
  rw [input_generator_one F hF] at he
  have hselector:(fun A:Finset (primePool F)=>
      if (∏i∈A,i.val)∈F then star (W (((∏i∈A,i.val).absNorm:ℝ)/Z^r)) else 0)=
      initialTest (poolPrimary F) (fun _=>1) (fun x=>star (W x)) Z r:=by
    funext A
    rw [complete_pool_selector E hE Dpool hbad (fun x=>star (W x)) b Z r hZ
      (fun x hx=>hW x (by simpa only [star_ne_zero] using hx)) hbudget]
    simp only [initialTest,one_mul,InitialMeanSquare.poolPrimary_norm F hF]
    rfl
  rw [hselector] at he
  rw [←he]
  unfold originalTotalPolynomial
  have hscalar:star ((Z^(-r/2):ℝ):ℂ)=((Z^(-r/2):ℝ):ℂ):=by simp
  simp only [add_zero,map_one,mul_one,star_mul,star_sum,hscalar,
    conjugateIdealCharacter_apply,heckeIdealCharacter_apply]
  rw [mul_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro I hI
  simp only [star_intCast]
  ring

theorem original_complete_child_norm
    (E:Finset (Ideal O))(hE:∀P∈E,Prime P)(Dpool:ℕ)(hbad:fixedBadPrimes⊆E)
    (η:Ideal O→*ℂ)(W:ℝ→ℂ)(b Z r t:ℝ)(hZ:0<Z)
    (hW:∀x,W x≠0→x≤b)(hbudget:b*Z^r≤(Dpool:ℝ))(u:O):
    let F:=InitialMeanSquare.outsideSquarefreeIdeals E Dpool;
    let hF:=InitialMeanSquare.outsideSquarefree_admissible E Dpool hbad;
    letI:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance;
    ‖originalTotalPolynomial F 1 η (fun _=>1) (InverseMoment.childLogTest W t) Z r 0 u‖^2=
      ‖((Z^(-r/2):ℝ):ℂ)*inputConjugateRow (poolPrimary F) (poolPrimary_good F hF)
        Finset.univ (elementCharacter (conjugateIdealCharacter η)) 1 1 1
        (initialTest (poolPrimary F) (fun _=>1)
          (InverseMoment.childLogTest (fun x=>star (W x)) (-t)) Z r) u‖^2:=by
  intro F hF
  let:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  have hw:∀x,InverseMoment.childLogTest W t x≠0→x≤b:=by
    intro x hx
    exact hW x ((mul_ne_zero_iff.mp hx).1)
  have he:=original_complete_star_input E hE Dpool hbad η
    (InverseMoment.childLogTest W t) b Z r hZ hw hbudget u
  dsimp only at he
  rw [DetectorDictionaryInverseRawConjugateGates.childLogTest_conjugate] at he
  have hn:=congrArg (fun z:ℂ=>‖z‖^2) he
  simpa only [norm_star] using hn

end SevenEighths.DetectorDictionaryInverseRawInput

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Dictionary.InverseRawRealRadial
namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.DetectorDictionaryInverseRawRealRadial
open InverseInitialConjugateEnergy ConcreteTraceCRT
local notation "O"=>HeckeFamily.O

theorem smoothedEnergy_eq_complex_norm (Φ:𝓢(ℝ,ℂ))
    (hΦ:∀x,0≤(Φ x).re)(hreal:∀x,(Φ x).im=0)
    (H:ℝ)(hH:0<H)(f:O→ℂ):
    smoothedEnergy Φ H f=
      ‖∑'u:O,Φ (‖eisEmbedding u‖^2/H)*(‖f u‖^2:ℝ)‖:=by
  rw [real_smoothed_sum_eq Φ (fun x _=>hreal x) hH,
    Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (smoothedEnergy_nonneg Φ (fun x _=>hΦ x) hH f)]

end SevenEighths.DetectorDictionaryInverseRawRealRadial

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Dictionary.InverseRawReference
namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap Topology
open Filter
namespace SevenEighths.DetectorDictionaryInverseRawReference
open HeckeFamily HeckeDyadic HeckeInverseAmplification InverseMoment
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge
open CanonicalRowCompletion CanonicalCoefficientClass CanonicalQuadraticSieve
open InverseInitialRawDictionary InverseInitialConjugateEnergy InverseInitialExcludedPeriod
open InverseInitialRayAttachment InverseInitialProfileBounds
open DetectorDictionaryInverseRawInitialGates DetectorDictionaryInverseRawInitialEnergy
open DetectorDictionaryInverseRawInput DetectorDictionaryInverseRawInputBound
open DetectorDictionaryInverseRawConjugateGates DetectorDictionaryInverseRawRealRadial
open DetectorDictionaryInverseRawGeometry IdealMobiusDivisorSum
local notation "O"=>HeckeFamily.O

theorem raw_reference_large (W:𝓢(ℝ,ℂ))(a b c κ:ℝ)(ha:0<a)(hb:0<b)
    (hs:Function.support W⊆Set.Icc a b)(hc:0<c)(hκ:0<κ):
    ∃J:ℕ,∀data:RowData,∃C H₀:ℝ,0<C ∧ 1<H₀ ∧
      ∀(t H D:ℝ),H₀≤H→1≤D→D^(1+c)≤H→∀rows:Finset NonzeroElement,
      (∀u∈rows,((Ideal.span {u.val}).absNorm:ℝ)≤H)→
      (∑u∈rows,‖polynomial (data.character u) true (childLogTest W t) D 0 0‖^2)≤
        (C*(1+‖t‖)^(2*J))*H*(H*max 1 D)^κ := by
  obtain ⟨Φ,hΦcompact,hΦ,hreal,hone⟩:=exists_real_raw_radial_majorant
  obtain ⟨η,τ,π,eps,hη,hτ,hπ,heps,hηone,hηgap,hτgap,hcost⟩:=
    raw_fixed_reserves c (κ/2) hc (by positivity)
  let gap:=capacityGap c/4
  have hgap:0<gap:=by dsimp [gap];exact div_pos (capacityGap_pos c hc) (by norm_num)
  have hηsmall:η≤gap/50:=by dsimp [gap];nlinarith
  have hτsmall:τ≤gap/50:=by dsimp [gap];nlinarith
  let Wbar:=SecondPassIntegration.conjugateProfile W
  have hsbar:Function.support Wbar⊆Set.Icc a b:=by
    intro x hx
    exact hs (by simpa only [Wbar,Function.mem_support,SecondPassIntegration.conjugateProfile_apply,star_ne_zero] using hx)
  obtain ⟨J,Btree,hBtree,hinput⟩:=raw_input_bound Wbar a b ha hsbar Φ
    gap eps π η τ (κ/4) hgap heps hπ hη hηone hηsmall hτ hτsmall (by positivity)
  refine ⟨J,?_⟩
  intro data
  obtain ⟨hq,hqset,hn,hperiod⟩:=raw_conjugate_base_gates data
  obtain ⟨C,Hq,hC,hHq,hinput⟩:=hinput (deletedPeriod (basePeriod data)) hq
  obtain ⟨Hg,hg⟩:=eventually_atTop.mp (shifted_raw_geometry_eventually data c η hc hη)
  let T:=idealDivisors (∏P∈excluded data,P)
  let Ctotal:=((T.card:ℝ)+1)^2*C
  refine ⟨Ctotal,max Hq Hg,by dsimp [Ctotal];positivity,lt_max_of_lt_left hHq,?_⟩
  intro t H D hH hD hcapacity rows hrows
  have hHq':Hq≤H:=(le_max_left _ _).trans hH
  obtain ⟨hHp,hgeom⟩:=hg H ((le_max_right _ _).trans hH)
  have hHpos:0<H:=zero_lt_one.trans hHp
  have hWt:∀x,childLogTest W t x≠0→x≤b:=by
    intro x hx
    exact (hs ((mul_ne_zero_iff.mp hx).1)).2
  have hraw:=raw_rows_le_initial Φ hΦ hone data (childLogTest W t) H D c b Btree 2 0 0
    hHp hD hc hcapacity hb.le hWt rows hrows
  have hterm (j:Ideal O)(hj:j∈T):
      smoothedEnergy Φ H (initialFunction data (childLogTest W t) H b Btree 2 D 0 0 j)≤
        C*H^(1+15*η+π+eps+κ/4)*(1+‖t‖)^(2*J):=by
    obtain ⟨hrlo,hr₁,hr₂,hex,hrcap,hDH⟩:=hgeom D hD hcapacity j hj
    let r:=Real.logb H (D/(j.absNorm:ℝ))
    let Dpool:=completeCutoff H b Btree 2
    have hpool:Btree*H^3≤(Dpool:ℝ):=by
      convert (preTransparency := .instances) completeCutoff_tree H b Btree 2 using 1 ; norm_num
    have hbcover:b*H^r≤(Dpool:ℝ):=by
      rw [hex]
      exact completeCutoff_columns H b Btree 2 D _ hb.le (zero_lt_one.trans_le hD).le hDH
        (excluded_divisor_norm data j hj).1
    have hbound:=hinput H hHq' Dpool hpool
      (elementCharacter (conjugateIdealCharacter (idealCoeff (deletedBase data)).toMonoidHom))
      hn hperiod r (-t) (by dsimp [r];linarith)
      (by dsimp [gap] at *;linarith [(capacityGap_pos c hc).le])
      (by dsimp [gap] at *;linarith [(capacityGap_pos c hc).le])
      (by have hh:=capacityGap_lt_one c hc;linarith)
    let F:=InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes (deletedPeriod (basePeriod data))) Dpool
    let hF:=InitialMeanSquare.outsideSquarefree_admissible (reflectionExcludedPrimes (deletedPeriod (basePeriod data))) Dpool
      (reflectionExcludedPrimes_bad (deletedPeriod (basePeriod data)))
    let:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by
      rw [poolPrimary_span F hF i];infer_instance
    have hf:initialFunction data (childLogTest W t) H b Btree 2 D 0 0 j=
        originalTotalPolynomial F 1 (idealCoeff (deletedBase data)).toMonoidHom
          (fun _=>1) (childLogTest W t) H r 0:=by
      unfold initialFunction
      dsimp only [F]
      rw [hqset]
      congr 1
      funext x
      simp [twistedProfile,HeckeDyadic.shift]
    rw [hf,smoothedEnergy_eq_complex_norm Φ hΦ hreal H hHpos]
    have he: (∑'u:O,Φ (‖eisEmbedding u‖^2/H)*
        (‖originalTotalPolynomial F 1 (idealCoeff (deletedBase data)).toMonoidHom
          (fun _=>1) (childLogTest W t) H r 0 u‖^2:ℝ))=
        (∑'u:O,Φ (‖eisEmbedding u‖^2/H)*
        (‖((H^(-r/2):ℝ):ℂ)*SecondPassArithmetic.inputConjugateRow
          (poolPrimary F) (poolPrimary_good F (InitialMeanSquare.outsideSquarefree_admissible
            (reflectionExcludedPrimes (deletedPeriod (basePeriod data))) Dpool
            (reflectionExcludedPrimes_bad (deletedPeriod (basePeriod data)))))
          Finset.univ (elementCharacter (conjugateIdealCharacter
            (idealCoeff (deletedBase data)).toMonoidHom)) 1 1 1
          (initialTest (poolPrimary F) (fun _=>1) (childLogTest Wbar (-t)) H r) u‖^2:ℝ)):=by
      apply tsum_congr
      intro u
      congr 2
      exact original_complete_child_norm (reflectionExcludedPrimes (deletedPeriod (basePeriod data)))
        (reflectionExcludedPrimes_prime (deletedPeriod (basePeriod data))) Dpool
        (reflectionExcludedPrimes_bad (deletedPeriod (basePeriod data))) _ W b H r t hHpos
        (fun x hx=>(hs hx).2) hbcover u
    rw [he]
    simpa only [norm_neg] using hbound
  apply hraw.trans
  calc
    _≤(T.card:ℝ)*∑j∈T,C*H^(1+15*η+π+eps+κ/4)*(1+‖t‖)^(2*J):=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (Nat.cast_nonneg _)
    _=(T.card:ℝ)^2*C*H^(1+15*η+π+eps+κ/4)*(1+‖t‖)^(2*J):=by
      simp only [Finset.sum_const,nsmul_eq_mul];ring
    _≤Ctotal*H^(1+15*η+π+eps+κ/4)*(1+‖t‖)^(2*J):=by
      dsimp [Ctotal]
      gcongr
      nlinarith [Nat.cast_nonneg (α:=ℝ) T.card]
    _≤(Ctotal*(1+‖t‖)^(2*J))*H*(H*max 1 D)^κ:=by
      have he:15*η+π+eps+κ/4≤κ:=by linarith
      have hh:=raw_output_budget H D κ (15*η+π+eps+κ/4) hHp.le hκ.le he
      rw [show (1+15*η+π+eps+κ/4:ℝ)=1+(15*η+π+eps+κ/4) by ring]
      nlinarith [mul_le_mul_of_nonneg_left hh
        (show 0≤Ctotal*(1+‖t‖)^(2*J) by dsimp [Ctotal];positivity)]

theorem raw_reference_moment_oai (W:𝓢(ℝ,ℂ))(a b c κ:ℝ)(ha:0<a)(hb:0<b)
    (hs:Function.support W⊆Set.Icc a b)(hc:0<c)(hκ:0<κ):
    ∃J:ℕ,∀data:RowData,∃C:ℝ,0<C ∧ ∀t:ℝ,
      RawMoment data (childLogTest W t) c κ (C*(1+‖t‖)^(2*J)) := by
  obtain ⟨J,hlarge⟩:=raw_reference_large W a b c κ ha hb hs hc hκ
  refine ⟨J,?_⟩
  intro data
  obtain ⟨C,H₀,hC,hH₀,hlarge⟩:=hlarge data
  obtain ⟨C₀,hC₀,hcomplete⟩:=DetectorDictionaryInverseRawCompact.rawMoment_of_large_rows_ge_one
    W a b ha hs H₀ hH₀.le
  refine ⟨C+C₀,add_pos hC hC₀,?_⟩
  exact hcomplete data c κ C J hc.le hκ.le hC.le hlarge

end SevenEighths.DetectorDictionaryInverseRawReference

end

end OAI
end

theorem solution : type_of% @OAI.SevenEighths.DetectorDictionaryInverseRawReference.raw_reference_moment_oai := @OAI.SevenEighths.DetectorDictionaryInverseRawReference.raw_reference_moment_oai
