-- Prove2me | solution 1 for OAI.SevenEighths.InverseInitialExcludedFourier.original_tuples_excluded_fourier
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T23:48:06.621754+00:00
-- url     : https://prove2.me/submissions/981ab032-857c-4b70-822b-628910157bfd

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B012

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.DescentProfiles
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge EisensteinSchwartzPoisson JointLogSeparation
noncomputable section

lemma schwartz_logPhase_inversion (g : 𝓢(ℝ, ℂ)) (x : ℝ) :
    g x = ∫ t : ℝ, logPhase t x * (𝓕 g) t := by
  convert (preTransparency := .instances) schwartz_log_inversion g x using 1
  apply integral_congr_ae
  filter_upwards with t
  congr 1
  simp only [logPhase, Real.inner_apply]
  congr 1
  push_cast
  ring

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

theorem primeMark_eq_tuple_sum (I : Finset σ) (L : σ → Finset ι)
    (a : σ → ι → ℂ) (A : Finset ι) :
    primeMark I L a A = ∑ p ∈ I.pi L,
      ∏ i ∈ I.attach, if p i.1 i.2 ∈ A then a i.1 (p i.1 i.2) else 0 := by
  exact Finset.prod_sum I L (fun i p => if p ∈ A then a i p else 0)

end

end SevenEighths.InverseMoment

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialOverlap
namespace OAI

noncomputable section
open scoped BigOperators Classical
open ActualEisensteinCubic CanonicalQuadraticSieve IdealMobiusDivisorSum
open UniqueFactorizationMonoid

namespace SevenEighths.InverseInitialOverlap

theorem mem_original {S : Finset (Ideal O)} {P j n : Ideal O} :
    n ∈ original S P j ↔ n ∈ S ∧ Squarefree n ∧ gcd n P = j := by
  simp only [original, Finset.mem_filter]

theorem residual_mul {P j : Ideal O} (hj : j ∣ P) : j * residual P j = P :=
  idealQuotient_mul hj

theorem residual_squarefree {P j : Ideal O} (hP : Squarefree P) (hj : j ∣ P) :
    Squarefree (residual P j) :=
  hP.squarefree_of_dvd (idealQuotient_dvd hj)

theorem quotient_mul_cancel {D H : Ideal O} (hD : D ≠ 0) :
    idealQuotient D (D * H) = H :=
  mul_left_cancel₀ hD (idealQuotient_mul (dvd_mul_right D H))

theorem column_properties {P j n : Ideal O} (hP : Squarefree P) (hj : j ∣ P)
    (hn : Squarefree n) (hg : gcd n P = j) :
    Squarefree (column P j n) ∧ IsCoprime (column P j n) j ∧
      residual P j ∣ column P j n := by
  have hjn : j ∣ n := hg ▸ GCDMonoid.gcd_dvd_left n P
  have hHP : IsCoprime (idealQuotient j n) P := by
    rw [← hg]
    exact squarefree_quotient_gcd_coprime n P hn
  have hHj := hHP.mono (dvd_refl _) hj
  have hHP0 := hHP.mono (dvd_refl _) (idealQuotient_dvd hj)
  have hJP0 : IsCoprime j (residual P j) :=
    ideals_coprime_of_relprime _ _ (squarefree_mul_iff.mp
      (show Squarefree (j * residual P j) by rw [residual_mul hj]; exact hP)).1
  refine ⟨squarefree_mul_iff.mpr ⟨hHP0.isRelPrime,
    hn.squarefree_of_dvd (idealQuotient_dvd hjn), residual_squarefree hP hj⟩,
    hHj.mul_left hJP0.symm, dvd_mul_left _ _⟩

theorem reconstruct_column {P j n : Ideal O} (hP : Squarefree P) (hj : j ∣ P)
    (hg : gcd n P = j) : reconstruct P j (column P j n) = n := by
  have hjn : j ∣ n := hg ▸ GCDMonoid.gcd_dvd_left n P
  have hP0 := (residual_squarefree hP hj).ne_zero
  unfold reconstruct column
  rw [mul_comm (idealQuotient j n), quotient_mul_cancel hP0, idealQuotient_mul hjn]

theorem reconstruct_properties {P j c : Ideal O} (hP : Squarefree P) (hj : j ∣ P)
    (hc : Squarefree c) (hcj : IsCoprime c j) (hPc : residual P j ∣ c) :
    Squarefree (reconstruct P j c) ∧ gcd (reconstruct P j c) P = j := by
  let H := idealQuotient (residual P j) c
  have hHc : H ∣ c := idealQuotient_dvd hPc
  have hHj : IsCoprime H j := hcj.mono hHc (dvd_refl _)
  have hHP0 : IsCoprime H (residual P j) :=
    (ideals_coprime_of_relprime _ _ (squarefree_mul_iff.mp
      (show Squarefree (residual P j * H) by rw [idealQuotient_mul hPc]; exact hc)).1).symm
  have hHP : IsCoprime H P := by
    rw [← residual_mul hj]
    exact hHj.mul_right hHP0
  exact ⟨squarefree_mul_iff.mpr ⟨hHj.symm.isRelPrime,
    hP.squarefree_of_dvd hj, hc.squarefree_of_dvd hHc⟩,
    gcd_mul_of_coprime_divisor j H P hj hHP⟩

theorem column_reconstruct {P j c : Ideal O} (hP : Squarefree P) (hj : j ∣ P)
    (hPc : residual P j ∣ c) : column P j (reconstruct P j c) = c := by
  have hj0 : j ≠ 0 := ne_zero_of_dvd_ne_zero hP.ne_zero hj
  unfold column reconstruct
  rw [quotient_mul_cancel hj0, mul_comm, idealQuotient_mul hPc]

theorem mem_columns {S : Finset (Ideal O)} {P j c : Ideal O}
    (hP : Squarefree P) (hj : j ∣ P) :
    c ∈ columns S P j ↔ Squarefree c ∧ IsCoprime c j ∧
      residual P j ∣ c ∧ reconstruct P j c ∈ S := by
  constructor
  · intro hc
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨hnS, hn, hg⟩ := mem_original.mp hn
    obtain ⟨hcs, hcj, hPc⟩ := column_properties hP hj hn hg
    exact ⟨hcs, hcj, hPc, by rwa [reconstruct_column hP hj hg]⟩
  · rintro ⟨hc, hcj, hPc, hnS⟩
    obtain ⟨hn, hg⟩ := reconstruct_properties hP hj hc hcj hPc
    exact Finset.mem_image.mpr ⟨reconstruct P j c,
      mem_original.mpr ⟨hnS, hn, hg⟩, column_reconstruct hP hj hPc⟩

theorem reconstruct_mul_residual {P j c : Ideal O} (hPc : residual P j ∣ c) :
    reconstruct P j c * residual P j = j * c := by
  unfold reconstruct
  rw [mul_assoc, mul_comm (idealQuotient _ _), idealQuotient_mul hPc]

theorem norm_reconstruct {P j c : Ideal O} (hPc : residual P j ∣ c) :
    Ideal.absNorm (reconstruct P j c) * Ideal.absNorm (residual P j) =
      Ideal.absNorm j * Ideal.absNorm c := by
  simpa only [map_mul] using congrArg Ideal.absNorm (reconstruct_mul_residual hPc)

theorem cutoff_argument {P j c : Ideal O} (hP : Squarefree P) (hj : j ∣ P)
    (hPc : residual P j ∣ c) (X : ℝ) :
    (Ideal.absNorm (reconstruct P j c) : ℝ) / X =
      (Ideal.absNorm j : ℝ) * Ideal.absNorm c /
        ((Ideal.absNorm (residual P j) : ℝ) * X) := by
  have h0 : (Ideal.absNorm (residual P j) : ℝ) ≠ 0 := by
    exact_mod_cast fun h => (residual_squarefree hP hj).ne_zero
      (Ideal.absNorm_eq_zero_iff.mp h)
  have hn : (Ideal.absNorm (reconstruct P j c) : ℝ) =
      (Ideal.absNorm j : ℝ) * Ideal.absNorm c / Ideal.absNorm (residual P j) := by
    apply (eq_div_iff h0).mpr
    exact_mod_cast norm_reconstruct hPc
  rw [hn, div_div]

theorem columns_filter (S : Finset (Ideal O)) {P j : Ideal O}
    (hP : Squarefree P) (hj : j ∣ P) (mask : Ideal O → Prop) [DecidablePred mask] :
    columns (S.filter mask) P j =
      (columns S P j).filter fun c => mask (reconstruct P j c) := by
  ext c
  simp only [mem_columns hP hj, Finset.mem_filter]
  tauto

theorem scaled_cutoff_argument {P j c : Ideal O} (hP : Squarefree P) (hj : j ∣ P)
    (hPc : residual P j ∣ c) {Z : ℝ} (hZ : 0 < Z) (r z G : ℝ) :
    (Ideal.absNorm (reconstruct P j c) : ℝ) / Z ^ r =
      (((Ideal.absNorm j : ℝ) / Z ^ G) *
        ((Ideal.absNorm c : ℝ) / Z ^ (r + z - 2 * G))) /
        ((Ideal.absNorm (residual P j) : ℝ) / Z ^ (z - G)) := by
  have hnorm : (Ideal.absNorm (residual P j) : ℝ) ≠ 0 := by
    exact_mod_cast fun h => (residual_squarefree hP hj).ne_zero
      (Ideal.absNorm_eq_zero_iff.mp h)
  have hscale : Z ^ G * Z ^ (r + z - 2 * G) = Z ^ r * Z ^ (z - G) := by
    rw [← Real.rpow_add hZ, ← Real.rpow_add hZ]
    congr 1
    ring
  rw [cutoff_argument hP hj hPc]
  rw [div_mul_div_comm, div_div_eq_mul_div]
  field_simp [hnorm, (Real.rpow_pos_of_pos hZ r).ne',
    (Real.rpow_pos_of_pos hZ G).ne',
    (Real.rpow_pos_of_pos hZ (r + z - 2 * G)).ne',
    (Real.rpow_pos_of_pos hZ (z - G)).ne']
  linear_combination ((Ideal.absNorm j : ℝ) * Ideal.absNorm c) * hscale

end SevenEighths.InverseInitialOverlap

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

end SevenEighths.InverseInitialPoissonBridge

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialKernelBridge
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
open ActualEisensteinCubic ConcretePrimeRowBridge ConcreteTraceCRT
open EisensteinSchwartzPoisson UniqueFactorizationMonoid CanonicalQuadraticSieve
open SevenEighths.InverseInitialPoissonBridge SevenEighths.InverseInitialOverlap
open SevenEighths.InverseInitialProfile
namespace SevenEighths.InverseInitialKernelBridge

local notation "Eis" => ActualEisensteinCubic.O
local notation "N" => fun I : Ideal Eis => (Ideal.absNorm I : ℝ)
variable {ι : Type*} [DecidableEq ι] (P : ι → Ideal Eis)
  [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
  (hg : ∀ i, goodLambda ∉ P i)

theorem overlapCoefficient_residual (P j c : Ideal Eis) (η : Ideal Eis →* ℂ)
    (a : Ideal Eis → ℂ) (W : ℝ → ℂ) (Z r z G : ℝ) :
    overlapResidualCoefficient P j η a W Z r z G c =
      bareOverlapCoefficient P j η a c *
        residualOverlapWindow P j W Z z G (N c/Z^(r+z-2*G)) := rfl

open InverseInitialArithmetic SecondPassArithmetic

end SevenEighths.InverseInitialKernelBridge

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

end SevenEighths.InverseInitialRayAttachment

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerSelector
namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve ConcretePrimeRowBridge
open SevenEighths.InverseInitialOverlap SevenEighths.InverseInitialRayAttachment
open SevenEighths.InverseMoment
namespace SevenEighths.InverseInitialEnergyCallerSelector
local notation "Eis" => ActualEisensteinCubic.O

theorem mask_nonzero_coprime (F : Finset (Ideal Eis)) (j : Ideal Eis) (hj : Admissible j)
    (A : Finset (primePool F))
    (hm : rowCoprimeMask (fun i : primePool F=>i.val) A (primaryGenerator j)≠0) :
    IsCoprime (∏ i∈A,i.val) j := by
  have hspan := (primaryGenerator_spec j (primaryGenerator_admissible j hj)).1
  apply IsCoprime.prod_left
  intro i hi
  apply Ideal.isCoprime_iff_sup_eq.mpr
  by_contra htop
  have he := Ideal.IsMaximal.eq_of_le (inferInstance : i.val.IsMaximal) htop
    (show (i.val : Ideal Eis) ≤ (i.val : Ideal Eis) ⊔ j from le_sup_left)
  have hmem : primaryGenerator j∈i.val := by
    rw [he]
    apply (show j ≤ (i.val : Ideal Eis) ⊔ j from le_sup_right)
    have hjmem : primaryGenerator j ∈ Ideal.span {primaryGenerator j} :=
      Ideal.subset_span (Set.mem_singleton _)
    rw [hspan] at hjmem
    exact hjmem
  apply hm
  unfold rowCoprimeMask
  exact if_pos ⟨i,hi,hmem⟩

end SevenEighths.InverseInitialEnergyCallerSelector

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialRawDictionary
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.InverseInitialRawDictionary
open HeckeFamily HeckeDetectorDyadicBridge
open InverseInitialPoissonBridge InverseInitialConjugateEnergy
open ConcretePrimeRowBridge CompletedGauss UniqueFactorizationMonoid
local notation "O" => HeckeFamily.O

theorem finite_source_cover (W : ℝ → ℂ) (D b : ℝ) (hD : 0<D)
    (hW : ∀x,W x≠0 → x≤b) (I : Ideal O) (hI : I≠0)
    (hi : W ((I.absNorm:ℝ)/D)≠0) : I∈idealsUpTo ⌈D*b⌉₊ := by
  apply mem_idealsUpTo.mpr
  refine ⟨Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI),?_⟩
  have hb := (div_le_iff₀ hD).mp (hW _ hi)
  have hn : (I.absNorm:ℝ)≤(⌈D*b⌉₊:ℝ) := by
    calc
      (I.absNorm:ℝ)≤D*b := by simpa only [mul_comm] using hb
      _≤(⌈D*b⌉₊:ℝ) := Nat.le_ceil _
  exact_mod_cast hn

end SevenEighths.InverseInitialRawDictionary

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerWindow
namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve ConcretePrimeRowBridge
open SevenEighths.InverseInitialOverlap SevenEighths.InverseInitialRayAttachment
open SevenEighths.InverseInitialPoissonBridge SevenEighths.InverseInitialKernelBridge
namespace SevenEighths.InverseInitialEnergyCallerWindow
local notation "Eis" => ActualEisensteinCubic.O

theorem residual_window_eq (W : ℝ→ℂ) {P j c : Ideal Eis}
    (hP : Squarefree P) (hj : j∣P) (hc : residual P j∣c)
    (Z r z G : ℝ) (hZ : 0<Z) :
    residualOverlapWindow P j W Z z G ((c.absNorm:ℝ)/Z^(r+z-2*G)) =
      W (((reconstruct P j c).absNorm:ℝ)/Z^r) := by
  unfold residualOverlapWindow
  rw [←scaled_cutoff_argument hP hj hc hZ r z G]

theorem reconstructed_mem_originalSource
    (W : ℝ→ℂ) (Z r z G b : ℝ) (hZ : 0<Z) (hW : ∀x,W x≠0→x≤b)
    {P j c : Ideal Eis} (hP : Admissible P) (hj : j∣P)
    (hc : Admissible c) (hPc : residual P j∣c)
    (hlive : residualOverlapWindow P j W Z z G ((c.absNorm:ℝ)/Z^(r+z-2*G))≠0) :
    reconstruct P j c∈originalSource Z r b := by
  have hs : Supported (reconstruct P j c) :=
    (supported_mul_iff _ _).mpr
      ⟨admissible_supported (admissible_of_dvd hP hj),
        admissible_supported (admissible_of_dvd hc (idealQuotient_dvd hPc))⟩
  apply Finset.mem_filter.mpr
  refine ⟨InverseInitialRawDictionary.finite_source_cover W (Z^r) b
    (Real.rpow_pos_of_pos hZ r) hW _ hs.1 ?_,hs⟩
  rwa [residual_window_eq W hP.2.1 hj hPc Z r z G hZ] at hlive

end SevenEighths.InverseInitialEnergyCallerWindow

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialCommonForcing
namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve ConcretePrimeRowBridge
open FirstCauchyArithmetic SecondPassArithmetic
namespace SevenEighths.InverseInitialCommonForcing
open InverseInitialOverlap InverseInitialPoissonBridge InverseInitialKernelBridge
open InverseInitialRayAttachment InverseInitialArithmetic
open InverseInitialEnergyCallerWindow InverseInitialEnergyCallerSelector
local notation "Eis"=>ActualEisensteinCubic.O

theorem common_selector_window
    (W:ℝ→ℂ)(Z r z G b:ℝ)(hZ:0<Z)(hW:∀x,W x≠0→x≤b)
    {P j:Ideal Eis}(hP:Admissible P)(hj:j∣P)
    (F:Finset (Ideal Eis))(hF:∀I∈F,Admissible I)(A:Finset (primePool F)) :
    (if (∏i∈A,i.val)∈columns (originalSource Z r b) P j then
      residualOverlapWindow P j W Z z G (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)) else 0)*
      rowCoprimeMask (fun i:primePool F=>i.val) A (primaryGenerator j) =
    (if residual P j∣(∏i∈A,i.val) then
      residualOverlapWindow P j W Z z G (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)) else 0)*
      rowCoprimeMask (fun i:primePool F=>i.val) A (primaryGenerator j) := by
  by_cases hm : rowCoprimeMask (fun i:primePool F=>i.val) A (primaryGenerator j)=0
  · simp only [hm,mul_zero]
  by_cases hw : residualOverlapWindow P j W Z z G (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G))=0
  · simp only [hw,ite_self,zero_mul]
  have hA := InitialMeanSquare.poolProduct_admissible F hF A
  have hcop := mask_nonzero_coprime F j (admissible_of_dvd hP hj) A hm
  by_cases hd : residual P j∣(∏i∈A,i.val)
  · have hmem := (mem_columns hP.2.1 hj).mpr ⟨hA.2.1,hcop,hd,
      reconstructed_mem_originalSource W Z r z G b hZ hW hP hj hA hd hw⟩
    simp only [hd,hmem,ite_true]
  · have hn : (∏i∈A,i.val)∉columns (originalSource Z r b) P j :=
      fun h=>hd ((mem_columns hP.2.1 hj).mp h).2.2.1
    simp only [hd,hn,ite_false]

end SevenEighths.InverseInitialCommonForcing

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialCommonTuples
namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve ConcretePrimeRowBridge
open FirstCauchyArithmetic SecondPassArithmetic
namespace SevenEighths.InverseInitialCommonTuples
open InverseInitialOverlap InverseInitialPoissonBridge InverseInitialKernelBridge
open InverseInitialRayAttachment InverseInitialArithmetic
open InverseInitialEnergyCallerWindow InverseInitialCommonForcing
local notation "Eis"=>ActualEisensteinCubic.O
variable {κ ι : Type*} [DecidableEq ι]

theorem input_finset_sum (p:ι→Eis) [∀i,(Ideal.span {p i}).IsMaximal]
    (hg:∀i,goodLambda∉Ideal.span {p i})(F:Finset ι)(Ψ:Eis→*ℂ)(j u:Eis)
    (T:Finset κ)(a:κ→ℂ)(H:κ→Finset ι→ℂ) :
    inputConjugateRow p hg F Ψ j 1 1 (fun A=>∑k∈T,a k*H k A) u=
      ∑k∈T,a k*inputConjugateRow p hg F Ψ j 1 1 (H k) u := by
  simp_rw [initial_input_row p hg]
  unfold supportConjugateSum
  simp only [Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro A hA
  ring

end SevenEighths.InverseInitialCommonTuples

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialCommonLists
namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve ConcretePrimeRowBridge
namespace SevenEighths.InverseInitialCommonLists
open InverseMoment
local notation "Eis"=>ActualEisensteinCubic.O
variable {σ:Type*} [DecidableEq σ]

theorem dividing_list_image (F:Finset (Ideal Eis))(L:Finset (Ideal Eis))
    (hL:∀P∈L,Prime P)(A:Finset (primePool F)) :
    ((poolList F L).filter (fun i=>i∈A)).image Subtype.val=
      L.filter (fun P=>P∣∏i∈A,i.val) := by
  ext P
  constructor
  · intro h
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp h
    obtain ⟨hiL,hiA⟩ := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hiL).2,Finset.dvd_prod_of_mem _ hiA⟩
  · intro h
    obtain ⟨hPL,hd⟩ := Finset.mem_filter.mp h
    obtain ⟨i,hi,hd⟩ := (hL P hPL).dvd_finsetProd_iff (fun i:primePool F=>i.val) |>.mp hd
    have hip : Prime i.val := Ideal.prime_of_isPrime (NeZero.ne i.val) inferInstance
    have he := (prime_dvd_prime_iff_eq (hL P hPL) hip).mp hd
    refine Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨?_,hi⟩,he.symm⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,he ▸ hPL⟩

theorem original_ideal_slot (F:Finset (Ideal Eis))(L:Finset (Ideal Eis))
    (hL:∀P∈L,Prime P)(a:Ideal Eis→ℂ)(A:Finset (primePool F)) :
    (∑P∈L,if P∣∏i∈A,i.val then a P else 0)=
      primeSlot (poolList F L) (fun i=>a i.val) A := by
  rw [←Finset.sum_filter,←dividing_list_image F L hL A,
    Finset.sum_image (fun i _ j _ h=>Subtype.val_injective h)]
  simp only [primeSlot,←Finset.sum_filter]

theorem original_ideal_mark (F:Finset (Ideal Eis))(I:Finset σ)
    (L:σ→Finset (Ideal Eis))(hL:∀i∈I,∀P∈L i,Prime P)
    (a:σ→Ideal Eis→ℂ)(A:Finset (primePool F)) :
    indexedIdealMark id I L a (∏i∈A,i.val)=
      primeMark I (fun i=>poolList F (L i)) (fun i q=>a i q.val) A := by
  unfold indexedIdealMark primeMark
  apply Finset.prod_congr rfl
  intro i hi
  exact original_ideal_slot F (L i) (hL i hi) (a i) A

end SevenEighths.InverseInitialCommonLists

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialCommonRatios
namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CanonicalQuadraticSieve
namespace SevenEighths.InverseInitialCommonRatios
open InverseInitialOverlap InverseInitialKernelBridge
local notation "Eis"=>ActualEisensteinCubic.O
variable {σ:Type*} [DecidableEq σ]

omit [DecidableEq σ] in
theorem actual_residual_product (I:Finset σ)(q:∀i∈I,Ideal Eis)
    (j:Ideal Eis)(hj:j≠0) : residual (j*survivingProduct I q) j=survivingProduct I q :=
  quotient_mul_cancel hj

omit [DecidableEq σ] in
theorem residual_ratio_product (I:Finset σ)(q:∀i∈I,Ideal Eis)
    (j:Ideal Eis)(hj:j≠0)(ell:σ→ℝ)(Z z G:ℝ)(hZ:0<Z)
    (hell:∑i∈I,ell i=z-G) :
    ((residual (j*survivingProduct I q) j).absNorm:ℝ)/Z^(z-G)=
      ∏i∈I.attach,((q i.val i.property).absNorm:ℝ)/Z^(ell i.val) := by
  rw [actual_residual_product I q j hj,Finset.prod_div_distrib]
  have hp : (∏i∈I.attach,Z^(ell i.val))=Z^(z-G) := by
    rw [←Real.rpow_sum_of_pos hZ]
    rw [Finset.sum_attach,hell]
  rw [hp]
  congr 1
  simp only [survivingProduct,map_prod,Nat.cast_prod]

omit [DecidableEq σ] in
theorem original_residual_window (I:Finset σ)(q:∀i∈I,Ideal Eis)
    (j:Ideal Eis)(hj:j≠0)(ell:σ→ℝ)(W:ℝ→ℂ)(Z r z G:ℝ)(hZ:0<Z)
    (hell:∑i∈I,ell i=z-G)(c:Ideal Eis) :
    residualOverlapWindow (j*survivingProduct I q) j W Z z G
      ((c.absNorm:ℝ)/Z^(r+z-2*G))=
      W (((j.absNorm:ℝ)/Z^G)*((c.absNorm:ℝ)/Z^(r+z-2*G))/
        (∏i∈I.attach,((q i.val i.property).absNorm:ℝ)/Z^(ell i.val))) := by
  unfold residualOverlapWindow
  rw [residual_ratio_product I q j hj ell Z z G hZ hell]

end SevenEighths.InverseInitialCommonRatios

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialOverlapFourier
namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge
namespace SevenEighths.InverseInitialOverlapFourier
open InverseMoment
variable {σ ι : Type*} [DecidableEq σ] [DecidableEq ι]

lemma phase_neg (t x : ℝ) : logPhase (-t) x=logPhase t (-x) := by
  unfold logPhase
  congr 1
  push_cast
  ring

lemma phase_sub (t xj xc y : ℝ) :
    logPhase t xj*logPhase t xc*logPhase (-t) y=logPhase t (xj+xc-y) := by
  rw [phase_neg,←logPhase_add,←logPhase_add]
  rfl

lemma fourier_phase_integrable (g : 𝓢(ℝ,ℂ)) (x : ℝ) (a : ℂ) :
    Integrable (fun t:ℝ=>(𝓕 g) t*logPhase t x*a) := by
  have h : Integrable (fun t:ℝ=>(𝓕 g) t*logPhase t x) (volume:Measure ℝ) :=
    (𝓕 g).integrable.mul_bdd (c:=1)
    (logPhase_continuous_left x).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun t=>le_of_eq (logPhase_norm t x)))
  exact h.mul_const a

theorem tuple_mark_phase (I : Finset σ) (L : σ→Finset ι) (a : σ→ι→ℂ)
    (y : σ→ι→ℝ) (A : Finset ι) (t : ℝ) :
    primeMark I L (fun i p=>a i p*logPhase (-t) (y i p)) A =
      ∑p∈I.pi L,(∏i∈I.attach,if p i.val i.property∈A then a i.val (p i.val i.property) else 0)*
        logPhase (-t) (∑i∈I.attach,y i.val (p i.val i.property)) := by
  rw [primeMark_eq_tuple_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [logPhase_sum,←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  split_ifs <;> simp

theorem overlap_tuple_separation (g : 𝓢(ℝ,ℂ))
    (I : Finset σ) (L : σ→Finset ι) (a : σ→ι→ℂ) (y : σ→ι→ℝ)
    (A : Finset ι) (xj xc : ℝ) :
    (∑p∈I.pi L,(∏i∈I.attach,if p i.val i.property∈A then a i.val (p i.val i.property) else 0)*
      g (xj+xc-∑i∈I.attach,y i.val (p i.val i.property))) =
      ∫t:ℝ,density g xj t*logPhase t xc*
        primeMark I L (fun i p=>a i p*logPhase (-t) (y i p)) A := by
  simp_rw [tuple_mark_phase]
  simp only [Finset.mul_sum,density]
  have he (p : ∀i∈I,ι) (t:ℝ) :
      (𝓕 g) t*logPhase t xj*logPhase t xc*
        ((∏i∈I.attach,if p i.val i.property∈A then a i.val (p i.val i.property) else 0)*
          logPhase (-t) (∑i∈I.attach,y i.val (p i.val i.property))) =
      (𝓕 g) t*logPhase t (xj+xc-∑i∈I.attach,y i.val (p i.val i.property))*
        (∏i∈I.attach,if p i.val i.property∈A then a i.val (p i.val i.property) else 0) := by
    rw [←phase_sub]
    ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun p hp=>fourier_phase_integrable g _ _)]
  apply Finset.sum_congr rfl
  intro p hp
  rw [integral_mul_const]
  have hinv := schwartz_logPhase_inversion g
    (xj+xc-∑i∈I.attach,y i.val (p i.val i.property))
  rw [mul_comm (∏i∈I.attach,if p i.val i.property∈A then a i.val (p i.val i.property) else 0)]
  congr 1
  rw [hinv]
  apply integral_congr_ae
  filter_upwards with t
  ring

theorem overlap_mode_integrable (g : 𝓢(ℝ,ℂ))
    (I : Finset σ) (L : σ→Finset ι) (a : σ→ι→ℂ) (y : σ→ι→ℝ)
    (A : Finset ι) (xj xc : ℝ) :
    Integrable (fun t:ℝ=>density g xj t*logPhase t xc*
      primeMark I L (fun i p=>a i p*logPhase (-t) (y i p)) A) := by
  simp_rw [tuple_mark_phase]
  simp only [Finset.mul_sum,density]
  apply integrable_finsetSum
  intro p hp
  convert (preTransparency := .instances) fourier_phase_integrable g
    (xj+xc-∑i∈I.attach,y i.val (p i.val i.property))
    (∏i∈I.attach,if p i.val i.property∈A then a i.val (p i.val i.property) else 0) using 1
  funext t
  rw [←phase_sub]
  ring

theorem actual_overlap_separation
    (W : ℝ→ℂ) (a₀ b₀ : ℝ) (ha₀ : 0<a₀)
    (hs : Function.support W⊆Set.Icc a₀ b₀) (hW : ContDiff ℝ ∞ W)
    (I : Finset σ) (L : σ→Finset ι) (a : σ→ι→ℂ) (y : σ→ι→ℝ)
    (hy : ∀i∈I,∀p∈L i,0<y i p) (A : Finset ι)
    (yj yc : ℝ) (hj : 0<yj) (hc : 0<yc) :
    (∑p∈I.pi L,(∏i∈I.attach,if p i.val i.property∈A then a i.val (p i.val i.property) else 0)*
      W (yj*yc/(∏i∈I.attach,y i.val (p i.val i.property)))) =
      ∫t:ℝ,density (CubicReflectionKernel.logSchwartz W a₀ b₀ ha₀ hs hW) (Real.log yj) t*
        logPhase t (Real.log yc)*
        primeMark I L (fun i p=>a i p*logPhase (-t) (Real.log (y i p))) A := by
  rw [←overlap_tuple_separation]
  apply Finset.sum_congr rfl
  intro p hp
  congr 1
  simp only [CubicReflectionKernel.logSchwartz_apply,Real.exp_sub,Real.exp_add,
    Real.exp_log hj,Real.exp_log hc,Real.exp_sum]
  congr 2
  apply Finset.prod_congr rfl
  intro i hi
  exact (Real.exp_log (hy i.val i.property (p i.val i.property)
    ((Finset.mem_pi.mp hp) i.val i.property))).symm

end SevenEighths.InverseInitialOverlapFourier

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialOverlapIdealFourier
namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge ActualEisensteinCubic
namespace SevenEighths.InverseInitialOverlapIdealFourier
open InverseMoment InverseInitialOverlapFourier
local notation "Eis"=>ActualEisensteinCubic.O
variable {σ ι : Type*} [DecidableEq σ] [DecidableEq ι]

omit [DecidableEq σ] in
theorem activeIndices_mem (primes : ι→Ideal Eis) (I : Finset σ) (L : σ→Finset ι)
    (c : Ideal Eis) {i : σ} (hi : i∈I) {p : ι} (hp : p∈L i) :
    p∈activeIndices primes I L c ↔ primes p∣c := by
  simp only [activeIndices,Finset.mem_filter]
  exact and_iff_right (Finset.mem_biUnion.mpr ⟨i,hi,hp⟩)

theorem indexed_mark_active (primes : ι→Ideal Eis) (I : Finset σ) (L : σ→Finset ι)
    (a : σ→ι→ℂ) (c : Ideal Eis) :
    indexedIdealMark primes I L a c=primeMark I L a (activeIndices primes I L c) := by
  unfold indexedIdealMark primeMark primeSlot
  apply Finset.prod_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro p hp
  simp only [activeIndices_mem primes I L c hi hp]

omit [DecidableEq σ] [DecidableEq ι] in
theorem tuple_gate_product (primes : ι→Ideal Eis) (I : Finset σ)
    (a : σ→ι→ℂ) (p : ∀i∈I,ι) (c : Ideal Eis)
    (hc : Pairwise (Function.onFun IsCoprime (fun i:I=>primes (p i.val i.property)))) :
    (∏i∈I.attach,if primes (p i.val i.property)∣c then a i.val (p i.val i.property) else 0)=
      if (∏i∈I.attach,primes (p i.val i.property))∣c then
        ∏i∈I.attach,a i.val (p i.val i.property) else 0 := by
  by_cases h : (∏i∈I.attach,primes (p i.val i.property))∣c
  · rw [if_pos h]
    apply Finset.prod_congr rfl
    intro i hi
    exact if_pos ((Finset.dvd_prod_of_mem (fun i:I=>primes (p i.val i.property)) hi).trans h)
  · rw [if_neg h]
    have hn : ∃i:I,¬primes (p i.val i.property)∣c := by
      by_contra hn
      push Not at hn
      apply h
      exact Finset.prod_dvd_of_coprime (hc.set_pairwise _) (fun i _=>hn i)
    obtain ⟨i,hi⟩ := hn
    exact Finset.prod_eq_zero (Finset.mem_attach _ i) (if_neg hi)

end SevenEighths.InverseInitialOverlapIdealFourier

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialCommonProfile
namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge
namespace SevenEighths.InverseInitialCommonProfile
open InverseMoment InverseInitialCommonLists InverseInitialCommonRatios
open InverseInitialOverlapFourier InverseInitialOverlapIdealFourier
local notation "Eis"=>ActualEisensteinCubic.O
variable {σ:Type*} [DecidableEq σ]

omit [DecidableEq σ] in
theorem slotRatio_pos (Z:ℝ)(hZ:0<Z)(ell:σ→ℝ)(i:σ){P:Ideal Eis}(hP:Prime P) :
    0<slotRatio Z ell i P := by
  apply div_pos _ (Real.rpow_pos_of_pos hZ _)
  exact_mod_cast Nat.pos_of_ne_zero (fun h=>hP.ne_zero (Ideal.absNorm_eq_zero_iff.mp h))

theorem common_profile_separation
    (W:ℝ→ℂ)(a₀ b₀:ℝ)(ha₀:0<a₀)
    (hs:Function.support W⊆Set.Icc a₀ b₀)(hW:ContDiff ℝ ∞ W)
    (F:Finset (Ideal Eis))(I:Finset σ)(L:σ→Finset (Ideal Eis))
    (hL:∀i∈I,∀P∈L i,Prime P)(a:σ→Ideal Eis→ℂ)
    (hcop:∀q∈I.pi L,Pairwise (Function.onFun IsCoprime
      (fun i:I=>q i.val i.property)))
    (Z:ℝ)(hZ:0<Z)(ell:σ→ℝ)(A:Finset (primePool F))
    (yj yc:ℝ)(hj:0<yj)(hc:0<yc) :
    (∑q∈I.pi L,(∏i∈I.attach,a i.val (q i.val i.property))*
      (if survivingProduct I q∣(∏i∈A,i.val) then
        W (yj*yc/(∏i∈I.attach,slotRatio Z ell i.val (q i.val i.property))) else 0)) =
      ∫t:ℝ,density (CubicReflectionKernel.logSchwartz W a₀ b₀ ha₀ hs hW)
        (Real.log yj) t*logPhase t (Real.log yc)*
        primeMark I (fun i=>poolList F (L i))
          (fun i q=>a i q.val*logPhase (-t) (Real.log (slotRatio Z ell i q.val))) A := by
  have hm (t:ℝ) : primeMark I (fun i=>poolList F (L i))
      (fun i q=>a i q.val*logPhase (-t) (Real.log (slotRatio Z ell i q.val))) A =
      primeMark I L (fun i P=>a i P*logPhase (-t) (Real.log (slotRatio Z ell i P)))
        (activeIndices id I L (∏i∈A,i.val)) :=
    (original_ideal_mark F I L hL
      (fun i P=>a i P*logPhase (-t) (Real.log (slotRatio Z ell i P))) A).symm.trans
      (indexed_mark_active id I L _ _)
  simp_rw [hm]
  have he := actual_overlap_separation W a₀ b₀ ha₀ hs hW I L a (slotRatio Z ell)
    (fun i hi P hP=>slotRatio_pos Z hZ ell i (hL i hi P hP))
    (activeIndices id I L (∏i∈A,i.val)) yj yc hj hc
  rw [←he]
  apply Finset.sum_congr rfl
  intro q hq
  have hprod : (∏i∈I.attach,if q i.val i.property∈activeIndices id I L (∏i∈A,i.val)
      then a i.val (q i.val i.property) else 0)=
      if survivingProduct I q∣(∏i∈A,i.val) then
        ∏i∈I.attach,a i.val (q i.val i.property) else 0 := by
    calc
      _ = ∏i∈I.attach,if q i.val i.property∣(∏i∈A,i.val) then a i.val (q i.val i.property) else 0 := by
        apply Finset.prod_congr rfl
        intro i hi
        simp only [activeIndices_mem id I L _ i.property ((Finset.mem_pi.mp hq) i.val i.property),id_eq]
      _ = _ := by
        convert! (preTransparency := .instances) tuple_gate_product id I a q (∏i∈A,i.val) (hcop q hq) using 1
  rw [hprod]
  split_ifs <;> simp

theorem common_profile_integrable (g:𝓢(ℝ,ℂ))
    (F:Finset (Ideal Eis))(I:Finset σ)(L:σ→Finset (Ideal Eis))
    (a:σ→Ideal Eis→ℂ)(Z:ℝ)(ell:σ→ℝ)(A:Finset (primePool F))(yj yc:ℝ) :
    Integrable (fun t:ℝ=>density g (Real.log yj) t*logPhase t (Real.log yc)*
      primeMark I (fun i=>poolList F (L i))
        (fun i q=>a i q.val*logPhase (-t) (Real.log (slotRatio Z ell i q.val))) A) :=
  overlap_mode_integrable g I (fun i=>poolList F (L i)) (fun i q=>a i q.val)
    (fun i q=>Real.log (slotRatio Z ell i q.val)) A (Real.log yj) (Real.log yc)

end SevenEighths.InverseInitialCommonProfile

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialOverlapInputFourier
namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge ActualEisensteinCubic FirstCauchyArithmetic SecondPassArithmetic
open FirstPassCubeLabels
namespace SevenEighths.InverseInitialOverlapInputFourier
open InverseMoment InverseInitialOverlapFourier InverseInitialArithmetic InverseInitialRayAttachment
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι→Eis) [∀i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem input_integral (F : Finset ι) (Ψ : Eis→*ℂ) (j u : Eis)
    (H : Finset ι→ℝ→ℂ) (hH : ∀A∈F.powerset,Integrable (H A)) :
    inputConjugateRow p hg F Ψ j 1 1 (fun A=>∫t:ℝ,H A t) u =
      ∫t:ℝ,inputConjugateRow p hg F Ψ j 1 1 (fun A=>H A t) u := by
  rw [initial_input_row p hg]
  simp_rw [initial_input_row p hg]
  unfold supportConjugateSum
  have he (A:Finset ι) (t:ℝ) :
      supportMobius (fun i=>Ideal.span {p i}) A*
        (Ψ (∏i∈A,p i)*rowCoprimeMask (fun i=>Ideal.span {p i}) A j*H A t)*
        star (finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg A u)=
      (supportMobius (fun i=>Ideal.span {p i}) A*Ψ (∏i∈A,p i)*
        rowCoprimeMask (fun i=>Ideal.span {p i}) A j*
        star (finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg A u))*H A t := by ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun A hA=>(hH A hA).const_mul _)]
  simp only [integral_const_mul]
  apply Finset.sum_congr rfl
  intro A hA
  ring

end SevenEighths.InverseInitialOverlapInputFourier

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialOverlapSource
namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap ContDiff
namespace SevenEighths.InverseInitialOverlapSource
open InverseInitialOverlapInputFourier
variable {σ ι : Type*} [DecidableEq σ] [DecidableEq ι]

omit [DecidableEq ι] in
theorem tupleCoordinate_product (I : Finset σ) (y : σ→ι→ℝ) (q : ∀i∈I,ι) :
    (∏i∈I,tupleCoordinate I y q i)=∏i∈I.attach,y i.val (q i.val i.property) := by
  rw [←Finset.prod_attach]
  apply Finset.prod_congr rfl
  intro i hi
  simp only [tupleCoordinate,dif_pos i.property]

theorem insert_original_fresh
    (I : Finset σ) (L : σ→Finset ι) (a : σ→ι→ℂ) (y : σ→ι→ℝ)
    (lo hi : σ→ℝ) (W wFresh : ℝ→ℂ) (a₀ b₀ jlo jhi : ℝ)
    (_hW : Function.support W⊆Set.Icc a₀ b₀)
    (ha : ∀i∈I,∀q∈L i,a i q≠0→y i q∈Set.Icc (lo i) (hi i))
    (hFresh : ∀(v:σ→ℝ)(yj yc:ℝ),
      (∀i∈I,v i∈Set.Icc (lo i) (hi i))→yj∈Set.Icc jlo jhi→0<yc→
      W (yj*yc/(∏i∈I,v i))≠0→wFresh yc=1)
    (A : Finset ι) (yj yc : ℝ) (hj : yj∈Set.Icc jlo jhi) (hc : 0<yc) :
    wFresh yc*(∑q∈I.pi L,
      (∏i∈I.attach,if q i.val i.property∈A then a i.val (q i.val i.property) else 0)*
        W (yj*yc/(∏i∈I.attach,y i.val (q i.val i.property)))) =
      ∑q∈I.pi L,
        (∏i∈I.attach,if q i.val i.property∈A then a i.val (q i.val i.property) else 0)*
          W (yj*yc/(∏i∈I.attach,y i.val (q i.val i.property))) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hz : (∏i∈I.attach,if q i.val i.property∈A then a i.val (q i.val i.property) else 0)=0
  · simp only [hz,zero_mul,mul_zero]
  by_cases hw : W (yj*yc/(∏i∈I.attach,y i.val (q i.val i.property)))=0
  · simp only [hw,mul_zero]
  have hcoord : ∀i∈I,tupleCoordinate I y q i∈Set.Icc (lo i) (hi i) := by
    intro i hi
    have hn := Finset.prod_ne_zero_iff.mp hz ⟨i,hi⟩ (Finset.mem_attach _ _)
    have hcoeff : a i (q i hi)≠0 := by
      intro he
      apply hn
      split_ifs
      · exact he
      · rfl
    simpa only [tupleCoordinate,dif_pos hi] using
      ha i hi (q i hi) ((Finset.mem_pi.mp hq) i hi) hcoeff
  have hf := hFresh (tupleCoordinate I y q) yj yc hcoord hj hc
    (by rwa [tupleCoordinate_product])
  rw [hf,one_mul]

end SevenEighths.InverseInitialOverlapSource

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialCommonCutoff
namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic
namespace SevenEighths.InverseInitialCommonCutoff
open InverseMoment InverseInitialCommonProfile InverseInitialCommonRatios
open InverseInitialOverlapIdealFourier InverseInitialOverlapSource
local notation "Eis"=>ActualEisensteinCubic.O
variable {σ:Type*} [DecidableEq σ]

theorem tupleProfile_gates (I:Finset σ)(L:σ→Finset (Ideal Eis))(a:σ→Ideal Eis→ℂ)
    (hcop:∀q∈I.pi L,Pairwise (Function.onFun IsCoprime (fun i:I=>q i.val i.property)))
    (Z:ℝ)(ell:σ→ℝ)(W:ℝ→ℂ)(yj yc:ℝ)(c:Ideal Eis) :
    tupleProfile I L a Z ell W yj yc c=
      ∑q∈I.pi L,
        (∏i∈I.attach,if q i.val i.property∈activeIndices id I L c then a i.val (q i.val i.property) else 0)*
          W (yj*yc/(∏i∈I.attach,slotRatio Z ell i.val (q i.val i.property))) := by
  apply Finset.sum_congr rfl
  intro q hq
  have hg : (∏i∈I.attach,if q i.val i.property∈activeIndices id I L c then a i.val (q i.val i.property) else 0)=
      if survivingProduct I q∣c then ∏i∈I.attach,a i.val (q i.val i.property) else 0 := by
    calc
      _ = ∏i∈I.attach,if q i.val i.property∣c then a i.val (q i.val i.property) else 0 := by
        apply Finset.prod_congr rfl
        intro i hi
        simp only [activeIndices_mem id I L _ i.property ((Finset.mem_pi.mp hq) i.val i.property),id_eq]
      _ = _ := by
        convert! (preTransparency := .instances) tuple_gate_product id I a q c (hcop q hq) using 1
  rw [hg]
  split_ifs <;> simp

theorem tupleProfile_insert_fresh
    (I:Finset σ)(L:σ→Finset (Ideal Eis))(a:σ→Ideal Eis→ℂ)
    (hcop:∀q∈I.pi L,Pairwise (Function.onFun IsCoprime (fun i:I=>q i.val i.property)))
    (Z:ℝ)(ell lo hi:σ→ℝ)(W wFresh:ℝ→ℂ)(a₀ b₀ jlo jhi:ℝ)
    (hs:Function.support W⊆Set.Icc a₀ b₀)
    (ha:∀i∈I,∀q∈L i,a i q≠0→slotRatio Z ell i q∈Set.Icc (lo i) (hi i))
    (hFresh:∀(v:σ→ℝ)(yj yc:ℝ),(∀i∈I,v i∈Set.Icc (lo i) (hi i))→
      yj∈Set.Icc jlo jhi→0<yc→W (yj*yc/(∏i∈I,v i))≠0→wFresh yc=1)
    (yj yc:ℝ)(hj:yj∈Set.Icc jlo jhi)(hc:0<yc)(c:Ideal Eis) :
    wFresh yc*tupleProfile I L a Z ell W yj yc c=tupleProfile I L a Z ell W yj yc c := by
  rw [tupleProfile_gates I L a hcop]
  exact insert_original_fresh I L a (slotRatio Z ell) lo hi W wFresh a₀ b₀ jlo jhi
    hs ha hFresh (activeIndices id I L c) yj yc hj hc

end SevenEighths.InverseInitialCommonCutoff

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialCommonTransform
namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve
open ConcretePrimeRowBridge FirstCauchyArithmetic SecondPassArithmetic FirstPassCubeLabels
namespace SevenEighths.InverseInitialCommonTransform
open InverseMoment InverseInitialCommonLists InverseInitialCommonRatios InverseInitialCommonProfile
open InverseInitialCommonCutoff InverseInitialCommonTuples InverseInitialOverlapFourier
open InverseInitialOverlapInputFourier InverseInitialRayAttachment InverseInitialArithmetic
open InverseInitialOverlap InverseInitialPoissonBridge InverseInitialKernelBridge
open InverseInitialEnergyCallerWindow
local notation "Eis"=>ActualEisensteinCubic.O
variable {σ:Type*} [DecidableEq σ]

theorem original_profile_point
    (W wFresh:ℝ→ℂ)(a₀ b₀:ℝ)(ha₀:0<a₀)
    (hs:Function.support W⊆Set.Icc a₀ b₀)(hW:ContDiff ℝ ∞ W)
    (F:Finset (Ideal Eis))(I:Finset σ)(L:σ→Finset (Ideal Eis))
    (hL:∀i∈I,∀P∈L i,Prime P)(a:σ→Ideal Eis→ℂ)
    (hcop:∀q∈I.pi L,Pairwise (Function.onFun IsCoprime (fun i:I=>q i.val i.property)))
    (Z:ℝ)(hZ:0<Z)(ell lo hi:σ→ℝ)(jlo jhi:ℝ)
    (ha:∀i∈I,∀q∈L i,a i q≠0→slotRatio Z ell i q∈Set.Icc (lo i) (hi i))
    (hFresh:∀(v:σ→ℝ)(yj yc:ℝ),(∀i∈I,v i∈Set.Icc (lo i) (hi i))→
      yj∈Set.Icc jlo jhi→0<yc→W (yj*yc/(∏i∈I,v i))≠0→wFresh yc=1)
    (A:Finset (primePool F))(yj yc:ℝ)(hj:yj∈Set.Icc jlo jhi)(hjpos:0<yj)(hc:0<yc) :
    tupleProfile I L a Z ell W yj yc (∏i∈A,i.val)=
      ∫t:ℝ,density (CubicReflectionKernel.logSchwartz W a₀ b₀ ha₀ hs hW) (Real.log yj) t*
        (primeMark I (fun i=>poolList F (L i))
          (fun i q=>a i q.val*logPhase (-t) (Real.log (slotRatio Z ell i q.val))) A*
          childLogTest wFresh t yc) := by
  have he := common_profile_separation W a₀ b₀ ha₀ hs hW F I L hL a hcop Z hZ ell A yj yc hjpos hc
  have hcut := tupleProfile_insert_fresh I L a hcop Z ell lo hi W wFresh a₀ b₀ jlo jhi hs ha hFresh yj yc hj hc (∏i∈A,i.val)
  rw [←hcut]
  unfold tupleProfile
  rw [he,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  unfold childLogTest
  ring

end SevenEighths.InverseInitialCommonTransform

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialLargePool
namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve ConcretePrimeRowBridge
open FirstCauchyArithmetic SecondPassArithmetic UniqueFactorizationMonoid CanonicalRowCompletion
namespace SevenEighths.InverseInitialLargePool
open InverseInitialOverlap InverseInitialPoissonBridge InverseInitialKernelBridge
open InverseInitialRayAttachment InverseInitialArithmetic
open InverseInitialEnergyCallerWindow InverseInitialCommonForcing InverseInitialCommonTuples
local notation "Eis"=>ActualEisensteinCubic.O
local notation "O"=>ActualEisensteinCubic.O
theorem selected_conjugate_row_supported (F : Finset (Ideal O))
    (hF : ∀ I ∈ F,Admissible I) (j : Ideal O) (hj : Admissible j)
    (η : Ideal O →* ℂ) (H : Ideal O → ℂ)
    (hcop : ∀ I ∈ F,H I≠0→IsCoprime I j) (u : O) :
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
  rw [initial_input_row (poolPrimary F) (poolPrimary_good F hF)]
  unfold supportConjugateSum
  apply Finset.sum_congr rfl
  intro A hA
  dsimp only
  rw [elementCharacter_product]
  simp only [he]
  by_cases hAF : (∏ i ∈ A,i.val)∈F
  · simp only [hAF,ite_true]
    by_cases hh:H (∏i∈A,i.val)=0
    · simp only [hh,mul_zero,zero_mul]
    rw [selected_mask F j hj A (hcop _ hAF hh),mul_one]
    rw [idealRowHom_eq_idealSexticRow F hF hAF]
    simp only [supportMobius,idealSexticRow,InitialMeanSquare.pool_support_product]
    ring
  · simp only [hAF,ite_false,mul_zero,zero_mul]

theorem residual_eq_large_input
    (S F : Finset (Ideal Eis)) {P j : Ideal Eis}
    (hP : Admissible P) (hj : j∣P) (hF : ∀I∈F,Admissible I)
    (hsub : columns S P j⊆F)
    (η : Ideal Eis→*ℂ) (a : Ideal Eis→ℂ) (W : ℝ→ℂ)
    (Z r z G : ℝ) (u : Eis) :
    letI : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    residualNormalizedPolynomial S P j η a W Z r z G u =
      ((Z^(-(r+z-2*G)/2):ℝ):ℂ)*inputConjugateRow
        (poolPrimary F) (poolPrimary_good F hF) Finset.univ
        (elementCharacter η) (primaryGenerator j) 1 1
        (fun A=>if (∏i∈A,i.val)∈columns S P j then
          a (reconstruct P j (∏i∈A,i.val))*residualOverlapWindow P j W Z z G
            (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)) else 0) u := by
  let : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  let H : Ideal Eis→ℂ := fun c=>if c∈columns S P j then
    a (reconstruct P j c)*residualOverlapWindow P j W Z z G
      ((c.absNorm:ℝ)/Z^(r+z-2*G)) else 0
  have hfilter : F.filter (fun c=>c∈columns S P j)=columns S P j := by
    ext c
    simp only [Finset.mem_filter]
    exact and_iff_right_of_imp (fun h=>hsub h)
  have he : (∑c∈columns S P j,
      overlapResidualCoefficient P j η a W Z r z G c*star (CanonicalRowCompletion.idealRowHom u c))=
      ∑c∈F,(moebius c:ℂ)*η c*H c*star (CanonicalRowCompletion.idealRowHom u c) := by
    conv_rhs => arg 2;ext c;dsimp only [H];simp only [mul_ite,mul_zero,ite_mul,zero_mul]
    rw [←Finset.sum_filter,hfilter]
    apply Finset.sum_congr rfl
    intro c hc
    rw [overlapCoefficient_residual]
    unfold bareOverlapCoefficient
    ring
  unfold residualNormalizedPolynomial
  have hcH : ∀I∈F,H I≠0→IsCoprime I j := by
    intro I hIF hHI
    by_cases hi:I∈columns S P j
    · exact ((mem_columns hP.2.1 hj).mp hi).2.1
    · exact False.elim (hHI (by simp [H,hi]))
  rw [he,selected_conjugate_row_supported F hF j (admissible_of_dvd hP hj) η H hcH u]
  apply congrArg (fun v:ℂ=>((Z^(-(r+z-2*G)/2):ℝ):ℂ)*v)
  congr 1
  funext A
  dsimp [H]
  by_cases hc : (∏i∈A,i.val)∈columns S P j
  · simp only [hc,hsub hc,ite_true]
  · simp only [hc,ite_false,ite_self]

variable {κ:Type*}

end SevenEighths.InverseInitialLargePool

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialExcludedPool
namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CanonicalQuadraticSieve ConcretePrimeRowBridge UniqueFactorizationMonoid
namespace SevenEighths.InverseInitialExcludedPool
open InverseInitialOverlap InverseInitialCommonTuples InverseInitialPoissonBridge
local notation "O"=>ActualEisensteinCubic.O

theorem column_outside (A E:Finset (Ideal O)){P j c:Ideal O}
    (hE:∀Q∈E,Prime Q)(hj:j∣P)(hP:outside E P)
    (hA:∀n∈A,outside E n)(hc:c∈columns A P j):outside E c := by
  obtain ⟨n,hn,rfl⟩:=Finset.mem_image.mp hc
  obtain ⟨hnA,hns,hg⟩:=mem_original.mp hn
  have hjn:j∣n:=hg ▸ GCDMonoid.gcd_dvd_left n P
  intro Q hQ hd
  rcases (hE Q hQ).dvd_mul.mp hd with hn|hpr
  · exact hA n hnA Q hQ (hn.trans (idealQuotient_dvd hjn))
  · exact hP Q hQ (hpr.trans (idealQuotient_dvd hj))

end SevenEighths.InverseInitialExcludedPool

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialExcludedOverlap
namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CanonicalQuadraticSieve ConcretePrimeRowBridge UniqueFactorizationMonoid
namespace SevenEighths.InverseInitialExcludedOverlap
open InverseInitialOverlap InverseInitialPoissonBridge InverseInitialExcludedPool
open HeckeFamily
local notation "O"=>ActualEisensteinCubic.O

theorem reconstruct_outside (E:Finset (Ideal O)){P j c:Ideal O}
    (hE:∀Q∈E,Prime Q)(hj:j∣P)(hP:outside E P)(hc:outside E c)
    (hres:residual P j∣c):outside E (reconstruct P j c) := by
  intro Q hQ hQn
  rcases (hE Q hQ).dvd_mul.mp hQn with hQj|hQc
  · exact hP Q hQ (hQj.trans hj)
  · exact hc Q hQ (hQc.trans (idealQuotient_dvd hres))

theorem columns_filter (A E:Finset (Ideal O)){P j:Ideal O}
    (hE:∀Q∈E,Prime Q)(hPs:Squarefree P)(hj:j∣P)(hP:outside E P):
    columns (originalOutside A E) P j=(columns A P j).filter (outside E) := by
  ext c
  constructor
  · intro hc
    have hd:=(mem_columns hPs hj).mp hc
    apply Finset.mem_filter.mpr
    refine ⟨(mem_columns hPs hj).mpr ⟨hd.1,hd.2.1,hd.2.2.1,?_⟩,?_⟩
    · exact (Finset.mem_filter.mp hd.2.2.2).1
    · exact column_outside _ E hE hj hP (fun n hn=>(Finset.mem_filter.mp hn).2) hc
  · intro hc
    obtain ⟨hcA,hout⟩:=Finset.mem_filter.mp hc
    obtain ⟨hcs,hcj,hres,hnA⟩:=(mem_columns hPs hj).mp hcA
    exact (mem_columns hPs hj).mpr ⟨hcs,hcj,hres,
      Finset.mem_filter.mpr ⟨hnA,reconstruct_outside E hE hj hP hout hres⟩⟩

theorem residual_filtered (A E:Finset (Ideal O)){P j:Ideal O}
    (hE:∀Q∈E,Prime Q)(hPs:Squarefree P)(hj:j∣P)(hP:outside E P)
    (η:Ideal O→*ℂ)(hη:∀I,¬outside E I→η I=0)
    (a:Ideal O→ℂ)(W:ℝ→ℂ)(Z r z G:ℝ)(u:O):
    residualNormalizedPolynomial A P j η a W Z r z G u=
    residualNormalizedPolynomial (originalOutside A E) P j η a W Z r z G u := by
  unfold residualNormalizedPolynomial
  rw [columns_filter A E hE hPs hj hP,Finset.sum_filter]
  congr 1
  apply Finset.sum_congr rfl
  intro c hc
  by_cases hout:outside E c
  · rw [if_pos hout]
  · rw [if_neg hout]
    simp only [overlapResidualCoefficient,hη c hout,mul_zero,zero_mul]

end SevenEighths.InverseInitialExcludedOverlap

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
open InverseInitialEnergyCallerWindow InverseInitialCommonForcing InverseInitialLargePool
open InverseInitialExcludedPool InverseInitialExcludedOverlap
open InverseInitialCommonTuples InverseInitialCommonTransform
local notation "O"=>ActualEisensteinCubic.O

theorem pool_product_outside (F E:Finset (Ideal O))(hE:∀Q∈E,Prime Q)
    (hF:∀I∈F,outside E I)(A:Finset (primePool F)):
    outside E (∏i∈A,i.val) := by
  intro Q hQ hd
  obtain ⟨i,hi,hQi⟩:=((hE Q hQ).dvd_finsetProd_iff (fun i:primePool F=>i.val)).mp hd
  obtain ⟨I,hIF,hfactor⟩:=mem_primePool_iff.mp i.property
  exact hF I hIF Q hQ (hQi.trans (dvd_of_mem_normalizedFactors hfactor))

theorem residual_excluded_forcing
    (W:ℝ→ℂ)(Z r z G b:ℝ)(hZ:0<Z)(hW:∀x,W x≠0→x≤b)
    (E:Finset (Ideal O))(hE:∀Q∈E,Prime Q)
    {P j:Ideal O}(hP:Admissible P)(hj:j∣P)(hPE:outside E P)
    (F:Finset (Ideal O))(hF:∀I∈F,Admissible I)(hFE:∀I∈F,outside E I)
    (hsub:columns (originalOutside (originalSource Z r b) E) P j⊆F)
    (η:Ideal O→*ℂ)(hη:∀I,¬outside E I→η I=0)(u:O):
    letI : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    residualNormalizedPolynomial (originalSource Z r b) P j η (fun _=>1) W Z r z G u=
      ((Z^(-(r+z-2*G)/2):ℝ):ℂ)*inputConjugateRow
        (poolPrimary F) (poolPrimary_good F hF) Finset.univ
        (elementCharacter η) (primaryGenerator j) 1 1
        (fun A=>if residual P j∣(∏i∈A,i.val) then
          residualOverlapWindow P j W Z z G
            (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)) else 0) u := by
  let : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  rw [residual_filtered _ E hE hP.2.1 hj hPE η hη,
    residual_eq_large_input _ F hP hj hF hsub η (fun _=>1) W Z r z G u]
  simp only [one_mul]
  apply congrArg (fun v:ℂ=>((Z^(-(r+z-2*G)/2):ℝ):ℂ)*v)
  rw [initial_input_row (poolPrimary F) (poolPrimary_good F hF),
    initial_input_row (poolPrimary F) (poolPrimary_good F hF)]
  unfold supportConjugateSum
  apply Finset.sum_congr rfl
  intro A hA
  have he:=common_selector_window W Z r z G b hZ hW hP hj F hF A
  have hm:rowCoprimeMask (fun i:primePool F=>Ideal.span {poolPrimary F i}) A
      (primaryGenerator j)=rowCoprimeMask (fun i:primePool F=>i.val) A (primaryGenerator j):=by
    congr 1
    funext i
    exact poolPrimary_span F hF i
  have hmem:((∏i∈A,i.val)∈columns (originalOutside (originalSource Z r b) E) P j)↔
      ((∏i∈A,i.val)∈columns (originalSource Z r b) P j):=by
    rw [columns_filter _ E hE hP.2.1 hj hPE,Finset.mem_filter]
    exact and_iff_left (pool_product_outside F E hE hFE A)
  dsimp only
  simp only [hm,hmem]
  linear_combination
    (supportMobius (fun i:primePool F=>Ideal.span {poolPrimary F i}) A *
      elementCharacter η (∏i∈A,poolPrimary F i) *
      star (finiteSquarefreeRow (fun i:primePool F=>Ideal.span {poolPrimary F i})
        (poolPrimary_good F hF) A u))*he

variable {κ:Type*}
theorem original_tuples_excluded_input
    (W:ℝ→ℂ)(Z r z G b:ℝ)(hZ:0<Z)(hW:∀x,W x≠0→x≤b)
    (E:Finset (Ideal O))(hE:∀Q∈E,Prime Q)
    (T:Finset κ)(P:κ→Ideal O)(j:Ideal O)
    (hP:∀k∈T,Admissible (P k))(hj:∀k∈T,j∣P k)
    (hPE:∀k∈T,outside E (P k))
    (F:Finset (Ideal O))(hF:∀I∈F,Admissible I)(hFE:∀I∈F,outside E I)
    (hsub:tupleColumns (originalOutside (originalSource Z r b) E) T P j⊆F)
    (η:Ideal O→*ℂ)(hη:∀I,¬outside E I→η I=0)(a:κ→ℂ)(u:O) :
    let S := originalSource Z r b
    letI : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    (∑k∈T,a k*residualNormalizedPolynomial S (P k) j η (fun _=>1) W Z r z G u)=
      ((Z^(-(r+z-2*G)/2):ℝ):ℂ)*inputConjugateRow
        (poolPrimary F) (poolPrimary_good F hF) Finset.univ
        (elementCharacter η) (primaryGenerator j) 1 1
        (fun A=>∑k∈T,a k*(if residual (P k) j∣(∏i∈A,i.val) then
          residualOverlapWindow (P k) j W Z z G
            (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)) else 0)) u := by
  intro S
  let : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  rw [input_finset_sum (poolPrimary F) (poolPrimary_good F hF)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [residual_excluded_forcing W Z r z G b hZ hW E hE (hP k hk) (hj k hk) (hPE k hk) F hF hFE
    (fun c hc=>hsub (Finset.mem_biUnion.mpr ⟨k,hk,hc⟩)) η hη u]
  ring

end SevenEighths.InverseInitialExcludedForcing

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialExcludedFourier
namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve
open ConcretePrimeRowBridge FirstCauchyArithmetic SecondPassArithmetic FirstPassCubeLabels
namespace SevenEighths.InverseInitialExcludedFourier
open InverseMoment InverseInitialCommonLists InverseInitialCommonRatios InverseInitialCommonProfile
open InverseInitialCommonCutoff InverseInitialCommonTuples InverseInitialOverlapFourier
open InverseInitialOverlapInputFourier InverseInitialRayAttachment InverseInitialArithmetic
open InverseInitialOverlap InverseInitialPoissonBridge InverseInitialKernelBridge
open InverseInitialEnergyCallerWindow
local notation "Eis"=>ActualEisensteinCubic.O
variable {σ:Type*} [DecidableEq σ]

open InverseInitialCommonTransform InverseInitialLargePool
open InverseInitialExcludedPool InverseInitialExcludedForcing
theorem original_tuples_excluded_fourier_oai
    (W wFresh:ℝ→ℂ)(a₀ b₀:ℝ)(ha₀:0<a₀)
    (hs:Function.support W⊆Set.Icc a₀ b₀)(hW:ContDiff ℝ ∞ W)
    (E:Finset (Ideal Eis))(hE:∀Q∈E,Prime Q)
    (I:Finset σ)(L:σ→Finset (Ideal Eis))(hL:∀i∈I,∀P∈L i,Prime P)
    (a:σ→Ideal Eis→ℂ)(j:Ideal Eis)(hj0:j≠0)
    (hP:∀q∈I.pi L,Admissible (j*survivingProduct I q))
    (hcop:∀q∈I.pi L,Pairwise (Function.onFun IsCoprime (fun i:I=>q i.val i.property)))
    (hPE:∀q∈I.pi L,outside E (j*survivingProduct I q))
    (η:Ideal Eis→*ℂ)(hη:∀c,¬outside E c→η c=0)(u:Eis)(Z r z G:ℝ)(hZ:0<Z)(ell lo hi:σ→ℝ)
    (hell:∑i∈I,ell i=z-G)(jlo jhi:ℝ)
    (hj:((j.absNorm:ℝ)/Z^G)∈Set.Icc jlo jhi)
    (ha:∀i∈I,∀q∈L i,a i q≠0→slotRatio Z ell i q∈Set.Icc (lo i) (hi i))
    (hFresh:∀(v:σ→ℝ)(yj yc:ℝ),(∀i∈I,v i∈Set.Icc (lo i) (hi i))→
      yj∈Set.Icc jlo jhi→0<yc→W (yj*yc/(∏i∈I,v i))≠0→wFresh yc=1)
    (F:Finset (Ideal Eis))(hF:∀c∈F,Admissible c)(hFE:∀c∈F,outside E c)
    (hsub:tupleColumns (originalOutside (originalSource Z r b₀) E) (I.pi L)
      (fun q:∀i∈I,Ideal Eis=>j*survivingProduct I q) j⊆F) :
    let S := originalSource Z r b₀
    let P := fun q:∀i∈I,Ideal Eis=>j*survivingProduct I q
    letI : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    (∑q∈I.pi L,(∏i∈I.attach,a i.val (q i.val i.property))*
      residualNormalizedPolynomial S (P q) j η (fun _=>1) W Z r z G u)=
      ∫t:ℝ,density (CubicReflectionKernel.logSchwartz W a₀ b₀ ha₀ hs hW)
        (Real.log ((j.absNorm:ℝ)/Z^G)) t*
        (((Z^(-(r+z-2*G)/2):ℝ):ℂ)*inputConjugateRow
          (poolPrimary F) (poolPrimary_good F hF) Finset.univ
          (elementCharacter η) (primaryGenerator j) 1 1
          (initialTest (poolPrimary F)
            (primeMark I (fun i=>poolList F (L i))
              (fun i q=>a i q.val*logPhase (-t) (Real.log (slotRatio Z ell i q.val))))
            (childLogTest wFresh t) Z (r+z-2*G)) u) := by
  intro S P
  let : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  have hjpos : 0<(j.absNorm:ℝ)/Z^G := by
    apply div_pos _ (Real.rpow_pos_of_pos hZ G)
    exact_mod_cast Nat.pos_of_ne_zero (fun h=>hj0 (Ideal.absNorm_eq_zero_iff.mp h))
  let g := CubicReflectionKernel.logSchwartz W a₀ b₀ ha₀ hs hW
  let H : Finset (primePool F)→ℝ→ℂ := fun A t=>density g (Real.log ((j.absNorm:ℝ)/Z^G)) t*
    (primeMark I (fun i=>poolList F (L i))
      (fun i q=>a i q.val*logPhase (-t) (Real.log (slotRatio Z ell i q.val))) A*
      childLogTest wFresh t (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)))
  have hHi (A:Finset (primePool F)) : Integrable (H A) := by
    have hh := (common_profile_integrable g F I L a Z ell A
      ((j.absNorm:ℝ)/Z^G) (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G))).const_mul
      (wFresh (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)))
    convert (preTransparency := .instances) hh using 1
    funext t
    dsimp [H,childLogTest]
    ring
  have hpoint (A:Finset (primePool F)) :
      (∑q∈I.pi L,(∏i∈I.attach,a i.val (q i.val i.property))*
        (if residual (P q) j∣(∏i∈A,i.val) then residualOverlapWindow (P q) j W Z z G
          (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)) else 0))=∫t:ℝ,H A t := by
    dsimp only [P]
    simp_rw [actual_residual_product I _ j hj0,original_residual_window I _ j hj0 ell W Z r z G hZ hell]
    apply original_profile_point W wFresh a₀ b₀ ha₀ hs hW F I L hL a hcop Z hZ ell lo hi jlo jhi ha hFresh A
      ((j.absNorm:ℝ)/Z^G) (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)) hj hjpos
    apply div_pos _ (Real.rpow_pos_of_pos hZ _)
    exact_mod_cast Nat.pos_of_ne_zero (fun h=>(InitialMeanSquare.poolProduct_admissible F hF A).1
      (Ideal.absNorm_eq_zero_iff.mp h))
  rw [original_tuples_excluded_input W Z r z G b₀ hZ (fun x hx=>(hs hx).2) E hE
    (I.pi L) P j hP (fun q _=>dvd_mul_right j _) hPE F hF hFE hsub η hη (fun q=>∏i∈I.attach,a i.val (q i.val i.property)) u]
  change ((Z^(-(r+z-2*G)/2):ℝ):ℂ)*inputConjugateRow
    (poolPrimary F) (poolPrimary_good F hF) Finset.univ
    (elementCharacter η) (primaryGenerator j) 1 1
    (fun A=>∑q∈I.pi L,(∏i∈I.attach,a i.val (q i.val i.property))*
      (if residual (P q) j∣(∏i∈A,i.val) then residualOverlapWindow (P q) j W Z z G
        (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)) else 0)) u = _
  rw [show (fun A:Finset (primePool F)=>∑q∈I.pi L,
    (∏i∈I.attach,a i.val (q i.val i.property))*
      (if residual (P q) j∣(∏i∈A,i.val) then residualOverlapWindow (P q) j W Z z G
        (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)) else 0)) = (fun A=>∫t:ℝ,H A t)
    from funext hpoint]
  rw [input_integral (poolPrimary F) (poolPrimary_good F hF) Finset.univ
    (elementCharacter η) (primaryGenerator j) u H (fun A _=>hHi A),←integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  dsimp only [H]
  rw [initial_input_row (poolPrimary F) (poolPrimary_good F hF),
    initial_input_row (poolPrimary F) (poolPrimary_good F hF)]
  unfold supportConjugateSum
  simp only [Finset.mul_sum,initialTest,InitialMeanSquare.poolPrimary_norm F hF]
  apply Finset.sum_congr rfl
  intro A hA
  ring

end SevenEighths.InverseInitialExcludedFourier

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.SevenEighths.InverseInitialExcludedFourier.original_tuples_excluded_fourier_oai.{u_1} := @OAI.SevenEighths.InverseInitialExcludedFourier.original_tuples_excluded_fourier_oai.{u_1}
