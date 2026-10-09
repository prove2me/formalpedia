-- Prove2me | solution 1 for OAI.SevenEighths.InverseInitialEnergyCallerIntegral.actual_common_integral_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T01:53:34.557157+00:00
-- url     : https://prove2.me/submissions/10d1525d-1691-4579-878e-ab612751ca83

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIHecke78B019

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.ActiveGaussFactorization
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

open scoped BigOperators Classical

namespace FiniteGaussPhase

open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

theorem norm_angularFactor (a : O) (ha : a ≠ 0) : ‖angularFactor a‖ = 1 := by
  rw [angularFactor, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _)]
  exact div_self (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero ha))

end FiniteGaussPhase

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.QuadraticSieve.CoefficientCancellation
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

open scoped BigOperators Classical SchwartzMap ContDiff

open scoped BigOperators Classical SchwartzMap
namespace QuadraticInitialBound
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

theorem norm_ideal_moebius_le_one (I : Ideal O) :
    ‖(UniqueFactorizationMonoid.moebius I : ℂ)‖ ≤ 1 := by
  unfold UniqueFactorizationMonoid.moebius
  split_ifs <;> simp

end QuadraticInitialBound

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Mellin.UniformKernelBounds
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
open MixedCrossSeparation (crossSymbol quadraticCrossPhase columnPrimeCoprime)
open FiniteGaussPhase (canonicalProductGauss canonicalProductGauss_cross_factors)
open MixedGaussConversion (localGauss)

theorem canonicalProductGauss_eq_gaussBlock {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S : Finset ι) (e : ι → ℕ)
    (he : ∀ i ∈ S, e i ≠ 0) :
    canonicalProductGauss (fun i : S => p i.val) (fun i => hp i.val)
      (columnPrimeCoprime p hcop S) (fun i => hg i.val) (fun i => e i.val) =
      gaussBlock p hp hg S e := by
  let : DecidableEq S := fun a b => Classical.propDecidable (a = b)
  rw [canonicalProductGauss_cross_factors, ← Finset.prod_mul_distrib]
  have hin (i : S) :
      (∏ k ∈ (Finset.univ : Finset S).erase i,
        (canonicalSextic (Ideal.span {p i.val}) (hg i.val) ^ e i.val)
          (Ideal.Quotient.mk (Ideal.span {p i.val}) (p k.val))) =
      ∏ k ∈ S.erase i.val, crossSymbol p hg i.val k ^ e i.val := by
    apply Finset.prod_bij (fun k _ => k.val)
    · intro k hk
      exact Finset.mem_erase.mpr ⟨fun h => (Finset.mem_erase.mp hk).1 (Subtype.ext h), k.property⟩
    · intro a ha b hb hab
      exact Subtype.ext hab
    · intro k hk
      refine ⟨⟨k, (Finset.mem_erase.mp hk).2⟩, ?_, rfl⟩
      exact Finset.mem_erase.mpr ⟨fun h => (Finset.mem_erase.mp hk).1 (congrArg Subtype.val h),
        Finset.mem_univ _⟩
    · intro k hk
      exact MulChar.pow_apply' _ (he i.val i.property) _
  calc
    _ = ∏ i : S, (∏ k ∈ S.erase i.val, crossSymbol p hg i.val k ^ e i.val) *
        localGauss (p i.val) (hp i.val) (hg i.val) (e i.val) := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [hin i]
      rfl
    _ = _ := Finset.prod_coe_sort S (fun i =>
      (∏ k ∈ S.erase i, crossSymbol p hg i k ^ e i) * localGauss (p i) (hp i) (hg i) (e i))

theorem columnCoefficient_eq_gaussBlock {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S : Finset ι) :
    MixedCrossSeparation.columnCoefficient p hp hcop hg S =
      star (FiniteGaussPhase.angularFactor (∏ i ∈ S, p i)) *
        gaussBlock p hp hg S (fun _ => 2) := by
  unfold MixedCrossSeparation.columnCoefficient FiniteGaussPhase.canonicalProductCoefficient
  rw [Finset.prod_coe_sort]
  rw [canonicalProductGauss_eq_gaussBlock p hp hcop hg S (fun _ => 2) (fun _ _ => by decide)]

theorem gaussBlock_norm_one {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (S : Finset ι) (e : ι → ℕ) (he : ∀ i ∈ S, e i ≠ 0) (he6 : ∀ i ∈ S, e i < 6) :
    ‖gaussBlock p hp hg S e‖ = 1 := by
  rw [← canonicalProductGauss_eq_gaussBlock p hp hcop hg S e he]
  exact FiniteGaussPhase.norm_canonicalProductGauss
    (fun i : S => p i.val) (fun i => hp i.val) (columnPrimeCoprime p hcop S)
    (fun i => hg i.val) (fun i => hc i.val) (fun i => e i.val)
    (fun i => he i.val i.property) (fun i => he6 i.val i.property)

end FirstPassCubeLabels

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.FirstPassage
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

namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open MixedCrossSeparation (columnCoefficient columnG convertedColumnBlock quadraticCrossPhase
  columnPrimeCoprime )
open FirstCauchyArithmetic (supportMobius activeGaussRowFactor)

theorem columnCoefficient_norm_one {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (S : Finset ι) :
    ‖columnCoefficient p hp hcop hg S‖ = 1 := by
  rw [FirstPassCubeLabels.columnCoefficient_eq_gaussBlock, norm_mul, norm_star,
    FiniteGaussPhase.norm_angularFactor _
      (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)),
    FirstPassCubeLabels.gaussBlock_norm_one p hp hcop hg hc S (fun _ => 2)
      (fun _ _ => by decide) (fun _ _ => by decide), one_mul]

end

open ActualEisensteinCubic
open FirstCauchyArithmetic (supportMobius)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

end SecondPassArithmetic

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

open scoped BigOperators Classical
namespace SecondPassArithmetic

open ActualEisensteinCubic
open FirstCauchyArithmetic (supportMobius)
open RayFourExpansion (RayCharacter gCoeff crossCoeff)

lemma secondRayMinus_norm_le (Ψ : O →* ℂ) (z : SecondRayIndex) (a : O) :
    ‖secondRayMinus Ψ z a‖ ≤ ‖Ψ a‖ := by
  simp only [secondRayMinus, MonoidHom.mul_apply, norm_mul, conjugateRayMonoid_apply, norm_star]
  calc
    _ ≤ 1 * (1 * ‖Ψ a‖) := by
      gcongr <;> exact FiniteRayExpansion.norm_char_le_one _ _
    _ = _ := by ring

lemma secondRayPlus_norm_le (Ψ : O →* ℂ) (z : SecondRayIndex) (a : O) :
    ‖secondRayPlus Ψ z a‖ ≤ ‖Ψ a‖ := by
  simp only [secondRayPlus, MonoidHom.mul_apply, norm_mul, conjugateRayMonoid_apply, rayMonoid_apply, norm_star]
  calc
    _ ≤ 1 * (1 * ‖Ψ a‖) := by
      gcongr <;> exact FiniteRayExpansion.norm_char_le_one _ _
    _ = _ := by ring

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem secondPreColumn_norm_le
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (Ψ : O →* ℂ) (m c d e k : O) (S : Finset ι) :
    ‖secondPreColumn p hp hcop hg Ψ m c d e k (fun _ => 1) S‖ ≤ ‖Ψ (∏ i ∈ S, p i)‖ := by
  have hm : ‖rowCoprimeMask (fun i => Ideal.span {p i}) S m‖ ≤ 1 := by
    unfold rowCoprimeMask
    split_ifs <;> norm_num
  simp only [secondPreColumn, norm_mul, norm_pow, norm_star, norm_one,
    columnCoefficient_norm_one p hp hcop hg hc S]
  calc
    _ ≤ 1 * ‖Ψ (∏ i ∈ S, p i)‖ * 1 * 1 ^ 4 * 1 * 1 * 1 * 1 := by
      gcongr <;> first | exact hm | exact finiteSquarefreeRow_norm_le_one _ hg S _
    _ = _ := by ring

end

end SecondPassArithmetic

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

theorem tripleCoefficient_weighted_integrable (b₁ b₂ b₃ : 𝓢(ℝ, ℂ)) (J : ℕ) :
    Integrable (fun t : Frequency =>
      ((1 + ‖t.1‖)^J * (1 + ‖t.2.1‖)^J * (1 + ‖t.2.2‖)^J) *
        ‖tripleCoefficient b₁ b₂ b₃ t‖) := by
  have hi (b : 𝓢(ℝ, ℂ)) : Integrable (fun t : ℝ => (1 + ‖t‖)^J * ‖b t‖) := by
    have he : (𝓕 (𝓕⁻ b) : 𝓢(ℝ, ℂ)) = b := by simp
    simpa only [he] using AnalyticBridge.schwartz_fourier_one_plus_integrable (𝓕⁻ b) J
  convert (preTransparency := .instances) (hi b₁).mul_prod ((hi b₂).mul_prod (hi b₃)) using 1
  funext t
  simp only [tripleCoefficient, norm_mul]
  ring

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.Fibers
namespace OAI

namespace SevenEighths.InverseMoment

open scoped BigOperators

noncomputable section

theorem fiber_energy_bound {ι κ : Type*} [DecidableEq κ]
    (s : Finset ι) (t : Finset κ) (p : ι → κ) (w : ι → ℝ)
    (D E : κ → ℝ) (hp : ∀ i ∈ s, p i ∈ t)
    (hE : ∀ j ∈ t, 0 ≤ E j)
    (hD : ∀ j ∈ t, ∑ i ∈ s with p i = j, w i ≤ D j) :
    ∑ i ∈ s, w i * E (p i) ≤ ∑ j ∈ t, D j * E j := by
  calc
    ∑ i ∈ s, w i * E (p i) =
        ∑ j ∈ t, ∑ i ∈ s with p i = j, w i * E (p i) :=
      (Finset.sum_fiberwise_of_maps_to hp _).symm
    _ = ∑ j ∈ t, (∑ i ∈ s with p i = j, w i) * E j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    _ ≤ ∑ j ∈ t, D j * E j :=
      Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_right (hD j hj) (hE j hj)

end

end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialFibers
namespace OAI

namespace SevenEighths.InverseInitialFibers

open ActualEisensteinCubic
open CompletedGauss (primaryGenerator primaryGenerator_mul)
open IdealMobiusDivisorSum (idealDivisors mem_idealDivisors)
open scoped BigOperators Classical
noncomputable section

lemma divisor_ne_zero {J : ℕ} {x : InitialTuple J} {t f : Ideal O} {k : O}
    (hx : Valid x t f k) (hf : f ≠ 0) : x.divisor ≠ 0 := by
  intro hz
  have he := hx.label_eq
  rw [hz, zero_mul] at he
  exact hf he.symm

theorem valid_key_injective {J : ℕ} (t f : Ideal O) (k : O) (hf : f ≠ 0)
    {x y : InitialTuple J} (hx : Valid x t f k) (hy : Valid y t f k)
    (hd : x.divisor = y.divisor) (ha : x.assigned = y.assigned) : x = y := by
  have hd0 := divisor_ne_zero hx hf
  have hc : x.common = y.common := by rw [← hx.common_eq, ← hy.common_eq, hd]
  have hs : x.residual = y.residual := by
    apply mul_left_cancel₀ hd0
    exact hx.label_eq.trans (by simpa only [hd] using hy.label_eq.symm)
  have hg : primaryGenerator x.divisor ≠ 0 := hx.divisor_good
  have hr : x.frequency = y.frequency := by
    apply mul_left_cancel₀ hg
    exact hx.row_eq.trans (by simpa only [hd] using hy.row_eq.symm)
  exact InitialTuple.ext hc hd hs hr ha

lemma divisors_mul_image (I J : Ideal O) (hI : I ≠ 0) (hJ : J ≠ 0) :
    idealDivisors (I*J) =
      ((idealDivisors I) ×ˢ (idealDivisors J)).image (fun p => p.1*p.2) := by
  ext D
  rw [mem_idealDivisors (mul_ne_zero hI hJ), Finset.mem_image]
  constructor
  · intro hD
    obtain ⟨A, B, hA, hB, hab⟩ := exists_dvd_and_dvd_of_dvd_mul hD
    exact ⟨(A,B), Finset.mem_product.mpr
      ⟨(mem_idealDivisors hI).mpr hA, (mem_idealDivisors hJ).mpr hB⟩, hab.symm⟩
  · rintro ⟨p, hp, rfl⟩
    exact mul_dvd_mul ((mem_idealDivisors hI).mp (Finset.mem_product.mp hp).1)
      ((mem_idealDivisors hJ).mp (Finset.mem_product.mp hp).2)

lemma divisor_card_mul_le (I J : Ideal O) (hI : I ≠ 0) (hJ : J ≠ 0) :
    (idealDivisors (I*J)).card ≤ (idealDivisors I).card * (idealDivisors J).card := by
  rw [divisors_mul_image I J hI hJ, ← Finset.card_product]
  exact Finset.card_image_le

theorem valid_tuple_card_le {J : ℕ} (T : Finset (InitialTuple J))
    (t f : Ideal O) (k : O) (ht : t ≠ 0) (hf : f ≠ 0)
    (hT : ∀ x ∈ T, Valid x t f k) :
    T.card ≤ (idealDivisors f).card * (idealDivisors (t*f)).card^J := by
  let D := idealDivisors f
  let E := idealDivisors (t*f)
  let encode (x : T) : D × (Fin J → E) :=
    (⟨x.val.divisor, (mem_idealDivisors hf).mpr (divisor_dvd (hT x.val x.property))⟩,
      fun i => ⟨(x.val.assigned i).val,
        (mem_idealDivisors (mul_ne_zero ht hf)).mpr ((hT x.val x.property).assigned_dvd i)⟩)
  have hi : Function.Injective encode := by
    intro x y hxy
    apply Subtype.ext
    apply valid_key_injective t f k hf (hT x.val x.property) (hT y.val y.property)
    · exact congrArg Subtype.val (congrArg Prod.fst hxy)
    · funext i
      apply Subtype.ext
      exact congrArg (fun z : E => z.val) (congrFun (congrArg Prod.snd hxy) i)
  simpa only [Fintype.card_coe, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_fin, D, E] using Fintype.card_le_of_injective encode hi

theorem valid_tuple_card_le_separated {J : ℕ} (T : Finset (InitialTuple J))
    (t f : Ideal O) (k : O) (ht : t ≠ 0) (hf : f ≠ 0)
    (hT : ∀ x ∈ T, Valid x t f k) :
    T.card ≤ (idealDivisors f).card^(J+1) * (idealDivisors t).card^J := by
  apply (valid_tuple_card_le T t f k ht hf hT).trans
  calc
    _ ≤ (idealDivisors f).card *
        ((idealDivisors t).card * (idealDivisors f).card)^J :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (divisor_card_mul_le t f ht hf) J)
    _ = _ := by rw [mul_pow, pow_succ]; ring

lemma divisor_card_pos (I : Ideal O) (hI : I ≠ 0) : 1 ≤ (idealDivisors I).card := by
  apply Finset.one_le_card.mpr
  exact ⟨1, (mem_idealDivisors hI).mpr (one_dvd I)⟩

end
end SevenEighths.InverseInitialFibers

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.InitializationEnergy
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CompletedGauss CanonicalQuadraticSieve SevenEighths.InverseInitialFibers
open IdealMobiusDivisorSum
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem initialChild_valid {J : ℕ} (x : InitialTuple J) (hx : InitialSourceValid x) :
    Valid x (initialChild x).1 (initialChild x).2.1 (initialChild x).2.2 := by
  have ht : idealQuotient x.divisor x.common * x.divisor = x.common := by
    rw [mul_comm, idealQuotient_mul hx.divisor_dvd]
  refine ⟨ht, rfl, hx.divisor_good, rfl, ?_⟩
  intro i
  change (x.assigned i).val ∣ idealQuotient x.divisor x.common * (x.divisor * x.residual)
  rw [← mul_assoc, ht]
  exact hx.assigned_dvd i

theorem initialChild_nonzero {J : ℕ} (x : InitialTuple J) (hx : InitialSourceValid x) :
    (initialChild x).1 ≠ 0 ∧ (initialChild x).2.1 ≠ 0 := by
  have hD : x.divisor ≠ 0 := by intro he; exact hx.divisor_good (by simp [he])
  constructor
  · intro ht
    have he := (initialChild_valid x hx).common_eq
    rw [ht, zero_mul] at he
    exact hx.common_ne_zero he.symm
  · exact mul_ne_zero hD hx.residual_ne_zero

theorem initialChild_fiber_weight {J : ℕ} (source : Finset (InitialTuple J))
    (hsource : ∀ x ∈ source, InitialSourceValid x) (c : InitialChild)
    (ht : c.1 ≠ 0) (hf : c.2.1 ≠ 0) (w : InitialTuple J → ℝ)
    (hw : ∀ x ∈ source, w x ≤ 1) :
    (∑ x ∈ source with initialChild x = c, w x) ≤ initialDivisorWeight J c := by
  have hvalid : ∀ x ∈ source.filter (fun x => initialChild x = c), Valid x c.1 c.2.1 c.2.2 := by
    intro x hx
    obtain ⟨hxs, he⟩ := Finset.mem_filter.mp hx
    simpa only [he] using initialChild_valid x (hsource x hxs)
  calc
    _ ≤ ∑ _x ∈ source.filter (fun x => initialChild x = c), (1 : ℝ) :=
      Finset.sum_le_sum (fun x hx => hw x (Finset.mem_filter.mp hx).1)
    _ = ((source.filter (fun x => initialChild x = c)).card : ℝ) := by simp
    _ ≤ initialDivisorWeight J c := by
      have hh := valid_tuple_card_le_separated _ c.1 c.2.1 c.2.2 ht hf hvalid
      dsimp only [initialDivisorWeight]
      exact_mod_cast hh

theorem initial_energy_projection {J : ℕ} (source : Finset (InitialTuple J))
    (hsource : ∀ x ∈ source, InitialSourceValid x)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis)
    (hlabels : ∀ f ∈ labels, f ≠ 0)
    (hchild : ∀ x ∈ source, (initialChild x).2.1 ∈ labels ∧ (initialChild x).2.2 ∈ rows)
    (w : InitialTuple J → ℝ) (hw : ∀ x ∈ source, w x ≤ 1) (F : InitialChild → ℂ) :
    (∑ x ∈ source, w x * ‖F (initialChild x)‖ ^ 2) ≤
      ∑ t ∈ initialQuotientSet source, ((idealDivisors t).card : ℝ) ^ J *
        ∑ f ∈ labels, ((idealDivisors f).card : ℝ) ^ (J + 1) *
          ∑ k ∈ rows, ‖F (t, f, k)‖ ^ 2 := by
  have hmaps : ∀ x ∈ source, initialChild x ∈ initialQuotientSet source ×ˢ (labels ×ˢ rows) := by
    intro x hx
    exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨x, hx, rfl⟩,
      Finset.mem_product.mpr (hchild x hx)⟩
  have hfiber : ∀ c ∈ initialQuotientSet source ×ˢ (labels ×ˢ rows),
      (∑ x ∈ source with initialChild x = c, w x) ≤ initialDivisorWeight J c := by
    intro c hc
    obtain ⟨ht, hfk⟩ := Finset.mem_product.mp hc
    obtain ⟨x, hx, he⟩ := Finset.mem_image.mp ht
    have ht0 : c.1 ≠ 0 := he ▸ (initialChild_nonzero x (hsource x hx)).1
    exact initialChild_fiber_weight source hsource c ht0
      (hlabels c.2.1 (Finset.mem_product.mp hfk).1) w hw
  have he := fiber_energy_bound source (initialQuotientSet source ×ˢ (labels ×ˢ rows))
    initialChild w (initialDivisorWeight J) (fun c => ‖F c‖ ^ 2) hmaps
    (fun _ _ => sq_nonneg _) hfiber
  apply he.trans_eq
  simp only [Finset.sum_product, initialDivisorWeight, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  apply Finset.sum_congr rfl
  intro f hf
  apply Finset.sum_congr rfl
  intro k hk
  ring

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.TripleMass
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open SevenEighths.InverseSecondFibers IdealMobiusDivisorSum
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem ideal_divisor_power_small (j : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ I : Ideal Eis, I ≠ 0 →
      ((idealDivisors I).card : ℝ)^j ≤ C*(Ideal.absNorm I : ℝ)^ε := by
  have hj : 0 < (j+1 : ℝ) := by positivity
  obtain ⟨C,hC,hb⟩ := IdealDivisorBound.ideal_divisor_small_power (ε/(j+1)) (div_pos hε hj)
  refine ⟨C ^(j+1), by positivity, ?_⟩
  intro I hI
  have hcard : (1 : ℝ) ≤ (idealDivisors I).card := by
    exact_mod_cast InverseInitialFibers.divisor_card_pos I hI
  calc
    _ ≤ ((idealDivisors I).card : ℝ)^(j+1) := pow_le_pow_right₀ hcard (by omega)
    _ ≤ (C*(Ideal.absNorm I : ℝ)^(ε/(j+1)))^(j+1) :=
      pow_le_pow_left₀ (by positivity) (hb I hI) _
    _ = C ^(j+1)*(Ideal.absNorm I : ℝ)^ε := by
      rw [mul_pow]
      congr 1
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      congr 1
      push_cast
      field_simp

end
end SevenEighths.InverseMoment

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

theorem coordinate_density_weighted_integrable (g : ι → 𝓢(ℝ, ℂ)) (J : ℕ) :
    Integrable (fun t : ι → ℝ => (∏ i, (1 + ‖t i‖)^J) * ‖coordinateDensity g t‖) := by
  have hi (i : ι) := AnalyticBridge.schwartz_fourier_one_plus_integrable (g i) J
  convert (preTransparency := .instances) Integrable.fintype_prod hi using 1
  funext t
  simp only [coordinateDensity, norm_prod, Finset.prod_mul_distrib]

theorem fullProfileDensity_weighted_integrable (g : ι → 𝓢(ℝ, ℂ))
    (b₁ b₂ b₃ : 𝓢(ℝ, ℂ)) (J : ℕ) :
    Integrable (fun p : Frequency × (ι → ℝ) =>
      tripleHeight J p.1 * coordinateHeight J p.2 * ‖fullProfileDensity g b₁ b₂ b₃ p‖) := by
  convert (preTransparency := .instances) (tripleCoefficient_weighted_integrable b₁ b₂ b₃ J).mul_prod
    (coordinate_density_weighted_integrable g J) using 1
  funext p
  simp only [tripleHeight, coordinateHeight, fullProfileDensity, norm_mul]
  ring

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

lemma secondOuterPhase_norm (h y : Fin 6 → ℝ) : ‖secondOuterPhase h y‖ = 1 := by
  simp only [secondOuterPhase,norm_mul,logPhase_norm,mul_one]

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

theorem initialColumn_eq_secondPre (Ψ : O →* ℂ) (j C d h : O)
    (H : Finset ι→ℂ) (S : Finset ι) :
    initialColumn p hp hcop hg Ψ j C d h H S =
      secondPreColumn p hp hcop hg Ψ (j*C) 1 1 d h H S := by
  have hone := ActualEisensteinCubic.finiteSquarefreeRow_one (fun i=>Ideal.span {p i}) hg S
  simp only [initialColumn,secondPreColumn,hone,one_pow,mul_one]

include hp in
omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem sourceIdeal_ne_zero (S : Finset ι) : sourceIdeal p S≠0 :=
  Ideal.span_singleton_eq_bot.not.mpr (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i))

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem sourceIdeal_union (S T : Finset ι) (hst : Disjoint S T) :
    sourceIdeal p (S∪T)=sourceIdeal p S*sourceIdeal p T := by
  simp only [sourceIdeal,Finset.prod_union hst,Ideal.span_singleton_mul_span_singleton]

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem sourceIdeal_dvd (E G : Finset ι) (hEG : E⊆G) : sourceIdeal p E∣sourceIdeal p G := by
  refine ⟨sourceIdeal p (G\E),?_⟩
  rw [←sourceIdeal_union p E (G\E) (by exact Finset.disjoint_left.mpr (fun i hi hj=>(Finset.mem_sdiff.mp hj).2 hi)),
    Finset.union_sdiff_of_subset hEG]

omit [DecidableEq ι] in
theorem source_prime_dvd (S : Finset ι) (i : ι) (hi : i∈S) :
    (sourcePrime p i).val∣sourceIdeal p S := by
  apply Ideal.dvd_iff_le.mpr
  apply Ideal.span_singleton_le_span_singleton.mpr
  exact Finset.dvd_prod_of_mem p hi

include hp in

theorem sourceTuple_valid (hpr : ∀ i,λ₀^2∣p i-1) {J : ℕ}
    (G E V : Finset ι) (h : O) (assigned : Fin J→ι)
    (hEG : E⊆G) (ha : ∀ i,assigned i∈G∪V) :
    InitialSourceValid (sourceTuple p G E V h assigned) := by
  refine ⟨sourceIdeal_ne_zero p hp G,sourceIdeal_ne_zero p hp V,?_,
    sourceIdeal_dvd p E G hEG,?_⟩
  · change primaryGenerator (sourceIdeal p E)≠0
    rw [sourceIdeal_gen p hp hpr E]
    exact Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)
  · intro i
    change (sourcePrime p (assigned i)).val∣sourceIdeal p G*sourceIdeal p V
    rcases Finset.mem_union.mp (ha i) with hi|hi
    · exact dvd_mul_of_dvd_left (source_prime_dvd p G (assigned i) hi) _
    · exact dvd_mul_of_dvd_right (source_prime_dvd p V (assigned i) hi) _

include hp in

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem source_quotient (G E : Finset ι) (hEG : E⊆G) :
    CanonicalQuadraticSieve.idealQuotient (sourceIdeal p E) (sourceIdeal p G)=
      sourceIdeal p (G\E) := by
  apply mul_left_cancel₀ (sourceIdeal_ne_zero p hp E)
  rw [CanonicalQuadraticSieve.idealQuotient_mul (sourceIdeal_dvd p E G hEG)]
  rw [←sourceIdeal_union p E (G\E) (by exact Finset.disjoint_left.mpr (fun i hi hj=>(Finset.mem_sdiff.mp hj).2 hi)),
    Finset.union_sdiff_of_subset hEG]

theorem sourceIdeal_injective (hinj : Function.Injective (fun i=>Ideal.span {p i})) :
    Function.Injective (sourceIdeal p) := by
  intro S T he
  simp only [sourceIdeal,FiniteGaussPhase.span_finset_prod] at he
  exact FirstCauchyArithmetic.family_product_injective _ hinj he

theorem toTuple_injective (hinj : Function.Injective (fun i=>Ideal.span {p i})) {J : ℕ} :
    Function.Injective (toTuple p (J:=J)) := by
  intro x y he
  have hC := congrArg InitialTuple.common he
  have hD := congrArg InitialTuple.divisor he
  have hV := congrArg InitialTuple.residual he
  have hf := congrArg InitialTuple.frequency he
  have ha := congrArg InitialTuple.assigned he
  apply Source.ext
  · exact sourceIdeal_injective p hinj hC
  · exact sourceIdeal_injective p hinj hD
  · exact sourceIdeal_injective p hinj hV
  · exact hf
  · funext i
    apply hinj
    exact congrArg Subtype.val (congrFun ha i)

omit [DecidableEq ι] in
theorem sectorSource_injective {J : ℕ} (u : Oˣ) :
    Function.Injective (sectorSource (J:=J) (ι:=ι) u) := by
  intro x y he
  apply Source.ext
  · simpa only [sectorSource] using congrArg (fun z : Source (ι:=ι) J=>z.common) he
  · simpa only [sectorSource] using congrArg (fun z : Source (ι:=ι) J=>z.divisor) he
  · simpa only [sectorSource] using congrArg (fun z : Source (ι:=ι) J=>z.overlap) he
  · have hh := congrArg Source.frequency he
    exact mul_left_cancel₀ (pow_ne_zero 5 (Units.ne_zero u)) hh
  · simpa only [sectorSource] using congrArg (fun z : Source (ι:=ι) J=>z.assigned) he

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

theorem primeMark_supported_assignments (I : Finset σ) (L : σ → Finset ι)
    (a : σ → ι → ℂ) (A : Finset ι) :
    primeMark I L a A = ∑ q ∈ I.pi (fun i => L i ∩ A), slotAssignmentWeight I a q := by
  simp only [primeMark,primeSlot,Finset.sum_ite_mem,slotAssignmentWeight]
  exact Finset.prod_sum I (fun i => L i ∩ A) a

theorem slotAssignmentWeight_norm_le_one (I : Finset σ) (L : σ → Finset ι)
    (a : σ → ι → ℂ) (A : Finset ι) (q : ∀ i ∈ I, ι)
    (hq : q ∈ I.pi (fun i => L i ∩ A))
    (ha : ∀ i ∈ I, ∀ p ∈ L i, ‖a i p‖ ≤ 1) : ‖slotAssignmentWeight I a q‖ ≤ 1 := by
  rw [slotAssignmentWeight,norm_prod]
  apply Finset.prod_le_one (fun _ _ => norm_nonneg _)
  intro i _
  exact ha i.val i.property _ (Finset.mem_inter.mp (Finset.mem_pi.mp hq i.val i.property)).1

omit [DecidableEq σ] [DecidableEq ι] in
theorem indexedSlotAssignment_injective (I : Finset σ) :
    Function.Injective (indexedSlotAssignment (ι:=ι) I) := by
  intro q r h
  funext i hi
  have he := congrFun h (I.equivFin ⟨i,hi⟩)
  simpa [indexedSlotAssignment] using he

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.SecondAssignedSource
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]

omit [DecidableEq ι] [DecidableEq σ] in
theorem pairedSlotAssignment_injective (J₁ J₂ : Finset σ) :
    Function.Injective (pairedSlotAssignment (ι:=ι) J₁ J₂) := by
  intro q r h
  apply Prod.ext
  · apply indexedSlotAssignment_injective J₁
    funext j
    simpa only [pairedSlotAssignment,Fin.addCases_left] using congrFun h (Fin.castAdd J₂.card j)
  · apply indexedSlotAssignment_injective J₂
    funext j
    simpa only [pairedSlotAssignment,Fin.addCases_right] using congrFun h (Fin.natAdd J₁.card j)

theorem paired_primeMark_assignments (J₁ J₂ : Finset σ)
    (L₁ L₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ) (A : Finset ι) :
    star (primeMark J₁ L₁ a₁ A)*primeMark J₂ L₂ a₂ A =
      ∑ q ∈ (J₁.pi (fun i => L₁ i∩A)) ×ˢ (J₂.pi (fun i => L₂ i∩A)),
        pairedSlotWeight J₁ J₂ a₁ a₂ q := by
  rw [primeMark_supported_assignments,primeMark_supported_assignments]
  simp only [star_sum,Finset.sum_product,pairedSlotWeight,Finset.sum_mul,Finset.mul_sum]
  exact Finset.sum_comm

theorem pairedSlotWeight_norm_le_one (J₁ J₂ : Finset σ)
    (L₁ L₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ) (A : Finset ι)
    (q : (∀ i ∈ J₁, ι) × (∀ i ∈ J₂, ι))
    (hq : q ∈ (J₁.pi (fun i => L₁ i∩A)) ×ˢ (J₂.pi (fun i => L₂ i∩A)))
    (ha₁ : ∀ i ∈ J₁, ∀ p ∈ L₁ i, ‖a₁ i p‖ ≤ 1)
    (ha₂ : ∀ i ∈ J₂, ∀ p ∈ L₂ i, ‖a₂ i p‖ ≤ 1) :
    ‖pairedSlotWeight J₁ J₂ a₁ a₂ q‖ ≤ 1 := by
  rw [pairedSlotWeight,norm_mul,norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    (slotAssignmentWeight_norm_le_one J₁ L₁ a₁ A q.1 (Finset.mem_product.mp hq).1 ha₁)).trans
    (slotAssignmentWeight_norm_le_one J₂ L₂ a₂ A q.2 (Finset.mem_product.mp hq).2 ha₂)

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialProfile
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge JointLogSeparation EisensteinSchwartzPoisson
open SevenEighths.InverseMoment

namespace SevenEighths.InverseInitialProfile

theorem familyDensity_weighted_integrable
    (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ))
    (c₁ c₂ θ₁ θ₂ L : ℝ) (J : ℕ) :
    Integrable (fun p : Frequency × (Fin 6 → ℝ) =>
      tripleHeight J p.1 * coordinateHeight J p.2 *
        ‖familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ L p‖) := by
  convert (preTransparency := .instances) (InverseMoment.fullProfileDensity_weighted_integrable g
    (𝓕 (clippedTwist g₁ c₁ θ₁)) (𝓕 (clippedTwist g₂ c₂ θ₂)) b₃ J).const_mul
      (Real.exp (-3*L)) using 1
  funext p
  simp only [familyDensity, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  ring

end SevenEighths.InverseInitialProfile

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialClippedColumns
namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge JointLogSeparation
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open SevenEighths.InverseMoment
namespace SevenEighths.InverseInitialClippedColumns
local notation "Eis" => ActualEisensteinCubic.O

section Arithmetic
variable {ι σ : Type*} [DecidableEq ι]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem columnEnergy_normalization
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis) (D : Ideal Eis → ℝ)
    (W : ℝ → ℂ) (X : ℝ) {Z : ℝ} (hZ : 0 < Z) (F : ℝ) :
    columnEnergy p hp hcop hg pool Ψ m slots lists a labels rows D W X =
      Z^F * normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a
        labels rows D W X Z F := by
  have hr : Z^F * (Z^(-F/2))^2 = 1 := by
    rw [← Real.rpow_mul_natCast hZ.le, ← Real.rpow_add hZ]
    rw [show F+(-F/2)*(2:ℕ) = 0 by ring, Real.rpow_zero]
  unfold columnEnergy normalizedColumnEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro f hf
  rw [← mul_assoc, mul_comm (Z^F) (D f), mul_assoc]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hZ _),mul_pow,← mul_assoc,hr,one_mul]

end Arithmetic

end SevenEighths.InverseInitialClippedColumns

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialQuotientGeometry
namespace OAI

noncomputable section
open scoped BigOperators Classical
open ActualEisensteinCubic IdealMobiusDivisorSum CompletedGauss CanonicalQuadraticSieve
open SevenEighths.InverseMoment SevenEighths.InverseInitialArithmetic
namespace SevenEighths.InverseInitialQuotientGeometry

local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι : Type*} [DecidableEq ι] (p : ι → Eis)

variable (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]

include hp in
omit [∀ i, (Ideal.span {p i}).IsMaximal] in
theorem quotientSet_nonzero {J : ℕ} (S : Finset (Source (ι:=ι) J)) :
    ∀ t ∈ quotientSet p S, t ≠ 0 := by
  intro t ht
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ht
  exact sourceIdeal_ne_zero p hp _

include hp in

theorem quotientSet_eq_initial {J : ℕ} (S : Finset (Source (ι:=ι) J))
    (u : Eisˣ) (hdiv : ∀ x ∈ S, x.divisor ⊆ x.common) :
    initialQuotientSet (S.image (fun x => toTuple p (sectorSource u x))) = quotientSet p S := by
  rw [initialQuotientSet, Finset.image_image]
  apply Finset.image_congr
  intro x hx
  change idealQuotient (sourceIdeal p x.divisor) (sourceIdeal p x.common) = _
  exact source_quotient p hp x.common x.divisor (hdiv x hx)

theorem normalized_mass_bound (J : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : Finset (Ideal Eis)) (H : ℝ), 0 < H →
      (∀ t ∈ T, t ≠ 0) → (∀ t ∈ T, (Ideal.absNorm t : ℝ) ≤ H) →
      normalizedMass J T H ≤ C*H^ε := by
  obtain ⟨C,hC,hb⟩ := ideal_divisor_power_small J ε hε
  refine ⟨128*C,by positivity,?_⟩
  intro T H hH hz hn
  rcases T.eq_empty_or_nonempty with he|⟨t,ht⟩
  · subst T
    simp only [normalizedMass,Finset.sum_empty,mul_zero]
    positivity
  have hH1 : 1 ≤ H := by
    have ht1 : (1:ℝ) ≤ Ideal.absNorm t := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (hz t ht))
    exact ht1.trans (hn t ht)
  have hw : ∀ t ∈ T, ((idealDivisors t).card : ℝ)^J ≤ C*H^ε := by
    intro t ht
    exact (hb t (hz t ht)).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) (hn t ht) hε.le) hC.le)
  have hs : (∑ t ∈ T, ((idealDivisors t).card : ℝ)^J) ≤ (128*H)*(C*H^ε) := by
    calc
      _ ≤ ∑ _t ∈ T, C*H^ε := Finset.sum_le_sum hw
      _ = (T.card:ℝ)*(C*H^ε) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (DescentFiberCost.finite_ideal_count_real T H hH1 hz hn) (by positivity)
  apply (mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hH.le)).trans_eq
  field_simp

end SevenEighths.InverseInitialQuotientGeometry

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerCanonical
namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss IdealMobiusDivisorSum
open SevenEighths.InverseMoment SevenEighths.InverseInitialArithmetic
open SevenEighths.InverseInitialQuotientGeometry SevenEighths.InverseInitialClippedColumns
namespace SevenEighths.InverseInitialEnergyCallerCanonical
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i≠0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

omit [DecidableEq σ] in
theorem energy_eq_normalized (pool : Finset ι) (Ψ : Eis →* ℂ) (j : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (W : ℝ → ℂ) (X : ℝ) (J : ℕ) (T : Finset (Ideal Eis))
    (labels : Finset (Ideal Eis)) (rows : Finset Eis)
    {Z : ℝ} (hZ : 0<Z) (F : ℝ) :
    (∑ t ∈ T, ((idealDivisors t).card:ℝ)^J *
      ∑ f ∈ labels, ((idealDivisors f).card:ℝ)^(J+1) *
        ∑ k ∈ rows, ‖child p hp hcop hg pool Ψ j slots lists a W X (t,f,k)‖^2) =
    Z^F * ∑ t ∈ T, ((idealDivisors t).card:ℝ)^J *
      normalizedColumnEnergy p hp hcop hg pool Ψ (j*primaryGenerator t)
        slots lists a labels rows (fun f=>((idealDivisors f).card:ℝ)^(J+1)) W X Z F := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  change ((idealDivisors t).card:ℝ)^J *
    columnEnergy p hp hcop hg pool Ψ (j*primaryGenerator t) slots lists a
      labels rows (fun f=>((idealDivisors f).card:ℝ)^(J+1)) W X = _
  rw [columnEnergy_normalization p hp hcop hg pool Ψ (j*primaryGenerator t)
    slots lists a labels rows _ W X hZ F]
  ring

omit [DecidableEq σ] in
theorem energy_le_moment (pool : Finset ι) (Ψ : Eis →* ℂ) (j : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (W : ℝ → ℂ) (X : ℝ) (J : ℕ) (T : Finset (Ideal Eis))
    (labels : Finset (Ideal Eis)) (rows : Finset Eis)
    {Z : ℝ} (hZ : 0<Z) (F B : ℝ)
    (hmoment : ∀ t ∈ T,
      normalizedColumnEnergy p hp hcop hg pool Ψ (j*primaryGenerator t)
        slots lists a labels rows (fun f=>((idealDivisors f).card:ℝ)^(J+1)) W X Z F ≤ B) :
    (∑ t ∈ T, ((idealDivisors t).card:ℝ)^J *
      ∑ f ∈ labels, ((idealDivisors f).card:ℝ)^(J+1) *
        ∑ k ∈ rows, ‖child p hp hcop hg pool Ψ j slots lists a W X (t,f,k)‖^2) ≤
    (Z^F * ∑ t ∈ T, ((idealDivisors t).card:ℝ)^J) * B := by
  rw [energy_eq_normalized p hp hcop hg pool Ψ j slots lists a W X J T labels rows hZ F,
    mul_assoc, Finset.sum_mul]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hZ.le _)
  exact Finset.sum_le_sum fun t ht =>
    mul_le_mul_of_nonneg_left (hmoment t ht) (by positivity)

theorem sqrt_pair_mass (M B₁ B₂ : ℝ) (hM : 0≤M) :
    Real.sqrt (M*B₁)*Real.sqrt (M*B₂) = M*(Real.sqrt B₁*Real.sqrt B₂) := by
  rw [Real.sqrt_mul hM,Real.sqrt_mul hM]
  calc
    _ = (Real.sqrt M*Real.sqrt M)*(Real.sqrt B₁*Real.sqrt B₂) := by ring
    _ = _ := by rw [Real.mul_self_sqrt hM]

end SevenEighths.InverseInitialEnergyCallerCanonical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerOpposite
namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss IdealMobiusDivisorSum
open SevenEighths.InverseMoment SevenEighths.InverseInitialArithmetic
open SevenEighths.InverseInitialQuotientGeometry SevenEighths.InverseInitialClippedColumns
open SevenEighths.InverseInitialEnergyCallerCanonical
namespace SevenEighths.InverseInitialEnergyCallerOpposite
local notation "Eis" => ActualEisensteinCubic.O

theorem energy_neg_rows (T labels : Finset (Ideal Eis)) (rows : Finset Eis)
    (hneg : ∀ k∈rows,-k∈rows) (J : ℕ) (F : InitialChild→ℂ) :
    (∑ t∈T,((idealDivisors t).card:ℝ)^J *
      ∑ f∈labels,((idealDivisors f).card:ℝ)^(J+1) *
        ∑ k∈rows,‖F (negativeChild (t,f,k))‖^2) =
    ∑ t∈T,((idealDivisors t).card:ℝ)^J *
      ∑ f∈labels,((idealDivisors f).card:ℝ)^(J+1) *
        ∑ k∈rows,‖F (t,f,k)‖^2 := by
  apply Finset.sum_congr rfl
  intro t ht
  congr 1
  apply Finset.sum_congr rfl
  intro f hf
  congr 1
  apply Finset.sum_bij (fun k _=>-k)
  · exact hneg
  · intro a ha b hb he
    exact neg_injective he
  · intro b hb
    exact ⟨-b,hneg b hb,neg_neg b⟩
  · intro k hk
    rfl

variable {ι σ : Type*} [DecidableEq ι]
  (p : ι → Eis) (hp : ∀ i, p i≠0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

end SevenEighths.InverseInitialEnergyCallerOpposite

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerAssigned
namespace OAI

noncomputable section

open scoped BigOperators Classical
open SevenEighths.InverseMoment SevenEighths.InverseInitialArithmetic
namespace SevenEighths.InverseInitialEnergyCallerAssigned
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]

omit [DecidableEq ι] in
theorem attach_injective {J : ℕ} :
    Function.Injective (fun z : Source (ι:=ι) 0 × (Fin J→ι) => attach z.1 z.2) := by
  intro x y h
  apply Prod.ext
  · simpa only [erase_attach] using congrArg erase h
  · exact congrArg Source.assigned h

omit [DecidableEq ι] [DecidableEq σ] in
theorem attachPair_injective (J₁ J₂ : Finset σ) :
    Function.Injective (attachPair (ι:=ι) J₁ J₂) := by
  intro x y h
  have he := @attach_injective ι (J₁.card + J₂.card)
    (x.1,pairedSlotAssignment J₁ J₂ x.2) (y.1,pairedSlotAssignment J₁ J₂ y.2) h
  exact Prod.ext (congrArg (fun z : Source (ι:=ι) 0 × (Fin (J₁.card+J₂.card)→ι)=>z.1) he)
    (pairedSlotAssignment_injective J₁ J₂
      (congrArg (fun z : Source (ι:=ι) 0 × (Fin (J₁.card+J₂.card)→ι)=>z.2) he))

omit [DecidableEq ι] [DecidableEq σ] in
@[simp] theorem coefficient_attach (J₁ J₂ : Finset σ) (a₁ a₂ : σ→ι→ℂ)
    (x : Source (ι:=ι) 0) (q : (∀ i∈J₁,ι) × (∀ i∈J₂,ι)) :
    coefficient J₁ J₂ a₁ a₂ (attachPair J₁ J₂ (x,q)) = pairedSlotWeight J₁ J₂ a₁ a₂ q := by
  simp only [coefficient,attachPair,attach,pairedSlotAssignment,
    Fin.addCases_left,Fin.addCases_right,indexedSlotAssignment_apply,pairedSlotWeight]

theorem assignedSource_sum (S : Finset (Source (ι:=ι) 0)) (J₁ J₂ : Finset σ)
    (L₁ L₂ : σ→Finset ι) (F : Source (ι:=ι) (J₁.card+J₂.card)→ℂ) :
    ∑ x∈assignedSource S J₁ J₂ L₁ L₂,F x =
      ∑ y∈S,∑ q∈(J₁.pi (fun i=>L₁ i∩(y.common∪y.overlap))) ×ˢ
        (J₂.pi (fun i=>L₂ i∩(y.common∪y.overlap))),F (attachPair J₁ J₂ (y,q)) := by
  rw [assignedSource,Finset.sum_image (fun x _ y _ he=>attachPair_injective J₁ J₂ he),
    Finset.sum_filter,Finset.sum_product]
  apply Finset.sum_congr rfl
  intro y hy
  rw [←Finset.sum_filter]
  dsimp only
  rw [paired_assignment_filter]

theorem original_marks_eq_assigned (S : Finset (Source (ι:=ι) 0))
    (J₁ J₂ : Finset σ) (L₁ L₂ : σ→Finset ι) (a₁ a₂ : σ→ι→ℂ)
    (w P : Source (ι:=ι) 0→ℂ) :
    (∑ y∈S,w y*(star (primeMark J₁ L₁ a₁ (y.common∪y.overlap))*
      primeMark J₂ L₂ a₂ (y.common∪y.overlap))*P y) =
    ∑ x∈assignedSource S J₁ J₂ L₁ L₂,
      (w (erase x)*coefficient J₁ J₂ a₁ a₂ x)*P (erase x) := by
  rw [assignedSource_sum]
  apply Finset.sum_congr rfl
  intro y hy
  rw [paired_primeMark_assignments]
  simp only [Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro q hq
  rw [coefficient_attach]
  simp only [attachPair,erase_attach]

theorem assignedSource_support (S : Finset (Source (ι:=ι) 0))
    (J₁ J₂ : Finset σ) (L₁ L₂ : σ→Finset ι)
    (hdiv : ∀ x∈S,x.divisor⊆x.common)
    {x : Source (ι:=ι) (J₁.card+J₂.card)} (hx : x∈assignedSource S J₁ J₂ L₁ L₂) :
    erase x∈S ∧ x.divisor⊆x.common ∧ ∀ i,x.assigned i∈x.common∪x.overlap := by
  obtain ⟨⟨y,q⟩,hy,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨hmem,hq⟩ := Finset.mem_filter.mp hy
  have hyS := (Finset.mem_product.mp hmem).1
  exact ⟨by simpa only [attachPair,erase_attach] using hyS,hdiv y hyS,hq⟩

theorem coefficient_norm_le_one (S : Finset (Source (ι:=ι) 0))
    (J₁ J₂ : Finset σ) (L₁ L₂ : σ→Finset ι) (a₁ a₂ : σ→ι→ℂ)
    (ha₁ : ∀ i∈J₁,∀ q∈L₁ i,‖a₁ i q‖≤1)
    (ha₂ : ∀ i∈J₂,∀ q∈L₂ i,‖a₂ i q‖≤1)
    {x : Source (ι:=ι) (J₁.card+J₂.card)} (hx : x∈assignedSource S J₁ J₂ L₁ L₂) :
    ‖coefficient J₁ J₂ a₁ a₂ x‖≤1 := by
  obtain ⟨⟨y,q⟩,hy,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨hmem,hq⟩ := Finset.mem_filter.mp hy
  have hq' : q∈(J₁.pi L₁ ×ˢ J₂.pi L₂).filter
      (fun q=>∀ i,pairedSlotAssignment J₁ J₂ q i∈y.common∪y.overlap) :=
    Finset.mem_filter.mpr ⟨(Finset.mem_product.mp hmem).2,hq⟩
  rw [paired_assignment_filter] at hq'
  rw [coefficient_attach]
  exact pairedSlotWeight_norm_le_one J₁ J₂ L₁ L₂ a₁ a₂ _ q hq' ha₁ ha₂

end SevenEighths.InverseInitialEnergyCallerAssigned

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerSupport
namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss IdealMobiusDivisorSum
open SevenEighths.InverseMoment SevenEighths.InverseInitialArithmetic
open SevenEighths.InverseInitialQuotientGeometry SevenEighths.InverseInitialClippedColumns
namespace SevenEighths.InverseInitialEnergyCallerSupport
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι] (p : ι → Eis)
  (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]

include hp in

theorem actual_sector_energy {J : ℕ}
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (S : Finset (Source (ι:=ι) J)) (u : Eisˣ)
    (hdiv : ∀ x ∈ S, x.divisor ⊆ x.common)
    (hsupport : ∀ x ∈ S, ∀i,x.assigned i∈x.common∪x.overlap)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis)
    (hlabels : ∀ f ∈ labels, f ≠ 0)
    (hchild : ∀ x ∈ S,
      (initialChild (toTuple p (sectorSource u x))).2.1 ∈ labels ∧
      (initialChild (toTuple p (sectorSource u x))).2.2 ∈ rows)
    (F : InitialChild → ℂ) :
    (∑ x ∈ S, ‖F (initialChild (toTuple p (sectorSource u x)))‖^2) ≤
      ∑ t ∈ quotientSet p S, ((idealDivisors t).card : ℝ)^J *
        ∑ f ∈ labels, ((idealDivisors f).card : ℝ)^(J+1) *
          ∑ k ∈ rows, ‖F (t,f,k)‖^2 := by
  let T := S.image (fun x => toTuple p (sectorSource u x))
  have hvalid : ∀ y ∈ T, InitialSourceValid y := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    exact sourceTuple_valid p hp hpr x.common x.divisor x.overlap
      ((u:Eis)^5*x.frequency) x.assigned (hdiv x hx) (hsupport x hx)
  have hc : ∀ y ∈ T, (initialChild y).2.1 ∈ labels ∧ (initialChild y).2.2 ∈ rows := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    exact hchild x hx
  have he := initial_energy_projection T hvalid labels rows hlabels hc
    (fun _ => 1) (fun _ _ => le_rfl) F
  simp only [one_mul] at he
  rw [show initialQuotientSet T = quotientSet p S from
    quotientSet_eq_initial p hp S u hdiv] at he
  have hs : (∑ y ∈ T, ‖F (initialChild y)‖^2) =
      ∑ x ∈ S, ‖F (initialChild (toTuple p (sectorSource u x)))‖^2 := by
    exact Finset.sum_image (fun x _ y _ he => sectorSource_injective u (toTuple_injective p hinj he))
  rw [hs] at he
  exact he

include hp in

theorem actual_sector_signed_pair {J : ℕ}
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (S : Finset (Source (ι:=ι) J)) (u : Eisˣ)
    (hdiv : ∀ x ∈ S, x.divisor ⊆ x.common)
    (hsupport : ∀ x ∈ S, ∀i,x.assigned i∈x.common∪x.overlap)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis)
    (hlabels : ∀ f ∈ labels, f ≠ 0)
    (hchild : ∀ x ∈ S,
      (initialChild (toTuple p (sectorSource u x))).2.1 ∈ labels ∧
      (initialChild (toTuple p (sectorSource u x))).2.2 ∈ rows)
    (c : Source (ι:=ι) J → ℂ) (A : ℝ) (hA : 0 ≤ A)
    (hc : ∀ x ∈ S, ‖c x‖ ≤ A) (F G : InitialChild → ℂ) :
    ‖∑ x ∈ S, c x * star (F (initialChild (toTuple p (sectorSource u x)))) *
        G (initialChild (toTuple p (sectorSource u x)))‖ ≤
      A * (Real.sqrt (∑ t ∈ quotientSet p S, ((idealDivisors t).card : ℝ)^J *
        ∑ f ∈ labels, ((idealDivisors f).card : ℝ)^(J+1) * ∑ k ∈ rows, ‖F (t,f,k)‖^2) *
        Real.sqrt (∑ t ∈ quotientSet p S, ((idealDivisors t).card : ℝ)^J *
        ∑ f ∈ labels, ((idealDivisors f).card : ℝ)^(J+1) * ∑ k ∈ rows, ‖G (t,f,k)‖^2)) := by
  let child := fun x : Source (ι:=ι) J => initialChild (toTuple p (sectorSource u x))
  have hF := actual_sector_energy p hp hinj hpr S u hdiv hsupport labels rows hlabels hchild F
  have hG := actual_sector_energy p hp hinj hpr S u hdiv hsupport labels rows hlabels hchild G
  calc
    _ ≤ ∑ x ∈ S, ‖c x * star (F (child x)) * G (child x)‖ := norm_sum_le _ _
    _ ≤ ∑ x ∈ S, A * (‖F (child x)‖ * ‖G (child x)‖) := by
      apply Finset.sum_le_sum
      intro x hx
      simp only [norm_mul, norm_star]
      nlinarith [mul_le_mul_of_nonneg_right (hc x hx)
        (mul_nonneg (norm_nonneg (F (child x))) (norm_nonneg (G (child x))))]
    _ = A * ∑ x ∈ S, ‖F (child x)‖ * ‖G (child x)‖ := by rw [Finset.mul_sum]
    _ ≤ A * (Real.sqrt (∑ x ∈ S, ‖F (child x)‖^2) *
        Real.sqrt (∑ x ∈ S, ‖G (child x)‖^2)) :=
      mul_le_mul_of_nonneg_left (Real.sum_mul_le_sqrt_mul_sqrt S _ _) hA
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (mul_le_mul (Real.sqrt_le_sqrt hF) (Real.sqrt_le_sqrt hG)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hA

end SevenEighths.InverseInitialEnergyCallerSupport

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerAssignedPair
namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss IdealMobiusDivisorSum
namespace SevenEighths.InverseInitialEnergyCallerAssignedPair
open InverseMoment InverseInitialArithmetic InverseInitialQuotientGeometry
open InverseInitialEnergyCallerAssigned InverseInitialEnergyCallerOpposite
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
  (p:ι→Eis)(hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]

omit [DecidableEq ι] in
theorem child_erase {J:ℕ}(u:Eisˣ)(x:Source (ι:=ι) J) :
    initialChild (toTuple p (sectorSource u (erase x)))=
      initialChild (toTuple p (sectorSource u x)) := rfl

include hp in

theorem original_assigned_pair
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (S:Finset (Source (ι:=ι) 0))(u:Eisˣ)
    (J₁ J₂:Finset σ)(L₁ L₂:σ→Finset ι)(a₁ a₂:σ→ι→ℂ)
    (ha₁:∀i∈J₁,∀q∈L₁ i,‖a₁ i q‖≤1)
    (ha₂:∀i∈J₂,∀q∈L₂ i,‖a₂ i q‖≤1)
    (hdiv:∀x∈S,x.divisor⊆x.common)
    (labels:Finset (Ideal Eis))(rows:Finset Eis)
    (hlabels:∀f∈labels,f≠0)
    (hchild:∀x∈S,(initialChild (toTuple p (sectorSource u x))).2.1∈labels ∧
      (initialChild (toTuple p (sectorSource u x))).2.2∈rows)
    (c:Source (ι:=ι) 0→ℂ)(A:ℝ)(hA:0≤A)(hc:∀x∈S,‖c x‖≤A)
    (F G:InitialChild→ℂ) :
    ‖∑x∈S,c x*(star (primeMark J₁ L₁ a₁ (x.common∪x.overlap))*
      primeMark J₂ L₂ a₂ (x.common∪x.overlap))*
      (star (F (initialChild (toTuple p (sectorSource u x))))*
        G (initialChild (toTuple p (sectorSource u x))))‖≤
      A*(Real.sqrt (∑t∈quotientSet p (assignedSource S J₁ J₂ L₁ L₂),
        ((idealDivisors t).card:ℝ)^(J₁.card+J₂.card)*
        ∑f∈labels,((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1)*
          ∑k∈rows,‖F (t,f,k)‖^2)*
        Real.sqrt (∑t∈quotientSet p (assignedSource S J₁ J₂ L₁ L₂),
        ((idealDivisors t).card:ℝ)^(J₁.card+J₂.card)*
        ∑f∈labels,((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1)*
          ∑k∈rows,‖G (t,f,k)‖^2)) := by
  let T := assignedSource S J₁ J₂ L₁ L₂
  have hs (x:Source (ι:=ι) (J₁.card+J₂.card))(hx:x∈T) :=
    assignedSource_support S J₁ J₂ L₁ L₂ hdiv hx
  have hcoeff (x:Source (ι:=ι) (J₁.card+J₂.card))(hx:x∈T) :
      ‖c (erase x)*coefficient J₁ J₂ a₁ a₂ x‖≤A := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left
      (coefficient_norm_le_one S J₁ J₂ L₁ L₂ a₁ a₂ ha₁ ha₂ hx)
      (norm_nonneg _)).trans (by simpa only [mul_one] using hc (erase x) (hs x hx).1)
  rw [original_marks_eq_assigned S J₁ J₂ L₁ L₂ a₁ a₂ c
    (fun x=>star (F (initialChild (toTuple p (sectorSource u x))))*
      G (initialChild (toTuple p (sectorSource u x))))]
  simp only [child_erase,←mul_assoc]
  simpa only [←mul_assoc] using InverseInitialEnergyCallerSupport.actual_sector_signed_pair p hp hinj hpr T u
    (fun x hx=>(hs x hx).2.1) (fun x hx=>(hs x hx).2.2) labels rows hlabels
    (fun x hx=>by simpa only [child_erase] using hchild (erase x) (hs x hx).1)
    (fun x=>c (erase x)*coefficient J₁ J₂ a₁ a₂ x) A hA hcoeff F G

end SevenEighths.InverseInitialEnergyCallerAssignedPair

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerAssignedCanonical
namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss IdealMobiusDivisorSum
namespace SevenEighths.InverseInitialEnergyCallerAssignedCanonical
open InverseMoment InverseInitialArithmetic InverseInitialQuotientGeometry
open InverseInitialEnergyCallerAssigned InverseInitialEnergyCallerOpposite
open InverseInitialEnergyCallerCanonical InverseInitialClippedColumns
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
  (p:ι→Eis)(hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem original_assigned_canonical_pair
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (S:Finset (Source (ι:=ι) 0))(u:Eisˣ)
    (J₁ J₂:Finset σ)(L₁ L₂:σ→Finset ι)(a₁ a₂:σ→ι→ℂ)
    (ha₁:∀i∈J₁,∀q∈L₁ i,‖a₁ i q‖≤1)
    (ha₂:∀i∈J₂,∀q∈L₂ i,‖a₂ i q‖≤1)
    (hdiv:∀x∈S,x.divisor⊆x.common)
    (labels:Finset (Ideal Eis))(rows:Finset Eis)
    (hlabels:∀f∈labels,f≠0)(hneg:∀k∈rows,-k∈rows)
    (hchild:∀x∈S,(initialChild (toTuple p (sectorSource u x))).2.1∈labels ∧
      (initialChild (toTuple p (sectorSource u x))).2.2∈rows)
    (c:Source (ι:=ι) 0→ℂ)(A:ℝ)(hA:0≤A)(hc:∀x∈S,‖c x‖≤A)
    (pool:Finset ι)(Ψ₁ Ψ₂:Eis→*ℂ)(j:Eis)(slots₁ slots₂:Finset σ)
    (W₁ W₂:ℝ→ℂ)(X₁ X₂:ℝ){Z:ℝ}(hZ:0<Z)(F B₁ B₂:ℝ)
    (hmoment₁:∀t∈quotientSet p (assignedSource S J₁ J₂ L₁ L₂),
      normalizedColumnEnergy p hp hcop hg pool Ψ₁ (j*primaryGenerator t)
        slots₁ L₁ a₁ labels rows (fun f=>((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1))
        W₁ X₁ Z F≤B₁)
    (hmoment₂:∀t∈quotientSet p (assignedSource S J₁ J₂ L₁ L₂),
      normalizedColumnEnergy p hp hcop hg pool Ψ₂ (j*primaryGenerator t)
        slots₂ L₂ a₂ labels rows (fun f=>((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1))
        W₂ X₂ Z F≤B₂) :
    ‖∑x∈S,c x*(star (primeMark J₁ L₁ a₁ (x.common∪x.overlap))*
      primeMark J₂ L₂ a₂ (x.common∪x.overlap))*
      (star (child p hp hcop hg pool Ψ₁ j slots₁ L₁ a₁ W₁ X₁
          (initialChild (toTuple p (sectorSource u x))))*
        child p hp hcop hg pool Ψ₂ j slots₂ L₂ a₂ W₂ X₂
          (negativeChild (initialChild (toTuple p (sectorSource u x)))))‖≤
      A*(Z^F*∑t∈quotientSet p (assignedSource S J₁ J₂ L₁ L₂),
        ((idealDivisors t).card:ℝ)^(J₁.card+J₂.card))*(Real.sqrt B₁*Real.sqrt B₂) := by
  let T := quotientSet p (assignedSource S J₁ J₂ L₁ L₂)
  let f := child p hp hcop hg pool Ψ₁ j slots₁ L₁ a₁ W₁ X₁
  let g := child p hp hcop hg pool Ψ₂ j slots₂ L₂ a₂ W₂ X₂
  have h₁ := energy_le_moment p hp hcop hg pool Ψ₁ j slots₁ L₁ a₁ W₁ X₁
    (J₁.card+J₂.card) T labels rows hZ F B₁ hmoment₁
  have h₂ := energy_le_moment p hp hcop hg pool Ψ₂ j slots₂ L₂ a₂ W₂ X₂
    (J₁.card+J₂.card) T labels rows hZ F B₂ hmoment₂
  rw [←energy_neg_rows T labels rows hneg (J₁.card+J₂.card) g] at h₂
  have hh := InverseInitialEnergyCallerAssignedPair.original_assigned_pair p hp hinj hpr
    S u J₁ J₂ L₁ L₂ a₁ a₂ ha₁ ha₂ hdiv labels rows hlabels hchild c A hA hc f
    (fun k=>g (negativeChild k))
  apply hh.trans
  calc
    _≤A*(Real.sqrt ((Z^F*∑t∈T,((idealDivisors t).card:ℝ)^(J₁.card+J₂.card))*B₁)*
      Real.sqrt ((Z^F*∑t∈T,((idealDivisors t).card:ℝ)^(J₁.card+J₂.card))*B₂)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul (Real.sqrt_le_sqrt h₁)
        (Real.sqrt_le_sqrt h₂) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hA
    _=_ := by
      rw [sqrt_pair_mass _ B₁ B₂ (mul_nonneg (Real.rpow_nonneg hZ.le _)
        (Finset.sum_nonneg fun t ht=>by positivity))]
      ring

end SevenEighths.InverseInitialEnergyCallerAssignedCanonical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerWeights
namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels FirstCauchyArithmetic SecondPassArithmetic
open SevenEighths.InverseInitialArithmetic SevenEighths.InverseInitialRayAttachment
open SevenEighths.InverseInitialPhysicalMeasure
namespace SevenEighths.InverseInitialEnergyCallerWeights
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι → Eis) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem initialColumn_norm_le
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i})≠2)
    (Ψ : Eis →* ℂ) (j C d h : Eis) (V : Finset ι) :
    ‖initialColumn p hp hcop hg Ψ j C d h (fun _=>1) V‖ ≤ ‖Ψ (∏ i∈V,p i)‖ := by
  rw [initialColumn_eq_secondPre]
  exact secondPreColumn_norm_le p hp hcop hg hc Ψ (j*C) 1 1 d h V

omit hp hcop hg in
omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem initialBeta_norm_le_one (Ψ : Eis →* ℂ) (hΨ : ∀ n, ‖Ψ n‖≤1)
    (j : Eis) (G : Finset ι) : ‖initialBeta p Ψ j G‖≤1 := by
  have hm : ‖rowCoprimeMask (fun i=>Ideal.span {p i}) G j‖≤1 := by
    unfold rowCoprimeMask
    split_ifs <;> norm_num
  have h := (mul_le_of_le_one_left (norm_nonneg _) (hΨ (∏ i∈G,p i))).trans hm
  simp only [initialBeta,Complex.norm_real,Real.norm_eq_abs]
  rw [abs_of_nonneg (sq_nonneg _),norm_mul]
  nlinarith [mul_nonneg (norm_nonneg (Ψ (∏ i∈G,p i)))
    (norm_nonneg (rowCoprimeMask (fun i=>Ideal.span {p i}) G j))]

theorem outerCoefficient_norm_le
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i})≠2)
    (Ψ : Eis →* ℂ) (hΨ : ∀ n, ‖Ψ n‖≤1)
    (j : Eis) (x : Point ι) (ρ : SecondRayIndex) :
    ‖outerCoefficient p hp hcop hg Ψ j x ρ‖ ≤ ‖secondRayCoefficient ρ‖ := by
  have hβ := initialBeta_norm_le_one p Ψ hΨ j x.common
  have hμ := QuadraticInitialBound.norm_ideal_moebius_le_one (sourceIdeal p x.divisor)
  have hV : ‖supportMobius (fun i=>Ideal.span {p i}) x.overlap‖≤1 :=
    QuadraticInitialBound.norm_ideal_moebius_le_one _
  have hL := (initialColumn_norm_le p hp hcop hg hc (secondRayMinus Ψ ρ)
    j (∏ i∈x.common,p i) (divisor p x) x.frequency x.overlap).trans
      ((secondRayMinus_norm_le Ψ ρ _).trans (hΨ _))
  have hR := (initialColumn_norm_le p hp hcop hg hc (secondRayPlus Ψ ρ)
    j (∏ i∈x.common,p i) (divisor p x) (-x.frequency) x.overlap).trans
      ((secondRayPlus_norm_le Ψ ρ _).trans (hΨ _))
  simp only [outerCoefficient,norm_mul,norm_star]
  calc
    _ ≤ 1*1*1*‖secondRayCoefficient ρ‖*1*1 := by
      gcongr
    _ = _ := by ring

end SevenEighths.InverseInitialEnergyCallerWeights

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerSector
namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
namespace SevenEighths.InverseInitialEnergyCallerSector
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialKernelBridge
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerCanonical InverseInitialEnergyCallerOpposite InverseInitialProfile
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
  (p:ι→Eis)(hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem markedModeColumn_sector
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (x:Source (ι:=ι) 0)(hdiv:x.divisor⊆x.common)(u:Eisˣ)
    (hu:unitSector p hp hpr (sourcePoint x ∅ ∅)=u)
    (pool:Finset ι)(Ψ:Eis→*ℂ)(j:Eis)(slots:Finset σ)
    (lists:σ→Finset ι)(a:σ→ι→ℂ)(W:ℝ→ℂ)(Z D B v:ℝ) :
    markedModeColumn p hp hcop hg hpr pool Ψ j x.frequency x slots lists a W Z D B v=
      ∑J∈slots.powerset,primeMark J lists a (x.common∪x.overlap)*
        child p hp hcop hg pool Ψ j (slots\J) lists a W (Z^(columnCenter D B v))
          (initialChild (toTuple p (sectorSource u x))) := by
  unfold markedModeColumn
  rw [hu]
  apply Finset.sum_congr rfl
  intro J hJ
  simp only [child,initialChild,toTuple,sectorSource,sourceTuple]
  rw [source_quotient p hp x.common x.divisor hdiv]
  rfl

theorem markedModeColumn_negative_sector
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (x:Source (ι:=ι) 0)(hdiv:x.divisor⊆x.common)(u:Eisˣ)
    (hu:unitSector p hp hpr (sourcePoint x ∅ ∅)=u)
    (pool:Finset ι)(Ψ:Eis→*ℂ)(j:Eis)(slots:Finset σ)
    (lists:σ→Finset ι)(a:σ→ι→ℂ)(W:ℝ→ℂ)(Z D B v:ℝ) :
    markedModeColumn p hp hcop hg hpr pool Ψ j (-x.frequency) x slots lists a W Z D B v=
      ∑J∈slots.powerset,primeMark J lists a (x.common∪x.overlap)*
        child p hp hcop hg pool Ψ j (slots\J) lists a W (Z^(columnCenter D B v))
          (negativeChild (initialChild (toTuple p (sectorSource u x)))) := by
  unfold markedModeColumn
  rw [hu]
  apply Finset.sum_congr rfl
  intro J hJ
  simp only [child,negativeChild,initialChild,toTuple,sectorSource,sourceTuple]
  rw [source_quotient p hp x.common x.divisor hdiv]
  simp only [quotient,sourcePoint,mul_neg]

end SevenEighths.InverseInitialEnergyCallerSector

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerAllocation
namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
namespace SevenEighths.InverseInitialEnergyCallerAllocation
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialKernelBridge
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerCanonical InverseInitialEnergyCallerOpposite InverseInitialProfile
open InverseInitialEnergyCallerSector
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
  (p:ι→Eis)(hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem rowMode_eq_allocations
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (x:Source (ι:=ι) 0)(hdiv:x.divisor⊆x.common)(u:Eisˣ)
    (hu:unitSector p hp hpr (sourcePoint x ∅ ∅)=u)
    (pool:Finset ι)(Ψ:Eis→*ℂ)(j:Eis)(slots:Finset σ)
    (lists:σ→Finset ι)(a:σ→ι→ℂ)(ω₁ ω₂:ℝ→ℂ)(Z D B v θ H:ℝ)
    (ρ:SecondRayIndex)(z:JointLogSeparation.Frequency×(Fin 6→ℝ)) :
    rowMode p hp hcop hg hpr pool Ψ j slots lists a ω₁ ω₂ Z D B v θ H x ρ z=
      ∑J₁∈slots.powerset,∑J₂∈slots.powerset,
        allocatedMode p hp hcop hg u pool Ψ j slots J₁ J₂ lists a ω₁ ω₂
          Z D B v θ H x ρ z := by
  unfold rowMode
  dsimp only
  rw [markedModeColumn_sector p hp hcop hg hpr x hdiv u hu,
    markedModeColumn_negative_sector p hp hcop hg hpr x hdiv u hu]
  simp only [star_sum,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro J₁ hJ₁
  apply Finset.sum_congr rfl
  intro J₂ hJ₂
  simp only [star_mul,allocatedMode,modeCoefficient]
  ring

theorem modeCoefficient_norm_le
    (hc:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (Ψ:Eis→*ℂ)(hΨ:∀n,‖Ψ n‖≤1)(j:Eis)(Z D B v θ H:ℝ)
    (x:Source (ι:=ι) 0)(ρ:SecondRayIndex)(z:JointLogSeparation.Frequency×(Fin 6→ℝ)) :
    ‖modeCoefficient p hp hcop hg Ψ j Z D B v θ H x ρ z‖≤‖secondRayCoefficient ρ‖ := by
  simp only [modeCoefficient,norm_mul,secondOuterPhase_norm,mul_one]
  exact InverseInitialEnergyCallerWeights.outerCoefficient_norm_le p hp hcop hg hc Ψ hΨ j _ ρ

end SevenEighths.InverseInitialEnergyCallerAllocation

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerBranch
namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic IdealMobiusDivisorSum
namespace SevenEighths.InverseInitialEnergyCallerBranch
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialKernelBridge
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerCanonical InverseInitialEnergyCallerOpposite InverseInitialProfile
open InverseInitialEnergyCallerAllocation InverseInitialEnergyCallerAssigned
open InverseInitialQuotientGeometry InverseInitialClippedColumns
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
  (p:ι→Eis)(hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem actual_allocated_mode_bound
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (hc:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (S:Finset (Source (ι:=ι) 0))(u:Eisˣ)(hdiv:∀x∈S,x.divisor⊆x.common)
    (pool:Finset ι)(Ψ:Eis→*ℂ)(hΨ:∀n,‖Ψ n‖≤1)(j:Eis)
    (slots J₁ J₂:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (ha₁:∀i∈J₁,∀q∈lists i,‖a i q‖≤1)(ha₂:∀i∈J₂,∀q∈lists i,‖a i q‖≤1)
    (ω₁ ω₂:ℝ→ℂ)(Z D B v θ H:ℝ)(hZ:0<Z)
    (ρ:SecondRayIndex)(z:JointLogSeparation.Frequency×(Fin 6→ℝ))
    (w:Source (ι:=ι) 0→ℂ)(hw:∀x∈S,‖w x‖≤1)
    (labels:Finset (Ideal Eis))(rows:Finset Eis)
    (hlabels:∀f∈labels,f≠0)(hneg:∀k∈rows,-k∈rows)
    (hchild:∀x∈S,(initialChild (toTuple p (sectorSource u x))).2.1∈labels ∧
      (initialChild (toTuple p (sectorSource u x))).2.2∈rows)
    (F B₁ B₂:ℝ)
    (hmoment₁:∀t∈quotientSet p (assignedSource S J₁ J₂ lists lists),
      normalizedColumnEnergy p hp hcop hg pool (secondRayMinus Ψ ρ) (j*primaryGenerator t)
        (slots\J₁) lists a labels rows (fun f=>((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1))
        (childLogTest ω₁ (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2) 4))
        (Z^(columnCenter D B v)) Z F≤B₁)
    (hmoment₂:∀t∈quotientSet p (assignedSource S J₁ J₂ lists lists),
      normalizedColumnEnergy p hp hcop hg pool (secondRayPlus Ψ ρ) (j*primaryGenerator t)
        (slots\J₂) lists a labels rows (fun f=>((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1))
        (childLogTest ω₂ ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2) 5))
        (Z^(columnCenter D B v)) Z F≤B₂) :
    ‖∑x∈S,w x*allocatedMode p hp hcop hg u pool Ψ j slots J₁ J₂ lists a ω₁ ω₂
      Z D B v θ H x ρ z‖≤
      ‖secondRayCoefficient ρ‖*(Z^F*∑t∈quotientSet p (assignedSource S J₁ J₂ lists lists),
        ((idealDivisors t).card:ℝ)^(J₁.card+J₂.card))*(Real.sqrt B₁*Real.sqrt B₂) := by
  let c := fun x=>w x*modeCoefficient p hp hcop hg Ψ j Z D B v θ H x ρ z
  have hcoeff (x:Source (ι:=ι) 0)(hx:x∈S) : ‖c x‖≤‖secondRayCoefficient ρ‖ := by
    dsimp only [c]
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hw x hx)).trans
      (modeCoefficient_norm_le p hp hcop hg hc Ψ hΨ j Z D B v θ H x ρ z)
  have he := InverseInitialEnergyCallerAssignedCanonical.original_assigned_canonical_pair
    p hp hcop hg hinj hpr S u J₁ J₂ lists lists a a ha₁ ha₂ hdiv labels rows hlabels hneg hchild
    c ‖secondRayCoefficient ρ‖ (norm_nonneg _) hcoeff pool (secondRayMinus Ψ ρ) (secondRayPlus Ψ ρ) j
    (slots\J₁) (slots\J₂)
    (childLogTest ω₁ (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2) 4))
    (childLogTest ω₂ ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2) 5))
    (Z^(columnCenter D B v)) (Z^(columnCenter D B v)) hZ F B₁ B₂ hmoment₁ hmoment₂
  apply le_trans (le_of_eq ?_) he
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  dsimp only [allocatedMode,c]
  ring

end SevenEighths.InverseInitialEnergyCallerBranch

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerMass
namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss IdealMobiusDivisorSum
namespace SevenEighths.InverseInitialEnergyCallerMass
open InverseMoment InverseInitialArithmetic InverseInitialQuotientGeometry
open InverseInitialEnergyCallerAssigned
local notation "Eis"=>ActualEisensteinCubic.O

theorem assigned_quotient_subset {ι σ:Type*}[DecidableEq ι][DecidableEq σ]
    (p:ι→Eis)(S:Finset (Source (ι:=ι) 0))(J₁ J₂:Finset σ)(L₁ L₂:σ→Finset ι) :
    quotientSet p (assignedSource S J₁ J₂ L₁ L₂)⊆quotientSet p S := by
  intro t ht
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ht
  obtain ⟨⟨y,q⟩,hy,rfl⟩ := Finset.mem_image.mp hx
  exact Finset.mem_image.mpr ⟨y,(Finset.mem_product.mp (Finset.mem_filter.mp hy).1).1,rfl⟩

theorem divisor_weight_mono {t:Ideal Eis}(ht:t≠0){J K:ℕ}(hJK:J≤K) :
    ((idealDivisors t).card:ℝ)^J≤((idealDivisors t).card:ℝ)^K := by
  have hc : (1:ℝ)≤(idealDivisors t).card := by
    exact_mod_cast Finset.card_pos.mpr ⟨1,(mem_idealDivisors ht).mpr (one_dvd t)⟩
  exact pow_le_pow_right₀ hc hJK

theorem assigned_quotient_mass (K:ℕ)(U π:ℝ)(hU:0≤U)(hπ:0<π) :
    ∃C:ℝ,0<C ∧ ∀{ι σ:Type*}[DecidableEq ι][DecidableEq σ]
      (p:ι→Eis)(_hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (S:Finset (Source (ι:=ι) 0))(J₁ J₂:Finset σ)(L₁ L₂:σ→Finset ι)
      (_hJ:J₁.card+J₂.card≤K)(Z R:ℝ)(_hZ:1≤Z)(_hR:R≤U)
      (_hn:∀t∈quotientSet p S,(t.absNorm:ℝ)≤Z^R),
      (∑t∈quotientSet p (assignedSource S J₁ J₂ L₁ L₂),
        ((idealDivisors t).card:ℝ)^(J₁.card+J₂.card))≤C*Z^(R+π) := by
  have hε : 0<π/(U+1) := div_pos hπ (by linarith)
  obtain ⟨C,hC,hb⟩ := normalized_mass_bound K (π/(U+1)) hε
  refine ⟨C,hC,?_⟩
  intro ι σ _ _ p hp _ S J₁ J₂ L₁ L₂ hJ Z R hZ hR hn
  have hZp : 0<Z := zero_lt_one.trans_le hZ
  let T := quotientSet p (assignedSource S J₁ J₂ L₁ L₂)
  have ht : ∀t∈T,t≠0 := quotientSet_nonzero p hp _
  have hnorm : ∀t∈T,(t.absNorm:ℝ)≤Z^R :=
    fun t hh=>hn t (assigned_quotient_subset p S J₁ J₂ L₁ L₂ hh)
  have hm := hb T (Z^R) (Real.rpow_pos_of_pos hZp _) ht hnorm
  have hpow : (Z^R)^(π/(U+1))≤Z^π := by
    rw [←Real.rpow_mul hZp.le]
    apply Real.rpow_le_rpow_of_exponent_le hZ
    apply (mul_le_mul_of_nonneg_right hR hε.le).trans
    rw [←mul_div_assoc]
    apply (div_le_iff₀ (by linarith : 0<U+1)).mpr
    nlinarith
  have hm' := hm.trans (mul_le_mul_of_nonneg_left hpow hC.le)
  have hs := mul_le_mul_of_nonneg_left hm' (Real.rpow_nonneg hZp.le R)
  simp only [normalizedMass,←mul_assoc,mul_inv_cancel₀ (Real.rpow_pos_of_pos hZp R).ne',one_mul] at hs
  calc
    _≤∑t∈T,((idealDivisors t).card:ℝ)^K :=
      Finset.sum_le_sum fun t hmem=>divisor_weight_mono (ht t hmem) hJ
    _≤Z^R*(C*Z^π) := by simpa only [mul_assoc] using hs
    _=C*Z^(R+π) := by rw [Real.rpow_add hZp];ring

end SevenEighths.InverseInitialEnergyCallerMass

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerAllSlots
namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic IdealMobiusDivisorSum
namespace SevenEighths.InverseInitialEnergyCallerAllSlots
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialKernelBridge
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerCanonical InverseInitialEnergyCallerOpposite InverseInitialProfile
open InverseInitialEnergyCallerAllocation InverseInitialEnergyCallerAssigned
open InverseInitialQuotientGeometry InverseInitialClippedColumns InverseInitialEnergyCallerBranch
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
  (p:ι→Eis)(hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem rowMode_sum_allocations
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (S:Finset (Source (ι:=ι) 0))(hdiv:∀x∈S,x.divisor⊆x.common)(u:Eisˣ)
    (hu:∀x∈S,unitSector p hp hpr (sourcePoint x ∅ ∅)=u)
    (pool:Finset ι)(Ψ:Eis→*ℂ)(j:Eis)(slots:Finset σ)
    (lists:σ→Finset ι)(a:σ→ι→ℂ)(ω₁ ω₂:ℝ→ℂ)(Z D B v θ H:ℝ)
    (ρ:SecondRayIndex)(z:JointLogSeparation.Frequency×(Fin 6→ℝ))(w:Source (ι:=ι) 0→ℂ) :
    (∑x∈S,w x*rowMode p hp hcop hg hpr pool Ψ j slots lists a ω₁ ω₂ Z D B v θ H x ρ z)=
      ∑J₁∈slots.powerset,∑J₂∈slots.powerset,
        ∑x∈S,w x*allocatedMode p hp hcop hg u pool Ψ j slots J₁ J₂ lists a ω₁ ω₂
          Z D B v θ H x ρ z := by
  calc
    _=∑x∈S,∑J₁∈slots.powerset,∑J₂∈slots.powerset,
        w x*allocatedMode p hp hcop hg u pool Ψ j slots J₁ J₂ lists a ω₁ ω₂
          Z D B v θ H x ρ z := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [rowMode_eq_allocations p hp hcop hg hpr x (hdiv x hx) u (hu x hx)]
      simp only [Finset.mul_sum]
    _=_ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro J hJ
      exact Finset.sum_comm

theorem all_slots_bound (N:ℕ)(U π:ℝ)(hU:0≤U)(hπ:0<π) :
    ∃C:ℝ,0<C ∧ ∀{ι σ:Type*}[DecidableEq ι][DecidableEq σ]
      (p:ι→Eis)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
      (_hc:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
      (S:Finset (Source (ι:=ι) 0))(u:Eisˣ)(_hdiv:∀x∈S,x.divisor⊆x.common)
      (_hu:∀x∈S,unitSector p hp hpr (sourcePoint x ∅ ∅)=u)
      (pool:Finset ι)(Ψ:Eis→*ℂ)(_hΨ:∀n,‖Ψ n‖≤1)(j:Eis)
      (slots:Finset σ)(_hslots:slots.card≤N)(lists:σ→Finset ι)(a:σ→ι→ℂ)
      (_ha:∀i∈slots,∀q∈lists i,‖a i q‖≤1)
      (ω₁ ω₂:ℝ→ℂ)(Z D B v θ H R:ℝ)(_hZ:1≤Z)(_hR:R≤U)
      (_hn:∀t∈quotientSet p S,(t.absNorm:ℝ)≤Z^R)
      (ρ:SecondRayIndex)(z:JointLogSeparation.Frequency×(Fin 6→ℝ))
      (w:Source (ι:=ι) 0→ℂ)(_hw:∀x∈S,‖w x‖≤1)
      (labels:Finset (Ideal Eis))(rows:Finset Eis)
      (_hlabels:∀f∈labels,f≠0)(_hneg:∀k∈rows,-k∈rows)
      (_hchild:∀x∈S,(initialChild (toTuple p (sectorSource u x))).2.1∈labels ∧
        (initialChild (toTuple p (sectorSource u x))).2.2∈rows)
      (F E:ℝ)(_hE:0≤E)
      (_hmoment:∀J₁∈slots.powerset,∀J₂∈slots.powerset,
        ∀t∈quotientSet p (assignedSource S J₁ J₂ lists lists),
        normalizedColumnEnergy p hp hcop hg pool (secondRayMinus Ψ ρ) (j*primaryGenerator t)
          (slots\J₁) lists a labels rows (fun f=>((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1))
          (childLogTest ω₁ (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2) 4))
          (Z^(columnCenter D B v)) Z F≤E ∧
        normalizedColumnEnergy p hp hcop hg pool (secondRayPlus Ψ ρ) (j*primaryGenerator t)
          (slots\J₂) lists a labels rows (fun f=>((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1))
          (childLogTest ω₂ ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2) 5))
          (Z^(columnCenter D B v)) Z F≤E),
      ‖∑x∈S,w x*rowMode p hp hcop hg hpr pool Ψ j slots lists a ω₁ ω₂
        Z D B v θ H x ρ z‖≤C*‖secondRayCoefficient ρ‖*Z^(F+R+π)*E := by
  obtain ⟨C,hC,hmass⟩ := InverseInitialEnergyCallerMass.assigned_quotient_mass (2*N) U π hU hπ
  refine ⟨C*4^N,by positivity,?_⟩
  intro ι σ _ _ p hp _ hcop hg hinj hpr hc S u hdiv hu pool Ψ hΨ j slots hslots lists a ha ω₁ ω₂
    Z D B v θ H R hZ hR hn ρ z w hw labels rows hlabels hneg hchild F E hE hmoment
  have hZp : 0<Z := zero_lt_one.trans_le hZ
  let bound := C*‖secondRayCoefficient ρ‖*Z^(F+R+π)*E
  have hb (J₁:Finset σ)(hJ₁:J₁∈slots.powerset)(J₂:Finset σ)(hJ₂:J₂∈slots.powerset) :
      ‖∑x∈S,w x*allocatedMode p hp hcop hg u pool Ψ j slots J₁ J₂ lists a ω₁ ω₂
        Z D B v θ H x ρ z‖≤bound := by
    have h₁ := Finset.mem_powerset.mp hJ₁
    have h₂ := Finset.mem_powerset.mp hJ₂
    have he := actual_allocated_mode_bound p hp hcop hg hinj hpr hc S u hdiv pool Ψ hΨ j
      slots J₁ J₂ lists a (fun i hi=>ha i (h₁ hi)) (fun i hi=>ha i (h₂ hi)) ω₁ ω₂
      Z D B v θ H hZp ρ z w hw labels rows hlabels hneg hchild F E E
      (fun t ht=>(hmoment J₁ hJ₁ J₂ hJ₂ t ht).1)
      (fun t ht=>(hmoment J₁ hJ₁ J₂ hJ₂ t ht).2)
    rw [Real.mul_self_sqrt hE] at he
    have hJ : J₁.card+J₂.card≤2*N := by
      have := (Finset.card_le_card h₁).trans hslots
      have := (Finset.card_le_card h₂).trans hslots
      omega
    have hm := hmass p hp S J₁ J₂ lists lists hJ Z R hZ hR hn
    apply he.trans
    calc
      _≤‖secondRayCoefficient ρ‖*(Z^F*(C*Z^(R+π)))*E := by gcongr
      _=bound := by dsimp only [bound];rw [add_assoc F R π,Real.rpow_add hZp F (R+π)];ring
  rw [rowMode_sum_allocations p hp hcop hg hpr S hdiv u hu]
  calc
    _≤∑J₁∈slots.powerset,∑J₂∈slots.powerset,
        ‖∑x∈S,w x*allocatedMode p hp hcop hg u pool Ψ j slots J₁ J₂ lists a ω₁ ω₂
          Z D B v θ H x ρ z‖ := (norm_sum_le _ _).trans
      (Finset.sum_le_sum fun J hJ=>norm_sum_le _ _)
    _≤∑_J₁∈slots.powerset,∑_J₂∈slots.powerset,bound :=
      Finset.sum_le_sum fun J₁ hJ₁=>Finset.sum_le_sum fun J₂ hJ₂=>hb J₁ hJ₁ J₂ hJ₂
    _=(4:ℝ)^slots.card*bound := by
      simp only [Finset.sum_const,Finset.card_powerset,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
      rw [show (4:ℝ)=2*2 by norm_num,mul_pow]
      ring
    _≤(4:ℝ)^N*bound := mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num) hslots) (by dsimp [bound];positivity)
    _=_ := by dsimp [bound];ring

end SevenEighths.InverseInitialEnergyCallerAllSlots

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerUnits
namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic IdealMobiusDivisorSum
namespace SevenEighths.InverseInitialEnergyCallerUnits
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialKernelBridge
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerCanonical InverseInitialEnergyCallerOpposite InverseInitialProfile
open InverseInitialEnergyCallerAllocation InverseInitialEnergyCallerAssigned
open InverseInitialQuotientGeometry InverseInitialClippedColumns InverseInitialEnergyCallerBranch
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
  (p:ι→Eis)(hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

attribute [local instance] OAI.SevenEighths.InverseInitialEnergyCallerUnits.initialEnergyUnits
omit [∀i,(Ideal.span {p i}).IsMaximal] in
theorem sourceSector_partition (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (S:Finset (Source (ι:=ι) 0))(f:Source (ι:=ι) 0→ℂ) :
    (∑x∈S,f x)=∑u:Eisˣ,∑x∈sourceSector p hp hpr S u,f x :=
  (Finset.sum_fiberwise S (fun x=>unitSector p hp hpr (sourcePoint x ∅ ∅)) f).symm

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem quotientSet_mono {J:ℕ}{S T:Finset (Source (ι:=ι) J)}(hst:S⊆T) :
    quotientSet p S⊆quotientSet p T := Finset.image_subset_image hst

theorem unit_sector_card : Fintype.card Eisˣ=6 := by
  simpa only [Nat.card_eq_fintype_card] using PrimaryIdealUnitReindex.card_units_eq_six

theorem all_units_bound (N:ℕ)(U π:ℝ)(hU:0≤U)(hπ:0<π) :
    ∃C:ℝ,0<C ∧ ∀{ι σ:Type*}[DecidableEq ι][DecidableEq σ]
      (p:ι→Eis)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
      (_hc:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
      (S:Finset (Source (ι:=ι) 0))(_hdiv:∀x∈S,x.divisor⊆x.common)
      (pool:Finset ι)(Ψ:Eis→*ℂ)(_hΨ:∀n,‖Ψ n‖≤1)(j:Eis)
      (slots:Finset σ)(_hslots:slots.card≤N)(lists:σ→Finset ι)(a:σ→ι→ℂ)
      (_ha:∀i∈slots,∀q∈lists i,‖a i q‖≤1)
      (ω₁ ω₂:ℝ→ℂ)(Z D B v θ H R:ℝ)(_hZ:1≤Z)(_hR:R≤U)
      (_hn:∀t∈quotientSet p S,(t.absNorm:ℝ)≤Z^R)
      (ρ:SecondRayIndex)(z:JointLogSeparation.Frequency×(Fin 6→ℝ))
      (w:Source (ι:=ι) 0→ℂ)(_hw:∀x∈S,‖w x‖≤1)
      (labels:Finset (Ideal Eis))(rows:Finset Eis)
      (_hlabels:∀f∈labels,f≠0)(_hneg:∀k∈rows,-k∈rows)
      (_hchild:∀x∈S,(initialChild (toTuple p (sectorSource (unitSector p hp hpr (sourcePoint x ∅ ∅)) x))).2.1∈labels ∧
        (initialChild (toTuple p (sectorSource (unitSector p hp hpr (sourcePoint x ∅ ∅)) x))).2.2∈rows)
      (F E:ℝ)(_hE:0≤E)
      (_hmoment:∀J₁∈slots.powerset,∀J₂∈slots.powerset,
        ∀t∈quotientSet p S,
        normalizedColumnEnergy p hp hcop hg pool (secondRayMinus Ψ ρ) (j*primaryGenerator t)
          (slots\J₁) lists a labels rows (fun f=>((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1))
          (childLogTest ω₁ (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2) 4))
          (Z^(columnCenter D B v)) Z F≤E ∧
        normalizedColumnEnergy p hp hcop hg pool (secondRayPlus Ψ ρ) (j*primaryGenerator t)
          (slots\J₂) lists a labels rows (fun f=>((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1))
          (childLogTest ω₂ ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2) 5))
          (Z^(columnCenter D B v)) Z F≤E),
      ‖∑x∈S,w x*rowMode p hp hcop hg hpr pool Ψ j slots lists a ω₁ ω₂
        Z D B v θ H x ρ z‖≤C*‖secondRayCoefficient ρ‖*Z^(F+R+π)*E := by
  obtain ⟨C,hC,hbound⟩ := InverseInitialEnergyCallerAllSlots.all_slots_bound N U π hU hπ
  refine ⟨6*C,by positivity,?_⟩
  intro ι σ _ _ p hp _ hcop hg hinj hpr hc S hdiv pool Ψ hΨ j slots hslots lists a ha ω₁ ω₂
    Z D B v θ H R hZ hR hn ρ z w hw labels rows hlabels hneg hchild F E hE hmoment
  have hb (u:Eisˣ) :
      ‖∑x∈sourceSector p hp hpr S u,w x*rowMode p hp hcop hg hpr pool Ψ j slots lists a ω₁ ω₂
        Z D B v θ H x ρ z‖≤C*‖secondRayCoefficient ρ‖*Z^(F+R+π)*E := by
    have hs : sourceSector p hp hpr S u⊆S := Finset.filter_subset _ _
    apply hbound p hp hcop hg hinj hpr hc (sourceSector p hp hpr S u) u
      (fun x hx=>hdiv x (hs hx)) (fun x hx=>(Finset.mem_filter.mp hx).2)
      pool Ψ hΨ j slots hslots lists a ha ω₁ ω₂ Z D B v θ H R hZ hR
      (fun t ht=>hn t (quotientSet_mono p hs ht)) ρ z w
      (fun x hx=>hw x (hs hx)) labels rows hlabels hneg
      (fun x hx=>by
        have hh := hchild x (hs hx)
        rw [(Finset.mem_filter.mp hx).2] at hh
        exact hh) F E hE
    intro J₁ hJ₁ J₂ hJ₂ t ht
    exact hmoment J₁ hJ₁ J₂ hJ₂ t
      (quotientSet_mono p hs (InverseInitialEnergyCallerMass.assigned_quotient_subset
        p (sourceSector p hp hpr S u) J₁ J₂ lists lists ht))
  rw [sourceSector_partition p hp hpr S]
  calc
    _≤∑u:Eisˣ,‖∑x∈sourceSector p hp hpr S u,w x*rowMode p hp hcop hg hpr pool Ψ j
      slots lists a ω₁ ω₂ Z D B v θ H x ρ z‖ := norm_sum_le _ _
    _≤∑_u:Eisˣ,C*‖secondRayCoefficient ρ‖*Z^(F+R+π)*E := Finset.sum_le_sum fun u _=>hb u
    _=_ := by simp only [Finset.sum_const,Finset.card_univ,unit_sector_card,nsmul_eq_mul];norm_num;ring

end SevenEighths.InverseInitialEnergyCallerUnits

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerRays
namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic IdealMobiusDivisorSum
namespace SevenEighths.InverseInitialEnergyCallerRays
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialKernelBridge
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerCanonical InverseInitialEnergyCallerOpposite InverseInitialProfile
open InverseInitialEnergyCallerAllocation InverseInitialEnergyCallerAssigned
open InverseInitialQuotientGeometry InverseInitialClippedColumns InverseInitialEnergyCallerBranch
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
  (p:ι→Eis)(hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem all_rays_bound (N:ℕ)(U π:ℝ)(hU:0≤U)(hπ:0<π) :
    ∃C:ℝ,0<C ∧ ∀{ι σ:Type*}[DecidableEq ι][DecidableEq σ]
      (p:ι→Eis)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
      (_hc:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
      (S:Finset (Source (ι:=ι) 0))(_hdiv:∀x∈S,x.divisor⊆x.common)
      (pool:Finset ι)(Ψ:Eis→*ℂ)(_hΨ:∀n,‖Ψ n‖≤1)(j:Eis)
      (slots:Finset σ)(_hslots:slots.card≤N)(lists:σ→Finset ι)(a:σ→ι→ℂ)
      (_ha:∀i∈slots,∀q∈lists i,‖a i q‖≤1)
      (ω₁ ω₂:ℝ→ℂ)(Z D B v θ H R:ℝ)(_hZ:1≤Z)(_hR:R≤U)
      (_hn:∀t∈quotientSet p S,(t.absNorm:ℝ)≤Z^R)
      (z:JointLogSeparation.Frequency×(Fin 6→ℝ))
      (w:Source (ι:=ι) 0→ℂ)(_hw:∀x∈S,‖w x‖≤1)
      (labels:Finset (Ideal Eis))(rows:Finset Eis)
      (_hlabels:∀f∈labels,f≠0)(_hneg:∀k∈rows,-k∈rows)
      (_hchild:∀x∈S,(initialChild (toTuple p (sectorSource (unitSector p hp hpr (sourcePoint x ∅ ∅)) x))).2.1∈labels ∧
        (initialChild (toTuple p (sectorSource (unitSector p hp hpr (sourcePoint x ∅ ∅)) x))).2.2∈rows)
      (F E:ℝ)(_hE:0≤E)
      (_hmoment:∀ρ:SecondRayIndex,∀J₁∈slots.powerset,∀J₂∈slots.powerset,
        ∀t∈quotientSet p S,
        normalizedColumnEnergy p hp hcop hg pool (secondRayMinus Ψ ρ) (j*primaryGenerator t)
          (slots\J₁) lists a labels rows (fun f=>((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1))
          (childLogTest ω₁ (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2) 4))
          (Z^(columnCenter D B v)) Z F≤E ∧
        normalizedColumnEnergy p hp hcop hg pool (secondRayPlus Ψ ρ) (j*primaryGenerator t)
          (slots\J₂) lists a labels rows (fun f=>((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1))
          (childLogTest ω₂ ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2) 5))
          (Z^(columnCenter D B v)) Z F≤E),
      ‖∑x∈S,∑ρ:SecondRayIndex,w x*rowMode p hp hcop hg hpr pool Ψ j slots lists a ω₁ ω₂
        Z D B v θ H x ρ z‖≤C*Z^(F+R+π)*E := by
  obtain ⟨C,hC,hbound⟩ := InverseInitialEnergyCallerUnits.all_units_bound N U π hU hπ
  let A : ℝ := ∑ρ:SecondRayIndex,‖secondRayCoefficient ρ‖
  have hA : 0≤A := Finset.sum_nonneg fun _ _=>norm_nonneg _
  refine ⟨C*(1+A),mul_pos hC (by linarith),?_⟩
  intro ι σ _ _ p hp _ hcop hg hinj hpr hc S hdiv pool Ψ hΨ j slots hslots lists a ha ω₁ ω₂
    Z D B v θ H R hZ hR hn z w hw labels rows hlabels hneg hchild F E hE hmoment
  have hb (ρ:SecondRayIndex) := hbound p hp hcop hg hinj hpr hc S hdiv pool Ψ hΨ j
    slots hslots lists a ha ω₁ ω₂ Z D B v θ H R hZ hR hn ρ z w hw labels rows
    hlabels hneg hchild F E hE (hmoment ρ)
  rw [Finset.sum_comm]
  calc
    _≤∑ρ:SecondRayIndex,‖∑x∈S,w x*rowMode p hp hcop hg hpr pool Ψ j slots lists a ω₁ ω₂
        Z D B v θ H x ρ z‖ := norm_sum_le _ _
    _≤∑ρ:SecondRayIndex,C*‖secondRayCoefficient ρ‖*Z^(F+R+π)*E := Finset.sum_le_sum fun ρ _=>hb ρ
    _=C*A*Z^(F+R+π)*E := by simp only [←Finset.sum_mul,←Finset.mul_sum,A]
    _≤C*(1+A)*Z^(F+R+π)*E := by gcongr;linarith

end SevenEighths.InverseInitialEnergyCallerRays

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerIntegral
namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap
open MeasureTheory
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic IdealMobiusDivisorSum
namespace SevenEighths.InverseInitialEnergyCallerIntegral
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialKernelBridge
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerCanonical InverseInitialEnergyCallerOpposite InverseInitialProfile
open InverseInitialEnergyCallerAllocation InverseInitialEnergyCallerAssigned
open InverseInitialQuotientGeometry InverseInitialClippedColumns InverseInitialEnergyCallerBranch
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
  (p:ι→Eis)(hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem actual_common_integral_bound_oai (N:ℕ)(U π:ℝ)(hU:0≤U)(hπ:0<π) :
    ∃C:ℝ,0<C ∧ ∀{ι σ:Type*}[DecidableEq ι][DecidableEq σ]
      (p:ι→Eis)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
      (_hc:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
      (S:Finset (Source (ι:=ι) 0))(_hdiv:∀x∈S,x.divisor⊆x.common)
      (pool:Finset ι)(Ψ:Eis→*ℂ)(_hΨ:∀n,‖Ψ n‖≤1)(j:Eis)
      (slots:Finset σ)(_hslots:slots.card≤N)(lists:σ→Finset ι)(a:σ→ι→ℂ)
      (_ha:∀i∈slots,∀q∈lists i,‖a i q‖≤1)
      (ω₁ ω₂:ℝ→ℂ)(Z D B v θ H R:ℝ)(_hZ:1≤Z)(_hR:R≤U)
      (_hn:∀t∈quotientSet p S,(t.absNorm:ℝ)≤Z^R)
      (w:Source (ι:=ι) 0→ℂ)(_hw:∀x∈S,‖w x‖≤1)
      (labels:Finset (Ideal Eis))(rows:Finset Eis)
      (_hlabels:∀f∈labels,f≠0)(_hneg:∀k∈rows,-k∈rows)
      (_hchild:∀x∈S,(initialChild (toTuple p (sectorSource (unitSector p hp hpr (sourcePoint x ∅ ∅)) x))).2.1∈labels ∧
        (initialChild (toTuple p (sectorSource (unitSector p hp hpr (sourcePoint x ∅ ∅)) x))).2.2∈rows)
      (F A:ℝ)(_hA:0≤A)(J:ℕ)
      (g:Fin 6→𝓢(ℝ,ℂ))(g₁ g₂ b₃:𝓢(ℝ,ℂ))(c₁ c₂ θ₁ θ₂ L:ℝ)
      (_hmoment:∀z:JointLogSeparation.Frequency×(Fin 6→ℝ),∀ρ:SecondRayIndex,∀J₁∈slots.powerset,∀J₂∈slots.powerset,
        ∀t∈quotientSet p S,
        normalizedColumnEnergy p hp hcop hg pool (secondRayMinus Ψ ρ) (j*primaryGenerator t)
          (slots\J₁) lists a labels rows (fun f=>((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1))
          (childLogTest ω₁ (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2) 4))
          (Z^(columnCenter D B v)) Z F≤A*(tripleHeight J z.1*coordinateHeight J z.2) ∧
        normalizedColumnEnergy p hp hcop hg pool (secondRayPlus Ψ ρ) (j*primaryGenerator t)
          (slots\J₂) lists a labels rows (fun f=>((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1))
          (childLogTest ω₂ ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2) 5))
          (Z^(columnCenter D B v)) Z F≤A*(tripleHeight J z.1*coordinateHeight J z.2)),
      ‖∫z:JointLogSeparation.Frequency×(Fin 6→ℝ),
        familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ L z*
        (∑x∈S,∑ρ:SecondRayIndex,w x*rowMode p hp hcop hg hpr pool Ψ j slots lists a ω₁ ω₂
          Z D B v θ H x ρ z)‖≤
        C*Z^(F+R+π)*A*(∫z:JointLogSeparation.Frequency×(Fin 6→ℝ),
          tripleHeight J z.1*coordinateHeight J z.2*‖familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ L z‖) := by
  obtain ⟨C,hC,hbound⟩ := InverseInitialEnergyCallerRays.all_rays_bound N U π hU hπ
  refine ⟨C,hC,?_⟩
  intro ι σ _ _ p hp _ hcop hg hinj hpr hc S hdiv pool Ψ hΨ j slots hslots lists a ha ω₁ ω₂
    Z D B v θ H R hZ hR hn w hw labels rows hlabels hneg hchild F A hA J g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ L hmoment
  have hb (z:JointLogSeparation.Frequency×(Fin 6→ℝ)) :=
    hbound p hp hcop hg hinj hpr hc S hdiv pool Ψ hΨ j slots hslots lists a ha ω₁ ω₂
      Z D B v θ H R hZ hR hn z w hw labels rows hlabels hneg hchild F
      (A*(tripleHeight J z.1*coordinateHeight J z.2))
      (by unfold tripleHeight coordinateHeight;positivity) (hmoment z)
  calc
    _≤∫z:JointLogSeparation.Frequency×(Fin 6→ℝ),
      (C*Z^(F+R+π)*A)*(tripleHeight J z.1*coordinateHeight J z.2*
        ‖familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ L z‖) := by
      apply norm_integral_le_of_norm_le
        ((familyDensity_weighted_integrable g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ L J).const_mul _)
      filter_upwards with z
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left (hb z) (norm_nonneg _)).trans_eq (by ring)
    _=_ := integral_const_mul _ _

end SevenEighths.InverseInitialEnergyCallerIntegral

end

end OAI
end

theorem solution.{u_3, u_4} : type_of% @OAI.SevenEighths.InverseInitialEnergyCallerIntegral.actual_common_integral_bound_oai.{u_3, u_4} := @OAI.SevenEighths.InverseInitialEnergyCallerIntegral.actual_common_integral_bound_oai.{u_3, u_4}
