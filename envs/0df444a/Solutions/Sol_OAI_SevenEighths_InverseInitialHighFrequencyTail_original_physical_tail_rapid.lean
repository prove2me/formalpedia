-- Prove2me | solution 1 for OAI.SevenEighths.InverseInitialHighFrequencyTail.original_physical_tail_rapid
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T23:53:41.381+00:00
-- url     : https://prove2.me/submissions/da61b6f6-2ad6-4184-9830-a5f895ef5e1e

import Mathlib
import Lean.Elab.Tactic.Omega
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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Poisson.RadialFourier
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

namespace EisensteinSchwartzPoisson

open ConcreteTraceCRT ActualEisensteinCubic
open scoped SchwartzMap

theorem polynomial_tail_majorant (A : ℕ) (K T q B f : ℝ)
    (hK : 0 < K) (hT : 0 ≤ T) (hq : 0 ≤ q) (hf : 0 ≤ f)
    (htail : T ≤ K * q) (hbound : (1 + K * q) ^ (A + 2) * f ≤ B) :
    f ≤ (B / ((min 1 K) ^ 2 * (1 + T) ^ A)) * ((1 + q) ^ 2)⁻¹ := by
  have hm : 0 < min 1 K := lt_min (by norm_num) hK
  have hm1 : min 1 K ≤ 1 := min_le_left _ _
  have hmK : min 1 K ≤ K := min_le_right _ _
  have hbase : min 1 K * (1 + q) ≤ 1 + K * q := by
    nlinarith [mul_le_mul_of_nonneg_right hmK hq]
  have htwo : (min 1 K) ^ 2 * (1 + q) ^ 2 ≤ (1 + K * q) ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hbase _
  have hpow : (1 + T) ^ A ≤ (1 + K * q) ^ A :=
    pow_le_pow_left₀ (by positivity) (by linarith) _
  have hden : ((min 1 K) ^ 2 * (1 + T) ^ A) * (1 + q) ^ 2 ≤
      (1 + K * q) ^ (A + 2) := by
    have hh := mul_le_mul hpow htwo (by positivity) (by positivity)
    rw [pow_add]
    nlinarith
  have hprod : f * (((min 1 K) ^ 2 * (1 + T) ^ A) * (1 + q) ^ 2) ≤ B := by
    calc
      _ = (((min 1 K) ^ 2 * (1 + T) ^ A) * (1 + q) ^ 2) * f := mul_comm _ _
      _ ≤ (1 + K * q) ^ (A + 2) * f := mul_le_mul_of_nonneg_right hden hf
      _ ≤ B := hbound
  have hraw := (le_div_iff₀ (show 0 < ((min 1 K) ^ 2 * (1 + T) ^ A) * (1 + q) ^ 2
      by positivity)).mpr hprod
  simpa only [div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm, mul_assoc] using hraw

theorem paperRadialFourier_lattice_summable_norm (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    Summable (fun h : O => ‖paperRadialFourier W (K * ‖eisEmbedding h‖ ^ 2)‖) := by
  obtain ⟨s, C, hC, hb⟩ := paperRadialFourier_source_weighted_bound 2
  let B := C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  let D := (min 1 K) ^ 2 * (1 + (0 : ℝ)) ^ (0 : ℕ)
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
    (eisenstein_cauchy_summable.mul_left (B / D))
  intro h
  exact polynomial_tail_majorant 0 K 0 _ B _ hK (by norm_num)
    (sq_nonneg _) (norm_nonneg _) (by positivity) (hb W _ (by positivity))

theorem paperRadialFourier_lattice_tail (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ, ℂ)) (K T : ℝ), 0 < K → 0 ≤ T →
        (∑' h : {h : O // T ≤ K * ‖eisEmbedding h‖ ^ 2},
          ‖paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖) ≤
        (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) /
          ((min 1 K) ^ 2 * (1 + T) ^ A) := by
  obtain ⟨s, C, hC, hb⟩ := paperRadialFourier_source_weighted_bound (A + 2)
  refine ⟨s, C * (eisensteinCauchyMass + 1), by
    have := eisensteinCauchyMass_nonneg
    positivity, ?_⟩
  intro W K T hK hT
  let B := C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  let D := (min 1 K) ^ 2 * (1 + T) ^ A
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hm : 0 < min 1 K := lt_min (by norm_num) hK
  have hD : 0 < D := by dsimp [D]; positivity
  let S := {h : O | T ≤ K * ‖eisEmbedding h‖ ^ 2}
  have hp (h : S) :
      ‖paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖ ≤
        (B / D) * ((1 + ‖eisEmbedding h.val‖ ^ 2) ^ 2)⁻¹ := by
    exact polynomial_tail_majorant A K T _ B _ hK hT (sq_nonneg _)
      (norm_nonneg _) h.property (hb W _ (by positivity))
  have hmajor : Summable (fun h : S => (B / D) *
      ((1 + ‖eisEmbedding h.val‖ ^ 2) ^ 2)⁻¹) :=
    (eisenstein_cauchy_summable.subtype S).mul_left (B / D)
  have hs : Summable (fun h : S =>
      ‖paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hp hmajor
  calc
    _ ≤ ∑' h : S, (B / D) * ((1 + ‖eisEmbedding h.val‖ ^ 2) ^ 2)⁻¹ :=
      hs.tsum_le_tsum hp hmajor
    _ = (B / D) * ∑' h : S, ((1 + ‖eisEmbedding h.val‖ ^ 2) ^ 2)⁻¹ := tsum_mul_left
    _ ≤ (B / D) * eisensteinCauchyMass :=
      mul_le_mul_of_nonneg_left (eisensteinCauchyMass_subtype S) (div_nonneg hB hD.le)
    _ ≤ (B / D) * (eisensteinCauchyMass + 1) := by
      gcongr
      linarith
    _ = _ := by dsimp [B, D]; ring

end EisensteinSchwartzPoisson

open scoped BigOperators Classical SchwartzMap ContDiff

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

include hinj in
theorem boundedPrimeSupports_card (F : Finset ι) (X : ℝ) (hX : 1 ≤ X) :
    ((boundedPrimeSupports p F X).card : ℝ) ≤ 128*X := by
  let q : Finset ι → Ideal O := fun S => ∏ i ∈ S, Ideal.span {p i}
  have hq : Function.Injective q := FirstCauchyArithmetic.family_product_injective _ hinj
  let I := (boundedPrimeSupports p F X).image q
  have hcard : I.card = (boundedPrimeSupports p F X).card := Finset.card_image_of_injective _ hq
  rw [← hcard]
  apply DescentFiberCost.finite_ideal_count_real I X hX
  · intro J hJ
    obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp hJ
    exact Finset.prod_ne_zero_iff.mpr (fun i hi => NeZero.ne (Ideal.span {p i}))
  · intro J hJ
    obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp hJ
    rw [← primeProductNorm_eq_ideal_norm p S]
    exact (Finset.mem_filter.mp hS).2

end SecondPassArithmetic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.Marks
namespace OAI

namespace SevenEighths.InverseMoment

open scoped BigOperators

noncomputable section

variable {σ ι : Type*} [DecidableEq σ] [DecidableEq ι]

theorem primeSlot_norm_le (L A : Finset ι) (a : ι → ℂ)
    (ha : ∀ p ∈ L, ‖a p‖ ≤ 1) :
    ‖primeSlot L a A‖ ≤ ((L ∩ A).card : ℝ) := by
  simp only [primeSlot, Finset.sum_ite_mem]
  apply (norm_sum_le _ _).trans
  calc
    ∑ p ∈ L ∩ A, ‖a p‖ ≤ ∑ p ∈ L ∩ A, (1 : ℝ) :=
      Finset.sum_le_sum fun p hp => ha p (Finset.mem_inter.mp hp).1
    _ = _ := by simp

omit [DecidableEq σ] in
theorem primeMark_norm_le_divisor_count (I : Finset σ) (L : σ → Finset ι)
    (a : σ → ι → ℂ) (A : Finset ι)
    (hL : (I : Set σ).PairwiseDisjoint L)
    (ha : ∀ i ∈ I, ∀ p ∈ L i, ‖a i p‖ ≤ 1) :
    ‖primeMark I L a A‖ ≤ (2 : ℝ) ^ A.card := by
  have hdis : (I : Set σ).PairwiseDisjoint (fun i => L i ∩ A) := by
    intro i hi j hj hij
    exact (hL hi hj hij).mono (Finset.inter_subset_left) (Finset.inter_subset_left)
  have hcard : (∑ i ∈ I, (L i ∩ A).card) ≤ A.card := by
    rw [← Finset.card_biUnion hdis]
    apply Finset.card_le_card
    intro p hp
    obtain ⟨i, hi, hp⟩ := Finset.mem_biUnion.mp hp
    exact (Finset.mem_inter.mp hp).2
  calc
    ‖primeMark I L a A‖ = ∏ i ∈ I, ‖primeSlot (L i) (a i) A‖ := by
      exact norm_prod _ _
    _ ≤ ∏ i ∈ I, ((L i ∩ A).card : ℝ) := by
      exact Finset.prod_le_prod (fun i _ => norm_nonneg _)
        (fun i hi => primeSlot_norm_le _ _ _ (ha i hi))
    _ ≤ ∏ i ∈ I, (2 : ℝ) ^ (L i ∩ A).card := by
      apply Finset.prod_le_prod (fun i _ => Nat.cast_nonneg _)
      intro i hi
      exact_mod_cast (Nat.le_of_lt (L i ∩ A).card.lt_two_pow_self)
    _ = (2 : ℝ) ^ (∑ i ∈ I, (L i ∩ A).card) :=
      Finset.prod_pow_eq_pow_sum _ _ _
    _ ≤ (2 : ℝ) ^ A.card := pow_le_pow_right₀ (by norm_num) hcard

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

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem sourceIdeal_union (S T : Finset ι) (hst : Disjoint S T) :
    sourceIdeal p (S∪T)=sourceIdeal p S*sourceIdeal p T := by
  simp only [sourceIdeal,Finset.prod_union hst,Ideal.span_singleton_mul_span_singleton]

end SevenEighths.InverseInitialArithmetic

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

private theorem physicalKernel_vector (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ))
    (Z D m q₀ q₁ q₂ q₃ q₄ q₅ : ℝ) :
    physicalKernel W₁ W₂ Φ Z D m ![q₀,q₁,q₂,q₃,q₄,q₅] =
      ((Z^(-D)*Z^m/(q₁*q₂*Real.sqrt (q₄*q₅)) : ℝ) : ℂ)*
        W₁ (q₀*q₂*q₄/Z^D)*W₂ (q₀*q₂*q₅/Z^D)*
          paperRadialFourier Φ (Z^m*q₃/(q₁*q₂^2*q₄*q₅)) := rfl

theorem physicalKernel_common_factor (C d s n₁ n₂ : Ideal Eis) (h : Eis)
    (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (Z D m : ℝ) :
    physicalKernel W₁ W₂ Φ Z D m (physicalCoordinates C d 1 (s*n₁) (s*n₂) h) =
      physicalKernel W₁ W₂ Φ Z D m (physicalCoordinates C d s n₁ n₂ h) := by
  have hroot : Real.sqrt ((N s*N n₁)*(N s*N n₂)) = N s*Real.sqrt (N n₁*N n₂) := by
    rw [show (N s*N n₁)*(N s*N n₂) = (N s)^2*(N n₁*N n₂) from by ring_nf,
      Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq_eq_abs,abs_of_nonneg (Nat.cast_nonneg _)]
  unfold physicalCoordinates
  rw [physicalKernel_vector,physicalKernel_vector]
  simp only [map_one,Nat.cast_one,map_mul,Nat.cast_mul,mul_one,one_pow]
  rw [hroot]
  have hl : N C*(N s*N n₁)/Z^D = N C*N s*N n₁/Z^D := by ring_nf
  have hr : N C*(N s*N n₂)/Z^D = N C*N s*N n₂/Z^D := by ring_nf
  have hk : Z^m*‖eisEmbedding h‖^2/(N d*(N s*N n₁)*(N s*N n₂)) =
      Z^m*‖eisEmbedding h‖^2/(N d*(N s)^2*N n₁*N n₂) := by ring_nf
  rw [hl,hr,hk]
  push_cast
  ring_nf

open InverseInitialArithmetic SecondPassArithmetic

end SevenEighths.InverseInitialKernelBridge

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

end SevenEighths.InverseInitialEnergyCallerWeights

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialHighFrequencyTailKernel
namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseInitialHighFrequencyTail
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
open InverseInitialProfile
local notation "O" => ActualEisensteinCubic.O

private theorem finite_sum_le_tsum_subtype (F : Finset O) (P : O → Prop)
    (hF : ∀ h ∈ F, P h) (b : O → ℝ) (hb : ∀ h, 0 ≤ b h)
    (hs : Summable (fun h : {h // P h} => b h.val)) :
    (∑ h ∈ F, b h) ≤ ∑' h : {h // P h}, b h.val := by
  let f : F → {h // P h} := fun h => ⟨h.val, hF h.val h.property⟩
  have hf : Function.Injective f := by
    intro x y h
    exact Subtype.ext (congrArg (fun z : {h // P h} => z.val) h)
  rw [← Finset.sum_coe_sort F]
  have ht : Summable (fun h : F => b h.val) := (hasSum_fintype _).summable
  simpa only [tsum_fintype] using
    ht.tsum_le_tsum_of_inj f hf (fun h _ => hb h.val) (fun _ => le_rfl) hs

theorem finite_radial_tail (A : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ), 0<C ∧
    ∀ (Φ : 𝓢(ℝ,ℂ)) (K T Γ : ℝ), 0<K → 0≤T → 0≤Γ →
    ∀ (F : Finset O) (a : O→ℂ),
    (∀h∈F,T≤K*‖eisEmbedding h‖^2) →
    (∀h∈F,‖a h‖≤Γ) →
    ‖∑h∈F,a h*paperRadialFourier Φ (K*‖eisEmbedding h‖^2)‖ ≤
      Γ*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ)/
        ((min 1 K)^2*(1+T)^A) := by
  obtain ⟨s,C,hC,hbound⟩ := paperRadialFourier_lattice_tail A
  refine ⟨s,C,hC,?_⟩
  intro Φ K T Γ hK hT hΓ F a hF ha
  have hsum := finite_sum_le_tsum_subtype F
    (fun h => T ≤ K * ‖eisEmbedding h‖^2) hF
    (fun h => ‖paperRadialFourier Φ (K * ‖eisEmbedding h‖^2)‖)
    (fun _ => norm_nonneg _)
    ((paperRadialFourier_lattice_summable_norm Φ K hK).subtype
      (fun h => T ≤ K * ‖eisEmbedding h‖^2))
  calc
    _ ≤ ∑h∈F,‖a h*paperRadialFourier Φ (K*‖eisEmbedding h‖^2)‖ := norm_sum_le _ _
    _ ≤ ∑h∈F,Γ*‖paperRadialFourier Φ (K*‖eisEmbedding h‖^2)‖ := by
      apply Finset.sum_le_sum
      intro h hh
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (ha h hh) (norm_nonneg _)
    _ = Γ*∑h∈F,‖paperRadialFourier Φ (K*‖eisEmbedding h‖^2)‖ := by rw [Finset.mul_sum]
    _ ≤ Γ*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ /
        ((min 1 K)^2*(1+T)^A)) :=
      mul_le_mul_of_nonneg_left (hsum.trans (hbound Φ K T hK hT)) hΓ
    _ = _ := by ring

theorem physicalKernel_frequency (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ))
    (Z D m C d v n₁ n₂ : ℝ) (h : O) :
    physicalKernel W₁ W₂ Φ Z D m ![C,d,v,‖eisEmbedding h‖^2,n₁,n₂] =
      ((Z^(-D)*Z^m/(d*v*Real.sqrt (n₁*n₂)):ℝ):ℂ)*
      W₁ (C*v*n₁/Z^D)*W₂ (C*v*n₂/Z^D)*
      paperRadialFourier Φ ((Z^m/(d*v^2*n₁*n₂))*‖eisEmbedding h‖^2) := by
  simp [physicalKernel, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

theorem physical_frequency_tail (A : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C₀ : ℝ), 0<C₀ ∧
    ∀ (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ))
      (Z D m C d v n₁ n₂ T Γ : ℝ),
    0<Z → 0<d → 0<v → 0<n₁ → 0<n₂ → 0≤T → 0≤Γ →
    ∀ (F : Finset O) (a : O→ℂ),
    (∀h∈F,T≤(Z^m/(d*v^2*n₁*n₂))*‖eisEmbedding h‖^2) →
    (∀h∈F,‖a h‖≤Γ) →
    ‖∑h∈F,a h*physicalKernel W₁ W₂ Φ Z D m
      ![C,d,v,‖eisEmbedding h‖^2,n₁,n₂]‖ ≤
      Γ*‖((Z^(-D)*Z^m/(d*v*Real.sqrt (n₁*n₂)):ℝ):ℂ)*
        W₁ (C*v*n₁/Z^D)*W₂ (C*v*n₂/Z^D)‖ *
      (C₀*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ)/
        ((min 1 (Z^m/(d*v^2*n₁*n₂)))^2*(1+T)^A) := by
  obtain ⟨s,C₀,hC₀,hbound⟩ := finite_radial_tail A
  refine ⟨s,C₀,hC₀,?_⟩
  intro W₁ W₂ Φ Z D m C d v n₁ n₂ T Γ hZ hd hv hn₁ hn₂ hT hΓ F a hF ha
  let b : ℂ := ((Z^(-D)*Z^m/(d*v*Real.sqrt (n₁*n₂)):ℝ):ℂ)*
        W₁ (C*v*n₁/Z^D)*W₂ (C*v*n₂/Z^D)
  simp_rw [physicalKernel_frequency,←mul_assoc]
  simpa only [b,←mul_assoc] using hbound Φ (Z^m/(d*v^2*n₁*n₂)) T (Γ*‖b‖) (by positivity) hT
    (by positivity) F (fun h=>a h*b) hF (by
      intro h hh
      exact (norm_mul _ _).trans_le (mul_le_mul_of_nonneg_right (ha h hh) (norm_nonneg _)))

end SevenEighths.InverseInitialHighFrequencyTail

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialHighFrequencyTailWeights
namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.InverseInitialHighFrequencyTail
open ActualEisensteinCubic FirstPassCubeLabels FirstCauchyArithmetic SecondPassArithmetic
open InverseMoment InverseInitialArithmetic InverseInitialEnergyCallerWeights
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι]

theorem marked_support_norm_bound
    (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (hdis : (slots:Set σ).PairwiseDisjoint lists)
    (ha : ∀i∈slots,∀k∈lists i,‖a i k‖≤1)
    (S : Finset ι) (L : ℝ) (hL : 1≤L) (hS : primeProductNorm p S≤L) :
    ‖primeMark slots lists a S‖≤128*L := by
  have heq : boundedPrimeSupports p S L=S.powerset := by
    apply Finset.filter_eq_self.mpr
    intro U hU
    exact (primeProductNorm_mono p hp (Finset.mem_powerset.mp hU)).trans hS
  have hc := boundedPrimeSupports_card p hinj S L hL
  rw [heq,Finset.card_powerset] at hc
  exact (primeMark_norm_le_divisor_count slots lists a S hdis ha).trans (by exact_mod_cast hc)

theorem initialColumn_mark_factor
    (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (Ψ : O→*ℂ) (j C d h : O) (H : Finset ι→ℂ) (S : Finset ι) :
    initialColumn p hp hcop hg Ψ j C d h H S =
      initialColumn p hp hcop hg Ψ j C d h (fun _=>1) S * H S := by
  simp only [initialColumn,mul_one]

theorem initialColumn_mark_norm
    (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (Ψ : O→*ℂ) (hΨ : ∀n,‖Ψ n‖≤1)
    (j C d h : O) (H : Finset ι→ℂ) (S : Finset ι) :
    ‖initialColumn p hp hcop hg Ψ j C d h H S‖≤‖H S‖ := by
  rw [initialColumn_mark_factor,norm_mul]
  exact (mul_le_mul_of_nonneg_right
    ((initialColumn_norm_le p hp hcop hg hc Ψ j C d h S).trans (hΨ _))
    (norm_nonneg _)).trans_eq (one_mul _)

end SevenEighths.InverseInitialHighFrequencyTail

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialHighFrequencyTailSource
namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.InverseInitialHighFrequencyTail
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseInitialPhysicalMeasure
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]

omit [DecidableEq ι] in
theorem sourcePoint_key (x : Point ι) : sourcePoint (sourceKey x) x.frequency=x := by
  cases x
  rfl

theorem mem_sourceFrequencies (S : Finset (Point ι)) (k : Fin 5→Finset ι) (h : O) :
    h∈sourceFrequencies S k ↔ sourcePoint k h∈S := by
  constructor
  · intro hh
    obtain ⟨x,hx,he⟩ := Finset.mem_image.mp hh
    obtain ⟨hx,hk⟩ := Finset.mem_filter.mp hx
    rw [←hk,←he,sourcePoint_key]
    exact hx
  · intro hh
    apply Finset.mem_image.mpr
    refine ⟨sourcePoint k h,Finset.mem_filter.mpr ⟨hh,?_⟩,rfl⟩
    funext i
    fin_cases i <;> rfl

theorem source_sum_fibers (S : Finset (Point ι)) (f : Point ι→ℂ) :
    ∑x∈S,f x = ∑k∈sourceKeys S,∑h∈sourceFrequencies S k,f (sourcePoint k h) := by
  rw [←Finset.sum_fiberwise_of_maps_to (s:=S) (t:=sourceKeys S) (g:=sourceKey)
    (fun x hx=>Finset.mem_image.mpr ⟨x,hx,rfl⟩) f]
  apply Finset.sum_congr rfl
  intro k hk
  rw [sourceFrequencies,Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro x hx
    rw [←(Finset.mem_filter.mp hx).2,sourcePoint_key]
  · intro x hx y hy hxy
    have hk := (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm
    rw [←sourcePoint_key x,←sourcePoint_key y,hk,hxy]

theorem sourceKeys_card
    (p : ι→O) (_hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (pool : Finset ι) (S : Finset (Point ι)) (L : ℝ) (hL : 1≤L)
    (hpool : ∀x∈S,∀i,sourceKey x i⊆pool)
    (hnorm : ∀x∈S,∀i,primeProductNorm p (sourceKey x i)≤L) :
    ((sourceKeys S).card:ℝ)≤(128*L)^5 := by
  let T := boundedPrimeSupports p pool L
  have hsub : sourceKeys S⊆Fintype.piFinset (fun _ : Fin 5=>T) := by
    intro k hk
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hk
    rw [Fintype.mem_piFinset]
    intro i
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (hpool x hx i),hnorm x hx i⟩
  have hc := Finset.card_le_card hsub
  have hcast : ((sourceKeys S).card:ℝ)≤(T.card:ℝ)^5 := by
    exact_mod_cast (by simpa using hc)
  exact hcast.trans (pow_le_pow_left₀ (by positivity)
    (boundedPrimeSupports_card p hinj pool L hL) 5)

end SevenEighths.InverseInitialHighFrequencyTail

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialHighFrequencyTailAggregate
namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.InverseInitialHighFrequencyTail
open InverseInitialPhysicalMeasure

theorem original_source_norm_fibers
    {ι ρ : Type*} [DecidableEq ι]
    (S : Finset (Point ι)) (R : Finset ρ) (f : Point ι→ρ→ℂ) (b : ρ→ℝ)
    (hb : ∀k∈sourceKeys S,∀r∈R,
      ‖∑h∈sourceFrequencies S k,f (sourcePoint k h) r‖≤b r) :
    ‖∑x∈S,∑r∈R,f x r‖≤((sourceKeys S).card:ℝ)*(∑r∈R,b r) := by
  rw [source_sum_fibers]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑k∈sourceKeys S,∑r∈R,b r := by
      apply Finset.sum_le_sum
      intro k hk
      rw [Finset.sum_comm]
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun r hr=>hb k hk r hr))
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]

end SevenEighths.InverseInitialHighFrequencyTail

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialHighFrequencyTailCoefficient
namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.InverseInitialHighFrequencyTail
open ActualEisensteinCubic FirstPassCubeLabels FirstCauchyArithmetic SecondPassArithmetic
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure
open InverseInitialEnergyCallerWeights InverseInitialProfile InverseInitialKernelBridge InverseInitialRayAttachment
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

include hp hcop hg in
theorem physicalTerm_original_coefficient
    (Ψ : O→*ℂ) (j : O) (mark : Finset ι→ℂ)
    (W₁ W₂ : ℝ→ℂ) (Φ : SchwartzMap ℝ ℂ) (Z D m : ℝ)
    (x : Point ι) (hx : Valid x) (ρ : SecondRayIndex) :
    physicalTerm p hp hcop hg Ψ j mark W₁ W₂ Φ Z D m x ρ =
      originalCoefficient p hp hcop hg Ψ j mark x ρ *
      physicalKernel W₁ W₂ Φ Z D m (coordinates p x) := by
  unfold physicalTerm
  rw [sourceIdeal_union p _ _ hx.overlap_left,sourceIdeal_union p _ _ hx.overlap_right,
    physicalKernel_common_factor]
  rfl

include hp hcop hg in
theorem originalCoefficient_marked_bound
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (Ψ : O→*ℂ) (hΨ : ∀n,‖Ψ n‖≤1) (j : O)
    (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (hdis : (slots:Set σ).PairwiseDisjoint lists)
    (ha : ∀i∈slots,∀k∈lists i,‖a i k‖≤1)
    (x : Point ι) (ρ : SecondRayIndex) (L : ℝ) (hL : 1≤L)
    (hleft : primeProductNorm p x.common*primeProductNorm p x.overlap*
      primeProductNorm p x.left≤L)
    (hright : primeProductNorm p x.common*primeProductNorm p x.overlap*
      primeProductNorm p x.right≤L) :
    ‖originalCoefficient p hp hcop hg Ψ j (primeMark slots lists a) x ρ‖≤
      ‖secondRayCoefficient ρ‖*(128*L)^2 := by
  have hmark (N : Finset ι)
      (hN : primeProductNorm p x.common*primeProductNorm p x.overlap*primeProductNorm p N≤L) :
      ‖primeMark slots lists a (x.common∪(x.overlap∪N))‖≤128*L := by
    apply marked_support_norm_bound p hp hinj slots lists a hdis ha _ L hL
    apply (primeProductNorm_union_le_mul p hp _ _).trans
    apply (mul_le_mul_of_nonneg_left (primeProductNorm_union_le_mul p hp _ _)
      (primeProductNorm_pos p hp _).le).trans
    simpa only [mul_assoc] using hN
  have hl := (initialColumn_mark_norm p hp hcop hg hc (secondRayMinus Ψ ρ)
    (fun n=>(secondRayMinus_norm_le Ψ ρ n).trans (hΨ n)) j (∏i∈x.common,p i)
    (divisor p x) x.frequency (fun A=>primeMark slots lists a (x.common∪A))
    (x.overlap∪x.left)).trans (hmark x.left hleft)
  have hr := (initialColumn_mark_norm p hp hcop hg hc (secondRayPlus Ψ ρ)
    (fun n=>(secondRayPlus_norm_le Ψ ρ n).trans (hΨ n)) j (∏i∈x.common,p i)
    (divisor p x) (-x.frequency) (fun A=>primeMark slots lists a (x.common∪A))
    (x.overlap∪x.right)).trans (hmark x.right hright)
  have hb := initialBeta_norm_le_one p Ψ hΨ j x.common
  have hm := QuadraticInitialBound.norm_ideal_moebius_le_one (sourceIdeal p x.divisor)
  have hv : ‖supportMobius (fun i=>Ideal.span {p i}) x.overlap‖≤1 :=
    QuadraticInitialBound.norm_ideal_moebius_le_one _
  simp only [originalCoefficient,norm_mul,norm_star]
  calc
    _ ≤ 1*1*1*‖secondRayCoefficient ρ‖*(128*L)*(128*L) := by gcongr
    _ = _ := by ring

end SevenEighths.InverseInitialHighFrequencyTail

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialHighFrequencyTailScale
namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseInitialHighFrequencyTail
open ActualEisensteinCubic ConcreteTraceCRT InverseInitialProfile
local notation "O"=>ActualEisensteinCubic.O

theorem initial_denominator_bound (C d v n₁ n₂ L : ℝ)
    (hC : 1≤C) (_hd : 0≤d) (hv : 0≤v) (hn₁ : 0≤n₁) (hn₂ : 0≤n₂)
    (hL : 0≤L) (hdL : d≤L) (h₁ : C*v*n₁≤L) (h₂ : C*v*n₂≤L) :
    d*v^2*n₁*n₂≤L^3 := by
  have h₁' : v*n₁≤L := by nlinarith [mul_nonneg (sub_nonneg.mpr hC) (mul_nonneg hv hn₁)]
  have h₂' : v*n₂≤L := by nlinarith [mul_nonneg (sub_nonneg.mpr hC) (mul_nonneg hv hn₂)]
  have hh := mul_le_mul h₁' h₂' (mul_nonneg hv hn₂) hL
  have he := mul_le_mul hdL hh (by positivity) hL
  nlinarith

theorem initial_scalar_bound (Z D m d v n₁ n₂ : ℝ) (hZ : 0<Z)
    (hd : 1≤d) (hv : 1≤v) (hn₁ : 1≤n₁) (hn₂ : 1≤n₂) :
    ‖((Z^(-D)*Z^m/(d*v*Real.sqrt (n₁*n₂)):ℝ):ℂ)‖≤Z^(m-D) := by
  have hroot : 1≤Real.sqrt (n₁*n₂) := by
    rw [Real.one_le_sqrt]
    exact one_le_mul_of_one_le_of_one_le hn₁ hn₂
  have hden : 1≤d*v*Real.sqrt (n₁*n₂) :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hd hv) hroot
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  have h := div_le_self (show 0≤Z^(-D)*Z^m by positivity) hden
  apply h.trans_eq
  rw [←Real.rpow_add hZ]
  congr 1
  ring

theorem physical_frequency_tail_uniform (A : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C₀ : ℝ), 0<C₀ ∧
    ∀ (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ))
      (Z D m C d v n₁ n₂ L T Γ B₁ B₂ : ℝ),
    0<Z → 1≤C → 1≤d → 1≤v → 1≤n₁ → 1≤n₂ → 1≤L →
    d≤L → C*v*n₁≤L → C*v*n₂≤L → 0≤T → 0≤Γ → 0≤B₁ → 0≤B₂ →
    ‖W₁ (C*v*n₁/Z^D)‖≤B₁ → ‖W₂ (C*v*n₂/Z^D)‖≤B₂ →
    ∀ (F : Finset O) (a : O→ℂ),
    (∀h∈F,T≤(Z^m/(d*v^2*n₁*n₂))*‖eisEmbedding h‖^2) →
    (∀h∈F,‖a h‖≤Γ) →
    ‖∑h∈F,a h*physicalKernel W₁ W₂ Φ Z D m
      ![C,d,v,‖eisEmbedding h‖^2,n₁,n₂]‖ ≤
      Γ*Z^(m-D)*B₁*B₂*(C₀*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ)/
        ((min 1 (Z^m/L^3))^2*(1+T)^A) := by
  obtain ⟨s,C₀,hC₀,hbound⟩ := physical_frequency_tail A
  refine ⟨s,C₀,hC₀,?_⟩
  intro W₁ W₂ Φ Z D m C d v n₁ n₂ L T Γ B₁ B₂ hZ hC hd hv hn₁ hn₂ hL
    hdL h₁ h₂ hT hΓ hB₁ hB₂ hw₁ hw₂ F a hF ha
  have hd0 : 0<d := zero_lt_one.trans_le hd
  have hv0 : 0<v := zero_lt_one.trans_le hv
  have hn₁0 : 0<n₁ := zero_lt_one.trans_le hn₁
  have hn₂0 : 0<n₂ := zero_lt_one.trans_le hn₂
  have hL0 : 0<L := zero_lt_one.trans_le hL
  have hden := initial_denominator_bound C d v n₁ n₂ L hC hd0.le hv0.le hn₁0.le hn₂0.le hL0.le hdL h₁ h₂
  have hK : Z^m/L^3≤Z^m/(d*v^2*n₁*n₂) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) hden
  have hscalar := initial_scalar_bound Z D m d v n₁ n₂ hZ hd hv hn₁ hn₂
  apply (hbound W₁ W₂ Φ Z D m C d v n₁ n₂ T Γ hZ hd0 hv0 hn₁0 hn₂0 hT hΓ F a hF ha).trans
  simp only [norm_mul]
  have hnorm : ‖((Z^(-D)*Z^m/(d*v*Real.sqrt (n₁*n₂)):ℝ):ℂ)‖*
      ‖W₁ (C*v*n₁/Z^D)‖*‖W₂ (C*v*n₂/Z^D)‖ ≤ Z^(m-D)*B₁*B₂ := by gcongr
  calc
    _ ≤ Γ*(Z^(m-D)*B₁*B₂)*(C₀*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ)/
        ((min 1 (Z^m/L^3))^2*(1+T)^A) := by
      gcongr
    _ = _ := by ring

end SevenEighths.InverseInitialHighFrequencyTail

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialHighFrequencyTailFiber
namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseInitialHighFrequencyTail
open ActualEisensteinCubic ConcreteTraceCRT FirstPassCubeLabels SecondPassArithmetic
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure
open InverseInitialKernelBridge InverseInitialProfile
local notation "O"=>ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]

omit [DecidableEq ι] in
theorem coordinates_sourcePoint (p : ι→O) (k : Fin 5→Finset ι) (h : O) :
    coordinates p (sourcePoint k h)=
      ![keyNorms p k 0,keyNorms p k 1,keyNorms p k 2,‖eisEmbedding h‖^2,
        keyNorms p k 3,keyNorms p k 4] := by
  have hn (A : Finset ι) : ((sourceIdeal p A).absNorm:ℝ)=primeProductNorm p A := by
    rw [sourceIdeal,←eisEmbedding_norm_sq_eq_absNorm_span]
    rfl
  funext i
  fin_cases i <;> simp [coordinates,sourcePoint,physicalCoordinates,keyNorms,hn]

theorem original_frequency_fiber_tail (A : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C₀ : ℝ), 0<C₀ ∧
    ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (Ψ : O→*ℂ), (∀n,‖Ψ n‖≤1) → ∀ (j : O)
      (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ),
    (slots:Set σ).PairwiseDisjoint lists → (∀i∈slots,∀k∈lists i,‖a i k‖≤1) →
    ∀ (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (Z D m L T Γ B₁ B₂ : ℝ),
    0<Z → 1≤L → 0≤T → 0≤Γ → 0≤B₁ → 0≤B₂ →
    (∀x,‖W₁ x‖≤B₁) → (∀x,‖W₂ x‖≤B₂) →
    ∀ (k : Fin 5→Finset ι) (F : Finset O) (w : Point ι→ℂ) (ρ : SecondRayIndex),
    keyNorms p k 1≤L →
    keyNorms p k 0*keyNorms p k 2*keyNorms p k 3≤L →
    keyNorms p k 0*keyNorms p k 2*keyNorms p k 4≤L →
    (∀h∈F,Valid (sourcePoint k h)) → (∀h∈F,‖w (sourcePoint k h)‖≤Γ) →
    (∀h∈F,T≤(Z^m/(keyNorms p k 1*(keyNorms p k 2)^2*
      keyNorms p k 3*keyNorms p k 4))*‖eisEmbedding h‖^2) →
    ‖∑h∈F,w (sourcePoint k h)*physicalTerm p hp hcop hg Ψ j
      (primeMark slots lists a) W₁ W₂ Φ Z D m (sourcePoint k h) ρ‖ ≤
    (Γ*‖secondRayCoefficient ρ‖*(128*L)^2)*Z^(m-D)*B₁*B₂*
      (C₀*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ)/
      ((min 1 (Z^m/L^3))^2*(1+T)^A) := by
  obtain ⟨s,C₀,hC₀,hbound⟩ := physical_frequency_tail_uniform A
  refine ⟨s,C₀,hC₀,?_⟩
  intro ι σ _ _ p hp _ hcop hg hinj hc Ψ hΨ j slots lists a hdis ha
    W₁ W₂ Φ Z D m L T Γ B₁ B₂ hZ hL hT hΓ hB₁ hB₂ hW₁ hW₂ k F w ρ hd hleft hright hvalid hw htail
  have hn (i : Fin 5) : 1≤keyNorms p k i := primeProductNorm_ge_one p hp _
  have he : (∑h∈F,w (sourcePoint k h)*physicalTerm p hp hcop hg Ψ j
      (primeMark slots lists a) W₁ W₂ Φ Z D m (sourcePoint k h) ρ) =
      ∑h∈F,(w (sourcePoint k h)*originalCoefficient p hp hcop hg Ψ j
        (primeMark slots lists a) (sourcePoint k h) ρ)*
        physicalKernel W₁ W₂ Φ Z D m
        ![keyNorms p k 0,keyNorms p k 1,keyNorms p k 2,‖eisEmbedding h‖^2,
          keyNorms p k 3,keyNorms p k 4] := by
    apply Finset.sum_congr rfl
    intro h hh
    rw [physicalTerm_original_coefficient p hp hcop hg Ψ j _ W₁ W₂ Φ Z D m _ (hvalid h hh) ρ,
      coordinates_sourcePoint]
    ring
  rw [he]
  apply hbound W₁ W₂ Φ Z D m (keyNorms p k 0) (keyNorms p k 1)
    (keyNorms p k 2) (keyNorms p k 3) (keyNorms p k 4) L T
    (Γ*‖secondRayCoefficient ρ‖*(128*L)^2) B₁ B₂ hZ (hn 0) (hn 1) (hn 2)
    (hn 3) (hn 4) hL hd hleft hright hT (by positivity) hB₁ hB₂ (hW₁ _) (hW₂ _) F _ htail
  intro h hh
  rw [norm_mul]
  have hc := originalCoefficient_marked_bound p hp hcop hg hinj hc Ψ hΨ j slots lists a
    hdis ha (sourcePoint k h) ρ L hL hleft hright
  calc
    _ ≤ Γ*(‖secondRayCoefficient ρ‖*(128*L)^2) := by gcongr; exact hw h hh
    _ = _ := by ring

end SevenEighths.InverseInitialHighFrequencyTail

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialHighFrequencyTail
namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseInitialHighFrequencyTail
open ActualEisensteinCubic ConcreteTraceCRT FirstPassCubeLabels SecondPassArithmetic
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure
local notation "O"=>ActualEisensteinCubic.O

theorem original_physical_tail (A : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C₀ : ℝ), 0<C₀ ∧
    ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (Ψ : O→*ℂ), (∀n,‖Ψ n‖≤1) → ∀ (j : O)
      (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ),
    (slots:Set σ).PairwiseDisjoint lists → (∀i∈slots,∀k∈lists i,‖a i k‖≤1) →
    ∀ (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (Z D m L T Γ B₁ B₂ : ℝ),
    0<Z → 1≤L → 0≤T → 0≤Γ → 0≤B₁ → 0≤B₂ →
    (∀x,‖W₁ x‖≤B₁) → (∀x,‖W₂ x‖≤B₂) →
    ∀ (pool : Finset ι) (S : Finset (Point ι)) (w : Point ι→ℂ),
    (∀x∈S,Valid x) → (∀x∈S,‖w x‖≤Γ) →
    (∀x∈S,∀i,sourceKey x i⊆pool) →
    (∀x∈S,∀i,primeProductNorm p (sourceKey x i)≤L) →
    (∀x∈S,primeProductNorm p x.common*primeProductNorm p x.overlap*primeProductNorm p x.left≤L) →
    (∀x∈S,primeProductNorm p x.common*primeProductNorm p x.overlap*primeProductNorm p x.right≤L) →
    (∀x∈S,T≤(Z^m/(primeProductNorm p x.divisor*(primeProductNorm p x.overlap)^2*
      primeProductNorm p x.left*primeProductNorm p x.right))*‖eisEmbedding x.frequency‖^2) →
    ‖physicalBlock p hp hcop hg S w Ψ j (primeMark slots lists a) W₁ W₂ Φ Z D m‖ ≤
      (128*L)^7*Γ*(∑ρ : SecondRayIndex,‖secondRayCoefficient ρ‖)*Z^(m-D)*B₁*B₂*
        (C₀*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ)/
        ((min 1 (Z^m/L^3))^2*(1+T)^A) := by
  obtain ⟨s,C₀,hC₀,hfiber⟩ := original_frequency_fiber_tail A
  refine ⟨s,C₀,hC₀,?_⟩
  intro ι σ _ _ p hp _ hcop hg hinj hc Ψ hΨ j slots lists a hdis ha W₁ W₂ Φ
    Z D m L T Γ B₁ B₂ hZ hL hT hΓ hB₁ hB₂ hW₁ hW₂ pool S w hvalid hw hpool hnorm hleft hright htail
  let R : ℝ := Z^(m-D)*B₁*B₂*(C₀*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ)/
    ((min 1 (Z^m/L^3))^2*(1+T)^A)
  have hR : 0≤R := by dsimp [R]; positivity
  let B : ℝ := Γ*(128*L)^2*R
  have hB : 0≤B := by dsimp [B]; positivity
  have hkey (k) (hk : k∈sourceKeys S) (ρ : SecondRayIndex) :
      ‖∑h∈sourceFrequencies S k,
        w (sourcePoint k h)*physicalTerm p hp hcop hg Ψ j (primeMark slots lists a)
          W₁ W₂ Φ Z D m (sourcePoint k h) ρ‖ ≤ B*‖secondRayCoefficient ρ‖ := by
    obtain ⟨x,hx,hk'⟩ := Finset.mem_image.mp hk
    have hkN (i) : keyNorms p k i=primeProductNorm p (sourceKey x i) := by rw [←hk'];rfl
    have hf (h) (hh : h∈sourceFrequencies S k) := (mem_sourceFrequencies S k h).mp hh
    have hkl : keyNorms p k 0*keyNorms p k 2*keyNorms p k 3≤L := by
      simpa [←hk',keyNorms,sourceKey] using hleft x hx
    have hkr : keyNorms p k 0*keyNorms p k 2*keyNorms p k 4≤L := by
      simpa [←hk',keyNorms,sourceKey] using hright x hx
    have htailk : ∀h∈sourceFrequencies S k,T≤(Z^m/(keyNorms p k 1*(keyNorms p k 2)^2*
        keyNorms p k 3*keyNorms p k 4))*‖eisEmbedding h‖^2 := by
      intro h hh
      simpa only [sourcePoint,keyNorms] using htail (sourcePoint k h) (hf h hh)
    have hb := hfiber p hp hcop hg hinj hc Ψ hΨ j slots lists a hdis ha W₁ W₂ Φ
      Z D m L T Γ B₁ B₂ hZ hL hT hΓ hB₁ hB₂ hW₁ hW₂ k (sourceFrequencies S k) w ρ
      (by rw [hkN];exact hnorm x hx 1) hkl hkr
      (fun h hh=>hvalid (sourcePoint k h) (hf h hh))
      (fun h hh=>hw (sourcePoint k h) (hf h hh)) htailk
    apply hb.trans_eq
    dsimp [B,R]
    ring
  have hsum := original_source_norm_fibers S Finset.univ
    (fun x ρ=>w x*physicalTerm p hp hcop hg Ψ j (primeMark slots lists a) W₁ W₂ Φ Z D m x ρ)
    (fun ρ=>B*‖secondRayCoefficient ρ‖) (fun k hk ρ _=>hkey k hk ρ)
  change ‖∑x∈S,∑ρ : SecondRayIndex,w x*physicalTerm p hp hcop hg Ψ j
    (primeMark slots lists a) W₁ W₂ Φ Z D m x ρ‖≤_
  apply hsum.trans
  rw [←Finset.mul_sum]
  calc
    _ ≤ (128*L)^5*(B*(∑ρ : SecondRayIndex,‖secondRayCoefficient ρ‖)) :=
      mul_le_mul_of_nonneg_right (sourceKeys_card p hp hinj pool S L hL hpool hnorm) (by positivity)
    _ = _ := by dsimp [B,R]; ring

end SevenEighths.InverseInitialHighFrequencyTail

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialHighFrequencyTailPower
namespace OAI

noncomputable section

namespace SevenEighths.InverseInitialHighFrequencyTail

theorem initial_tail_power_cost (A : ℕ) (Z L Lcap m D τ : ℝ)
    (hZ : 1≤Z) (hL : 1≤L) (hcap : 0≤Lcap) (hsize : L≤Z^Lcap)
    (hm : -m≤Lcap) (hmd : m-D≤Lcap) :
    (128*L)^7*Z^(m-D)/((min 1 (Z^m/L^3))^2*(1+Z^τ)^A) ≤
      128^7*Z^(16*Lcap-τ*A) := by
  have hz : 0<Z := zero_lt_one.trans_le hZ
  have hl : 0<L := zero_lt_one.trans_le hL
  have hbase : Z^(-4*Lcap)≤ min 1 (Z^m/L^3) := by
    apply le_min
    · exact Real.rpow_le_one_of_one_le_of_nonpos hZ (by linarith)
    · calc
        _ = Z^(-Lcap)/(Z^Lcap)^3 := by
          rw [←Real.rpow_mul_natCast hz.le,←Real.rpow_sub hz]
          congr 1
          norm_num
          ring
        _ ≤ Z^m/L^3 := by
          gcongr ; linarith
  calc
    _ ≤ (128*Z^Lcap)^7*Z^Lcap/((Z^(-4*Lcap))^2*(Z^τ)^A) := by
      gcongr ; linarith
    _ = 128^7*Z^(16*Lcap-τ*A) := by
      rw [mul_pow,←Real.rpow_mul_natCast hz.le,←Real.rpow_mul_natCast hz.le,
        ←Real.rpow_mul_natCast hz.le]
      rw [mul_assoc,←Real.rpow_add hz,←Real.rpow_add hz,mul_div_assoc,
        ←Real.rpow_sub hz]
      congr 2
      norm_num
      ring

theorem initial_tail_rapid_order (Lcap saving τ : ℝ) (hτ : 0<τ) :
    ∃ A : ℕ, ∀ (Z L m D : ℝ), 1≤Z → 1≤L → 0≤Lcap → L≤Z^Lcap →
      -m≤Lcap → m-D≤Lcap →
      (128*L)^7*Z^(m-D)/((min 1 (Z^m/L^3))^2*(1+Z^τ)^A) ≤
        128^7*Z^(-saving) := by
  obtain ⟨A,hA⟩ := exists_nat_gt ((16*Lcap+saving)/τ)
  refine ⟨A,?_⟩
  intro Z L m D hZ hL hcap hsize hm hmd
  apply (initial_tail_power_cost A Z L Lcap m D τ hZ hL hcap hsize hm hmd).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.rpow_le_rpow_of_exponent_le hZ
  have h := (div_lt_iff₀ hτ).mp hA
  nlinarith

end SevenEighths.InverseInitialHighFrequencyTail

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialHighFrequencyTailRapid
namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseInitialHighFrequencyTail
open ActualEisensteinCubic ConcreteTraceCRT FirstPassCubeLabels SecondPassArithmetic
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure
local notation "O"=>ActualEisensteinCubic.O

theorem original_physical_tail_rapid_oai (Lcap saving τ : ℝ) (hτ : 0<τ) :
    ∃ (s : Finset (ℕ×ℕ)) (C₀ : ℝ), 0<C₀ ∧
    ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (Ψ : O→*ℂ), (∀n,‖Ψ n‖≤1) → ∀ (j : O)
      (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ),
    (slots:Set σ).PairwiseDisjoint lists → (∀i∈slots,∀k∈lists i,‖a i k‖≤1) →
    ∀ (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (Z D m L Γ B₁ B₂ : ℝ),
    1≤Z → 1≤L → 0≤Lcap → L≤Z^Lcap → -m≤Lcap → m-D≤Lcap → 0≤Γ → 0≤B₁ → 0≤B₂ →
    (∀x,‖W₁ x‖≤B₁) → (∀x,‖W₂ x‖≤B₂) →
    ∀ (pool : Finset ι) (S : Finset (Point ι)) (w : Point ι→ℂ),
    (∀x∈S,Valid x) → (∀x∈S,‖w x‖≤Γ) →
    (∀x∈S,∀i,sourceKey x i⊆pool) →
    (∀x∈S,∀i,primeProductNorm p (sourceKey x i)≤L) →
    (∀x∈S,primeProductNorm p x.common*primeProductNorm p x.overlap*primeProductNorm p x.left≤L) →
    (∀x∈S,primeProductNorm p x.common*primeProductNorm p x.overlap*primeProductNorm p x.right≤L) →
    (∀x∈S,Z^τ≤(Z^m/(primeProductNorm p x.divisor*(primeProductNorm p x.overlap)^2*
      primeProductNorm p x.left*primeProductNorm p x.right))*‖eisEmbedding x.frequency‖^2) →
    ‖physicalBlock p hp hcop hg S w Ψ j (primeMark slots lists a) W₁ W₂ Φ Z D m‖ ≤
      C₀*Γ*B₁*B₂*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*Z^(-saving) := by
  obtain ⟨A,hA⟩ := initial_tail_rapid_order Lcap saving τ hτ
  obtain ⟨s,C₀,hC₀,hraw⟩ := original_physical_tail A
  let R : ℝ := ∑ρ : SecondRayIndex,‖secondRayCoefficient ρ‖
  have hR : 0≤R := Finset.sum_nonneg (fun _ _=>norm_nonneg _)
  refine ⟨s,128^7*(R+1)*C₀,by positivity,?_⟩
  intro ι σ _ _ p hp _ hcop hg hinj hc Ψ hΨ j slots lists a hdis ha W₁ W₂ Φ
    Z D m L Γ B₁ B₂ hZ hL hcap hsize hm hmd hΓ hB₁ hB₂ hW₁ hW₂ pool S w
    hvalid hw hpool hnorm hleft hright htail
  have hz : 0<Z := zero_lt_one.trans_le hZ
  have hb := hraw p hp hcop hg hinj hc Ψ hΨ j slots lists a hdis ha W₁ W₂ Φ
    Z D m L (Z^τ) Γ B₁ B₂ hz hL (by positivity) hΓ hB₁ hB₂ hW₁ hW₂
    pool S w hvalid hw hpool hnorm hleft hright htail
  have hs : 0≤ s.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ := apply_nonneg _ _
  apply hb.trans
  calc
    _ = ((128*L)^7*Z^(m-D)/((min 1 (Z^m/L^3))^2*(1+Z^τ)^A))*
        (Γ*R*B₁*B₂*C₀*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ) := by dsimp [R];ring
    _ ≤ (128^7*Z^(-saving))*(Γ*R*B₁*B₂*C₀*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ) :=
      mul_le_mul_of_nonneg_right (hA Z L m D hZ hL hcap hsize hm hmd) (by positivity)
    _ ≤ (128^7*Z^(-saving))*(Γ*(R+1)*B₁*B₂*C₀*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ) := by
      gcongr
      linarith
    _ = _ := by ring

end SevenEighths.InverseInitialHighFrequencyTail

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.SevenEighths.InverseInitialHighFrequencyTail.original_physical_tail_rapid_oai.{u_1, u_2} := @OAI.SevenEighths.InverseInitialHighFrequencyTail.original_physical_tail_rapid_oai.{u_1, u_2}
