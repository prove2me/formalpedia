-- Prove2me | solution 1 for OAI.SevenEighths.InverseMoment.first_whole_cube_rapid_physical_tail
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T22:44:19.474233+00:00
-- url     : https://prove2.me/submissions/e683f865-eee6-489f-a3e4-65ab63c40fc3

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIHecke78B007

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.LocalBrackets
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

open scoped BigOperators Classical SchwartzMap ContDiff
namespace FirstPassCubeLabels
open ActualEisensteinCubic
open MixedCrossSeparation (columnPrimeCoprime quadraticCrossPhase)
open FiniteGaussPhase (canonicalProductGauss)
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)

theorem blockRow_eq_product {ι : Type*} (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S : Finset ι) (e : ι → ℕ) (u : O) :
    blockRow p hg S e u = ∏ i ∈ S,
      (canonicalSextic (Ideal.span {p i}) (hg i) ^ e i) (Ideal.Quotient.mk (Ideal.span {p i}) u) :=
  Finset.prod_coe_sort S (fun i =>
    (canonicalSextic (Ideal.span {p i}) (hg i) ^ e i) (Ideal.Quotient.mk (Ideal.span {p i}) u))

end FirstPassCubeLabels

open scoped Classical BigOperators
open AddChar MulChar

open scoped Classical BigOperators
open AddChar MulChar

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.KernelEnergy
namespace OAI

noncomputable section

namespace FirstPassCubeLabels

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

section
open scoped BigOperators Classical
open ActualEisensteinCubic
open RayFourExpansion (RayCharacter crossCoeff)

theorem blockRow_norm_le_one {ι : Type*} (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (S : Finset ι) (e : ι → ℕ) (a : O) : ‖blockRow p hg S e a‖ ≤ 1 := by
  rw [blockRow_eq_product, norm_prod]
  calc
    _ ≤ ∏ i ∈ S, (1 : ℝ) := by
      apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
      intro i hi
      let : Fintype (O ⧸ Ideal.span {p i}) := Fintype.ofFinite _
      exact FiniteRayExpansion.norm_char_le_one _ _
    _ = 1 := by simp

end

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)
open EisensteinSchwartzPoisson (paperRadialFourier)
open FourierBridge (logPhase)

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.QuadraticSieve.PrimePools
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

open scoped BigOperators Classical SchwartzMap ContDiff
namespace SecondPassIntegration
open ActualEisensteinCubic JointLogSeparation FirstPassCubeLabels
open ConcreteTraceCRT (eisEmbedding)

lemma elementNorm_pos (a : O) (ha : a ≠ 0) : 0 < elementNorm a := by
  exact sq_pos_of_pos (norm_pos_iff.mpr (ConcreteTraceCRT.eisEmbedding_ne_zero ha))

end SecondPassIntegration

open scoped BigOperators Classical SchwartzMap

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

theorem columnLog_norm_upper {ι : Type*} (p : ι → O) (hp : ∀ i, p i ≠ 0)
    (X M : ℝ) (hX : 0 < X) (S : Finset ι) (hS : columnLog p X S ≤ M) :
    primeProductNorm p S ≤ X * Real.exp M := by
  have he := Real.exp_le_exp.mpr hS
  rw [columnLog, Real.exp_log (div_pos (primeProductNorm_pos p hp S) hX)] at he
  exact (div_le_iff₀ hX).mp he |>.trans_eq (mul_comm _ _)

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

theorem aLabel_left (p : ι → O) (x : CubeCoordinates ι) (hx : x.Admissible) :
    aLabel p x.support x.leftBit = ∏ i ∈ x.leftDivisor,p i := by
  simp only [aLabel,primeProduct,leftBit,FirstPassCubeLabels.bit,decide_eq_true_eq]
  simp_rw [apply_ite, pow_one, pow_zero]
  rw [← Finset.prod_filter]
  have he : x.support.filter (fun i => i ∈ x.leftDivisor)=x.leftDivisor := by
    ext i
    simp only [Finset.mem_filter]
    exact and_iff_right_of_imp (fun hi => hx.1 hi)
  rw [he]

theorem aLabel_right (p : ι → O) (x : CubeCoordinates ι) (hx : x.Admissible) :
    aLabel p x.support x.rightBit = ∏ i ∈ x.rightDivisor,p i := by
  simp only [aLabel,primeProduct,rightBit,FirstPassCubeLabels.bit,decide_eq_true_eq]
  simp_rw [apply_ite, pow_one, pow_zero]
  rw [← Finset.prod_filter]
  have he : x.support.filter (fun i => i ∈ x.rightDivisor)=x.rightDivisor := by
    ext i
    simp only [Finset.mem_filter]
    exact and_iff_right_of_imp (fun hi => hx.2 hi)
  rw [he]

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.MeanSquare.LogarithmicBins
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

namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (bit conductorExponent dilationExponent retained parity evenDouble
  primeProduct primeProductNorm aLabel dilationLabel jLabel j2Label squarefreeLabel cubeActiveSupport)
open ConcreteTraceCRT (eisEmbedding)

theorem local_first_conductor_bound (parityBit e₁ e₂ : Bool) (n : ℕ) (hn : 0<n) :
    (if conductorExponent parityBit e₁ e₂=0 then 0 else 1)+dilationExponent parityBit e₁ e₂+
      bit (retained parityBit e₁ e₂)≤bit e₁+bit e₂+2*n := by
  have h : (if conductorExponent parityBit e₁ e₂=0 then 0 else 1)+dilationExponent parityBit e₁ e₂+
      bit (retained parityBit e₁ e₂)≤bit e₁+bit e₂+2 := by
    cases parityBit <;> cases e₁ <;> cases e₂ <;> decide
  omega

variable {ι : Type*} [DecidableEq ι] (p : ι → O)

omit [DecidableEq ι] in
theorem firstActiveProduct_as_primeProduct (S : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) :
    (∏ i∈cubeActiveSupport S v ε₁ ε₂,p i)=
      primeProduct p S (fun i => if conductorExponent (parity (v i)) (ε₁ i) (ε₂ i)=0 then 0 else 1) := by
  unfold cubeActiveSupport primeProduct
  rw [Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro i hi
  by_cases h : conductorExponent (parity (v i)) (ε₁ i) (ε₂ i)=0 <;> simp [h]

variable [∀ i,(Ideal.span {p i}).IsMaximal]

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem first_conductor_product_dvd (S : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (hv : ∀ i∈S,0<v₁ i+v₂ i) :
    (∏ i∈cubeActiveSupport S (fun i => v₁ i+v₂ i) ε₁ ε₂,p i)*
      dilationLabel p S (fun i => v₁ i+v₂ i) ε₁ ε₂*jLabel p S (fun i => v₁ i+v₂ i) ε₁ ε₂ ∣
      aLabel p S ε₁*aLabel p S ε₂*(primeProduct p S v₁*primeProduct p S v₂)^2 := by
  rw [firstActiveProduct_as_primeProduct,← primeProduct_add]
  simp only [dilationLabel,jLabel,aLabel,primeProduct,← Finset.prod_pow,← Finset.prod_mul_distrib,← pow_mul,← pow_add]
  apply Finset.prod_dvd_prod_of_dvd
  intro i hi
  apply pow_dvd_pow
  simpa only [mul_comm] using local_first_conductor_bound (parity (v₁ i+v₂ i)) (ε₁ i) (ε₂ i) (v₁ i+v₂ i) (hv i hi)

variable (hp : ∀ i,p i≠0)
include hp in
omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem first_conductor_norm_bound (S : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (hv : ∀ i∈S,0<v₁ i+v₂ i) (B : ℝ) (hB : 0≤B)
    (hb₁ : ‖eisEmbedding (primeProduct p S v₁)‖^2≤B)
    (hb₂ : ‖eisEmbedding (primeProduct p S v₂)‖^2≤B) :
    ‖eisEmbedding (∏ i∈cubeActiveSupport S (fun i => v₁ i+v₂ i) ε₁ ε₂,p i)‖^2*
      ‖eisEmbedding (dilationLabel p S (fun i => v₁ i+v₂ i) ε₁ ε₂)‖^2*
      ‖eisEmbedding (jLabel p S (fun i => v₁ i+v₂ i) ε₁ ε₂)‖^2 ≤
    ‖eisEmbedding (aLabel p S ε₁)‖^2*‖eisEmbedding (aLabel p S ε₂)‖^2*B^4 := by
  have hn : aLabel p S ε₁*aLabel p S ε₂*(primeProduct p S v₁*primeProduct p S v₂)^2≠0 := by
    apply mul_ne_zero (mul_ne_zero (primeProduct_ne_zero p hp _ _) (primeProduct_ne_zero p hp _ _))
    exact pow_ne_zero _ (mul_ne_zero (primeProduct_ne_zero p hp _ _) (primeProduct_ne_zero p hp _ _))
  have h := element_norm_le_of_dvd hn (first_conductor_product_dvd p S v₁ v₂ ε₁ ε₂ hv)
  simp only [map_mul,map_pow,norm_mul,norm_pow,mul_pow] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hm := mul_le_mul hb₁ hb₂ (sq_nonneg _) hB
  have hs := pow_le_pow_left₀ (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hm 2
  convert (preTransparency := .instances) hs using 1 <;> ring

end
section

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm primeProduct aLabel dilationLabel jLabel cubeActiveSupport)
open ConcreteTraceCRT (eisEmbedding)

lemma first_row_numeric_bound (an en jn a1 a2 cn dn hn fn ell K B F : ℝ)
    (ha : 0≤an) (he : 0≤en) (hj : 0<jn) (h1 : 0<a1) (h2 : 0<a2) (hc : 0<cn)
    (hd : 0≤dn) (_hh : 0≤hn) (hf : 0≤fn) (hell : 0<ell) (hK : 0<K) (_hB : 0<B) (hF : 0<F)
    (hcon : an*en*jn≤a1*a2*B^4) (hfreq : hn≤ell^2*an*dn/(K*a1*a2*cn^2)) (hlabel : fn≤F) :
    hn*fn^2*en≤ell^2*B^4*F^2*dn/(K*cn^2*jn) := by
  have hratio : an*en/(a1*a2)≤B^4/jn := by
    apply (div_le_div_iff₀ (mul_pos h1 h2) hj).mpr
    nlinarith [hcon]
  calc
    hn*fn^2*en ≤ (ell^2*an*dn/(K*a1*a2*cn^2))*F^2*en := by
      apply mul_le_mul_of_nonneg_right _ he
      exact mul_le_mul hfreq (pow_le_pow_left₀ hf hlabel 2) (sq_nonneg _) (by positivity)
    _ = (ell^2*dn*F^2/(K*cn^2))*(an*en/(a1*a2)) := by
      field_simp

    _ ≤ (ell^2*dn*F^2/(K*cn^2))*(B^4/jn) := mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = _ := by ring

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]

end

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm primeProduct aLabel dilationLabel cubeActiveSupport)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]

end SecondPassArithmetic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.MeanSquare.PoissonSource
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

open scoped BigOperators

open scoped BigOperators Classical

open scoped BigOperators Classical SchwartzMap
namespace FirstPassCubeLabels
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)
open EisensteinSchwartzPoisson (paperRadialFourier)
open MixedCrossSeparation (columnCoefficient columnPrimeCoprime)

variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

lemma canonicalPairMode_summable (N P B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (C₁ C₂ : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ)) (V₁ V₂ : ℝ→ℂ)
    (X₁ X₂ K : ℝ) (hK : 0<K) (d : O) (hd : d≠0) :
    Summable (canonicalPairMode p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d) := by
  let S := (N∪P)∪cubeActiveSupport B v ε₁ ε₂
  let e := threeBlockExponent N P v ε₁ ε₂
  let t := K/(‖eisEmbedding d‖^2*primeProductNorm p S)
  have ht : 0<t := div_pos hK (mul_pos
    (sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hd))) (primeProductNorm_pos p hp S))
  have hs : Summable (fun h : O => paperRadialFourier W (t*‖eisEmbedding h‖^2)*star (blockRow p hg S e h)) := by
    apply Summable.of_norm
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
      (EisensteinSchwartzPoisson.paperRadialFourier_lattice_summable_norm W t ht)
    intro h
    rw [norm_mul,norm_star]
    exact mul_le_of_le_one_right (norm_nonneg _) (blockRow_norm_le_one p hg S e h)
  let a : ℂ := (V₁ (columnLog p X₁ N)*V₂ (columnLog p X₂ P))*
    ((K:ℂ)/(‖eisEmbedding (∏i∈S,p i)‖:ℂ))*
    (star (columnCoefficient p hp hcop hg N*C₁ N)*(columnCoefficient p hp hcop hg P*C₂ P)*
    FiniteGaussPhase.canonicalProductGauss (fun i:S => p i.val) (fun i=>hp i.val)
      (columnPrimeCoprime p hcop S) (fun i=>hg i.val) (fun i=>e i.val))*blockRow p hg S e d
  apply (hs.mul_left a).congr
  intro h
  dsimp only [canonicalPairMode,threeGaussRowFactor,a,t,S,e]
  have ht' : K/(‖eisEmbedding d‖^2*primeProductNorm p ((N∪P)∪cubeActiveSupport B v ε₁ ε₂))*
      ‖eisEmbedding h‖^2 = K*‖eisEmbedding h‖^2/(‖eisEmbedding d‖^2*
        primeProductNorm p ((N∪P)∪cubeActiveSupport B v ε₁ ε₂)) := by ring
  rw [ht']
  ring

end FirstPassCubeLabels

open scoped BigOperators Classical SchwartzMap

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.MeanSquare.SourceRemainders
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

open scoped BigOperators Classical SchwartzMap
namespace FirstPassCubeLabels

section
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)
open EisensteinSchwartzPoisson (paperRadialFourier)
open MixedCrossSeparation (columnCoefficient columnPrimeCoprime)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

lemma threeBlockExponent_ne_zero_on (N P B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool) :
    ∀i∈(N∪P)∪cubeActiveSupport B v ε₁ ε₂,threeBlockExponent N P v ε₁ ε₂ i≠0 := by
  intro i hi
  by_cases hn:i∈N
  · simp [threeBlockExponent,hn]
  by_cases hp':i∈P
  · simp [threeBlockExponent,hn,hp']
  · have hiC:i∈cubeActiveSupport B v ε₁ ε₂ := by simpa [hn,hp'] using hi
    simp only [threeBlockExponent,if_neg hn,if_neg hp']
    exact (ZMod.val_eq_zero _).not.mpr (Finset.mem_filter.mp hiC).2

lemma threeBlockExponent_lt_six_on (N P B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool) :
    ∀i∈(N∪P)∪cubeActiveSupport B v ε₁ ε₂,threeBlockExponent N P v ε₁ ε₂ i<6 := by
  intro i hi
  unfold threeBlockExponent
  split_ifs <;> first | omega | exact ZMod.val_lt _

lemma threeGaussRowFactor_norm_le
    (hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (N P B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (C₁ C₂ : Finset ι→ℂ) (d h : O) :
    ‖threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d h‖≤‖C₁ N‖*‖C₂ P‖ := by
  let S := (N∪P)∪cubeActiveSupport B v ε₁ ε₂
  let e := threeBlockExponent N P v ε₁ ε₂
  have hG := FiniteGaussPhase.norm_canonicalProductGauss
    (fun i:S=>p i.val) (fun i=>hp i.val) (columnPrimeCoprime p hcop S)
    (fun i=>hg i.val) (fun i=>hc i.val) (fun i=>e i.val)
    (fun i=>threeBlockExponent_ne_zero_on N P B v ε₁ ε₂ i.val i.property)
    (fun i=>threeBlockExponent_lt_six_on N P B v ε₁ ε₂ i.val i.property)
  change ‖star (columnCoefficient p hp hcop hg N*C₁ N)*
    (columnCoefficient p hp hcop hg P*C₂ P)*
    FiniteGaussPhase.canonicalProductGauss (fun i:S=>p i.val) (fun i=>hp i.val)
      (columnPrimeCoprime p hcop S) (fun i=>hg i.val) (fun i=>e i.val)*
    (blockRow p hg S e d*star (blockRow p hg S e h))‖≤_
  simp only [norm_mul,norm_star,SecondPassArithmetic.columnCoefficient_norm_one p hp hcop hg hc,
    hG,one_mul,mul_one]
  apply mul_le_of_le_one_right (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  exact (mul_le_of_le_one_left (norm_nonneg _)
    (blockRow_norm_le_one p hg S e d)).trans (blockRow_norm_le_one p hg S e h)

lemma canonicalPairMode_norm_le
    (hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (N P B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (C₁ C₂ : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ)) (V₁ V₂ : ℝ→ℂ)
    (X₁ X₂ K : ℝ) (hK : 0<K) (d h : O) :
    ‖canonicalPairMode p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d h‖≤
      (‖V₁ (columnLog p X₁ N)‖*‖V₂ (columnLog p X₂ P)‖*
        (K/‖eisEmbedding (∏i∈(N∪P)∪cubeActiveSupport B v ε₁ ε₂,p i)‖)*
        (‖C₁ N‖*‖C₂ P‖))*
      ‖paperRadialFourier W ((K/(‖eisEmbedding d‖^2*
        primeProductNorm p ((N∪P)∪cubeActiveSupport B v ε₁ ε₂)))*‖eisEmbedding h‖^2)‖ := by
  have hn : 0<‖eisEmbedding (∏i∈(N∪P)∪cubeActiveSupport B v ε₁ ε₂,p i)‖ :=
    norm_pos_iff.mpr (eisEmbedding_ne_zero (Finset.prod_ne_zero_iff.mpr (fun i hi=>hp i)))
  have ha : K*‖eisEmbedding h‖^2/(‖eisEmbedding d‖^2*
      primeProductNorm p ((N∪P)∪cubeActiveSupport B v ε₁ ε₂)) =
      (K/(‖eisEmbedding d‖^2*primeProductNorm p ((N∪P)∪cubeActiveSupport B v ε₁ ε₂)))*
        ‖eisEmbedding h‖^2 := by ring
  simp only [canonicalPairMode,norm_mul,norm_div,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos hK,abs_of_pos hn,ha]
  calc
    _ ≤ (‖V₁ (columnLog p X₁ N)‖*‖V₂ (columnLog p X₂ P)‖*
        (K/‖eisEmbedding (∏i∈(N∪P)∪cubeActiveSupport B v ε₁ ε₂,p i)‖))*
      ‖paperRadialFourier W ((K/(‖eisEmbedding d‖^2*
        primeProductNorm p ((N∪P)∪cubeActiveSupport B v ε₁ ε₂)))*‖eisEmbedding h‖^2)‖*
      (‖C₁ N‖*‖C₂ P‖) := mul_le_mul_of_nonneg_left
        (threeGaussRowFactor_norm_le p hp hcop hg hc N P B v ε₁ ε₂ C₁ C₂ d h) (by positivity)
    _ = _ := by ring

end

theorem full_uniform_canonicalPairMode_remainder (A : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ),0<C ∧
    ∀ {ι : Type*} [DecidableEq ι]
      (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀i,lambda∉Ideal.span {p i}) (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (N P B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
      (C₁ C₂ : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ)) (V₁ V₂ : ℝ→ℂ)
      (X₁ X₂ K H : ℝ),0<K → 0≤H → ∀(d : O),d≠0 → ∀T:Finset O,
      let S := (N∪P)∪cubeActiveSupport B v ε₁ ε₂
      let scale := K/(‖eisEmbedding d‖^2*primeProductNorm p S)
      (∀h:O,h∉T → H≤ scale*‖eisEmbedding h‖^2) →
      ‖∑'h:{h:O // h∉T},canonicalPairMode p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d h.val‖≤
      (‖V₁ (columnLog p X₁ N)‖*‖V₂ (columnLog p X₂ P)‖*
        (K/‖eisEmbedding (∏i∈S,p i)‖)*(‖C₁ N‖*‖C₂ P‖))*
      ((C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/((min 1 scale)^2*(1+H)^A)) := by
  obtain ⟨s,C,hC,hb⟩ := EisensteinSchwartzPoisson.paperRadialFourier_lattice_tail A
  refine ⟨s,C,hC,?_⟩
  intro ι _ p hp _ hcop hg hc N P B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K H hK hH d hd T
  dsimp only
  intro hT
  let S := (N∪P)∪cubeActiveSupport B v ε₁ ε₂
  let scale := K/(‖eisEmbedding d‖^2*primeProductNorm p S)
  let c := ‖V₁ (columnLog p X₁ N)‖*‖V₂ (columnLog p X₂ P)‖*
        (K/‖eisEmbedding (∏i∈S,p i)‖)*(‖C₁ N‖*‖C₂ P‖)
  have hscale : 0<scale := div_pos hK (mul_pos
    (sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hd))) (primeProductNorm_pos p hp S))
  have hc0 : 0≤ c := by dsimp [c]; positivity
  let small : Set O := {h|h∉T}
  let large : Set O := {h|H≤ scale*‖eisEmbedding h‖^2}
  let f : small→large := fun h=>⟨h.val,hT h.val h.property⟩
  have hfi : Function.Injective f := by
    intro a b hab
    exact Subtype.ext (congrArg (fun x:large=>x.val) hab)
  have hrad := EisensteinSchwartzPoisson.paperRadialFourier_lattice_summable_norm W scale hscale
  have hmajor := (hrad.subtype small).mul_left c
  have hpnt (h:small) :
      ‖canonicalPairMode p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d h.val‖≤
      c*‖paperRadialFourier W (scale*‖eisEmbedding h.val‖^2)‖ :=
    canonicalPairMode_norm_le p hp hcop hg hc N P B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K hK d h.val
  have hsmall := Summable.of_nonneg_of_le (fun _=>norm_nonneg _) hpnt hmajor
  calc
    _ ≤ ∑'h:small,‖canonicalPairMode p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d h.val‖ :=
      norm_tsum_le_tsum_norm hsmall
    _ ≤ ∑'h:small,c*‖paperRadialFourier W (scale*‖eisEmbedding h.val‖^2)‖ :=
      hsmall.tsum_le_tsum hpnt hmajor
    _ = c*∑'h:small,‖paperRadialFourier W (scale*‖eisEmbedding h.val‖^2)‖ := tsum_mul_left
    _ ≤ c*∑'h:large,‖paperRadialFourier W (scale*‖eisEmbedding h.val‖^2)‖ :=
      mul_le_mul_of_nonneg_left ((hrad.subtype small).tsum_le_tsum_of_inj f hfi
        (fun _ _=>norm_nonneg _) (fun _=>le_rfl) (hrad.subtype large)) hc0
    _ ≤ _ := mul_le_mul_of_nonneg_left (hb W scale H hscale hH) hc0

end

open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)
open SecondPassArithmetic (columnLog_norm_upper)

end FirstPassCubeLabels

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.DualZeroMode
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

open scoped BigOperators Classical SchwartzMap

namespace SecondPassArithmetic

open ActualEisensteinCubic
open FirstPassCubeLabels

theorem boundedPrimeSupports_card_positive {ι : Type*} [DecidableEq ι]
    (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (F : Finset ι) (X : ℝ) (hX : 0<X) :
    ((boundedPrimeSupports p F X).card:ℝ)≤128*X := by
  by_cases hx : 1≤X
  · exact boundedPrimeSupports_card p hinj F X hx
  · have he : boundedPrimeSupports p F X=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro S hS
      exact hx ((primeProductNorm_ge_one p hp S).trans (Finset.mem_filter.mp hS).2)
    rw [he,Finset.card_empty,Nat.cast_zero]
    positivity

end SecondPassArithmetic

namespace FirstPassCubeLabels
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)
open EisensteinSchwartzPoisson (paperRadialFourier)
open SecondPassArithmetic (boundedPrimeSupports boundedPrimeSupports_card_positive
  columnLog_norm_upper primeProductNorm_ge_one)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

theorem actualFirstKernel_complement_eq_pairs
    (F B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (C₁ C₂ : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ)) (V₁ V₂ : ℝ→ℂ)
    (X₁ X₂ K : ℝ) (hK : 0<K) (d : O) (hd : d≠0) (T : Finset O) :
    (∑'h:{h:O // h∉T},actualFirstKernel p hp hcop hg F B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d h.val)=
      ∑N∈F.powerset,∑Q∈F.powerset,if Disjoint N Q then
        ∑'h:{h:O // h∉T},canonicalPairMode p hp hcop hg N Q B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d h.val
        else 0 := by
  have hs (N Q : Finset ι) : Summable (fun h:{h:O // h∉T}=>if Disjoint N Q then
      canonicalPairMode p hp hcop hg N Q B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d h.val else 0) := by
    by_cases hNQ : Disjoint N Q
    · simp only [hNQ,ite_true]
      exact (canonicalPairMode_summable p hp hcop hg N Q B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K hK d hd).subtype _
    · simp only [hNQ,ite_false]
      exact summable_zero
  change (∑'h:{h:O // h∉T},∑N∈F.powerset,∑Q∈F.powerset,if Disjoint N Q then
    canonicalPairMode p hp hcop hg N Q B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d h.val else 0)=_
  rw [Summable.tsum_finsetSum (fun N hN=>summable_sum (fun Q hQ=>hs N Q))]
  apply Finset.sum_congr rfl
  intro N hN
  rw [Summable.tsum_finsetSum (fun Q hQ=>hs N Q)]
  apply Finset.sum_congr rfl
  intro Q hQ
  split_ifs <;> simp

end

end FirstPassCubeLabels

namespace SecondPassArithmetic

open ActualEisensteinCubic
open FirstPassCubeLabels
open ConcreteTraceCRT (eisEmbedding)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

omit [DecidableEq ι] in
lemma originalLabelColumn_core_norm_le
    (B : Finset ι) (ε₁ ε₂ : ι→Bool) (negative : Bool)
    (Ψ : O→*ℂ) (hΨ : ∀u,‖Ψ u‖≤1) (m c f : O) (H : Finset ι→ℂ) (S : Finset ι) :
    ‖originalLabelColumn p hg B ε₁ ε₂ negative (multiplicativeCoreColumn p Ψ m H) c f S‖≤‖H S‖ := by
  have hm (z:O):‖rowCoprimeMask (fun i=>Ideal.span {p i}) S z‖≤1:=by
    unfold rowCoprimeMask;split_ifs <;> simp
  have hrow (z:O):‖finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg S z‖^4≤1:=by
    simpa using pow_le_pow_left₀ (norm_nonneg _)
      (finiteSquarefreeRow_norm_le_one (fun i=>Ideal.span {p i}) hg S z) 4
  simp only [originalLabelColumn,multiplicativeCoreColumn,norm_mul,norm_pow]
  calc
    _ ≤ 1*‖H S‖*1*1*1 := by
      exact mul_le_mul
        (mul_le_mul
          (mul_le_mul
            (mul_le_mul_of_nonneg_right
              ((mul_le_mul (hΨ _) (hm m) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)) (norm_nonneg _))
            (hm _) (norm_nonneg _) (by positivity))
          (hrow _) (pow_nonneg (norm_nonneg _) _) (by positivity))
        (hrow _) (pow_nonneg (norm_nonneg _) _) (by positivity)
    _ = _ := by ring

omit [DecidableEq ι] in
lemma originalLabelColumn_core_test_ne_zero
    (B : Finset ι) (ε₁ ε₂ : ι→Bool) (negative : Bool)
    (Ψ : O→*ℂ) (m c f : O) (H : Finset ι→ℂ) (S : Finset ι)
    (h : originalLabelColumn p hg B ε₁ ε₂ negative
      (multiplicativeCoreColumn p Ψ m H) c f S≠0) : H S≠0 := by
  intro hz
  apply h
  simp only [originalLabelColumn,multiplicativeCoreColumn,hz,mul_zero,zero_mul]

end

end SecondPassArithmetic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.MeanSquare.CanonicalTailBounds
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

open scoped BigOperators Classical SchwartzMap ContDiff

open scoped BigOperators Classical
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels
open ConcreteTraceCRT (eisEmbedding)

lemma firstTail_inverse_scale_bound (K D U:ℝ) (hK:0<K) (hD:0<D) (hU:D≤U):
    ((min 1 (K/D))⁻¹)^2≤(1+U/K)^2 := by
  have hU0:0≤U/K:=div_nonneg (hD.le.trans hU) hK.le
  have hi:(min 1 (K/D))⁻¹≤1+U/K:=by
    by_cases h:1≤K/D
    · rw [min_eq_left h,inv_one];linarith
    · rw [min_eq_right (le_of_lt (lt_of_not_ge h)),inv_div]
      exact (div_le_div_of_nonneg_right hU hK.le).trans (by linarith)
  exact pow_le_pow_left₀ (inv_nonneg.mpr (le_min zero_le_one (div_pos hK hD).le)) hi 2

lemma firstTail_scalar_bound (K D E U₁ U₂ lengthScale B G₁ G₂ P H:ℝ) (A:ℕ)
    (hK:0<K) (hD:0<D) (hE:0<E) (hU₁:0<U₁) (hU₂:0<U₂)
    (hL:0≤lengthScale) (hG₁:0≤G₁) (hG₂:0≤G₂) (hP:0≤P) (hH:0≤H)
    (hDb:D≤lengthScale*B^2) (hEb:E≤B^2) (hU₁b:U₁≤lengthScale) (hU₂b:U₂≤lengthScale):
    (128*U₁)*(128*U₂)*(G₁*G₂*K)*
      (P/((min 1 (K/(D*E*U₁*U₂)))^2*(1+H)^A))≤
    (128*lengthScale)^2*(G₁*G₂*K)*P*(1+lengthScale^3*B^4/K)^2/(1+H)^A := by
  have hden:D*E*U₁*U₂≤lengthScale^3*B^4:=by
    calc
      _ ≤ (lengthScale*B^2)*B^2*lengthScale*lengthScale:=mul_le_mul
        (mul_le_mul (mul_le_mul hDb hEb hE.le (mul_nonneg hL (sq_nonneg _))) hU₁b hU₁.le (by positivity))
        hU₂b hU₂.le (by positivity)
      _ = _:=by ring
  have hi:=firstTail_inverse_scale_bound K (D*E*U₁*U₂) (lengthScale^3*B^4) hK (by positivity) hden
  have hpref:(128*U₁)*(128*U₂)*(G₁*G₂*K)≤(128*lengthScale)^2*(G₁*G₂*K):=by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    calc
      _ ≤ (128*lengthScale)*(128*lengthScale):=mul_le_mul (mul_le_mul_of_nonneg_left hU₁b (by norm_num))
        (mul_le_mul_of_nonneg_left hU₂b (by norm_num)) (by positivity) (by positivity)
      _ = _:=by ring
  calc
    _ = ((128*U₁)*(128*U₂)*(G₁*G₂*K))*P*((min 1 (K/(D*E*U₁*U₂)))⁻¹)^2/(1+H)^A:=by
      simp only [div_eq_mul_inv,mul_inv_rev,inv_pow];ring
    _ ≤ _:=by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul (mul_le_mul_of_nonneg_right hpref hP) hi (sq_nonneg _) (by positivity)

variable {ι:Type*} [DecidableEq ι]
  (p:ι→ActualEisensteinCubic.O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]

include hp

omit [∀ (i : ι), (span {p i}).IsMaximal] in
lemma cubeCoordinates_radical_bound (b:CubeCoordinates ι) (B:ℝ) (hB:0≤B)
    (hb₁:‖eisEmbedding (primeProduct p b.support b.leftExponent)‖^2≤B)
    (hb₂:‖eisEmbedding (primeProduct p b.support b.rightExponent)‖^2≤B):
    primeProductNorm p b.support≤B^2 := by
  have hd:(∏i∈b.support,p i)∣primeProduct p b.support b.leftExponent*primeProduct p b.support b.rightExponent:=by
    rw [←primeProduct_add]
    apply Finset.prod_dvd_prod_of_dvd
    intro i hi
    simpa only [pow_one] using pow_dvd_pow (p i) (b.support_pos i hi)
  have hb0:=mul_ne_zero (primeProduct_ne_zero p hp b.support b.leftExponent)
    (primeProduct_ne_zero p hp b.support b.rightExponent)
  have hn:=element_norm_le_of_dvd hb0 hd
  simp only [map_mul,norm_mul,mul_pow] at hn
  exact hn.trans (by simpa only [pow_two] using mul_le_mul hb₁ hb₂ (sq_nonneg _) hB)

omit [∀ (i : ι), (span {p i}).IsMaximal] in
lemma cubeSourceDivisor_norm_bound (b:CubeCoordinates ι) (C D:Finset ι) (B lengthScale:ℝ)
    (hB:0≤B) (hL:0≤lengthScale) (hCB:Disjoint C b.support)
    (hb₁:‖eisEmbedding (primeProduct p b.support b.leftExponent)‖^2≤B)
    (hb₂:‖eisEmbedding (primeProduct p b.support b.rightExponent)‖^2≤B)
    (hC:primeProductNorm p C≤lengthScale)
    (hD:D⊆C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit):
    primeProductNorm p D≤lengthScale*B^2 := by
  calc
    _ ≤ primeProductNorm p (C∪b.support):=primeProductNorm_mono p hp
      (hD.trans (Finset.union_subset_union_right (Finset.filter_subset _ _)))
    _ = primeProductNorm p C*primeProductNorm p b.support:=primeProductNorm_union p _ _ hCB
    _ ≤ _:=mul_le_mul hC (cubeCoordinates_radical_bound p hp b B hB hb₁ hb₂)
      (primeProductNorm_pos p hp _).le hL

end

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct)
open ConcreteTraceCRT (eisEmbedding)

variable {ι:Type*} [DecidableEq ι]
  (p:ι→ActualEisensteinCubic.O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]

end SecondPassArithmetic

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

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.FirstRowGeometry
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "O" => ActualEisensteinCubic.O

lemma first_whole_frequency_numeric (K P dn an cn a1 a2 sn tn hn L : ℝ)
    (hK : 0<K) (hP : 0<P) (hdn : 0<dn) (han : 0<an)
    (hcn : 0<cn) (ha1 : 0<a1) (ha2 : 0<a2)
    (hsn : 0<sn) (htn : 0<tn) (_hhn : 0≤hn) (hL : 0<L)
    (hS : a1*cn*sn≤L) (hT : a2*cn*tn≤L)
    (hratio : (K/(dn*(sn*tn*an)))*hn≤P) :
    hn≤L^2*an*dn/((K/P)*a1*a2*cn^2) := by
  have hprod : sn*tn*(a1*a2*cn^2)≤L^2 := by
    have hh := mul_le_mul hS hT (by positivity : 0≤a2*cn*tn) hL.le
    nlinarith [hh]
  have hraw : K*hn≤P*(dn*(sn*tn*an)) := by
    rw [div_mul_eq_mul_div] at hratio
    exact (div_le_iff₀ (by positivity)).mp hratio
  have hfull : K*hn*(a1*a2*cn^2)≤P*dn*an*L^2 := by
    have hh := mul_le_mul_of_nonneg_right hraw (by positivity : 0≤a1*a2*cn^2)
    have hh' := mul_le_mul_of_nonneg_left hprod (by positivity : 0≤P*dn*an)
    nlinarith [hh,hh']
  apply (le_div_iff₀ (by positivity)).mpr
  convert (preTransparency := .instances) div_le_div_of_nonneg_right hfull hP.le using 1 <;> field_simp

theorem first_ratio_actual_row {ι : Type*} [DecidableEq ι]
    (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (S N Q : Finset ι) (v₁ v₂ : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (hv : ∀ i∈S,0<v₁ i+v₂ i)
    (hNQ : Disjoint N Q) (hNS : Disjoint N S) (hQS : Disjoint Q S)
    (common divisor : Finset ι) (f : Ideal O) (h : O)
    (K P L B F : ℝ) (hK : 0<K) (hP : 0<P) (hL : 0<L) (hB : 0<B) (hF : 0<F)
    (hb₁ : ‖eisEmbedding (primeProduct p S v₁)‖^2≤B)
    (hb₂ : ‖eisEmbedding (primeProduct p S v₂)‖^2≤B)
    (hf : (Ideal.absNorm f : ℝ)≤F)
    (hcol₁ : ‖eisEmbedding (aLabel p S ε₁)‖^2*primeProductNorm p common*primeProductNorm p N≤L)
    (hcol₂ : ‖eisEmbedding (aLabel p S ε₂)‖^2*primeProductNorm p common*primeProductNorm p Q≤L)
    (hratio : (K/(primeProductNorm p divisor *
      primeProductNorm p ((N∪Q)∪cubeActiveSupport S (fun i=>v₁ i+v₂ i) ε₁ ε₂)))*‖eisEmbedding h‖^2≤P) :
    ‖eisEmbedding (DescentWeightedCauchy.firstElementRowMap
      (dilationLabel p S (fun i=>v₁ i+v₂ i) ε₁ ε₂) (f,h))‖^2 ≤
    P*L^2*B^4*F^2*primeProductNorm p divisor /
      (K*(primeProductNorm p common)^2*‖eisEmbedding (jLabel p S (fun i=>v₁ i+v₂ i) ε₁ ε₂)‖^2) := by
  let active := cubeActiveSupport S (fun i=>v₁ i+v₂ i) ε₁ ε₂
  let e := dilationLabel p S (fun i=>v₁ i+v₂ i) ε₁ ε₂
  let j := jLabel p S (fun i=>v₁ i+v₂ i) ε₁ ε₂
  let a1 := aLabel p S ε₁
  let a2 := aLabel p S ε₂
  have hactive : active ⊆ S := Finset.filter_subset _ _
  have hnorm : primeProductNorm p ((N∪Q)∪active)=
      primeProductNorm p N*primeProductNorm p Q*primeProductNorm p active := by
    rw [primeProductNorm_union p (N∪Q) active (Finset.disjoint_union_left.mpr
      ⟨hNS.mono_right hactive,hQS.mono_right hactive⟩),
      primeProductNorm_union p _ _ hNQ]
  change (K/(primeProductNorm p divisor*primeProductNorm p ((N∪Q)∪active)))*‖eisEmbedding h‖^2≤P at hratio
  rw [hnorm] at hratio
  have hpos (v : ι→ℕ) : 0<‖eisEmbedding (primeProduct p S v)‖^2 :=
    SecondPassIntegration.elementNorm_pos _ (primeProduct_ne_zero p hp _ _)
  have hfreq := first_whole_frequency_numeric K P (primeProductNorm p divisor)
    (primeProductNorm p active) (primeProductNorm p common) (‖eisEmbedding a1‖^2)
    (‖eisEmbedding a2‖^2) (primeProductNorm p N) (primeProductNorm p Q)
    (‖eisEmbedding h‖^2) L hK hP (primeProductNorm_pos p hp _) (primeProductNorm_pos p hp _)
    (primeProductNorm_pos p hp _) (hpos _) (hpos _) (primeProductNorm_pos p hp _)
    (primeProductNorm_pos p hp _) (sq_nonneg _) hL hcol₁ hcol₂ hratio
  have hcon := first_conductor_norm_bound p hp S v₁ v₂ ε₁ ε₂ hv B hB.le hb₁ hb₂
  have hnum := first_row_numeric_bound (primeProductNorm p active) (‖eisEmbedding e‖^2)
    (‖eisEmbedding j‖^2) (‖eisEmbedding a1‖^2) (‖eisEmbedding a2‖^2)
    (primeProductNorm p common) (primeProductNorm p divisor) (‖eisEmbedding h‖^2)
    (Ideal.absNorm f) L (K/P) B F (primeProductNorm_pos p hp _).le (sq_nonneg _)
    (hpos _) (hpos _) (hpos _) (primeProductNorm_pos p hp _) (primeProductNorm_pos p hp _).le
    (sq_nonneg _) (Nat.cast_nonneg _) hL (div_pos hK hP) hB hF hcon hfreq hf
  have hgen : ‖eisEmbedding (ConcretePrimeRowBridge.idealGenerator f)‖^2=(Ideal.absNorm f : ℝ) := by
    rw [eisEmbedding_norm_sq_eq_absNorm_span,ConcretePrimeRowBridge.span_idealGenerator]
  have hrow : ‖eisEmbedding (DescentWeightedCauchy.firstElementRowMap e (f,h))‖^2 =
      ‖eisEmbedding h‖^2*(Ideal.absNorm f : ℝ)^2*‖eisEmbedding e‖^2 := by
    simp only [DescentWeightedCauchy.firstElementRowMap,map_mul,map_pow,norm_mul,norm_pow,mul_pow]
    rw [hgen]
  rw [hrow]
  apply hnum.trans_eq
  field_simp
  ring

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.FirstCutoffScale
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem first_physical_row_scale_bound
    (Z M r ell V delta B j eta tau dn cn jn : ℝ) (hZ : 0<Z)
    (_hdn : 0≤dn) (hcn : 0<cn) (_hjn : 0<jn)
    (hd : dn≤Z^(delta+eta)) (hc : Z^(B-eta)≤ cn) (hj : Z^(j-eta)≤jn) :
    Z^tau*(Z^(r+eta))^2*(Z^(ell+eta))^4*(Z^(V+eta))^2*dn /
      (Z^M*cn^2*jn) ≤ Z^(firstPhysicalHeight M r ell V delta B j+12*eta+tau) := by
  have hpow (x : ℝ) (n : ℕ) : (Z^x)^n=Z^(x*n) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hZ.le]
  calc
    _ ≤ Z^tau*(Z^(r+eta))^2*(Z^(ell+eta))^4*(Z^(V+eta))^2*Z^(delta+eta) /
        (Z^M*(Z^(B-eta))^2*Z^(j-eta)) := by
      apply div_le_div₀ (by positivity)
      · exact mul_le_mul_of_nonneg_left hd (by positivity)
      · positivity
      · exact mul_le_mul (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (Real.rpow_pos_of_pos hZ _).le hc 2) (Real.rpow_pos_of_pos hZ _).le)
          hj (Real.rpow_pos_of_pos hZ _).le (by positivity)
    _ = _ := by
      simp only [hpow,←Real.rpow_add hZ,←Real.rpow_sub hZ]
      congr 1
      unfold firstPhysicalHeight
      norm_num
      ring

theorem first_ratio_canonical_row {ι : Type*} [DecidableEq ι]
    (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (S N Q : Finset ι) (v₁ v₂ : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (hv : ∀ i∈S,0<v₁ i+v₂ i)
    (hNQ : Disjoint N Q) (hNS : Disjoint N S) (hQS : Disjoint Q S)
    (common divisor : Finset ι) (f : Ideal O) (h : O)
    (Z M r ell V delta B j eta tau : ℝ) (hZ : 0<Z)
    (hb₁ : ‖eisEmbedding (primeProduct p S v₁)‖^2≤Z^(ell+eta))
    (hb₂ : ‖eisEmbedding (primeProduct p S v₂)‖^2≤Z^(ell+eta))
    (hf : (Ideal.absNorm f : ℝ)≤Z^(V+eta))
    (hd : primeProductNorm p divisor≤Z^(delta+eta))
    (hc : Z^(B-eta)≤primeProductNorm p common)
    (hj : Z^(j-eta)≤‖eisEmbedding (jLabel p S (fun i=>v₁ i+v₂ i) ε₁ ε₂)‖^2)
    (hcol₁ : ‖eisEmbedding (aLabel p S ε₁)‖^2*primeProductNorm p common*primeProductNorm p N≤Z^(r+eta))
    (hcol₂ : ‖eisEmbedding (aLabel p S ε₂)‖^2*primeProductNorm p common*primeProductNorm p Q≤Z^(r+eta))
    (hratio : (Z^M/(primeProductNorm p divisor *
      primeProductNorm p ((N∪Q)∪cubeActiveSupport S (fun i=>v₁ i+v₂ i) ε₁ ε₂)))*‖eisEmbedding h‖^2≤Z^tau) :
    ‖eisEmbedding (DescentWeightedCauchy.firstElementRowMap
      (dilationLabel p S (fun i=>v₁ i+v₂ i) ε₁ ε₂) (f,h))‖^2 ≤
      Z^(firstPhysicalHeight M r ell V delta B j+12*eta+tau) := by
  have hrow := first_ratio_actual_row p hp S N Q v₁ v₂ ε₁ ε₂ hv hNQ hNS hQS common divisor f h
    (Z^M) (Z^tau) (Z^(r+eta)) (Z^(ell+eta)) (Z^(V+eta))
    (Real.rpow_pos_of_pos hZ _) (Real.rpow_pos_of_pos hZ _) (Real.rpow_pos_of_pos hZ _)
    (Real.rpow_pos_of_pos hZ _) (Real.rpow_pos_of_pos hZ _) hb₁ hb₂ hf hcol₁ hcol₂ hratio
  exact hrow.trans (first_physical_row_scale_bound Z M r ell V delta B j eta tau
    (primeProductNorm p divisor) (primeProductNorm p common)
    (‖eisEmbedding (jLabel p S (fun i=>v₁ i+v₂ i) ε₁ ε₂)‖^2) hZ
    (primeProductNorm_pos p hp _).le (primeProductNorm_pos p hp _)
    (SecondPassIntegration.elementNorm_pos _ (primeProduct_ne_zero p hp _ _)) hd hc hj)

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

lemma firstPhysicalMultiplier_row {ι : Type*} (p : ι→O) (S : Finset ι)
    (v₁ v₂ : ι→ℕ) (ε₁ ε₂ : ι→Bool) (f : Ideal O) (h : O) :
    firstPhysicalMultiplier p S v₁ v₂ ε₁ ε₂ f*h =
      DescentWeightedCauchy.firstElementRowMap (dilationLabel p S (fun i=>v₁ i+v₂ i) ε₁ ε₂) (f,h) := by
  unfold firstPhysicalMultiplier DescentWeightedCauchy.firstElementRowMap
  ring

theorem first_physical_cutoff_raw_tail {ι : Type*} [DecidableEq ι]
    (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (S N Q : Finset ι) (v₁ v₂ : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (hv : ∀ i∈S,0<v₁ i+v₂ i)
    (hNQ : Disjoint N Q) (hNS : Disjoint N S) (hQS : Disjoint Q S)
    (common divisor : Finset ι) (f : Ideal O) (hf0 : f≠0) (h : O)
    (Z M r ell V delta B j eta tau : ℝ) (hZ : 0<Z)
    (hb₁ : ‖eisEmbedding (primeProduct p S v₁)‖^2≤Z^(ell+eta))
    (hb₂ : ‖eisEmbedding (primeProduct p S v₂)‖^2≤Z^(ell+eta))
    (hf : (Ideal.absNorm f : ℝ)≤Z^(V+eta))
    (hd : primeProductNorm p divisor≤Z^(delta+eta))
    (hc : Z^(B-eta)≤primeProductNorm p common)
    (hj : Z^(j-eta)≤‖eisEmbedding (jLabel p S (fun i=>v₁ i+v₂ i) ε₁ ε₂)‖^2)
    (hcol₁ : ‖eisEmbedding (aLabel p S ε₁)‖^2*primeProductNorm p common*primeProductNorm p N≤Z^(r+eta))
    (hcol₂ : ‖eisEmbedding (aLabel p S ε₂)‖^2*primeProductNorm p common*primeProductNorm p Q≤Z^(r+eta))
    (hout : h∉childFrequencyBall (firstPhysicalMultiplier p S v₁ v₂ ε₁ ε₂ f)
      (Z^(firstPhysicalHeight M r ell V delta B j+12*eta+tau))) :
    Z^tau ≤ (Z^M/(primeProductNorm p divisor *
      primeProductNorm p ((N∪Q)∪cubeActiveSupport S (fun i=>v₁ i+v₂ i) ε₁ ε₂)))*‖eisEmbedding h‖^2 := by
  by_contra hbad
  have hratio := (lt_of_not_ge hbad).le
  have hrow := first_ratio_canonical_row p hp S N Q v₁ v₂ ε₁ ε₂ hv hNQ hNS hQS common divisor f h
    Z M r ell V delta B j eta tau hZ hb₁ hb₂ hf hd hc hj hcol₁ hcol₂ hratio
  apply hout
  apply (mem_childFrequencyBall _ (firstPhysicalMultiplier_ne_zero p hp S v₁ v₂ ε₁ ε₂ f hf0) _ h).mpr
  simpa only [firstPhysicalMultiplier_row] using hrow

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.MarkBounds
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CompletedGauss FirstPassCubeLabels SecondPassArithmetic
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

 theorem finite_primeSupport_card {ι : Type*} [DecidableEq ι]
    (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i}))) (U : Finset ι) :
    (IdealMobiusDivisorSum.primeSupport (Ideal.span {∏ i ∈ U, p i})).card = U.card := by
  have hc : Pairwise (Function.onFun IsCoprime (fun i : U => Ideal.span {p i.val})) := by
    intro i j hij
    exact hcop (fun he => hij (Subtype.ext he))
  have he := Fintype.card_congr (productPrimeIndexEquiv (fun i : U => p i.val) hc)
  simpa only [Finset.prod_coe_sort, PrimeIndex, Fintype.card_coe, CompletedGauss.primeSupport, IdealMobiusDivisorSum.primeSupport] using he.symm

theorem finite_primeMark_small_power (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι → Eis) (_hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (_hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ),
      (slots : Set σ).PairwiseDisjoint lists →
      (∀ i ∈ slots, ∀ k ∈ lists i, ‖a i k‖ ≤ 1) → ∀ U : Finset ι,
      ‖primeMark slots lists a U‖ ≤ C * (primeProductNorm p U)^ε := by
  obtain ⟨C,hC,hb⟩ := SquarefreeDivisorBound.prime_support_subsets_bound ε hε
  refine ⟨C,hC,?_⟩
  intro ι σ _ _ p hp _ hcop slots lists a hslots ha U
  have hI : (Ideal.span {∏ i ∈ U, p i} : Ideal Eis) ≠ 0 :=
    Ideal.span_singleton_eq_bot.not.mpr (Finset.prod_ne_zero_iff.mpr (fun i hi => hp i))
  have hh := hb (Ideal.span {∏ i ∈ U, p i}) hI
  rw [finite_primeSupport_card p hcop U] at hh
  have hn : (Ideal.absNorm (Ideal.span {∏ i ∈ U, p i}) : ℝ) = primeProductNorm p U :=
    (ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span _).symm
  rw [hn] at hh
  exact (primeMark_norm_le_divisor_count slots lists a U hslots ha).trans hh

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.FirstWholeTail
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem full_first_supported_remainder (A : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ),0<C ∧
    ∀ {ι : Type*} [DecidableEq ι]
      (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i}) (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (F B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool),Disjoint F B →
      ∀ (C₁ C₂ : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ)) (G₁ G₂ X₁ X₂ K P M₁ M₂ : ℝ),
      0≤G₁ → 0≤G₂ → 0<X₁ → 0<X₂ → 0<K → 0≤P →
      (∀N∈F.powerset,‖C₁ N‖≤G₁) → (∀N∈F.powerset,‖C₂ N‖≤G₂) →
      (∀N∈F.powerset,C₁ N≠0 → columnLog p X₁ N≤M₁) →
      (∀N∈F.powerset,C₂ N≠0 → columnLog p X₂ N≤M₂) →
      ∀(d : O),d≠0 → ∀ T : Finset O,
      (∀ N∈F.powerset,∀ Q∈F.powerset,Disjoint N Q → C₁ N≠0 → C₂ Q≠0 →
        ∀ h : O,h∉T → P≤(K/(‖eisEmbedding d‖^2*
          primeProductNorm p ((N∪Q)∪cubeActiveSupport B v ε₁ ε₂)))*‖eisEmbedding h‖^2) →
      let U₁ := X₁*Real.exp M₁
      let U₂ := X₂*Real.exp M₂
      let slow := K/(‖eisEmbedding d‖^2*primeProductNorm p (cubeActiveSupport B v ε₁ ε₂)*U₁*U₂)
      ‖∑'h:{h:O // h∉T},actualFirstKernel p hp hcop hg F B v ε₁ ε₂ C₁ C₂ W (fun _=>1) (fun _=>1) X₁ X₂ K d h.val‖≤
      (128*U₁)*(128*U₂)*(G₁*G₂*K)*
        ((C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
          ((min 1 slow)^2*(1+P)^A)) := by
  obtain ⟨s,C,hC,hb⟩:=full_uniform_canonicalPairMode_remainder A
  refine ⟨s,C,hC,?_⟩
  intro ι _ p hp _ hinj hcop hg hc F B v ε₁ ε₂ hFB C₁ C₂ W G₁ G₂ X₁ X₂ K P M₁ M₂ hG₁ hG₂ hX₁ hX₂ hK hP hC₁ hC₂ hS₁ hS₂ d hd T hT
  dsimp only
  let U₁:=X₁*Real.exp M₁
  let U₂:=X₂*Real.exp M₂
  let S:=cubeActiveSupport B v ε₁ ε₂
  let slow:=K/(‖eisEmbedding d‖^2*primeProductNorm p S*U₁*U₂)
  let tail:ℝ:=(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
    ((min 1 slow)^2*(1+P)^A)
  let Q:ℝ:=G₁*G₂*K*tail
  have hU₁:0<U₁:=mul_pos hX₁ (Real.exp_pos _)
  have hU₂:0<U₂:=mul_pos hX₂ (Real.exp_pos _)
  have hNd:0<‖eisEmbedding d‖^2:=sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hd))
  have hslow:0<slow:=div_pos hK (mul_pos (mul_pos (mul_pos hNd (primeProductNorm_pos p hp S)) hU₁) hU₂)
  have hH:0≤P:=hP
  have htail:0≤tail:=by dsimp [tail]; positivity
  have hQ:0≤Q:=mul_nonneg (mul_nonneg (mul_nonneg hG₁ hG₂) hK.le) htail
  let rem (N R:Finset ι):ℂ:=if Disjoint N R then
    ∑'h:{h:O // h∉T},canonicalPairMode p hp hcop hg N R B v ε₁ ε₂ C₁ C₂ W (fun _=>1) (fun _=>1) X₁ X₂ K d h.val else 0
  have hnzero (N R:Finset ι) (hn:C₁ N=0):rem N R=0:=by
    simp [rem,canonicalPairMode,threeGaussRowFactor,hn]
  have hrzero (N R:Finset ι) (hr:C₂ R=0):rem N R=0:=by
    simp [rem,canonicalPairMode,threeGaussRowFactor,hr]
  have heq : (∑'h:{h:O // h∉T},actualFirstKernel p hp hcop hg F B v ε₁ ε₂ C₁ C₂ W (fun _=>1) (fun _=>1) X₁ X₂ K d h.val)=
      ∑N∈boundedPrimeSupports p F U₁,∑R∈boundedPrimeSupports p F U₂,rem N R := by
    rw [actualFirstKernel_complement_eq_pairs p hp hcop hg F B v ε₁ ε₂ C₁ C₂ W (fun _=>1) (fun _=>1) X₁ X₂ K hK d hd T]
    change (∑N∈F.powerset,∑R∈F.powerset,rem N R)=_
    calc
      _ = ∑N∈boundedPrimeSupports p F U₁,∑R∈F.powerset,rem N R := by
        symm
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro N hN hn
        have hz:C₁ N=0:=by
          by_contra h
          exact hn (Finset.mem_filter.mpr ⟨hN,columnLog_norm_upper p hp X₁ M₁ hX₁ N (hS₁ N hN h)⟩)
        simp only [hnzero N _ hz,Finset.sum_const_zero]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro N hN
        symm
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro R hR hr
        have hz:C₂ R=0:=by
          by_contra h
          exact hr (Finset.mem_filter.mpr ⟨hR,columnLog_norm_upper p hp X₂ M₂ hX₂ R (hS₂ R hR h)⟩)
        exact hrzero N R hz
  have hrem (N:Finset ι) (hN:N∈boundedPrimeSupports p F U₁) (R:Finset ι) (hR:R∈boundedPrimeSupports p F U₂):‖rem N R‖≤Q:=by
    have hNF: N∈F.powerset:=(Finset.mem_filter.mp hN).1
    have hRF: R∈F.powerset:=(Finset.mem_filter.mp hR).1
    by_cases hn:C₁ N=0
    · rw [hnzero N R hn,norm_zero]; exact hQ
    by_cases hr:C₂ R=0
    · rw [hrzero N R hr,norm_zero]; exact hQ
    by_cases hNR:Disjoint N R
    · have hNB:=hFB.mono_left (Finset.mem_powerset.mp hNF)
      have hRB:=hFB.mono_left (Finset.mem_powerset.mp hRF)
      have hNS:Disjoint N S:=hNB.mono_right (Finset.filter_subset _ _)
      have hRS:Disjoint R S:=hRB.mono_right (Finset.filter_subset _ _)
      have hnorm:primeProductNorm p ((N∪R)∪S)=primeProductNorm p N*primeProductNorm p R*primeProductNorm p S:=by
        rw [primeProductNorm_union p _ _ (Finset.disjoint_union_left.mpr ⟨hNS,hRS⟩),primeProductNorm_union p _ _ hNR]
      have hprod:=mul_le_mul (Finset.mem_filter.mp hN).2 (Finset.mem_filter.mp hR).2
        (primeProductNorm_pos p hp R).le hU₁.le
      have hscale:slow≤K/(‖eisEmbedding d‖^2*primeProductNorm p ((N∪R)∪S)):=by
        apply div_le_div_of_nonneg_left hK.le (mul_pos hNd (primeProductNorm_pos p hp _))
        rw [hnorm]
        calc
          _ ≤ ‖eisEmbedding d‖^2*(U₁*U₂*primeProductNorm p S):=mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hprod (primeProductNorm_pos p hp S).le) hNd.le
          _ = _ := by ring
      have hnroot:1≤‖eisEmbedding (∏i∈(N∪R)∪S,p i)‖:=by
        have hx:=primeProductNorm_ge_one p hp ((N∪R)∪S)
        change 1≤‖eisEmbedding (∏i∈(N∪R)∪S,p i)‖^2 at hx
        nlinarith [norm_nonneg (eisEmbedding (∏i∈(N∪R)∪S,p i))]
      have hpre:(K/‖eisEmbedding (∏i∈(N∪R)∪S,p i)‖)*(‖C₁ N‖*‖C₂ R‖)≤G₁*G₂*K:=by
        calc
          _ ≤ K*(G₁*G₂):=mul_le_mul (div_le_self hK.le hnroot)
            (mul_le_mul (hC₁ N hNF) (hC₂ R hRF) (norm_nonneg _) hG₁)
            (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hK.le
          _ = _ := by ring
      have hfrac:(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
          ((min 1 (K/(‖eisEmbedding d‖^2*primeProductNorm p ((N∪R)∪S))))^2*(1+P)^A)≤tail:=by
        apply div_le_div_of_nonneg_left (by positivity)
          (mul_pos (sq_pos_of_pos (lt_min (by norm_num) hslow)) (pow_pos (by linarith) _))
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (le_min zero_le_one hslow.le)
          (min_le_min_left 1 hscale) 2) (pow_nonneg (by linarith) _)
      have hpair:=hb p hp hcop hg hc N R B v ε₁ ε₂ C₁ C₂ W (fun _=>1) (fun _=>1)
        X₁ X₂ K P hK hP d hd T (hT N hNF R hRF hNR hn hr)
      simp only [norm_one,one_mul] at hpair
      dsimp only [rem]
      rw [if_pos hNR]
      exact hpair.trans (mul_le_mul hpre hfrac (by positivity) (mul_nonneg (mul_nonneg hG₁ hG₂) hK.le))
    · simp only [rem,if_neg hNR,norm_zero];exact hQ
  rw [heq]
  calc
    _ ≤ ∑N∈boundedPrimeSupports p F U₁,∑R∈boundedPrimeSupports p F U₂,‖rem N R‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun N hN=>norm_sum_le _ _))
    _ ≤ ∑N∈boundedPrimeSupports p F U₁,∑R∈boundedPrimeSupports p F U₂,Q:=
      Finset.sum_le_sum (fun N hN=>Finset.sum_le_sum (fun R hR=>hrem N hN R hR))
    _ = ((boundedPrimeSupports p F U₁).card:ℝ)*((boundedPrimeSupports p F U₂).card:ℝ)*Q:=by simp;ring
    _ ≤ (128*U₁)*(128*U₂)*Q:=mul_le_mul_of_nonneg_right
      (mul_le_mul (boundedPrimeSupports_card_positive p hp hinj F U₁ hU₁)
        (boundedPrimeSupports_card_positive p hp hinj F U₂ hU₂) (Nat.cast_nonneg _) (by positivity)) hQ
    _ = _ := by dsimp [Q,tail,slow,U₁,U₂,S];ring

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.FirstPhysicalTail
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem full_first_physical_tail (order : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (Ct : ℝ),0<Ct ∧
    ∀ {ι : Type*} [DecidableEq ι]
      (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hchar : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
      (pool S common divisor : Finset ι) (v₁ v₂ : ι→ℕ) (ε₁ ε₂ : ι→Bool),
      (∀ i∈S,0<v₁ i+v₂ i) → Disjoint pool S →
      ∀ (f : Ideal O),f≠0 → ∀ (C₁ C₂ : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ))
      (G₁ G₂ Z M r ell V delta B j eta tau : ℝ),0≤G₁ → 0≤G₂ → 0<Z →
      (∀ U∈pool.powerset,‖C₁ U‖≤G₁) → (∀ U∈pool.powerset,‖C₂ U‖≤G₂) →
      ‖eisEmbedding (primeProduct p S v₁)‖^2≤Z^(ell+eta) →
      ‖eisEmbedding (primeProduct p S v₂)‖^2≤Z^(ell+eta) →
      (Ideal.absNorm f : ℝ)≤Z^(V+eta) → primeProductNorm p divisor≤Z^(delta+eta) →
      Z^(B-eta)≤primeProductNorm p common →
      Z^(j-eta)≤‖eisEmbedding (jLabel p S (fun i=>v₁ i+v₂ i) ε₁ ε₂)‖^2 →
      (∀ N∈pool.powerset,C₁ N≠0 →
        ‖eisEmbedding (aLabel p S ε₂)‖^2*primeProductNorm p common*primeProductNorm p N≤Z^(r+eta)) →
      (∀ Q∈pool.powerset,C₂ Q≠0 →
        ‖eisEmbedding (aLabel p S ε₁)‖^2*primeProductNorm p common*primeProductNorm p Q≤Z^(r+eta)) →
      let U₁ := Z^(r+eta)/(‖eisEmbedding (aLabel p S ε₂)‖^2*primeProductNorm p common)
      let U₂ := Z^(r+eta)/(‖eisEmbedding (aLabel p S ε₁)‖^2*primeProductNorm p common)
      let active := cubeActiveSupport S (fun i=>v₁ i+v₂ i) ε₁ ε₂
      let slow := Z^M/(primeProductNorm p divisor*primeProductNorm p active*U₁*U₂)
      let T := childFrequencyBall (firstPhysicalMultiplier p S v₁ v₂ ε₁ ε₂ f)
        (Z^(firstPhysicalHeight M r ell V delta B j+12*eta+tau))
      ‖∑' h : {h : O // h∉T},actualFirstKernel p hp hcop hg pool S (fun i=>v₁ i+v₂ i) ε₁ ε₂
        C₁ C₂ W (fun _=>1) (fun _=>1) 1 1 (Z^M)
        (primeSubsetGenerator (fun i=>Ideal.span {p i}) divisor) h.val‖ ≤
      (128*U₁)*(128*U₂)*(G₁*G₂*Z^M)*
        ((Ct*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/((min 1 slow)^2*(1+Z^tau)^order)) := by
  obtain ⟨s,Ct,hCt,hfull⟩ := full_first_supported_remainder order
  refine ⟨s,Ct,hCt,?_⟩
  intro ι _ p hp _ hinj hcop hg hchar pool S common divisor v₁ v₂ ε₁ ε₂ hv hpool f hf0
    C₁ C₂ W G₁ G₂ Z M r ell V delta B j eta tau hG₁ hG₂ hZ hC₁ hC₂ hb₁ hb₂ hf hd hc hj hcol₁ hcol₂
    U₁ U₂ active slow T
  have hA (ε : ι→Bool) : 0<‖eisEmbedding (aLabel p S ε)‖^2 :=
    SecondPassIntegration.elementNorm_pos _ (primeProduct_ne_zero p hp _ _)
  have hU₁ : 0<U₁ := div_pos (Real.rpow_pos_of_pos hZ _)
    (mul_pos (hA ε₂) (primeProductNorm_pos p hp _))
  have hU₂ : 0<U₂ := div_pos (Real.rpow_pos_of_pos hZ _)
    (mul_pos (hA ε₁) (primeProductNorm_pos p hp _))
  have hlog₁ (N : Finset ι) (hN : N∈pool.powerset) (hn : C₁ N≠0) : columnLog p 1 N≤Real.log U₁ := by
    unfold columnLog
    rw [div_one]
    apply Real.log_le_log (primeProductNorm_pos p hp _)
    apply (le_div_iff₀ (mul_pos (hA ε₂) (primeProductNorm_pos p hp _))).mpr
    simpa only [mul_comm] using hcol₁ N hN hn
  have hlog₂ (N : Finset ι) (hN : N∈pool.powerset) (hn : C₂ N≠0) : columnLog p 1 N≤Real.log U₂ := by
    unfold columnLog
    rw [div_one]
    apply Real.log_le_log (primeProductNorm_pos p hp _)
    apply (le_div_iff₀ (mul_pos (hA ε₁) (primeProductNorm_pos p hp _))).mpr
    simpa only [mul_comm] using hcol₂ N hN hn
  have hb := hfull p hp hinj hcop hg hchar pool S (fun i=>v₁ i+v₂ i) ε₁ ε₂ hpool C₁ C₂ W
    G₁ G₂ 1 1 (Z^M) (Z^tau) (Real.log U₁) (Real.log U₂) hG₁ hG₂ zero_lt_one zero_lt_one
    (Real.rpow_pos_of_pos hZ _) (Real.rpow_pos_of_pos hZ _).le hC₁ hC₂ hlog₁ hlog₂
    (primeSubsetGenerator (fun i=>Ideal.span {p i}) divisor) (primeSubsetGenerator_ne_zero _ _) T
    (fun N hN Q hQ hNQ hn hq h hout=>by
      simpa only [primeSubsetGenerator_norm_eq_productNorm, Finset.union_comm] using
        first_physical_cutoff_raw_tail p hp S Q N v₁ v₂ ε₁ ε₂ hv hNQ.symm
          (hpool.mono_left (Finset.mem_powerset.mp hQ)) (hpool.mono_left (Finset.mem_powerset.mp hN))
          common divisor f hf0 h Z M r ell V delta B j eta tau hZ hb₁ hb₂ hf hd hc hj
          (hcol₂ Q hQ hq) (hcol₁ N hN hn) hout)
  simpa only [Real.exp_log hU₁,Real.exp_log hU₂,one_mul,primeSubsetGenerator_norm_eq_productNorm]
    using hb

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.FirstMarkedColumns
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "O" => ActualEisensteinCubic.O

variable {ι : Type*} [DecidableEq ι]

theorem cube_whole_column_norm (p : ι→O) (b : CubeCoordinates ι) (hb : b.Admissible)
    (C N : Finset ι) (hC : Disjoint C b.support) (hN : Disjoint N (b.support∪C))
    (negative : Bool) :
    primeProductNorm p (((if negative then b.rightDivisor else b.leftDivisor)∪C)∪N) =
      ‖eisEmbedding (aLabel p b.support (if negative then b.rightBit else b.leftBit))‖^2 *
        primeProductNorm p C * primeProductNorm p N := by
  have hd : (if negative then b.rightDivisor else b.leftDivisor) ⊆ b.support := by
    cases negative
    · exact hb.1
    · exact hb.2
  rw [primeProductNorm_union p _ _ (hN.symm.mono_left (Finset.union_subset_union hd (Finset.Subset.refl C))),
    primeProductNorm_union p _ _ (hC.symm.mono_left hd)]
  congr 2
  cases negative <;> simp only [Bool.false_eq_true,ite_false,ite_true]
  · rw [CubeCoordinates.aLabel_left p b hb]; rfl
  · rw [CubeCoordinates.aLabel_right p b hb]; rfl

variable (p : ι→O) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem canonical_residual_norm (b : CubeCoordinates ι) (C : Finset ι) (negative : Bool)
    (Ψ : O→*ℂ) (hΨ : ∀ u,‖Ψ u‖≤1) (m f : O) (H : Finset ι→ℂ) (N : Finset ι) :
    ‖canonicalCubeResidual p hg b C negative Ψ m f H N‖ ≤
      ‖H (((if negative then b.rightDivisor else b.leftDivisor)∪C)∪N)‖ := by
  exact originalLabelColumn_core_norm_le p hg b.support b.leftBit b.rightBit negative
    Ψ hΨ m (∏i∈C,p i) f _ N

theorem canonical_residual_test_nonzero (b : CubeCoordinates ι) (C : Finset ι) (negative : Bool)
    (Ψ : O→*ℂ) (m f : O) (H : Finset ι→ℂ) (N : Finset ι)
    (hn : canonicalCubeResidual p hg b C negative Ψ m f H N≠0) :
    H (((if negative then b.rightDivisor else b.leftDivisor)∪C)∪N)≠0 := by
  exact originalLabelColumn_core_test_ne_zero p hg b.support b.leftBit b.rightBit negative
    Ψ m (∏i∈C,p i) f _ N hn

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.FirstTailAbsorption
namespace OAI

namespace SevenEighths.InverseMoment
open SecondPassArithmetic
noncomputable section

lemma first_tail_fixed_cap (K D E U₁ U₂ B G₁ G₂ P H : ℝ) (A : ℕ)
    (hK : 0<K) (hD : 0<D) (hE : 0<E) (hU₁ : 0<U₁) (hU₂ : 0<U₂) (hB : 1≤B)
    (hG₁ : 0≤G₁) (hG₂ : 0≤G₂) (hP : 0≤P) (hH : 0≤H)
    (hKb : K≤B) (hKi : K⁻¹≤B) (hDb : D≤B) (hEb : E≤B) (h₁ : U₁≤B) (h₂ : U₂≤B) :
    (128*U₁)*(128*U₂)*(G₁*G₂*K)*
      (P/((min 1 (K/(D*E*U₁*U₂)))^2*(1+H)^A)) ≤
    65536*G₁*G₂*P*B^19/(1+H)^A := by
  have hB0 : 0≤B := zero_le_one.trans hB
  have hB2 : B≤B^2 := by nlinarith
  have hB3 : B≤B*B^2 := le_mul_of_one_le_right hB0 (one_le_pow₀ hB)
  have hb := firstTail_scalar_bound K D E U₁ U₂ B B G₁ G₂ P H A hK hD hE hU₁ hU₂
    hB0 hG₁ hG₂ hP hH (hDb.trans hB3) (hEb.trans hB2) h₁ h₂
  have hscale : 1+B^3*B^4/K≤2*B^8 := by
    calc
      _ ≤ 1+B^3*B^4*B := by rw [div_eq_mul_inv]; gcongr
      _ ≤ 2*B^8 := by have hh : 1≤B^8 := one_le_pow₀ hB; nlinarith [hh]
  apply hb.trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc
    _ ≤ (128*B)^2*(G₁*G₂*B)*P*(2*B^8)^2 := by gcongr
    _ = _ := by ring

theorem choose_first_tail_order (Lcap tau saving : ℝ) (hL : 0≤Lcap) (htau : 0<tau) :
    ∃ A : ℕ, ∀ (Z K D E U₁ U₂ G₁ G₂ P : ℝ),1≤Z →
      0<K → 0<D → 0<E → 0<U₁ → 0<U₂ → 0≤G₁ → 0≤G₂ → 0≤P →
      K≤Z^Lcap → K⁻¹≤Z^Lcap → D≤Z^Lcap → E≤Z^Lcap → U₁≤Z^Lcap → U₂≤Z^Lcap →
      (128*U₁)*(128*U₂)*(G₁*G₂*K)*
        (P/((min 1 (K/(D*E*U₁*U₂)))^2*(1+Z^tau)^A)) ≤
      65536*G₁*G₂*P*Z^(-saving) := by
  obtain ⟨A,hA⟩ := exists_nat_gt ((19*Lcap+saving)/tau)
  refine ⟨A,?_⟩
  intro Z K D E U₁ U₂ G₁ G₂ P hZ hK hD hE hU₁ hU₂ hG₁ hG₂ hP hKb hKi hDb hEb h₁ h₂
  have hz : 0<Z := zero_lt_one.trans_le hZ
  have hb := first_tail_fixed_cap K D E U₁ U₂ (Z^Lcap) G₁ G₂ P (Z^tau) A
    hK hD hE hU₁ hU₂ (Real.one_le_rpow hZ hL) hG₁ hG₂ hP
    (Real.rpow_pos_of_pos hz _).le hKb hKi hDb hEb h₁ h₂
  have hdecay : (Z^Lcap)^19/(1+Z^tau)^A≤Z^(-saving) := by
    calc
      _ ≤ (Z^Lcap)^19/(Z^tau)^A := div_le_div_of_nonneg_left (by positivity)
        (by positivity) (pow_le_pow_left₀ (by positivity) (by linarith) A)
      _ = Z^(19*Lcap-tau*(A:ℝ)) := by
        rw [←Real.rpow_mul_natCast hz.le,←Real.rpow_mul_natCast hz.le,←Real.rpow_sub hz]
        congr 1
        norm_num
        ring
      _ ≤ _ := by
        apply Real.rpow_le_rpow_of_exponent_le hZ
        have hh := (div_lt_iff₀ htau).mp hA
        nlinarith
  apply hb.trans
  calc
    _ = (65536*G₁*G₂*P)*((Z^Lcap)^19/(1+Z^tau)^A) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hdecay (by positivity)

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.FirstSourceSize
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} (p : ι→O) (hp : ∀i,p i≠0)

variable [DecidableEq ι]

include hp in
theorem first_source_scalar_caps (b : CubeCoordinates ι) (C D : Finset ι)
    (hCB : Disjoint C b.support)
    (hD : D⊆C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit)
    (Z M Mmax Fmax r ell V eta : ℝ) (hZ : 1≤Z)
    (hM : 0≤M) (hMm : M≤Mmax) (hF : 0≤Fmax) (hell : 0≤ell) (hV : 0≤V)
    (heta : 0≤eta) (hr : -eta≤ r) (hwhole : r+3*ell+V≤Fmax)
    (h1 : ‖eisEmbedding (primeProduct p b.support b.leftExponent)‖^2≤Z^(ell+eta))
    (h2 : ‖eisEmbedding (primeProduct p b.support b.rightExponent)‖^2≤Z^(ell+eta))
    (hC : primeProductNorm p C≤Z^(r+eta)) :
    let cap := Mmax+Fmax+3*eta
    Z^M≤Z^cap ∧ (Z^M)⁻¹≤Z^cap ∧ primeProductNorm p D≤Z^cap ∧
    primeProductNorm p (cubeActiveSupport b.support
      (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit)≤Z^cap ∧
    (∀ eps : ι→Bool,Z^(r+eta)/(‖eisEmbedding (aLabel p b.support eps)‖^2*primeProductNorm p C)≤Z^cap) := by
  dsimp only
  have hz : 0<Z := zero_lt_one.trans_le hZ
  have hcap : 0≤Mmax+Fmax+3*eta := by linarith
  refine ⟨Real.rpow_le_rpow_of_exponent_le hZ (by linarith),?_,?_,?_,?_⟩
  · calc
      _ ≤ 1 := inv_le_one_of_one_le₀ (Real.one_le_rpow hZ hM)
      _ ≤ _ := Real.one_le_rpow hZ hcap
  · have hd := cubeSourceDivisor_norm_bound p hp b C D (Z^(ell+eta)) (Z^(r+eta))
      (Real.rpow_pos_of_pos hz _).le (Real.rpow_pos_of_pos hz _).le hCB h1 h2 hC hD
    apply hd.trans
    rw [←Real.rpow_mul_natCast hz.le,←Real.rpow_add hz]
    apply Real.rpow_le_rpow_of_exponent_le hZ
    norm_num
    linarith
  · apply (primeProductNorm_mono p hp (Finset.filter_subset _ _)).trans
    apply (cubeCoordinates_radical_bound p hp b (Z^(ell+eta)) (Real.rpow_pos_of_pos hz _).le h1 h2).trans
    rw [←Real.rpow_mul_natCast hz.le]
    apply Real.rpow_le_rpow_of_exponent_le hZ
    norm_num
    linarith
  · intro eps
    have ha := element_norm_ge_one (aLabel p b.support eps) (primeProduct_ne_zero p hp _ _)
    have hc := primeProductNorm_ge_one p hp C
    calc
      _ ≤ Z^(r+eta) := div_le_self (Real.rpow_pos_of_pos hz _).le (one_le_mul_of_one_le_of_one_le ha hc)
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hZ (by linarith)

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.FirstSourceTail
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem choose_actual_first_tail_order (Mmax Fmax eta tau saving : ℝ)
    (hMm : 0≤Mmax) (hFm : 0≤Fmax) (heta : 0≤eta) (htau : 0<tau) :
    ∃ order : ℕ,∀ {ι : Type*} [DecidableEq ι]
      (p : ι→O) (_hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (b : CubeCoordinates ι) (C D : Finset ι),Disjoint C b.support →
      D⊆C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit →
      ∀ (Z M r ell V G₁ G₂ P : ℝ),1≤Z → 0≤M → M≤Mmax → 0≤ell → 0≤V → -eta≤ r →
      r+3*ell+V≤Fmax → 0≤G₁ → 0≤G₂ → 0≤P →
      ‖eisEmbedding (primeProduct p b.support b.leftExponent)‖^2≤Z^(ell+eta) →
      ‖eisEmbedding (primeProduct p b.support b.rightExponent)‖^2≤Z^(ell+eta) →
      primeProductNorm p C≤Z^(r+eta) →
      let U₁ := Z^(r+eta)/(‖eisEmbedding (aLabel p b.support b.rightBit)‖^2*primeProductNorm p C)
      let U₂ := Z^(r+eta)/(‖eisEmbedding (aLabel p b.support b.leftBit)‖^2*primeProductNorm p C)
      let active := cubeActiveSupport b.support
        (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
      let slow := Z^M/(primeProductNorm p D*primeProductNorm p active*U₁*U₂)
      (128*U₁)*(128*U₂)*(G₁*G₂*Z^M)*(P/((min 1 slow)^2*(1+Z^tau)^order))≤
        65536*G₁*G₂*P*Z^(-saving) := by
  obtain ⟨order,he⟩ := choose_first_tail_order (Mmax+Fmax+3*eta) tau saving (by linarith) htau
  refine ⟨order,?_⟩
  intro ι _ p hp _ b C D hCB hD Z M r ell V G₁ G₂ P hZ hM hMmax hell hV hr hwhole hG₁ hG₂ hP h1 h2 hC
  dsimp only
  have hz : 0<Z := zero_lt_one.trans_le hZ
  obtain ⟨hk,hki,hd,ha,hu⟩ := first_source_scalar_caps p hp b C D hCB hD
    Z M Mmax Fmax r ell V eta hZ hM hMmax hFm hell hV heta hr hwhole h1 h2 hC
  have hapos (eps : ι→Bool) : 0<‖eisEmbedding (aLabel p b.support eps)‖^2 :=
    SecondPassIntegration.elementNorm_pos _ (primeProduct_ne_zero p hp _ _)
  exact he Z (Z^M) (primeProductNorm p D)
    (primeProductNorm p (cubeActiveSupport b.support
      (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit))
    (Z^(r+eta)/(‖eisEmbedding (aLabel p b.support b.rightBit)‖^2*primeProductNorm p C))
    (Z^(r+eta)/(‖eisEmbedding (aLabel p b.support b.leftBit)‖^2*primeProductNorm p C))
    G₁ G₂ P hZ (Real.rpow_pos_of_pos hz _) (primeProductNorm_pos p hp _) (primeProductNorm_pos p hp _)
    (div_pos (Real.rpow_pos_of_pos hz _) (mul_pos (hapos _) (primeProductNorm_pos p hp _)))
    (div_pos (Real.rpow_pos_of_pos hz _) (mul_pos (hapos _) (primeProductNorm_pos p hp _)))
    hG₁ hG₂ hP hk hki hd ha (hu _) (hu _)

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

theorem whole_cube_marked_test_uniform (ε : ℝ) (hε : 0<ε) :
    ∃ Cm : ℝ,0<Cm ∧ ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι→O) (_hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (_hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ),
      (slots : Set σ).PairwiseDisjoint lists → (∀ i∈slots,∀ k∈lists i,‖a i k‖≤1) →
      ∀ (extra : Finset ι) (test : Finset ι→ℂ) (E G L : ℝ),0≤E → 0≤G → 0≤L →
      primeProductNorm p extra≤E → (∀ U,‖test U‖≤G) →
      (∀ U,test U≠0→primeProductNorm p U≤L) →
      ∀ U,‖primeMark slots lists a (extra∪U)*test U‖≤Cm*(E*L)^ε*G := by
  obtain ⟨Cm,hCm,hmark⟩ := finite_primeMark_small_power ε hε
  refine ⟨Cm,hCm,?_⟩
  intro ι σ _ _ p hp _ hcop slots lists a hslots ha extra test E G L hE hG hL he hb hs U
  by_cases hz : test U=0
  · simp only [hz,mul_zero,norm_zero];positivity
  have hnorm : primeProductNorm p (extra∪U)≤E*L :=
    (primeProductNorm_union_le_mul p hp extra U).trans
      (mul_le_mul he (hs U hz) (primeProductNorm_pos p hp U).le hE)
  have hnorm0 := (primeProductNorm_pos p hp (extra∪U)).le
  rw [norm_mul]
  calc
    _ ≤ (Cm*(primeProductNorm p (extra∪U))^ε)*G :=
      mul_le_mul (hmark p hp hcop slots lists a hslots ha _) (hb U) (norm_nonneg _) (by positivity)
    _ ≤ _ := by gcongr

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.FirstWholeCanonicalTail
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem first_whole_cube_canonical_tail (ε : ℝ) (hε : 0<ε) (order : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (Ct Cm : ℝ),0<Ct ∧ 0<Cm ∧
    ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hchar : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
      (pool : Finset ι) (b : CubeCoordinates ι),b.Admissible →
      ∀ (common divisor : Finset ι),Disjoint common b.support →
      ∀ (f : Ideal O),f≠0 →
      ∀ (Ψ₁ Ψ₂ : O→*ℂ),(∀ u,‖Ψ₁ u‖≤1) → (∀ u,‖Ψ₂ u‖≤1) →
      ∀ (m₁ m₂ : O) (extra₁ extra₂ : Finset ι) (E : ℝ) (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ),
      0≤E → primeProductNorm p extra₁≤E → primeProductNorm p extra₂≤E →
      (slots : Set σ).PairwiseDisjoint lists → (∀ i∈slots,∀ k∈lists i,‖a i k‖≤1) →
      ∀ (test₁ test₂ : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ))
      (G₁ G₂ Z M r ell V delta B j eta tau : ℝ),0≤G₁ → 0≤G₂ → 0<Z →
      (∀ U,‖test₁ U‖≤G₁) → (∀ U,‖test₂ U‖≤G₂) →
      (∀ U,test₁ U≠0 → primeProductNorm p U≤Z^(r+eta)) →
      (∀ U,test₂ U≠0 → primeProductNorm p U≤Z^(r+eta)) →
      ‖eisEmbedding (primeProduct p b.support b.leftExponent)‖^2≤Z^(ell+eta) →
      ‖eisEmbedding (primeProduct p b.support b.rightExponent)‖^2≤Z^(ell+eta) →
      (Ideal.absNorm f : ℝ)≤Z^(V+eta) → primeProductNorm p divisor≤Z^(delta+eta) →
      Z^(B-eta)≤primeProductNorm p common →
      Z^(j-eta)≤‖eisEmbedding (jLabel p b.support (fun i=>b.leftExponent i+b.rightExponent i)
        b.leftBit b.rightBit)‖^2 →
      let residualPool := pool\(b.support∪common)
      let C₁ := canonicalCubeResidual p hg b common true Ψ₁ m₁ (ConcretePrimeRowBridge.idealGenerator f)
        (fun U=>primeMark slots lists a (extra₁∪U)*test₁ U)
      let C₂ := canonicalCubeResidual p hg b common false Ψ₂ m₂ (ConcretePrimeRowBridge.idealGenerator f)
        (fun U=>primeMark slots lists a (extra₂∪U)*test₂ U)
      let U₁ := Z^(r+eta)/(‖eisEmbedding (aLabel p b.support b.rightBit)‖^2*primeProductNorm p common)
      let U₂ := Z^(r+eta)/(‖eisEmbedding (aLabel p b.support b.leftBit)‖^2*primeProductNorm p common)
      let G₁' := Cm*(E*Z^(r+eta))^ε*G₁
      let G₂' := Cm*(E*Z^(r+eta))^ε*G₂
      let active := cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
      let slow := Z^M/(primeProductNorm p divisor*primeProductNorm p active*U₁*U₂)
      let T := childFrequencyBall (firstPhysicalMultiplier p b.support b.leftExponent b.rightExponent b.leftBit b.rightBit f)
        (Z^(firstPhysicalHeight M r ell V delta B j+12*eta+tau))
      ‖∑' h : {h : O // h∉T},actualFirstKernel p hp hcop hg residualPool b.support
        (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit C₁ C₂ W
        (fun _=>1) (fun _=>1) 1 1 (Z^M)
        (primeSubsetGenerator (fun i=>Ideal.span {p i}) divisor) h.val‖ ≤
      (128*U₁)*(128*U₂)*(G₁'*G₂'*Z^M)*
        ((Ct*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/((min 1 slow)^2*(1+Z^tau)^order)) := by
  obtain ⟨s,Ct,hCt,htail⟩ := full_first_physical_tail order
  obtain ⟨Cm,hCm,hmark⟩ := whole_cube_marked_test_uniform ε hε
  refine ⟨s,Ct,Cm,hCt,hCm,?_⟩
  intro ι σ _ _ p hp _ hinj hcop hg hchar pool b hb common divisor hcommon f hf0 Ψ₁ Ψ₂ hΨ₁ hΨ₂
    m₁ m₂ extra₁ extra₂ E slots lists a hE he₁ he₂ hslots ha test₁ test₂ W G₁ G₂ Z M r ell V delta B j eta tau hG₁ hG₂ hZ
    htest₁ htest₂ hs₁ hs₂ hb₁ hb₂ hf hd hc hj residualPool C₁ C₂ U₁ U₂ G₁' G₂' active slow T
  have hdis : Disjoint residualPool (b.support∪common) := by
    apply Finset.disjoint_left.mpr
    intro i hi hi2
    exact (Finset.mem_sdiff.mp hi).2 hi2
  apply htail p hp hinj hcop hg hchar residualPool b.support common divisor b.leftExponent b.rightExponent
    b.leftBit b.rightBit b.support_pos (hdis.mono_right Finset.subset_union_left) f hf0 C₁ C₂ W
    G₁' G₂' Z M r ell V delta B j eta tau (by dsimp [G₁']; positivity) (by dsimp [G₂']; positivity) hZ
  · intro N hN
    exact (canonical_residual_norm p hg b common true Ψ₁ hΨ₁ m₁ _ _ N).trans
      (hmark p hp hcop slots lists a hslots ha extra₁ test₁ E G₁ (Z^(r+eta)) hE hG₁
        (Real.rpow_pos_of_pos hZ _).le he₁ htest₁ hs₁ _)
  · intro N hN
    exact (canonical_residual_norm p hg b common false Ψ₂ hΨ₂ m₂ _ _ N).trans
      (hmark p hp hcop slots lists a hslots ha extra₂ test₂ E G₂ (Z^(r+eta)) hE hG₂
        (Real.rpow_pos_of_pos hZ _).le he₂ htest₂ hs₂ _)
  · exact hb₁
  · exact hb₂
  · exact hf
  · exact hd
  · exact hc
  · exact hj
  · intro N hN hn
    have ht := canonical_residual_test_nonzero p hg b common true Ψ₁ m₁
      (ConcretePrimeRowBridge.idealGenerator f) _ N hn
    have hn' := hs₁ _ (mul_ne_zero_iff.mp ht).2
    have he := cube_whole_column_norm p b hb common N hcommon
      (hdis.mono_left (Finset.mem_powerset.mp hN)) true
    simp only [ite_true] at he
    exact he ▸ hn'
  · intro N hN hn
    have ht := canonical_residual_test_nonzero p hg b common false Ψ₂ m₂
      (ConcretePrimeRowBridge.idealGenerator f) _ N hn
    have hn' := hs₂ _ (mul_ne_zero_iff.mp ht).2
    have he := cube_whole_column_norm p b hb common N hcommon
      (hdis.mono_left (Finset.mem_powerset.mp hN)) false
    simp only [ite_false,Bool.false_eq_true] at he
    exact he ▸ hn'

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.FirstRapidPhysicalTail
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

theorem first_whole_cube_rapid_physical_tail_oai (ε:ℝ) (hε:0<ε)
    (Mmax Fmax eta tau saving:ℝ) (hMm:0≤Mmax) (hFm:0≤Fmax)
    (heta:0≤eta) (htau:0<tau) :
    ∃ (s:Finset (ℕ×ℕ)) (Ct Cm:ℝ),0<Ct ∧ 0<Cm ∧
    ∀{ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
      (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (pool:Finset ι) (b:CubeCoordinates ι) (C D extra₁ extra₂:Finset ι)
      (f:Ideal O) (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂:O)
      (slots:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ)
      (test₁ test₂:Finset ι→ℂ) (W:𝓢(ℝ,ℂ))
      (E G₁ G₂ Z M r ell V B j:ℝ) (delta:Finset ι→ℝ),
      b.Admissible → Disjoint C b.support →
      D⊆C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit →
      f≠0 → 0≤E → 0≤G₁ → 0≤G₂ → 1≤Z → 0≤M → M≤Mmax →
      0≤ell → 0≤V → -eta≤ r → r+3*ell+V≤Fmax →
      primeProductNorm p C≤Z^(r+eta) →
      primeProductNorm p extra₁≤E → primeProductNorm p extra₂≤E →
      (∀u,‖Ψ₁ u‖≤1) → (∀u,‖Ψ₂ u‖≤1) →
      (slots:Set σ).PairwiseDisjoint lists → (∀i∈slots,∀k∈lists i,‖a i k‖≤1) →
      (∀U,‖test₁ U‖≤G₁) → (∀U,‖test₂ U‖≤G₂) →
      (∀U,test₁ U≠0→primeProductNorm p U≤Z^(r+eta)) →
      (∀U,test₂ U≠0→primeProductNorm p U≤Z^(r+eta)) →
      ‖eisEmbedding (primeProduct p b.support b.leftExponent)‖^2≤Z^(ell+eta) →
      ‖eisEmbedding (primeProduct p b.support b.rightExponent)‖^2≤Z^(ell+eta) →
      (Ideal.absNorm f:ℝ)≤Z^(V+eta) → primeProductNorm p D≤Z^(delta D+eta) →
      Z^(B-eta)≤primeProductNorm p C →
      Z^(j-eta)≤‖eisEmbedding (jLabel p b.support
        (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit)‖^2 →
      ‖firstLocalPhysicalTail p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂
        (ConcretePrimeRowBridge.idealGenerator f)
        (fun U=>primeMark slots lists a (extra₁∪U)*test₁ U)
        (fun U=>primeMark slots lists a (extra₂∪U)*test₂ U) W (Z^M)
        (fun D=>childFrequencyBall (firstPhysicalMultiplier p b.support b.leftExponent
          b.rightExponent b.leftBit b.rightBit f)
          (Z^(firstPhysicalHeight M r ell V (delta D) B j+12*eta+tau))) D‖≤
      65536*(Cm*(E*Z^(r+eta))^ε*G₁)*(Cm*(E*Z^(r+eta))^ε*G₂)*
        (Ct*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)*Z^(-saving) := by
  obtain ⟨order,horder⟩:=choose_actual_first_tail_order Mmax Fmax eta tau saving hMm hFm heta htau
  obtain ⟨s,Ct,Cm,hCt,hCm,htail⟩:=first_whole_cube_canonical_tail ε hε order
  refine ⟨s,Ct,Cm,hCt,hCm,?_⟩
  intro ι σ _ _ p hp _ hinj hcop hg hc pool b C D extra₁ extra₂ f Ψ₁ Ψ₂ m₁ m₂ slots lists a
    test₁ test₂ W E G₁ G₂ Z M r ell V B j delta hb hCB hD hf hE hG₁ hG₂ hZ hM hMmax
    hell hV hr hwhole hC he₁ he₂ hΨ₁ hΨ₂ hslots ha ht₁ ht₂ hs₁ hs₂ hb₁ hb₂ hF hdelta hBlo hj
  have hz:0<Z:=zero_lt_one.trans_le hZ
  have hlocal:=htail p hp hinj hcop hg hc pool b hb C D hCB f hf Ψ₁ Ψ₂ hΨ₁ hΨ₂
    m₁ m₂ extra₁ extra₂ E slots lists a hE he₁ he₂ hslots ha test₁ test₂ W G₁ G₂ Z M r ell V
    (delta D) B j eta tau hG₁ hG₂ hz ht₁ ht₂ hs₁ hs₂ hb₁ hb₂ hF hdelta hBlo hj
  dsimp only at hlocal
  apply hlocal.trans
  exact horder p hp b C D hCB hD Z M r ell V
    (Cm*(E*Z^(r+eta))^ε*G₁) (Cm*(E*Z^(r+eta))^ε*G₂)
    (Ct*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)
    hZ hM hMmax hell hV hr hwhole (by positivity) (by positivity) (by positivity) hb₁ hb₂ hC

end SevenEighths.InverseMoment

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.SevenEighths.InverseMoment.first_whole_cube_rapid_physical_tail_oai.{u_1, u_2} := @OAI.SevenEighths.InverseMoment.first_whole_cube_rapid_physical_tail_oai.{u_1, u_2}
