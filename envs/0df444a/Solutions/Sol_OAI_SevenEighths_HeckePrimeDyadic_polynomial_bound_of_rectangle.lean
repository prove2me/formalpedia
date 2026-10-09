-- Prove2me | solution 1 for OAI.SevenEighths.HeckePrimeDyadic.polynomial_bound_of_rectangle
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T02:02:15.706715+00:00
-- url     : https://prove2.me/submissions/92843cc0-3a58-4b4f-bb26-5cb82094c2f6

import Mathlib
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B017
import Theorems.Thm_OAI_SevenEighths_HeckePrimeDyadic_polynomial_finite_shift
import Theorems.Thm_OAI_SmoothMobiusCorrection_prime_norm_two_le

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.PrimeExtraction
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

namespace FiniteSFactor

theorem mem_fiber {n : ℕ} {I : Ideal O} : I ∈ fiber n ↔ Ideal.absNorm I = n := by
  simp [fiber]

open scoped Classical

open scoped Classical

end FiniteSFactor

open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Mellin.ReflectedKernel
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

namespace CubicReflectionKernel

open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter Asymptotics

theorem compact_source_mellin_convergent
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (s : ℂ) : MellinConvergent V s := by
  have hlocal : LocallyIntegrableOn V (Set.Ioi (0 : ℝ)) :=
    hV.continuous.continuousOn.locallyIntegrableOn measurableSet_Ioi
  have htopzero : V =ᶠ[atTop] (fun _ => 0) := by
    filter_upwards [eventually_gt_atTop b] with y hy
    by_contra hn
    exact (not_le_of_gt hy) (hsupp hn).2
  have hbotzero : V =ᶠ[𝓝[>] (0 : ℝ)] (fun _ => 0) := by
    filter_upwards [Ioo_mem_nhdsGT ha] with y hy
    by_contra hn
    exact (not_le_of_gt hy.2) (hsupp hn).1
  have htop : V =O[atTop] (fun y : ℝ => y ^ (-(s.re + 1))) :=
    htopzero.isBigO.trans (isBigO_zero _ _)
  have hbot : V =O[𝓝[>] (0 : ℝ)] (fun y : ℝ => y ^ (-(s.re - 1))) :=
    hbotzero.isBigO.trans (isBigO_zero _ _)
  exact mellinConvergent_of_isBigO_rpow hlocal htop (by linarith)
    hbot (by linarith)

end CubicReflectionKernel

open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter
namespace CubicReflectionKernel

open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter Asymptotics

theorem compact_source_mellin_hasDerivAt
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (s : ℂ) :
    HasDerivAt (mellin V) (mellin (fun t => Real.log t • V t) s) s := by
  have hlocal : LocallyIntegrableOn V (Set.Ioi (0 : ℝ)) :=
    hV.continuous.continuousOn.locallyIntegrableOn measurableSet_Ioi
  have htopzero : V =ᶠ[atTop] (fun _ => 0) := by
    filter_upwards [eventually_gt_atTop b] with y hy
    by_contra hn
    exact (not_le_of_gt hy) (hsupp hn).2
  have hbotzero : V =ᶠ[𝓝[>] (0 : ℝ)] (fun _ => 0) := by
    filter_upwards [Ioo_mem_nhdsGT ha] with y hy
    by_contra hn
    exact (not_le_of_gt hy.2) (hsupp hn).1
  have htop : V =O[atTop] (fun y : ℝ => y ^ (-(s.re + 1))) :=
    htopzero.isBigO.trans (isBigO_zero _ _)
  have hbot : V =O[𝓝[>] (0 : ℝ)] (fun y : ℝ => y ^ (-(s.re - 1))) :=
    hbotzero.isBigO.trans (isBigO_zero _ _)
  exact (mellin_hasDerivAt_of_isBigO_rpow hlocal htop (by linarith)
    hbot (by linarith)).2

theorem compact_source_mellin_differentiable
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V) :
    Differentiable ℂ (mellin V) :=
  fun s => (compact_source_mellin_hasDerivAt V a b ha hsupp hV s).differentiableAt

end CubicReflectionKernel

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.QuadraticSieve.MainTermDifference
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

open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter

open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter Set
namespace CubicReflectionKernel

theorem mellinLogFamily_smooth (V : ℝ → ℂ) (hV : ContDiff ℝ ∞ V) :
    ContDiff ℝ ∞ (Function.uncurry (mellinLogFamily V)) := by
  change ContDiff ℝ ∞ (fun p : ℝ × ℝ => Real.exp (-p.1 * p.2) • V (Real.exp (-p.2)))
  exact (Real.contDiff_exp.comp (contDiff_fst.neg.mul contDiff_snd)).smul
    (hV.comp (Real.contDiff_exp.comp contDiff_snd.neg))

theorem mellinLogFamily_support (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (σ : ℝ) :
    Function.support (mellinLogFamily V σ) ⊆ Set.Icc (-Real.log b) (-Real.log a) := by
  intro u hu
  have hv : V (Real.exp (-u)) ≠ 0 := by
    intro hv
    exact hu (by simp [mellinLogFamily, hv])
  have hm := hsupp hv
  have hlow := Real.log_le_log ha hm.1
  have hhigh := Real.log_le_log (Real.exp_pos (-u)) hm.2
  simp only [Real.log_exp] at hlow hhigh
  constructor <;> linarith

theorem mellin_eq_logFamily_fourier (V : ℝ → ℂ) (σ t : ℝ) :
    mellin V ((σ : ℂ) + t * Complex.I) = 𝓕 (mellinLogFamily V σ) (t / (2 * Real.pi)) := by
  rw [mellin_eq_fourier]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, mul_zero,  sub_zero, add_zero, Complex.add_im,
    Complex.mul_im, Complex.I_im, mul_one, zero_add]
  rfl

end CubicReflectionKernel

open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter Set
namespace CubicReflectionKernel

theorem weighted_two_to_cauchy {C B : ℝ} (hB : 0 ≤ B) (t : ℝ)
    (h : (1 + |t|) ^ 2 * B ≤ C) : B ≤ C / (1 + t ^ 2) := by
  apply (le_div_iff₀ (by positivity : 0 < 1 + t ^ 2)).mpr
  have hpow : 1 + t ^ 2 ≤ (1 + |t|) ^ 2 := by nlinarith [abs_nonneg t, sq_abs t]
  exact (mul_le_mul_of_nonneg_left hpow hB).trans (by simpa only [mul_comm] using h)

end CubicReflectionKernel

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

open scoped BigOperators Classical
namespace QuadraticDivisorSplit

theorem exists_unique_split (B C D : Ideal O) (hBC : IsCoprime B C)
    (hD : D ∣ B * C) :
    ∃! x : Ideal O × Ideal O, x.1 ∣ B ∧ x.2 ∣ C ∧ x.1 * x.2 = D := by
  obtain ⟨D₁, D₂, h₁, h₂, hprod⟩ := exists_dvd_and_dvd_of_dvd_mul hD
  refine ⟨(D₁, D₂), ⟨h₁, h₂, hprod.symm⟩, ?_⟩
  intro y hy
  apply Prod.ext
  · apply associated_iff_eq.mp
    apply associated_of_dvd_dvd
    · apply (hBC.mono hy.1 h₂).dvd_of_dvd_mul_right
      rw [← hprod, ← hy.2.2]
      exact dvd_mul_right _ _
    · apply (hBC.mono h₁ hy.2.1).dvd_of_dvd_mul_right
      rw [hy.2.2, hprod]
      exact dvd_mul_right _ _
  · apply associated_iff_eq.mp
    apply associated_of_dvd_dvd
    · apply (hBC.symm.mono hy.2.1 h₁).dvd_of_dvd_mul_left
      rw [← hprod, ← hy.2.2]
      exact dvd_mul_left _ _
    · apply (hBC.symm.mono h₂ hy.1).dvd_of_dvd_mul_left
      rw [hy.2.2, hprod]
      exact dvd_mul_left _ _

theorem split_product_injective (B C : Ideal O) (hBC : IsCoprime B C) :
    Function.Injective (fun x : {x : Ideal O × Ideal O // x.1 ∣ B ∧ x.2 ∣ C} =>
      x.val.1 * x.val.2) := by
  intro x y hxy
  have hD : x.val.1 * x.val.2 ∣ B * C := mul_dvd_mul x.property.1 x.property.2
  obtain ⟨z, hz, huniq⟩ := exists_unique_split B C (x.val.1 * x.val.2) hBC hD
  apply Subtype.ext
  exact (huniq x.val ⟨x.property.1, x.property.2, rfl⟩).trans
    (huniq y.val ⟨y.property.1, y.property.2, hxy.symm⟩).symm

open IdealMobiusDivisorSum

theorem divisors_coprime_product (B C : Ideal O) (hB : B ≠ 0) (hC : C ≠ 0)
    (hBC : IsCoprime B C) :
    idealDivisors (B * C) =
      ((idealDivisors B) ×ˢ (idealDivisors C)).image (fun x => x.1 * x.2) := by
  ext D
  rw [mem_idealDivisors (mul_ne_zero hB hC), Finset.mem_image]
  constructor
  · intro hD
    obtain ⟨x, hx, _⟩ := exists_unique_split B C D hBC hD
    exact ⟨x, Finset.mem_product.mpr
      ⟨(mem_idealDivisors hB).mpr hx.1, (mem_idealDivisors hC).mpr hx.2.1⟩, hx.2.2⟩
  · rintro ⟨x, hx, rfl⟩
    exact mul_dvd_mul ((mem_idealDivisors hB).mp (Finset.mem_product.mp hx).1)
      ((mem_idealDivisors hC).mp (Finset.mem_product.mp hx).2)

theorem sum_divisors_coprime_product (B C : Ideal O) (hB : B ≠ 0) (hC : C ≠ 0)
    (hBC : IsCoprime B C) (f : Ideal O → ℂ) :
    (∑ D ∈ idealDivisors (B * C), f D) =
      ∑ D₁ ∈ idealDivisors B, ∑ D₂ ∈ idealDivisors C, f (D₁ * D₂) := by
  rw [divisors_coprime_product B C hB hC hBC, Finset.sum_image]
  · exact Finset.sum_product _ _ _
  · intro x hx y hy hxy
    have hx' : x.1 ∣ B ∧ x.2 ∣ C :=
      ⟨(mem_idealDivisors hB).mp (Finset.mem_product.mp hx).1,
        (mem_idealDivisors hC).mp (Finset.mem_product.mp hx).2⟩
    have hy' : y.1 ∣ B ∧ y.2 ∣ C :=
      ⟨(mem_idealDivisors hB).mp (Finset.mem_product.mp hy).1,
        (mem_idealDivisors hC).mp (Finset.mem_product.mp hy).2⟩
    have he : (⟨x, hx'⟩ : {z : Ideal O × Ideal O // z.1 ∣ B ∧ z.2 ∣ C}) = ⟨y, hy'⟩ :=
      split_product_injective B C hBC hxy
    exact congrArg Subtype.val he

end QuadraticDivisorSplit

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.MobiusEulerCorrection
namespace OAI

noncomputable section

namespace SmoothMobiusCorrection

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

open ActualEisensteinCubic

open scoped BigOperators Classical
open ActualEisensteinCubic
open ShortDraftHeckeBridge hiding O

lemma normFiber_tsum (a : Ideal ActualEisensteinCubic.O→ℂ) (n : ℕ) :
    (∑'I : {I : Ideal ActualEisensteinCubic.O // Ideal.absNorm I=n},a I.val)=normFiberCoeff a n := by
  let : Fintype {I : Ideal ActualEisensteinCubic.O // Ideal.absNorm I=n} :=
    (Ideal.finite_setOfPred_absNorm_eq (S := ActualEisensteinCubic.O) n).fintype
  rw [tsum_fintype]
  symm
  change (∑I∈FiniteSFactor.fiber n,a I)=_
  apply Finset.sum_bij (fun I hI => (⟨I,FiniteSFactor.mem_fiber.mp hI⟩ : {I : Ideal ActualEisensteinCubic.O // Ideal.absNorm I=n}))
  · intro I hI
    exact Finset.mem_univ _
  · intro I hI J hJ he
    exact congrArg Subtype.val he
  · intro I hI
    exact ⟨I.val,FiniteSFactor.mem_fiber.mpr I.property,rfl⟩
  · intro I hI
    rfl

lemma idealDirichlet_fiber (a : Ideal ActualEisensteinCubic.O→ℂ) (s : ℂ) (n : ℕ) :
    (∑'I : {I : Ideal ActualEisensteinCubic.O // Ideal.absNorm I=n},a I.val*CubicEisenstein.fullIdealWeight s I.val)=
      LSeries.term (normFiberCoeff a) s n := by
  by_cases hn : n=0
  · subst n
    have hz (I : {I : Ideal ActualEisensteinCubic.O // Ideal.absNorm I=0}) : CubicEisenstein.fullIdealWeight s I.val=0 := by
      have hI : I.val=0 := Ideal.absNorm_eq_zero_iff.mp I.property
      simp [CubicEisenstein.fullIdealWeight,hI]
    simp only [hz,mul_zero,tsum_zero,LSeries.term_zero]
  · have ht (I : {I : Ideal ActualEisensteinCubic.O // Ideal.absNorm I=n}) :
        CubicEisenstein.fullIdealWeight s I.val=(n:ℂ)^(-s) := by
      have hI : I.val≠0 := fun h => hn (by rw [←I.property,h,map_zero])
      rw [CubicEisenstein.fullIdealWeight,if_neg hI,I.property]
    simp_rw [ht]
    rw [tsum_mul_right,normFiber_tsum,LSeries.term_of_ne_zero hn,Complex.cpow_neg,div_eq_mul_inv]

end SmoothMobiusCorrection

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.SourceMellinInversion
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

namespace CompletedGauss

section
open Filter MeasureTheory
open scoped Classical BigOperators Topology FourierTransform SchwartzMap ContDiff

lemma compactMellin_vertical_integrable (V : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support V⊆Set.Icc a b) (hV : ContDiff ℝ ∞ V) (σ : ℝ) :
    Complex.VerticalIntegrable (mellin V) σ := by
  have hc : HasCompactSupport (CubicReflectionKernel.mellinLogFamily V σ) :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc
      (CubicReflectionKernel.mellinLogFamily_support V a b ha hsupp σ)
  have hd : ContDiff ℝ ∞ (CubicReflectionKernel.mellinLogFamily V σ) :=
    (CubicReflectionKernel.mellinLogFamily_smooth V hV).comp (contDiff_const.prodMk contDiff_id)
  let f : 𝓢(ℝ,ℂ) := hc.toSchwartzMap hd
  have hf : Integrable (fun t : ℝ=>(𝓕 f) (t/(2*Real.pi))) := by
    simpa only [div_eq_mul_inv] using
      (𝓕 f).integrable.comp_mul_right' (inv_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero))
  change Integrable (fun t : ℝ=>mellin V ((σ:ℂ)+t*Complex.I))
  have hfcoe : (f:ℝ→ℂ)=CubicReflectionKernel.mellinLogFamily V σ := rfl
  simpa only [CubicReflectionKernel.mellin_eq_logFamily_fourier,
    SchwartzMap.fourier_coe,hfcoe] using hf

theorem compactMellin_inversion (V : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support V⊆Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (σ x : ℝ) (hx : 0<x) :
    V x=(1/(2*Real.pi):ℂ)*∫t : ℝ,
      (x:ℂ)^(-((σ:ℂ)+t*Complex.I))*mellin V ((σ:ℂ)+t*Complex.I) := by
  have hm := mellinInv_mellin_eq σ V hx
    (CubicReflectionKernel.compact_source_mellin_convergent V a b ha hsupp hV σ)
    (compactMellin_vertical_integrable V a b ha hsupp hV σ) hV.continuous.continuousAt
  simpa only [mellinInv,smul_eq_mul,Complex.real_smul,Complex.ofReal_div,
    Complex.ofReal_one,Complex.ofReal_mul,Complex.ofReal_ofNat] using hm.symm

end

open Filter MeasureTheory
open scoped Classical BigOperators Topology ContDiff

lemma positive_cpow_vertical_norm (r σ t : ℝ) (hr : 0< r) :
    ‖(r:ℂ)^((σ:ℂ)+t*Complex.I)‖=r^σ := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hr]
  simp

lemma positive_cpow_negative_vertical_norm (r σ t : ℝ) (hr : 0< r) :
    ‖(r:ℂ)^(-((σ:ℂ)+t*Complex.I))‖=r^(-σ) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hr]
  simp

lemma positive_cpow_vertical_continuous (r σ : ℝ) (hr : 0< r) :
    Continuous (fun t : ℝ=>(r:ℂ)^((σ:ℂ)+t*Complex.I)) := by
  let : NeZero (r:ℂ) := ⟨Complex.ofReal_ne_zero.mpr hr.ne'⟩
  exact (_root_.continuous_const_cpow (r:ℂ)).comp (by fun_prop)

lemma positive_cpow_negative_vertical_continuous (r σ : ℝ) (hr : 0< r) :
    Continuous (fun t : ℝ=>(r:ℂ)^(-((σ:ℂ)+t*Complex.I))) := by
  let : NeZero (r:ℂ) := ⟨Complex.ofReal_ne_zero.mpr hr.ne'⟩
  exact (_root_.continuous_const_cpow (r:ℂ)).comp (by fun_prop)

lemma vertical_power_mul_integrable (M : ℝ→ℂ) (hM : Integrable M)
    (r σ : ℝ) (hr : 0< r) :
    Integrable (fun t : ℝ=>(r:ℂ)^((σ:ℂ)+t*Complex.I)*M t) := by
  apply (hM.norm.const_mul (r^σ)).mono'
    ((positive_cpow_vertical_continuous r σ hr).aestronglyMeasurable.mul hM.aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun t=>by simp only [Pi.mul_apply,norm_mul,positive_cpow_vertical_norm r σ t hr,le_refl])

lemma weighted_vertical_power_integrable (M : ℝ→ℂ) (hM : Integrable M)
    (r σ : ℝ) (hr : 0< r) (c : ℂ) :
    Integrable (fun t : ℝ=>c*(r:ℂ)^(-((σ:ℂ)+t*Complex.I))*M t) := by
  apply (hM.norm.const_mul (‖c‖*r^(-σ))).mono'
    ((continuous_const.mul (positive_cpow_negative_vertical_continuous r σ hr)).aestronglyMeasurable.mul hM.aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun t=>by
    simp only [Pi.mul_apply,norm_mul,positive_cpow_negative_vertical_norm r σ t hr,le_refl])

lemma weighted_vertical_power_integral_norm (M : ℝ→ℂ) (r σ : ℝ) (hr : 0< r) (c : ℂ) :
    (∫t : ℝ,‖c*(r:ℂ)^(-((σ:ℂ)+t*Complex.I))*M t‖)=
      (‖c‖*r^(-σ))*(∫t : ℝ,‖M t‖) := by
  simp only [norm_mul,positive_cpow_negative_vertical_norm r σ _ hr,integral_const_mul]

theorem weighted_vertical_sum_integral {α : Type*} [Countable α]
    (r : α→ℝ) (hr : ∀i,0< r i) (c : α→ℂ) (σ : ℝ)
    (hc : Summable (fun i=>‖c i‖*(r i)^(-σ)))
    (M : ℝ→ℂ) (hM : Integrable M) :
    (∑' i,∫t : ℝ,c i*(r i:ℂ)^(-((σ:ℂ)+t*Complex.I))*M t)=
      ∫t : ℝ,(∑' i,c i*(r i:ℂ)^(-((σ:ℂ)+t*Complex.I)))*M t := by
  have hi (i : α) := weighted_vertical_power_integrable M hM (r i) σ (hr i) (c i)
  have hs : Summable (fun i=>∫t : ℝ,‖c i*(r i:ℂ)^(-((σ:ℂ)+t*Complex.I))*M t‖) := by
    simp only [weighted_vertical_power_integral_norm M _ σ (hr _) _]
    exact hc.mul_right _
  rw [integral_tsum_of_summable_integral_norm hi hs]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun t=>tsum_mul_right)

lemma positive_quotient_cpow_neg (r X : ℝ) (hr : 0< r) (hX : 0<X) (s : ℂ) :
    ((r/X:ℝ):ℂ)^(-s)=(r:ℂ)^(-s)*(X:ℂ)^s := by
  rw [Complex.ofReal_div,Complex.div_cpow_ofReal_nonneg hr.le hX.le,
    Complex.cpow_neg,Complex.cpow_neg,div_inv_eq_mul]

theorem weightedMellin_inversion {α : Type*} [Countable α]
    (r : α→ℝ) (hr : ∀i,0< r i) (c : α→ℂ) (σ : ℝ)
    (hc : Summable (fun i=>‖c i‖*(r i)^(-σ)))
    (V : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support V⊆Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (X : ℝ) (hX : 0<X) :
    (∑'i,c i*V (r i/X))=(1/(2*Real.pi):ℂ)*∫t : ℝ,
      mellin V ((σ:ℂ)+t*Complex.I)*(X:ℂ)^((σ:ℂ)+t*Complex.I)*
        (∑'i,c i*(r i:ℂ)^(-((σ:ℂ)+t*Complex.I))) := by
  let M : ℝ→ℂ := fun t=>(X:ℂ)^((σ:ℂ)+t*Complex.I)*mellin V ((σ:ℂ)+t*Complex.I)
  have hM : Integrable M := vertical_power_mul_integrable _
    (compactMellin_vertical_integrable V a b ha hsupp hV σ) X σ hX
  have hi (i : α) : c i*V (r i/X)=(1/(2*Real.pi):ℂ)*
      ∫t : ℝ,c i*(r i:ℂ)^(-((σ:ℂ)+t*Complex.I))*M t := by
    rw [compactMellin_inversion V a b ha hsupp hV σ _ (div_pos (hr i) hX)]
    rw [←mul_assoc,mul_comm (c i),mul_assoc,←integral_const_mul]
    congr 1
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun t=>by
      dsimp only
      rw [positive_quotient_cpow_neg _ _ (hr i) hX]
      dsimp only [M]
      ring)
  simp_rw [hi]
  rw [tsum_mul_left,weighted_vertical_sum_integral r hr c σ hc M hM]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun t=>by dsimp only [M];ring)

end CompletedGauss

open Filter MeasureTheory
open scoped Classical BigOperators Topology

open scoped BigOperators Classical
open Finset AddChar MulChar EisensteinEmbedding

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.Theta
namespace OAI

noncomputable section
open Filter Asymptotics Set MeasureTheory
open scoped Topology BigOperators
namespace SevenEighths.HeckeTheta
open EisensteinTheta

theorem completed_differentiableAt {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ)
    {s : ℂ} (hs₀ : s ≠ 0) (hs₁ : s ≠ 1) : DifferentiableAt ℂ (completed w) s :=
  (pair w).differentiableAt_Λ (Or.inl hs₀) (Or.inl (by simpa using hs₁))

theorem completed_differentiableAt_of_mean_zero {N : ℕ} [NeZero N]
    (w : Fin N × Fin N → ℂ) (hw : ∑ a, w a = 0) {s : ℂ} (hs₀ : s ≠ 0) :
    DifferentiableAt ℂ (completed w) s :=
  (pair w).differentiableAt_Λ (Or.inl hs₀) (Or.inr (pair_g₀_eq_zero w hw))

theorem latticeL_differentiableAt {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ)
    {s : ℂ} (hs₀ : s ≠ 0) (hs₁ : s ≠ 1 ∨ ∑ a, w a = 0) :
    DifferentiableAt ℂ (latticeL w) s := by
  have hΛ : DifferentiableAt ℂ (completed w) s := by
    rcases hs₁ with hs₁ | hw
    · exact completed_differentiableAt w hs₀ hs₁
    · exact completed_differentiableAt_of_mean_zero w hw hs₀
  exact (((differentiable_id.const_cpow (Or.inl
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))).differentiableAt).mul
      (Complex.differentiable_one_div_Gamma s)).mul hΛ

theorem regularizedCompleted_differentiableAt {N : ℕ} [NeZero N]
    (w : Fin N × Fin N → ℂ) {s : ℂ} (hs₀ : s ≠ 0) :
    DifferentiableAt ℂ (regularizedCompleted w) s := by
  exact (((differentiableAt_id.sub_const 1).mul
    (((pair w).differentiable_Λ₀ s).sub
      ((differentiableAt_id.inv hs₀).mul_const (pair w).f₀))).add_const (pair w).g₀)

theorem regularizedCompleted_eq {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ)
    {s : ℂ} (hs₀ : s ≠ 0) (hs₁ : s ≠ 1) :
    regularizedCompleted w s = (s - 1) * completed w s := by
  unfold regularizedCompleted completed WeakFEPair.Λ
  simp only [pair_k, Complex.ofReal_one, show (pair w).ε = 1 from rfl,
    smul_eq_mul, one_div]
  have hsub : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr hs₁.symm
  field_simp
  ring

theorem regularizedLatticeL_differentiableAt {N : ℕ} [NeZero N]
    (w : Fin N × Fin N → ℂ) {s : ℂ} (hs₀ : s ≠ 0) :
    DifferentiableAt ℂ (regularizedLatticeL w) s := by
  exact (((differentiable_id.const_cpow (Or.inl
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))).differentiableAt).mul
      (Complex.differentiable_one_div_Gamma s)).mul
        (regularizedCompleted_differentiableAt w hs₀)

theorem regularizedLatticeL_eq {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ)
    {s : ℂ} (hs₀ : s ≠ 0) (hs₁ : s ≠ 1) :
    regularizedLatticeL w s = (s - 1) * latticeL w s := by
  unfold regularizedLatticeL latticeL
  rw [regularizedCompleted_eq w hs₀ hs₁]
  ring

end SevenEighths.HeckeTheta

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.Family
namespace OAI

noncomputable section
open scoped BigOperators
namespace SevenEighths.HeckeFamily

theorem continuedLattice_differentiableAt (χ : Character) {s : ℂ}
    (hs₀ : s ≠ 0) (hs₁ : s ≠ 1 ∨ ∑ a, (coefficients χ) a = 0) :
    DifferentiableAt ℂ (continuedLattice χ) s :=
  HeckeTheta.latticeL_differentiableAt (coefficients χ) hs₀ hs₁

end SevenEighths.HeckeFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.CharacterAnalytic
namespace OAI

noncomputable section
open scoped BigOperators
namespace SevenEighths.HeckeCharacterAnalytic

theorem continuedLattice_differentiableAt_nonprincipal (χ : HeckeFamily.Character)
    (hχ : χ.residue ≠ 1) {s : ℂ} (hs₀ : s ≠ 0) :
    DifferentiableAt ℂ (HeckeFamily.continuedLattice χ) s :=
  HeckeFamily.continuedLattice_differentiableAt χ hs₀
    (Or.inr (coefficients_sum_eq_zero χ hχ))

end SevenEighths.HeckeCharacterAnalytic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.IdealBridge
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.HeckeFamily

theorem LFunction_differentiableAt (χ : Character) {s : ℂ}
    (hs₀ : s ≠ 0) (hs₁ : s ≠ 1 ∨ χ.residue ≠ 1) :
    DifferentiableAt ℂ (LFunction χ) s := by
  apply DifferentiableAt.div_const
  rcases hs₁ with hs₁ | hχ
  · exact continuedLattice_differentiableAt χ hs₀ (Or.inl hs₁)
  · exact HeckeCharacterAnalytic.continuedLattice_differentiableAt_nonprincipal χ hχ hs₀

end SevenEighths.HeckeFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.IdealEuler
namespace OAI

namespace SevenEighths.IdealEuler

open ActualEisensteinCubic UniqueFactorizationMonoid
open CompletedGauss (MulFiber mulFiber_moebius_sum)
open SmoothMobiusCorrection (PrimeIdeal)
open scoped BigOperators Classical

noncomputable section

theorem inverseSeries_eq_inv (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) : inverseSeries a s = (series a s)⁻¹ := by
  calc
    _ = (inverseSeries a s * series a s) * (series a s)⁻¹ := by
      rw [mul_assoc, mul_inv_cancel₀ (series_ne_zero a ha s hs), mul_one]
    _ = _ := by rw [inverseSeries_mul_series a ha s hs, one_mul]

end

end SevenEighths.IdealEuler

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.ZeroSupremum
namespace OAI

noncomputable section
namespace SevenEighths.HeckeZeroSupremum
open HeckeFamily

theorem zeroRealParts_le_one {x : ℝ} (hx : x ∈ zeroRealParts) : x ≤ 1 := by
  obtain ⟨χ, s, _, _, hz, rfl⟩ := hx
  by_contra h
  exact LFunction_ne_zero_of_one_lt_re χ (lt_of_not_ge h) hz

theorem zeroSet_bddAbove : BddAbove zeroSetWithSentinel := by
  refine ⟨1, ?_⟩
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl | hx
  · norm_num
  · exact zeroRealParts_le_one hx

theorem zeroSet_nonempty : zeroSetWithSentinel.Nonempty :=
  Set.insert_nonempty _ _

theorem half_le_beta : (1 / 2 : ℝ) ≤ beta :=
  le_csSup zeroSet_bddAbove (Set.mem_insert _ _)

theorem beta_le_one : beta ≤ 1 := by
  apply csSup_le zeroSet_nonempty
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl | hx
  · norm_num
  · exact zeroRealParts_le_one hx

theorem zero_re_le_beta (χ : Character) {s : ℂ} (hs : 0 < s.re)
    (hpole : s ≠ 1 ∨ χ.residue ≠ 1) (hz : LFunction χ s = 0) :
    s.re ≤ beta :=
  le_csSup zeroSet_bddAbove (Set.mem_insert_of_mem _ ⟨χ, s, hs, hpole, hz, rfl⟩)

theorem LFunction_ne_zero_of_beta_lt (χ : Character) {s : ℂ}
    (hs : beta < s.re) (hpole : s ≠ 1 ∨ χ.residue ≠ 1) :
    LFunction χ s ≠ 0 := by
  intro hz
  have hpos : 0 < s.re := lt_trans (by linarith [half_le_beta]) hs
  exact (not_lt_of_ge (zero_re_le_beta χ hpos hpole hz)) hs

end SevenEighths.HeckeZeroSupremum

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.Reciprocal
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeReciprocal
open HeckeFamily HeckeCharacterAnalytic HeckeCoordinates

theorem regularizedL_eq (χ : Character) {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    regularizedL χ s = (s - 1) * LFunction χ s := by
  unfold regularizedL LFunction continuedLattice
  rw [HeckeTheta.regularizedLatticeL_eq _ h0 h1]
  ring

theorem regularizedL_differentiableAt (χ : Character) {s : ℂ} (h0 : s ≠ 0) :
    DifferentiableAt ℂ (regularizedL χ) s :=
  (HeckeTheta.regularizedLatticeL_differentiableAt _ h0).div_const 6

theorem regularizedL_ne_zero (χ : Character) (hχ : χ.residue = 1) {s : ℂ}
    (hs : HeckeZeroSupremum.beta < s.re) : regularizedL χ s ≠ 0 := by
  by_cases h1 : s = 1
  · subst s
    exact regularizedL_ne_zero_at_one χ hχ
  have h0 : s ≠ 0 := by
    intro h
    simp only [h, Complex.zero_re] at hs
    linarith [HeckeZeroSupremum.half_le_beta]
  rw [regularizedL_eq χ h0 h1]
  exact mul_ne_zero (sub_ne_zero.mpr h1)
    (HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt χ hs (Or.inl h1))

theorem reciprocal_eq_inv (χ : Character) {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    reciprocal χ s = (LFunction χ s)⁻¹ := by
  unfold reciprocal
  split_ifs
  · rw [regularizedL_eq χ h0 h1, div_mul_eq_div_div,
      div_self (sub_ne_zero.mpr h1), one_div]
  · rfl

theorem reciprocal_differentiableAt (χ : Character) {s : ℂ}
    (hs : HeckeZeroSupremum.beta < s.re) : DifferentiableAt ℂ (reciprocal χ) s := by
  have h0 : s ≠ 0 := by
    intro h
    simp only [h, Complex.zero_re] at hs
    linarith [HeckeZeroSupremum.half_le_beta]
  by_cases hχ : χ.residue = 1
  · have heq : reciprocal χ = fun z => (z - 1) / regularizedL χ z := by
      funext z
      simp [reciprocal, hχ]
    rw [heq]
    exact (differentiableAt_id.sub_const 1).div
      (regularizedL_differentiableAt χ h0) (regularizedL_ne_zero χ hχ hs)
  · have heq : reciprocal χ = fun z => (LFunction χ z)⁻¹ := by
      funext z
      simp [reciprocal, hχ]
    rw [heq]
    exact (LFunction_differentiableAt χ h0 (Or.inr hχ)).inv
      (HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt χ hs (Or.inr hχ))

end SevenEighths.HeckeReciprocal

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.ReciprocalBound
namespace OAI

noncomputable section
open scoped BigOperators
namespace SevenEighths.HeckeReciprocalBound
open HeckeFamily

theorem normWeight_le_of_re_ge {σ : ℝ} {s : ℂ} (hs : σ ≤ s.re) (I : Ideal O) :
    ‖CubicEisenstein.fullIdealWeight s I‖ ≤
      ‖CubicEisenstein.fullIdealWeight (σ : ℂ) I‖ := by
  by_cases hI : I = 0
  · simp [hI, CubicEisenstein.fullIdealWeight]
  · have hN : (1 : ℝ) ≤ Ideal.absNorm I := by
      have hpos : 0 < Ideal.absNorm I := Nat.pos_of_ne_zero ((Ideal.absNorm_ne_zero_iff I).mpr (Ring.HasFiniteQuotients.finiteQuotient hI))
      exact_mod_cast hpos
    simp only [CubicEisenstein.fullIdealWeight, hI, ite_false]
    have hn : (0 : ℝ) < Ideal.absNorm I := lt_of_lt_of_le zero_lt_one hN
    rw [show (Ideal.absNorm I : ℂ) = ((Ideal.absNorm I : ℝ) : ℂ) by simp,
      Complex.norm_cpow_eq_rpow_re_of_pos hn,
      Complex.norm_cpow_eq_rpow_re_of_pos hn]
    simp only [Complex.neg_re, Complex.ofReal_re]
    exact Real.rpow_le_rpow_of_exponent_le hN (neg_le_neg hs)

theorem reciprocal_norm_le (χ : Character) {σ : ℝ} (hσ : 1 < σ)
    {s : ℂ} (hs : σ ≤ s.re) : ‖HeckeReciprocal.reciprocal χ s‖ ≤ bound σ := by
  have hs1 : 1 < s.re := hσ.trans_le hs
  have hs0 : s ≠ 0 := by intro h; norm_num [h] at hs1
  have hsp : s ≠ 1 := by intro h; norm_num [h] at hs1
  rw [HeckeReciprocal.reciprocal_eq_inv χ hs0 hsp, LFunction_eq_series χ hs1,
    ← IdealEuler.inverseSeries_eq_inv _ (idealCoeff_norm_le_one χ) s hs1]
  have hsum := IdealEuler.inverse_summable_norm (idealCoeff χ)
    (idealCoeff_norm_le_one χ) s hs1
  apply (norm_tsum_le_tsum_norm hsum).trans
  apply Summable.tsum_le_tsum _ hsum
    (CubicEisenstein.fullIdealWeight_summable_norm (σ : ℂ) (by simpa using hσ))
  intro I
  change ‖(UniqueFactorizationMonoid.moebius I : ℂ) *
    (idealCoeff χ I * CubicEisenstein.fullIdealWeight s I)‖ ≤ _
  rw [norm_mul, norm_mul]
  calc
    _ ≤ ‖CubicEisenstein.fullIdealWeight s I‖ := by
      apply (mul_le_of_le_one_left (by positivity)
        (CubicEisenstein.norm_ideal_moebius_le_one I)).trans
      exact mul_le_of_le_one_left (norm_nonneg _) (idealCoeff_norm_le_one χ I)
    _ ≤ _ := normWeight_le_of_re_ge hs I

end SevenEighths.HeckeReciprocalBound

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

theorem norm_pos (I : NonzeroIdeal) : 0 < norm I := by
  unfold norm
  exact_mod_cast Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr I.property)

theorem coefficient_norm_le (χ : Character) (inverse : Bool) (I : Ideal O) :
    ‖coefficient χ inverse I‖ ≤ 1 := by
  cases inverse
  · exact idealCoeff_norm_le_one χ I
  · change ‖(UniqueFactorizationMonoid.moebius I : ℂ)*idealCoeff χ I‖ ≤ 1
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (CubicEisenstein.norm_ideal_moebius_le_one I)).trans
      (idealCoeff_norm_le_one χ I)

theorem series_eq_tsum (χ : Character) (inverse : Bool) {s : ℂ} (hs : 1 < s.re) :
    series χ inverse s =
      ∑' I : NonzeroIdeal, coefficient χ inverse I.val * (norm I : ℂ)^(-s) := by
  have he : (∑' I : NonzeroIdeal, coefficient χ inverse I.val *
      CubicEisenstein.fullIdealWeight s I.val) =
      ∑' I : Ideal O, coefficient χ inverse I * CubicEisenstein.fullIdealWeight s I := by
    apply tsum_subtype_eq_of_support_subset
      (s := {I : Ideal O | I ≠ 0})
      (f := fun I : Ideal O => coefficient χ inverse I * CubicEisenstein.fullIdealWeight s I)
    intro I hI hi
    subst I
    exact hI (by
      change coefficient χ inverse 0 * CubicEisenstein.fullIdealWeight s 0 = 0
      rw [coefficient_zero, zero_mul])
  have hc : (∑' I : NonzeroIdeal, coefficient χ inverse I.val * (norm I : ℂ)^(-s)) =
      ∑' I : Ideal O, coefficient χ inverse I * CubicEisenstein.fullIdealWeight s I := by
    rw [← he]
    apply tsum_congr
    intro I
    have hI : I.val ≠ 0 := I.property
    rw [CubicEisenstein.fullIdealWeight, if_neg hI]
    simp only [norm, Complex.ofReal_natCast]
  rw [hc]
  cases inverse
  · exact LFunction_eq_series χ hs
  · have h0 : s ≠ 0 := by intro h; norm_num [h] at hs
    have h1 : s ≠ 1 := by intro h; norm_num [h] at hs
    change HeckeReciprocal.reciprocal χ s = _
    rw [HeckeReciprocal.reciprocal_eq_inv χ h0 h1, LFunction_eq_series χ hs,
      ← IdealEuler.inverseSeries_eq_inv _ (idealCoeff_norm_le_one χ) s hs]
    apply tsum_congr
    intro I
    simp only [coefficient,  ite_true, IdealEuler.weighted,
      IdealEuler.normWeight, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
    ring

end SevenEighths.HeckeDyadic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.StripActual
namespace OAI

noncomputable section
open scoped Classical Topology BigOperators
open Set MeasureTheory
namespace SevenEighths.HeckeStripActual
open HeckeFamily HeckePrimitive

variable (c : O) [NeZero c]

theorem LFunction_norm_le (η : Character) {σ : ℝ} (hσ : 1 < σ)
    {s : ℂ} (hs : σ ≤ s.re) : ‖LFunction η s‖ ≤ HeckeReciprocalBound.bound σ := by
  have hs1 := hσ.trans_le hs
  rw [LFunction_eq_series η hs1, IdealEuler.series]
  have hsum := IdealEuler.weighted_summable_norm (idealCoeff η) (idealCoeff_norm_le_one η) s hs1
  apply (norm_tsum_le_tsum_norm hsum).trans
  apply Summable.tsum_le_tsum _ hsum
    (CubicEisenstein.fullIdealWeight_summable_norm (σ : ℂ) (by simpa using hσ))
  intro I
  change ‖idealCoeff η I * CubicEisenstein.fullIdealWeight s I‖ ≤ _
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (idealCoeff_norm_le_one η I)).trans
    (HeckeReciprocalBound.normWeight_le_of_re_ge hs I)

end SevenEighths.HeckeStripActual

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DyadicMellin
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open MeasureTheory Set
namespace SevenEighths.HeckeDyadic
open HeckeFamily

theorem twisted_coefficient_summable (χ : Character) (inverse : Bool) (c σ freq : ℝ)
    (hc : 1 < c+σ) :
    Summable (fun I : NonzeroIdeal => ‖twistedCoefficient χ inverse σ freq I‖*(norm I)^(-c)) := by
  have hf := (CubicEisenstein.fullIdealWeight_summable_norm ((c+σ : ℝ) : ℂ)
    (by simpa using hc)).comp_injective (Subtype.val_injective : Function.Injective
      (fun I : NonzeroIdeal => I.val))
  apply hf.of_nonneg_of_le (fun I => mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_pos I).le _))
  intro I
  have hI : I.val ≠ 0 := I.property
  change ‖twistedCoefficient χ inverse σ freq I‖*(norm I)^(-c) ≤
    ‖CubicEisenstein.fullIdealWeight ((c+σ : ℝ) : ℂ) I.val‖
  rw [CubicEisenstein.fullIdealWeight, if_neg hI]
  change ‖twistedCoefficient χ inverse σ freq I‖*(norm I)^(-c) ≤
    ‖(norm I : ℂ)^(-((c+σ : ℝ) : ℂ))‖
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (norm_pos I)]
  simp only [Complex.neg_re, Complex.ofReal_re]
  unfold twistedCoefficient
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (norm_pos I), Complex.neg_re, shift_re]
  calc
    _ = ‖coefficient χ inverse I.val‖ * (norm I)^(-(c+σ)) := by
      rw [mul_assoc, ← Real.rpow_add (norm_pos I)]
      congr 2
      ring
    _ ≤ _ := mul_le_of_le_one_left (Real.rpow_nonneg (norm_pos I).le _)
      (coefficient_norm_le χ inverse I.val)

theorem twisted_series_eq (χ : Character) (inverse : Bool) (σ freq : ℝ)
    {s : ℂ} (hs : 1 < (s+shift σ freq).re) :
    (∑' I : NonzeroIdeal, twistedCoefficient χ inverse σ freq I*(norm I : ℂ)^(-s)) =
      series χ inverse (s+shift σ freq) := by
  rw [series_eq_tsum χ inverse hs]
  apply tsum_congr
  intro I
  unfold twistedCoefficient
  rw [mul_assoc, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (norm_pos I).ne')]
  congr 2
  ring

theorem polynomial_eq_weighted (χ : Character) (inverse : Bool) (W : ℝ → ℂ)
    (D σ freq : ℝ) (hD : 0 < D) :
    polynomial χ inverse W D σ freq =
      (D : ℂ)^(shift σ freq-(1/2 : ℂ)) *
        ∑' I : NonzeroIdeal, twistedCoefficient χ inverse σ freq I * W (norm I/D) := by
  have he (I : NonzeroIdeal) : summand χ inverse W D σ freq I =
      (D : ℂ)^(shift σ freq) * (twistedCoefficient χ inverse σ freq I * W (norm I/D)) := by
    unfold summand twistedCoefficient
    rw [CompletedGauss.positive_quotient_cpow_neg _ _ (norm_pos I) hD]
    ring
  unfold polynomial
  simp_rw [he]
  rw [tsum_mul_left, ← mul_assoc, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hD.ne')]
  congr 2
  ring

theorem polynomial_mellin (χ : Character) (inverse : Bool) (W : ℝ → ℂ)
    (a b : ℝ) (ha : 0 < a) (hWs : Function.support W ⊆ Icc a b)
    (hW : ContDiff ℝ ∞ W) (D c σ freq : ℝ) (hD : 0 < D) (hc : 1 < c+σ) :
    polynomial χ inverse W D σ freq = (1/(2*Real.pi) : ℂ)*∫ t : ℝ,
      mellin W ((c : ℂ)+t*Complex.I) *
        (D : ℂ)^(((c : ℂ)+t*Complex.I)+shift σ freq-(1/2 : ℂ)) *
          series χ inverse (((c : ℂ)+t*Complex.I)+shift σ freq) := by
  rw [polynomial_eq_weighted χ inverse W D σ freq hD]
  rw [CompletedGauss.weightedMellin_inversion norm norm_pos
    (twistedCoefficient χ inverse σ freq) c (twisted_coefficient_summable χ inverse c σ freq hc)
    W a b ha hWs hW D hD]
  rw [mul_left_comm, ← integral_const_mul]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  rw [twisted_series_eq χ inverse σ freq (by simpa using hc)]
  have he : (D : ℂ)^(shift σ freq-(1/2 : ℂ))*(D : ℂ)^((c : ℂ)+t*Complex.I) =
      (D : ℂ)^(((c : ℂ)+t*Complex.I)+shift σ freq-(1/2 : ℂ)) := by
    rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hD.ne')]
    congr 1
    ring
  calc
    _ = mellin W ((c : ℂ)+t*Complex.I) *
        ((D : ℂ)^(shift σ freq-(1/2 : ℂ))*(D : ℂ)^((c : ℂ)+t*Complex.I)) *
          series χ inverse (((c : ℂ)+t*Complex.I)+shift σ freq) := by ring
    _ = _ := by rw [he]

end SevenEighths.HeckeDyadic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DyadicContour
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open MeasureTheory Set Complex
namespace SevenEighths.HeckeDyadic
open HeckeFamily

theorem series_norm_le (χ : Character) (inverse : Bool) {b : ℝ} (hb : 1<b)
    {s : ℂ} (hs : b≤ s.re) :
    ‖series χ inverse s‖ ≤ HeckeReciprocalBound.bound b := by
  cases inverse
  · exact HeckeStripActual.LFunction_norm_le χ hb hs
  · exact HeckeReciprocalBound.reciprocal_norm_le χ hb hs

theorem series_differentiableAt_right (χ : Character) (inverse : Bool) {s : ℂ}
    (hs : 1<s.re) : DifferentiableAt ℂ (series χ inverse) s := by
  cases inverse
  · exact LFunction_differentiableAt χ
      (by intro h; norm_num [h] at hs) (Or.inl (by intro h; norm_num [h] at hs))
  · exact HeckeReciprocal.reciprocal_differentiableAt χ
      (lt_of_le_of_lt HeckeZeroSupremum.beta_le_one hs)

theorem series_differentiableAt_nonprincipal (χ : Character) (hχ : χ.residue≠1)
    (inverse : Bool) {s : ℂ} (hz : inverse=true → LFunction χ s≠0) :
    DifferentiableAt ℂ (series χ inverse) s := by
  cases inverse
  · exact LFunction_entire_nonprincipal χ hχ s
  · have he : series χ true = fun z => (LFunction χ z)⁻¹ := by
      funext z
      simp [series, HeckeReciprocal.reciprocal, hχ]
    rw [he]
    exact (LFunction_entire_nonprincipal χ hχ s).inv (hz rfl)

theorem integrand_differentiableAt (χ : Character) (inverse : Bool) (W : ℝ → ℂ)
    (a b : ℝ) (ha : 0<a) (hWs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (D σ freq : ℝ) (hD : 0<D) {s : ℂ}
    (hseries : DifferentiableAt ℂ (series χ inverse) (s+shift σ freq)) :
    DifferentiableAt ℂ (integrand χ inverse W D σ freq) s := by
  apply DifferentiableAt.mul
  · apply DifferentiableAt.mul
    · exact CubicReflectionKernel.compact_source_mellin_differentiable W a b ha hWs hW s
    · exact ((differentiableAt_id.add_const (shift σ freq)).sub_const (1/2)).const_cpow
        (Or.inl (Complex.ofReal_ne_zero.mpr hD.ne'))
  · exact hseries.comp s (differentiableAt_id.add_const (shift σ freq))

theorem integrand_norm (χ : Character) (inverse : Bool) (W : ℝ → ℂ)
    (D σ freq : ℝ) (hD : 0<D) (s : ℂ) :
    ‖integrand χ inverse W D σ freq s‖ =
      ‖mellin W s‖*D^(s.re+σ-1/2)*‖series χ inverse (s+shift σ freq)‖ := by
  unfold integrand
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hD]
  simp

theorem integrand_vertical_integrable (χ : Character) (inverse : Bool) (W : ℝ → ℂ)
    (a b : ℝ) (ha : 0<a) (hWs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (D c σ freq : ℝ) (hD : 0<D) (hc : 1<c+σ) :
    Integrable (fun t : ℝ => integrand χ inverse W D σ freq ((c : ℂ)+t*I)) := by
  have hcont : Continuous (fun t : ℝ => integrand χ inverse W D σ freq ((c : ℂ)+t*I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply (integrand_differentiableAt χ inverse W a b ha hWs hW D σ freq hD
      (series_differentiableAt_right χ inverse (by simpa using hc))).continuousAt.comp
    fun_prop
  have hm := (CompletedGauss.compactMellin_vertical_integrable W a b ha hWs hW c).norm
  apply (hm.mul_const (D^(c+σ-1/2)*HeckeReciprocalBound.bound (c+σ))).mono'
    hcont.aestronglyMeasurable
  apply ae_of_all
  intro t
  rw [integrand_norm χ inverse W D σ freq hD]
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im, zero_mul,
    sub_self, add_zero]
  rw [← mul_assoc]
  apply mul_le_mul_of_nonneg_left
    (series_norm_le χ inverse hc (by simp))
  positivity

theorem finite_rectangle (χ : Character) (hχ : χ.residue≠1) (inverse : Bool)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (D σ freq l r T : ℝ) (hD : 0<D)
    (hz : ∀ s ∈ (uIcc l r ×ℂ uIcc (-T) T), inverse=true →
      LFunction χ (s+shift σ freq)≠0) :
    (∫ t : ℝ in -T..T, integrand χ inverse W D σ freq ((r : ℂ)+t*I)) =
      (∫ t : ℝ in -T..T, integrand χ inverse W D σ freq ((l : ℂ)+t*I)) +
      I*((∫ x : ℝ in l..r, integrand χ inverse W D σ freq ((x : ℂ)+(-T)*I)) -
        (∫ x : ℝ in l..r, integrand χ inverse W D σ freq ((x : ℂ)+T*I))) := by
  have hhol : DifferentiableOn ℂ (integrand χ inverse W D σ freq)
      (uIcc l r ×ℂ uIcc (-T) T) := by
    intro s hs
    exact (integrand_differentiableAt χ inverse W a b ha hWs hW D σ freq hD
      (series_differentiableAt_nonprincipal χ hχ inverse (hz s hs))).differentiableWithinAt
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (integrand χ inverse W D σ freq) ((l : ℂ)+(-T)*I) ((r : ℂ)+T*I)
    (by simpa using hhol)
  have hr :
      (∫ x : ℝ in l..r, integrand χ inverse W D σ freq ((x : ℂ)+(-T)*I)) -
      (∫ x : ℝ in l..r, integrand χ inverse W D σ freq ((x : ℂ)+T*I)) +
      I*(∫ t : ℝ in -T..T, integrand χ inverse W D σ freq ((r : ℂ)+t*I)) -
      I*(∫ t : ℝ in -T..T, integrand χ inverse W D σ freq ((l : ℂ)+t*I)) = 0 := by
    simpa [smul_eq_mul] using h
  have hh := congrArg (fun z : ℂ => -I*z) hr
  ring_nf at hh ⊢
  simp only [I_sq] at hh
  linear_combination hh

theorem polynomial_finite_shift (χ : Character) (hχ : χ.residue≠1) (inverse : Bool)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (D σ freq l r T : ℝ) (hD : 0<D) (hr : 1< r+σ) (hT : 0≤T)
    (hz : ∀ s ∈ (uIcc l r ×ℂ uIcc (-T) T), inverse=true →
      LFunction χ (s+shift σ freq)≠0) :
    polynomial χ inverse W D σ freq = (1/(2*Real.pi) : ℂ)*
      ((∫ t : ℝ in -T..T, integrand χ inverse W D σ freq ((l : ℂ)+t*I)) +
      I*((∫ x : ℝ in l..r, integrand χ inverse W D σ freq ((x : ℂ)+(-T)*I)) -
        (∫ x : ℝ in l..r, integrand χ inverse W D σ freq ((x : ℂ)+T*I))) +
      ∫ t : ℝ in (Icc (-T) T)ᶜ, integrand χ inverse W D σ freq ((r : ℂ)+t*I)) := by
  rw [polynomial_mellin χ inverse W a b ha hWs hW D r σ freq hD hr]
  change (1/(2*Real.pi) : ℂ)*(∫ t : ℝ, integrand χ inverse W D σ freq ((r : ℂ)+t*I)) = _
  rw [← integral_add_compl measurableSet_Icc
    (integrand_vertical_integrable χ inverse W a b ha hWs hW D r σ freq hD hr)]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith : -T≤T)]
  rw [finite_rectangle χ hχ inverse W a b ha hWs hW D σ freq l r T hD hz]

end SevenEighths.HeckeDyadic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DyadicEstimates
namespace OAI

noncomputable section
open scoped Classical Topology ContDiff
open MeasureTheory Set Complex
namespace SevenEighths.HeckeDyadic
open HeckeFamily

theorem rapid_tail_bound (F : ℝ → ℂ) (C T : ℝ) (n : ℕ) (hC : 0≤C) (hT : 0≤T)
    (hF : ∀ t : ℝ, (1+|t|)^(n+2)*‖F t‖≤C) :
    ‖∫ t : ℝ in (Icc (-T) T)ᶜ, F t‖ ≤ C/(1+T)^n*Real.pi := by
  have hen (t : ℝ) (ht : t ∈ (Icc (-T) T)ᶜ) :
      ‖F t‖≤(C/(1+T)^n)*(1+t^2)⁻¹ := by
    have ht' : T≤|t| := by
      by_contra h
      have hab : |t|<T := lt_of_not_ge h
      exact ht ⟨(abs_lt.mp hab).1.le, (abs_lt.mp hab).2.le⟩
    have hp : (1+T)^n*(1+t^2)≤(1+|t|)^(n+2) := by
      rw [pow_add]
      apply mul_le_mul
      · exact pow_le_pow_left₀ (by linarith) (by linarith) n
      · nlinarith [sq_abs t, abs_nonneg t]
      · positivity
      · positivity
    have hh : ‖F t‖*((1+T)^n*(1+t^2))≤C :=
      (mul_le_mul_of_nonneg_left hp (norm_nonneg _)).trans (by simpa [mul_comm] using hF t)
    have hb := (le_div_iff₀ (by positivity : 0<(1+T)^n*(1+t^2))).mpr hh
    simpa [div_mul_eq_div_div, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hb
  have hint := (integrable_inv_one_add_sq.const_mul (C/(1+T)^n))
  calc
    _ ≤ ∫ t : ℝ in (Icc (-T) T)ᶜ, (C/(1+T)^n)*(1+t^2)⁻¹ := by
      apply norm_integral_le_of_norm_le hint.integrableOn
      filter_upwards [ae_restrict_mem measurableSet_Icc.compl] with t ht
      exact hen t ht
    _ ≤ ∫ t : ℝ, (C/(1+T)^n)*(1+t^2)⁻¹ :=
      integral_mono_measure Measure.restrict_le_self (by filter_upwards [] with t; positivity) hint
    _ = _ := by rw [integral_const_mul, integral_univ_inv_one_add_sq]

theorem absolute_tail_bound (χ : Character) (inverse : Bool) (W : ℝ → ℂ)
    (D r σ freq C T : ℝ) (n : ℕ) (hD : 0<D) (hr : 1< r+σ) (hC : 0≤C) (hT : 0≤T)
    (hm : ∀ t : ℝ, (1+|t|)^(n+2)*‖mellin W ((r : ℂ)+t*I)‖≤C) :
    ‖∫ t : ℝ in (Icc (-T) T)ᶜ, integrand χ inverse W D σ freq ((r : ℂ)+t*I)‖ ≤
      (C*D^(r+σ-1/2)*HeckeReciprocalBound.bound (r+σ))/(1+T)^n*Real.pi := by
  apply rapid_tail_bound _ _ T n
  · exact mul_nonneg (mul_nonneg hC (Real.rpow_nonneg hD.le _))
      (tsum_nonneg (fun _ => norm_nonneg _))
  · exact hT
  · intro t
    rw [integrand_norm χ inverse W D σ freq hD]
    have hb := series_norm_le χ inverse hr (s := (r : ℂ)+t*I+shift σ freq) (by simp)
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im, zero_mul,
      sub_self, add_zero]
    calc
      _ = ((1+|t|)^(n+2)*‖mellin W ((r : ℂ)+t*I)‖)*D^(r+σ-1/2)*
        ‖series χ inverse ((r : ℂ)+t*I+shift σ freq)‖ := by ring
      _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_right (hm t) (Real.rpow_nonneg hD.le _))
        hb (norm_nonneg _) (mul_nonneg hC (Real.rpow_nonneg hD.le _))

theorem central_segment_bound (χ : Character) (inverse : Bool) (W : ℝ → ℂ)
    (D l σ freq C K T : ℝ) (hD : 0<D) (hC : 0≤C) (hK : 0≤K) (hT : 0≤T)
    (hm : ∀ t : ℝ, (1+|t|)^2*‖mellin W ((l : ℂ)+t*I)‖≤C)
    (hs : ∀ t ∈ Icc (-T) T, ‖series χ inverse ((l : ℂ)+t*I+shift σ freq)‖≤K) :
    ‖∫ t : ℝ in -T..T, integrand χ inverse W D σ freq ((l : ℂ)+t*I)‖ ≤
      C*D^(l+σ-1/2)*K*Real.pi := by
  rw [intervalIntegral.integral_of_le (by linarith : -T≤T)]
  have hint := integrable_inv_one_add_sq.const_mul (C*D^(l+σ-1/2)*K)
  calc
    _ ≤ ∫ t : ℝ in Ioc (-T) T, (C*D^(l+σ-1/2)*K)*(1+t^2)⁻¹ := by
      apply norm_integral_le_of_norm_le hint.integrableOn
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      rw [integrand_norm χ inverse W D σ freq hD]
      have hb := CubicReflectionKernel.weighted_two_to_cauchy (norm_nonneg _) t (hm t)
      simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im, zero_mul,
        sub_self, add_zero]
      calc
        _ ≤ (C/(1+t^2))*D^(l+σ-1/2)*K :=
          mul_le_mul (mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg hD.le _))
            (hs t ⟨ht.1.le,ht.2⟩) (norm_nonneg _) (by positivity)
        _ = _ := by ring
    _ ≤ ∫ t : ℝ, (C*D^(l+σ-1/2)*K)*(1+t^2)⁻¹ :=
      integral_mono_measure Measure.restrict_le_self (by filter_upwards [] with t; positivity) hint
    _ = _ := by rw [integral_const_mul, integral_univ_inv_one_add_sq]

end SevenEighths.HeckeDyadic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DyadicJoins
namespace OAI

noncomputable section
open scoped Classical Topology ContDiff
open MeasureTheory Set Complex
namespace SevenEighths.HeckeDyadic
open HeckeFamily

theorem horizontal_join_bound (χ : Character) (inverse : Bool) (W : ℝ → ℂ)
    (D σ freq l r y C K : ℝ) (n : ℕ)
    (hD : 1≤D) (hlr : l≤ r) (hC : 0≤C) (_hK : 0≤K)
    (hm : ∀ x ∈ Icc l r, (1+|y|)^n*‖mellin W ((x : ℂ)+y*I)‖≤C)
    (hs : ∀ x ∈ Icc l r, ‖series χ inverse ((x : ℂ)+y*I+shift σ freq)‖≤K) :
    ‖∫ x : ℝ in l..r, integrand χ inverse W D σ freq ((x : ℂ)+y*I)‖ ≤
      (C*D^(r+σ-1/2)*K/(1+|y|)^n)*|r-l| := by
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro x hx
  have hx' : x ∈ Icc l r := by simpa [uIcc_of_le hlr] using uIoc_subset_uIcc hx
  have hb : ‖mellin W ((x : ℂ)+y*I)‖≤C/(1+|y|)^n := by
    apply (le_div_iff₀ (by positivity : 0<(1+|y|)^n)).mpr
    simpa [mul_comm] using hm x hx'
  have hpow : D^(x+σ-1/2)≤D^(r+σ-1/2) :=
    Real.rpow_le_rpow_of_exponent_le hD (by linarith [hx'.2])
  rw [integrand_norm χ inverse W D σ freq (by linarith)]
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im, zero_mul,
    sub_self, add_zero]
  calc
    _ ≤ (C/(1+|y|)^n)*D^(r+σ-1/2)*K :=
      mul_le_mul (mul_le_mul hb hpow (by positivity) (by positivity))
        (hs x hx') (norm_nonneg _) (by positivity)
    _ = _ := by ring

end SevenEighths.HeckeDyadic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DyadicPointwise
namespace OAI

noncomputable section
open scoped Classical Topology ContDiff
open Set MeasureTheory Complex
namespace SevenEighths.HeckeDyadic
open HeckeFamily

theorem norm_four_sides (A B C D : ℂ) :
    ‖A+I*(B-C)+D‖≤‖A‖+‖B‖+‖C‖+‖D‖ := by
  have h₁ := norm_add_le (A+I*(B-C)) D
  have h₂ := norm_add_le A (I*(B-C))
  have h₃ := norm_sub_le B C
  simp only [norm_mul,norm_I,one_mul] at h₂
  linarith

end SevenEighths.HeckeDyadic

end

end OAI
end

section
-- module Solutions.OAIHecke.Vendor.PrimeNumberTheoremAnd.Wiener
open Real BigOperators ArithmeticFunction MeasureTheory Filter Set FourierTransform LSeries
  Asymptotics SchwartzMap
open Complex hiding log
open scoped Topology
open scoped ContDiff
open scoped ComplexConjugate

variable {n : ℕ} {A a b c d u x y t σ' : ℝ} {ψ Ψ : ℝ → ℂ} {F G : ℂ → ℂ} {f : ℕ → ℂ} {𝕜 : Type}
  [RCLike 𝕜]

attribute [fun_prop] Real.continuous_fourierChar

attribute [fun_prop] measurable_coe_nnreal_ennreal

theorem sum_range_succ (a : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range n, a (i + 1) = (∑ i ∈ Finset.range (n + 1), a i) - a 0 := by
  have := Finset.sum_range_sub a n
  rw [Finset.sum_sub_distrib, sub_eq_iff_eq_add] at this
  rw [Finset.sum_range_succ, this] ; ring
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.IdealMangoldt
namespace OAI

namespace SevenEighths.IdealMangoldt

open ActualEisensteinCubic UniqueFactorizationMonoid ArithmeticFunction
open scoped BigOperators Classical

noncomputable section

theorem primeBase_spec {I : Ideal O} (hI : IsPrimePow I) :
    Prime (primeBase I) ∧ ∃ k : ℕ, 0 < k ∧ primeBase I ^ k = I := by
  obtain ⟨k, hp, hk, heq⟩ := hI.choose_spec
  simp only [primeBase, hI, dite_true]
  exact ⟨hp, k, hk, heq⟩

theorem primeBase_pow {P : Ideal O} (hP : Prime P) {k : ℕ} (hk : 0 < k) :
    primeBase (P ^ k) = P := by
  have hpow : IsPrimePow (P ^ k) := ⟨P, k, hP, hk, rfl⟩
  obtain ⟨hQ, l, hl, heq⟩ := primeBase_spec hpow
  apply associated_iff_eq.mp
  apply hQ.associated_of_dvd hP
  exact hQ.dvd_of_dvd_pow (heq ▸ dvd_pow_self (primeBase (P ^ k)) hl.ne')

theorem value_pow {P : Ideal O} (hP : Prime P) {k : ℕ} (hk : 0 < k) :
    value (P ^ k) = Real.log (Ideal.absNorm P) := by
  rw [value, if_pos (show IsPrimePow (P ^ k) from ⟨P, k, hP, hk, rfl⟩),
    primeBase_pow hP hk]

theorem value_nonneg (I : Ideal O) : 0 ≤ value I := by
  by_cases hI : IsPrimePow I
  · rw [value, if_pos hI]
    apply Real.log_nonneg
    exact_mod_cast (SmoothMobiusCorrection.prime_norm_two_le ⟨_, (primeBase_spec hI).1⟩).trans' (by decide : 1 ≤ 2)
  · simp only [value, hI, ite_false, le_refl]

end

end SevenEighths.IdealMangoldt

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.IdealLogDerivative
namespace OAI

namespace SevenEighths.IdealLogDerivative

open ActualEisensteinCubic UniqueFactorizationMonoid IdealEuler
open IdealMobiusDivisorSum (idealDivisors mem_idealDivisors)
open scoped BigOperators Classical Topology

noncomputable section

theorem primePow_coprime_factor {B C : Ideal O} (h : IsPrimePow (B * C))
    (hBC : IsRelPrime B C) : B = 1 ∨ C = 1 := by
  obtain ⟨P, k, hP, hk, heq⟩ := h
  obtain ⟨i, hi, hBi⟩ := (dvd_prime_pow hP k).mp
    (heq.symm ▸ dvd_mul_right B C)
  obtain ⟨j, hj, hCj⟩ := (dvd_prime_pow hP k).mp
    (heq.symm ▸ dvd_mul_left C B)
  have hB := associated_iff_eq.mp hBi
  have hC := associated_iff_eq.mp hCj
  by_cases hi0 : i = 0
  · left; simpa only [hi0, pow_zero] using hB
  by_cases hj0 : j = 0
  · right; simpa only [hj0, pow_zero] using hC
  exact (hP.not_isUnit (hBC (hB ▸ dvd_pow_self P hi0) (hC ▸ dvd_pow_self P hj0))).elim

theorem value_mul_coprime {B C : Ideal O} (hBC : IsRelPrime B C) :
    IdealMangoldt.value (B * C) =
      (if C = 1 then IdealMangoldt.value B else 0) +
      (if B = 1 then IdealMangoldt.value C else 0) := by
  by_cases hB : B = 1
  · subst B
    simp only [one_mul, IdealMangoldt.value_one, ite_self, ite_true, zero_add]
  by_cases hC : C = 1
  · subst C
    simp only [mul_one, IdealMangoldt.value_one, ite_self, ite_true, add_zero]
  have hnot : ¬IsPrimePow (B * C) := by
    intro h
    exact (primePow_coprime_factor h hBC).elim hB hC
  simp only [IdealMangoldt.value, hnot, hB, hC, ite_false, zero_add]

theorem idealDivisors_one : idealDivisors (1 : Ideal O) = {1} := by
  ext D
  rw [mem_idealDivisors (show (1 : Ideal O) ≠ ⊥ from one_ne_zero), Finset.mem_singleton]
  exact isUnit_iff_dvd_one.symm.trans isUnit_iff_eq_one

theorem idealDivisors_prime_pow (P : Ideal O) (hP : Prime P) (k : ℕ) :
    idealDivisors (P ^ k) = (Finset.range (k + 1)).image (fun j => P ^ j) := by
  ext D
  rw [mem_idealDivisors (show P ^ k ≠ ⊥ from pow_ne_zero k hP.ne_zero), Finset.mem_image]
  constructor
  · intro hD
    obtain ⟨j, hj, hDj⟩ := (dvd_prime_pow hP k).mp hD
    exact ⟨j, Finset.mem_range.mpr (by omega), (associated_iff_eq.mp hDj).symm⟩
  · rintro ⟨j, hj, rfl⟩
    exact pow_dvd_pow P (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj)

theorem sum_value_prime_pow (P : Ideal O) (hP : Prime P) (k : ℕ) :
    (∑ D ∈ idealDivisors (P ^ k), (IdealMangoldt.value D : ℂ)) =
      k * (Real.log (Ideal.absNorm P) : ℂ) := by
  rw [idealDivisors_prime_pow P hP k, Finset.sum_image]
  · induction k with
    | zero => simp only [Nat.zero_add, Finset.sum_range_one, pow_zero,
        IdealMangoldt.value_one, Complex.ofReal_zero, Nat.cast_zero, zero_mul]
    | succ k ih =>
      rw [Finset.sum_range_succ, ih, IdealMangoldt.value_pow hP (Nat.succ_pos k)]
      push_cast
      ring
  · exact fun i _ j _ hij => pow_injective_of_not_isUnit hP.not_isUnit hP.ne_zero hij

theorem sum_value_mul (B C : Ideal O) (hB : B ≠ 0) (hC : C ≠ 0)
    (hBC : IsRelPrime B C) :
    (∑ D ∈ idealDivisors (B * C), (IdealMangoldt.value D : ℂ)) =
      (∑ D ∈ idealDivisors B, (IdealMangoldt.value D : ℂ)) +
      ∑ D ∈ idealDivisors C, (IdealMangoldt.value D : ℂ) := by
  have hcop : IsCoprime B C := by
    apply Ideal.isCoprime_iff_sup_eq.mpr
    apply Ideal.isUnit_iff.mp
    exact hBC (Ideal.dvd_iff_le.mpr le_sup_left) (Ideal.dvd_iff_le.mpr le_sup_right)
  have h1B : (1 : Ideal O) ∈ idealDivisors B := (mem_idealDivisors hB).mpr (one_dvd _)
  have h1C : (1 : Ideal O) ∈ idealDivisors C := (mem_idealDivisors hC).mpr (one_dvd _)
  rw [QuadraticDivisorSplit.sum_divisors_coprime_product B C hB hC hcop]
  calc
    _ = ∑ D ∈ idealDivisors B, ∑ E ∈ idealDivisors C,
        ((if E = 1 then (IdealMangoldt.value D : ℂ) else 0) +
        (if D = 1 then (IdealMangoldt.value E : ℂ) else 0)) := by
      apply Finset.sum_congr rfl
      intro D hD
      apply Finset.sum_congr rfl
      intro E hE
      rw [value_mul_coprime ((hBC.of_dvd_left ((mem_idealDivisors hB).mp hD)).of_dvd_right
        ((mem_idealDivisors hC).mp hE)), Complex.ofReal_add]
      split_ifs <;> rfl
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_ite_irrel,
        Finset.sum_ite_eq', if_pos h1C, if_pos h1B, Finset.sum_const_zero]

theorem sum_value_divisors (B : Ideal O) (hB : B ≠ 0) :
    (∑ D ∈ idealDivisors B, (IdealMangoldt.value D : ℂ)) =
      (Real.log (Ideal.absNorm B) : ℂ) := by
  induction B using UniqueFactorizationMonoid.induction_on_coprime with
  | h0 => exact (hB rfl).elim
  | h1 hunit =>
    rw [isUnit_iff_eq_one.mp hunit, idealDivisors_one, Finset.sum_singleton]
    simp only [IdealMangoldt.value_one, map_one, Nat.cast_one, Real.log_one]
  | hpr k hP =>
    rw [sum_value_prime_pow _ hP k, map_pow, Nat.cast_pow, Real.log_pow]
    push_cast
    rfl
  | @hcp B C hBC ihB ihC =>
    have hB0 : B ≠ 0 := left_ne_zero_of_mul hB
    have hC0 : C ≠ 0 := right_ne_zero_of_mul hB
    rw [sum_value_mul B C hB0 hC0 hBC, ihB hB0, ihC hC0, map_mul, Nat.cast_mul,
      Real.log_mul (by exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr hB0))
        (by exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr hC0)), Complex.ofReal_add]

theorem value_le_log_norm (B : Ideal O) :
    IdealMangoldt.value B ≤ Real.log (Ideal.absNorm B) := by
  by_cases h : IsPrimePow B
  · obtain ⟨P, k, hP, hk, rfl⟩ := h
    rw [IdealMangoldt.value_pow hP hk, map_pow, Nat.cast_pow, Real.log_pow]
    apply le_mul_of_one_le_left
    · exact Real.log_natCast_nonneg _
    · exact_mod_cast hk
  · rw [IdealMangoldt.value, if_neg h]
    exact Real.log_natCast_nonneg _

theorem weighted_eq_term (a : Ideal O →*₀ ℂ) (s : ℂ) (B : Ideal O) :
    weighted a s B = LSeries.term (fun _ => a B) s (Ideal.absNorm B) := by
  by_cases hB : B = 0
  · subst B
    simp only [map_zero, LSeries.term_zero]
  · have hn : Ideal.absNorm B ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr hB
    change a B * CubicEisenstein.fullIdealWeight s B = _
    simp only [CubicEisenstein.fullIdealWeight, hB, ite_false,
      LSeries.term_of_ne_zero hn, Complex.cpow_neg, div_eq_mul_inv]

theorem weighted_hasDerivAt (a : Ideal O →*₀ ℂ) (s : ℂ) (B : Ideal O) :
    HasDerivAt (fun z => weighted a z B)
      (-((Real.log (Ideal.absNorm B) : ℂ) * weighted a s B)) s := by
  simp_rw [weighted_eq_term]
  convert (preTransparency := .instances) LSeries.hasDerivAt_term (fun _ => a B) (Ideal.absNorm B) s using 1
  by_cases hn : Ideal.absNorm B = 0
  · simp only [hn, LSeries.term_zero, mul_zero]
  · simp only [LSeries.term_of_ne_zero hn, LSeries.logMul, Complex.natCast_log,
      mul_div_assoc]

theorem log_weighted_hasSum (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) :
    HasSum (fun B : Ideal O => (Real.log (Ideal.absNorm B) : ℂ) * weighted a s B)
      (-deriv (series a) s) := by
  obtain ⟨x, hx, hxs⟩ := exists_between hs
  have hu := weighted_summable_norm a ha (x : ℂ) (by simpa using hx)
  have hd (B : Ideal O) : DifferentiableOn ℂ (fun z => weighted a z B) {z : ℂ | x < z.re} :=
    fun z _ => (weighted_hasDerivAt a z B).differentiableAt.differentiableWithinAt
  have hU : IsOpen {z : ℂ | x < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hbound (B : Ideal O) (z : ℂ) (hz : z ∈ {z : ℂ | x < z.re}) :
      ‖weighted a z B‖ ≤ ‖weighted a (x : ℂ) B‖ := by
    simp only [weighted_eq_term]
    exact LSeries.norm_term_le_of_re_le_re _ (by simpa using hz.le) _
  have H := Complex.hasSum_deriv_of_summable_norm hu hd hU hbound hxs
  simp_rw [(weighted_hasDerivAt a s _).deriv] at H
  unfold IdealEuler.series
  simpa only [neg_neg] using H.neg

theorem mangoldt_weighted_summable_norm (a : Ideal O →*₀ ℂ)
    (ha : ∀ I, ‖a I‖ ≤ 1) (s : ℂ) (hs : 1 < s.re) :
    Summable (fun B : Ideal O => ‖(IdealMangoldt.value B : ℂ) * weighted a s B‖) := by
  apply (log_weighted_hasSum a ha s hs).summable.norm.of_nonneg_of_le (fun _ => norm_nonneg _)
  intro B
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (IdealMangoldt.value_nonneg B), abs_of_nonneg (Real.log_natCast_nonneg _)]
  exact mul_le_mul_of_nonneg_right (value_le_log_norm B) (norm_nonneg _)

theorem mangoldt_series_eq_LSeries (a : Ideal O →*₀ ℂ)
    (ha : ∀ I, ‖a I‖ ≤ 1) (s : ℂ) (hs : 1 < s.re) :
    (∑' B : Ideal O, (IdealMangoldt.value B : ℂ) * weighted a s B) = LSeries (coeff a) s := by
  have H := (mangoldt_weighted_summable_norm a ha s hs).of_norm.hasSum.tsum_fiberwise Ideal.absNorm
  change HasSum (fun n : ℕ => ∑' B : {B : Ideal O // Ideal.absNorm B = n},
    (IdealMangoldt.value B.val : ℂ) * weighted a s B.val) _ at H
  have hf (n : ℕ) : (∑' B : {B : Ideal O // Ideal.absNorm B = n},
      (IdealMangoldt.value B.val : ℂ) * weighted a s B.val) = LSeries.term (coeff a) s n := by
    unfold coeff
    simpa only [weighted, normWeight,
      MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, mul_assoc]
      using SmoothMobiusCorrection.idealDirichlet_fiber
        (fun B => (IdealMangoldt.value B : ℂ) * a B) s n
  simp_rw [hf] at H
  exact H.tsum_eq.symm

theorem mulFiber_value_sum (B : Ideal O) (hB : B ≠ 0) :
    (∑' p : CompletedGauss.MulFiber B, (IdealMangoldt.value p.val.1 : ℂ)) =
      (Real.log (Ideal.absNorm B) : ℂ) := by
  let e := CompletedGauss.mulFiberDivisorEquiv B hB
  calc
    _ = ∑' D : {D : Ideal O // D ∈ idealDivisors B}, (IdealMangoldt.value D.val : ℂ) :=
      e.tsum_eq (fun D => (IdealMangoldt.value D.val : ℂ))
    _ = ∑ D ∈ idealDivisors B, (IdealMangoldt.value D : ℂ) := by
      rw [tsum_fintype]
      exact (Finset.sum_subtype (idealDivisors B) (fun _ => Iff.rfl)
        (fun D => (IdealMangoldt.value D : ℂ))).symm
    _ = _ := sum_value_divisors B hB

theorem coeff_LSeries_mul_series (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) :
    LSeries (coeff a) s * series a s = -deriv (series a) s := by
  let f := weighted a s
  let F : Ideal O × Ideal O → ℂ := fun p => (IdealMangoldt.value p.1 : ℂ) * f (p.1 * p.2)
  have hprod := (mangoldt_weighted_summable_norm a ha s hs).mul_norm
    (weighted_summable_norm a ha s hs)
  have hF : Summable F := by
    apply hprod.of_norm.congr
    intro p
    dsimp only [F, f]
    rw [map_mul]
    ring
  have hfiber (B : Ideal O) : (∑' p : CompletedGauss.MulFiber B, F p.val) =
      (Real.log (Ideal.absNorm B) : ℂ) * f B := by
    by_cases hB : B = 0
    · subst B
      have hz (p : CompletedGauss.MulFiber 0) : F p.val = 0 := by
        simp only [F, p.property, map_zero, mul_zero]
      simp only [hz, tsum_zero, map_zero, mul_zero]
    · calc
        _ = (∑' p : CompletedGauss.MulFiber B, (IdealMangoldt.value p.val.1 : ℂ)) * f B := by
          rw [← tsum_mul_right]
          exact tsum_congr (fun p => by simp only [F, p.property])
        _ = _ := by rw [mulFiber_value_sum B hB]
  have hsum := hF.hasSum.tsum_fiberwise (fun p : Ideal O × Ideal O => p.1 * p.2)
  change HasSum (fun B : Ideal O => ∑' p : CompletedGauss.MulFiber B, F p.val) _ at hsum
  simp_rw [hfiber] at hsum
  calc
    _ = (∑' B : Ideal O, (IdealMangoldt.value B : ℂ) * f B) * ∑' B : Ideal O, f B := by
      rw [mangoldt_series_eq_LSeries a ha s hs]
      rfl
    _ = ∑' p : Ideal O × Ideal O, ((IdealMangoldt.value p.1 : ℂ) * f p.1) * f p.2 :=
      tsum_mul_tsum_of_summable_norm (mangoldt_weighted_summable_norm a ha s hs)
        (weighted_summable_norm a ha s hs)
    _ = ∑' p, F p := by
      apply tsum_congr
      intro p
      simp only [F, map_mul]
      ring
    _ = -deriv (series a) s := hsum.unique (log_weighted_hasSum a ha s hs)

theorem coeff_LSeries_eq_neg_logDeriv (a : Ideal O →*₀ ℂ)
    (ha : ∀ I, ‖a I‖ ≤ 1) (s : ℂ) (hs : 1 < s.re) :
    LSeries (coeff a) s = -deriv (series a) s / series a s := by
  apply (eq_div_iff (series_ne_zero a ha s hs)).mpr
  exact coeff_LSeries_mul_series a ha s hs

theorem coeff_LSeries_eq_neg_logDeriv_of_eq (a : Ideal O →*₀ ℂ)
    (ha : ∀ I, ‖a I‖ ≤ 1) (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, 1 < z.re → F z = series a z)
    (s : ℂ) (hs : 1 < s.re) :
    LSeries (coeff a) s = -deriv F s / F s := by
  have hd : deriv F s = deriv (series a) s := by
    apply Filter.EventuallyEq.deriv_eq
    have hU : {z : ℂ | 1 < z.re} ∈ nhds s :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs
    filter_upwards [hU] with z hz
    exact hF z hz
  rw [hd, hF s hs]
  exact coeff_LSeries_eq_neg_logDeriv a ha s hs

end
end SevenEighths.IdealLogDerivative

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.LogDerivative
namespace OAI

noncomputable section
open scoped Classical Topology
namespace SevenEighths.HeckeLogDerivative
open HeckeFamily

theorem coeff_LSeries_eq (χ : Character) {s : ℂ} (hs : 1 < s.re) :
    LSeries (coeff χ) s = -deriv (LFunction χ) s / LFunction χ s :=
  IdealLogDerivative.coeff_LSeries_eq_neg_logDeriv_of_eq _ (idealCoeff_norm_le_one χ)
    (LFunction χ) (fun _ hz => LFunction_eq_series χ hz) s hs

end SevenEighths.HeckeLogDerivative

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.PrimeDyadic
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open MeasureTheory Set
namespace SevenEighths.HeckePrimeDyadic
open HeckeFamily HeckeDyadic

theorem series_eq_tsum (χ : Character) {s : ℂ} (hs : 1 < s.re) :
    series χ s = ∑' I : NonzeroIdeal, coefficient χ I.val * (norm I : ℂ)^(-s) := by
  have he : (∑' I : NonzeroIdeal, (IdealMangoldt.value I.val : ℂ) *
      IdealEuler.weighted (idealCoeff χ) s I.val) =
      ∑' I : Ideal O, (IdealMangoldt.value I : ℂ) * IdealEuler.weighted (idealCoeff χ) s I := by
    apply tsum_subtype_eq_of_support_subset (s := {I : Ideal O | I ≠ 0})
      (f := fun I : Ideal O => (IdealMangoldt.value I : ℂ) * IdealEuler.weighted (idealCoeff χ) s I)
    intro I hI hi
    subst I
    exact hI (by
      change (IdealMangoldt.value 0 : ℂ) * IdealEuler.weighted (idealCoeff χ) s 0 = 0
      rw [IdealMangoldt.value_zero, Complex.ofReal_zero, zero_mul])
  change -deriv (LFunction χ) s / LFunction χ s = _
  rw [← HeckeLogDerivative.coeff_LSeries_eq χ hs]
  change LSeries (IdealLogDerivative.coeff (idealCoeff χ)) s = _
  rw [← IdealLogDerivative.mangoldt_series_eq_LSeries _ (idealCoeff_norm_le_one χ) s hs, ← he]
  apply tsum_congr
  intro I
  simp only [coefficient, IdealEuler.weighted, IdealEuler.normWeight,
    MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, CubicEisenstein.fullIdealWeight]
  rw [ite_eq_right_iff.mpr (fun h => (I.property h).elim)]
  simp only [HeckeDyadic.norm, Complex.ofReal_natCast, mul_assoc]

end SevenEighths.HeckePrimeDyadic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.PrimeDyadicEuler
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
namespace SevenEighths.HeckePrimeDyadic
open HeckeFamily HeckeDyadic

theorem eulerBound_summable {b : ℝ} (hb : 1<b) :
    Summable (fun I : NonzeroIdeal => IdealMangoldt.value I.val * (norm I)^(-b)) := by
  have ha (I : Ideal O) : ‖IdealEuler.normWeight 0 I‖ ≤ 1 := by
    change ‖CubicEisenstein.fullIdealWeight 0 I‖ ≤ 1
    by_cases hI : I = 0
    · rw [CubicEisenstein.fullIdealWeight, ite_eq_left_iff.mpr (fun h => (h hI).elim), norm_zero]
      norm_num
    · rw [CubicEisenstein.fullIdealWeight, ite_eq_right_iff.mpr (fun h => (hI h).elim)]
      simp
  have hf := (IdealLogDerivative.mangoldt_weighted_summable_norm
    (IdealEuler.normWeight 0) ha (b : ℂ) (by simpa using hb)).comp_injective
      (Subtype.val_injective : Function.Injective (fun I : NonzeroIdeal => I.val))
  convert (preTransparency := .instances) hf using 1
  ext I
  simp only [Function.comp_apply, IdealEuler.weighted, IdealEuler.normWeight,
    MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, CubicEisenstein.fullIdealWeight,
    ite_eq_right_iff.mpr (fun h => (I.property h).elim), neg_zero, Complex.cpow_zero, one_mul]
  change IdealMangoldt.value I.val * (norm I)^(-b) =
    ‖(IdealMangoldt.value I.val : ℂ) * (norm I : ℂ)^(-(b : ℂ))‖
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (IdealMangoldt.value_nonneg _),
    Complex.norm_cpow_eq_rpow_re_of_pos (norm_pos I)]
  simp

theorem series_norm_le (χ : Character) {b : ℝ} (hb : 1<b)
    {s : ℂ} (hs : b≤ s.re) : ‖series χ s‖ ≤ eulerBound b := by
  rw [series_eq_tsum χ (hb.trans_le hs)]
  have hbound (I : NonzeroIdeal) :
      ‖coefficient χ I.val * (norm I : ℂ)^(-s)‖ ≤
        IdealMangoldt.value I.val * (norm I)^(-b) := by
    rw [norm_mul]
    have hn : 1 ≤ norm I := by
      unfold HeckeDyadic.norm
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr I.property)
    have hc : ‖coefficient χ I.val‖ ≤ IdealMangoldt.value I.val := by
      rw [coefficient, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (IdealMangoldt.value_nonneg _)]
      exact mul_le_of_le_one_right (IdealMangoldt.value_nonneg _) (idealCoeff_norm_le_one χ _)
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (norm_pos I), Complex.neg_re]
    exact mul_le_mul hc (Real.rpow_le_rpow_of_exponent_le hn (neg_le_neg hs))
      (Real.rpow_nonneg (norm_pos I).le _) (IdealMangoldt.value_nonneg _)

  have hf := (eulerBound_summable hb).of_nonneg_of_le (fun _ => norm_nonneg _) hbound
  exact (norm_tsum_le_tsum_norm hf).trans (hf.tsum_le_tsum hbound (eulerBound_summable hb))

end SevenEighths.HeckePrimeDyadic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.PrimeDyadicContour
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open MeasureTheory Set Complex
namespace SevenEighths.HeckePrimeDyadic
open HeckeFamily HeckeDyadic

theorem integrand_norm (χ : Character) (W : ℝ → ℂ)
    (D σ freq : ℝ) (hD : 0<D) (s : ℂ) :
    ‖integrand χ W D σ freq s‖ =
      ‖mellin W s‖*D^(s.re+σ-1/2)*‖series χ (s+HeckeDyadic.shift σ freq)‖ := by
  unfold integrand
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hD]
  simp

end SevenEighths.HeckePrimeDyadic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.PrimeDyadicEstimates
namespace OAI

noncomputable section
open scoped Classical Topology ContDiff
open MeasureTheory Set Complex
namespace SevenEighths.HeckePrimeDyadic
open HeckeFamily HeckeDyadic

theorem absolute_tail_bound (χ : Character) (W : ℝ → ℂ)
    (D r σ freq C T : ℝ) (n : ℕ) (hD : 0<D) (hr : 1< r+σ) (hC : 0≤C) (hT : 0≤T)
    (hm : ∀ t : ℝ, (1+|t|)^(n+2)*‖mellin W ((r : ℂ)+t*I)‖≤C) :
    ‖∫ t : ℝ in (Icc (-T) T)ᶜ, integrand χ W D σ freq ((r : ℂ)+t*I)‖ ≤
      (C*D^(r+σ-1/2)*eulerBound (r+σ))/(1+T)^n*Real.pi := by
  apply rapid_tail_bound _ _ T n
  · exact mul_nonneg (mul_nonneg hC (Real.rpow_nonneg hD.le _))
      (tsum_nonneg (fun I => mul_nonneg (IdealMangoldt.value_nonneg _) (Real.rpow_nonneg (norm_pos I).le _)))
  · exact hT
  · intro t
    rw [integrand_norm χ W D σ freq hD]
    have hb := series_norm_le χ hr (s := (r : ℂ)+t*I+shift σ freq) (by simp)
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im, zero_mul,
      sub_self, add_zero]
    calc
      _ = ((1+|t|)^(n+2)*‖mellin W ((r : ℂ)+t*I)‖)*D^(r+σ-1/2)*
        ‖series χ ((r : ℂ)+t*I+shift σ freq)‖ := by ring
      _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_right (hm t) (Real.rpow_nonneg hD.le _))
        hb (norm_nonneg _) (mul_nonneg hC (Real.rpow_nonneg hD.le _))

theorem central_segment_bound (χ : Character) (W : ℝ → ℂ)
    (D l σ freq C K T : ℝ) (hD : 0<D) (hC : 0≤C) (hK : 0≤K) (hT : 0≤T)
    (hm : ∀ t : ℝ, (1+|t|)^2*‖mellin W ((l : ℂ)+t*I)‖≤C)
    (hs : ∀ t ∈ Icc (-T) T, ‖series χ ((l : ℂ)+t*I+shift σ freq)‖≤K) :
    ‖∫ t : ℝ in -T..T, integrand χ W D σ freq ((l : ℂ)+t*I)‖ ≤
      C*D^(l+σ-1/2)*K*Real.pi := by
  rw [intervalIntegral.integral_of_le (by linarith : -T≤T)]
  have hint := integrable_inv_one_add_sq.const_mul (C*D^(l+σ-1/2)*K)
  calc
    _ ≤ ∫ t : ℝ in Ioc (-T) T, (C*D^(l+σ-1/2)*K)*(1+t^2)⁻¹ := by
      apply norm_integral_le_of_norm_le hint.integrableOn
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      rw [integrand_norm χ W D σ freq hD]
      have hb := CubicReflectionKernel.weighted_two_to_cauchy (norm_nonneg _) t (hm t)
      simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im, zero_mul,
        sub_self, add_zero]
      calc
        _ ≤ (C/(1+t^2))*D^(l+σ-1/2)*K :=
          mul_le_mul (mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg hD.le _))
            (hs t ⟨ht.1.le,ht.2⟩) (norm_nonneg _) (by positivity)
        _ = _ := by ring
    _ ≤ ∫ t : ℝ, (C*D^(l+σ-1/2)*K)*(1+t^2)⁻¹ :=
      integral_mono_measure Measure.restrict_le_self (by filter_upwards [] with t; positivity) hint
    _ = _ := by rw [integral_const_mul, integral_univ_inv_one_add_sq]

theorem horizontal_join_bound (χ : Character) (W : ℝ → ℂ)
    (D σ freq l r y C K : ℝ) (n : ℕ)
    (hD : 1≤D) (hlr : l≤ r) (hC : 0≤C) (_hK : 0≤K)
    (hm : ∀ x ∈ Icc l r, (1+|y|)^n*‖mellin W ((x : ℂ)+y*I)‖≤C)
    (hs : ∀ x ∈ Icc l r, ‖series χ ((x : ℂ)+y*I+shift σ freq)‖≤K) :
    ‖∫ x : ℝ in l..r, integrand χ W D σ freq ((x : ℂ)+y*I)‖ ≤
      (C*D^(r+σ-1/2)*K/(1+|y|)^n)*|r-l| := by
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro x hx
  have hx' : x ∈ Icc l r := by simpa [uIcc_of_le hlr] using uIoc_subset_uIcc hx
  have hb : ‖mellin W ((x : ℂ)+y*I)‖≤C/(1+|y|)^n := by
    apply (le_div_iff₀ (by positivity : 0<(1+|y|)^n)).mpr
    simpa [mul_comm] using hm x hx'
  have hpow : D^(x+σ-1/2)≤D^(r+σ-1/2) :=
    Real.rpow_le_rpow_of_exponent_le hD (by linarith [hx'.2])
  rw [integrand_norm χ W D σ freq (by linarith)]
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im, zero_mul,
    sub_self, add_zero]
  calc
    _ ≤ (C/(1+|y|)^n)*D^(r+σ-1/2)*K :=
      mul_le_mul (mul_le_mul hb hpow (by positivity) (by positivity))
        (hs x hx') (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem polynomial_bound_of_rectangle_oai (χ : Character) (hχ : χ.residue≠1)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (D σ freq l r T C₂ Cn K : ℝ) (n : ℕ)
    (hD : 1≤D) (hlr : l≤ r) (hr : 1< r+σ) (hT : 0≤T)
    (hC₂ : 0≤C₂) (hCn : 0≤Cn) (hK : 0≤K)
    (hm₂ : ∀ t : ℝ, (1+|t|)^2*‖mellin W ((l : ℂ)+t*I)‖≤C₂)
    (hmn : ∀ x ∈ Icc l r, ∀ t : ℝ,
      (1+|t|)^(n+2)*‖mellin W ((x : ℂ)+t*I)‖≤Cn)
    (hz : ∀ s ∈ (uIcc l r ×ℂ uIcc (-T) T), LFunction χ (s+shift σ freq)≠0)
    (hs : ∀ s ∈ (uIcc l r ×ℂ uIcc (-T) T),
      ‖series χ (s+shift σ freq)‖≤K) :
    ‖polynomial χ W D σ freq‖≤(1/(2*Real.pi))*
      (C₂*D^(l+σ-1/2)*K*Real.pi +
       2*(Cn*D^(r+σ-1/2)*K/(1+T)^n)*|r-l| +
       (Cn*D^(r+σ-1/2)*eulerBound (r+σ))/(1+T)^n*Real.pi) := by
  have hDp : 0<D := by linarith
  have hmem (x t : ℝ) (hx : x∈Icc l r) (ht : t∈Icc (-T) T) :
      ((x : ℂ)+t*I) ∈ (uIcc l r ×ℂ uIcc (-T) T) := by
    change (((x : ℂ)+t*I).re∈uIcc l r) ∧ (((x : ℂ)+t*I).im∈uIcc (-T) T)
    simpa [uIcc_of_le hlr,uIcc_of_le (by linarith : -T≤T)] using And.intro hx ht
  have hcentral := central_segment_bound χ W D l σ freq C₂ K T hDp hC₂ hK hT
    hm₂ (fun t ht => hs _ (hmem l t ⟨le_rfl,hlr⟩ ht))
  have hm (x : ℝ) (hx : x∈Icc l r) (t : ℝ) :
      (1+|t|)^n*‖mellin W ((x : ℂ)+t*I)‖≤Cn := by
    apply le_trans _ (hmn x hx t)
    gcongr
    · exact le_add_of_nonneg_right (abs_nonneg t)
    · omega
  have hbottom := horizontal_join_bound χ W D σ freq l r (-T) Cn K n hD hlr hCn hK
    (fun x hx => hm x hx (-T)) (fun x hx => hs _ (hmem x (-T) hx ⟨le_rfl,by linarith⟩))
  have htop := horizontal_join_bound χ W D σ freq l r T Cn K n hD hlr hCn hK
    (fun x hx => hm x hx T) (fun x hx => hs _ (hmem x T hx ⟨by linarith,le_rfl⟩))
  simp only [abs_neg,abs_of_nonneg hT,ofReal_neg] at hbottom htop
  have htail := absolute_tail_bound χ W D r σ freq Cn T n hDp hr hCn hT
    (hmn r ⟨hlr,le_rfl⟩)
  rw [polynomial_finite_shift χ hχ W a b ha hWs hW D σ freq l r T hDp hr hT hz,
    norm_mul]
  have hnorm : ‖(1/(2*Real.pi) : ℂ)‖=(1/(2*Real.pi) : ℝ) := by
    simp [Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  rw [hnorm]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact (norm_four_sides _ _ _ _).trans (by linarith)

end SevenEighths.HeckePrimeDyadic

end

end OAI
end

theorem solution : type_of% @OAI.SevenEighths.HeckePrimeDyadic.polynomial_bound_of_rectangle_oai := @OAI.SevenEighths.HeckePrimeDyadic.polynomial_bound_of_rectangle_oai
