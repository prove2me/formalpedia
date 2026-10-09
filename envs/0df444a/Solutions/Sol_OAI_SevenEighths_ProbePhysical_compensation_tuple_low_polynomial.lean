-- Prove2me | solution 1 for OAI.SevenEighths.ProbePhysical.compensation_tuple_low_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T04:21:25.845952+00:00
-- url     : https://prove2.me/submissions/6eb29186-e33b-4b84-a0c1-010a98738125

import Mathlib
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B026

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

namespace DyadicTransfer

theorem annularCutoff_eq_zero_of_le_half (φ : ℝ → ℂ)
    (hsmall : ∀ y : ℝ, y ≤ 1 → φ y = 1)
    {y : ℝ} (hy : y ≤ 1 / 2) : annularCutoff φ y = 0 := by
  have hy1 : y ≤ 1 := by linarith
  have h2y : 2 * y ≤ 1 := by linarith
  simp [annularCutoff, hsmall y hy1, hsmall (2 * y) h2y]

end DyadicTransfer

open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

end

end OAI
end

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

theorem triple_scale_bounds (a b c : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) :
    a ≤ a * b ^ 3 * c ^ 3 ∧ b ≤ a * b ^ 3 * c ^ 3 ∧ c ≤ a * b ^ 3 * c ^ 3 := by
  have ha0 : 0 ≤ a := by linarith
  have hb0 : 0 ≤ b := by linarith
  have hc0 : 0 ≤ c := by linarith
  have hb3 : 1 ≤ b ^ 3 := one_le_pow₀ hb
  have hc3 : 1 ≤ c ^ 3 := one_le_pow₀ hc
  constructor
  · calc a = a * 1 * 1 := by ring
         _ ≤ a * b ^ 3 * c ^ 3 := by gcongr
  constructor
  · calc b ≤ b ^ 3 := le_self_pow₀ hb (by decide)
         _ = 1 * b ^ 3 * 1 := by ring
         _ ≤ a * b ^ 3 * c ^ 3 := by gcongr
  · calc c ≤ c ^ 3 := le_self_pow₀ hc (by decide)
         _ = 1 * 1 * c ^ 3 := by ring
         _ ≤ a * b ^ 3 * c ^ 3 := by gcongr

theorem finite_support_norm_triple (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (X : ℝ) (hX : 0 < X) (F : Ideal O × Ideal O × Ideal O → ℂ)
    (hzero : ∀ I J H, I = 0 ∨ J = 0 ∨ H = 0 → F (I, J, H) = 0)
    (hwindow : ∀ I J H,
      W ((Ideal.absNorm I : ℝ) * (Ideal.absNorm J : ℝ) ^ 3 *
        (Ideal.absNorm H : ℝ) ^ 3 / X) = 0 → F (I, J, H) = 0) :
    (Function.support F).Finite := by
  obtain ⟨B, hB, hbound⟩ := compact_window_bound W hW
  obtain ⟨M, hM⟩ := exists_nat_gt (B * X)
  let S := {I : Ideal O | Ideal.absNorm I ≤ M}
  have hS : S.Finite := Ideal.finite_setOfPred_absNorm_le M
  apply (hS.prod (hS.prod hS)).subset
  rintro ⟨I, J, H⟩ hF
  have hF0 : F (I, J, H) ≠ 0 := hF
  have hI : I ≠ 0 := fun h => hF0 (hzero I J H (Or.inl h))
  have hJ : J ≠ 0 := fun h => hF0 (hzero I J H (Or.inr (Or.inl h)))
  have hH : H ≠ 0 := fun h => hF0 (hzero I J H (Or.inr (Or.inr h)))
  have hw : W ((Ideal.absNorm I : ℝ) * (Ideal.absNorm J : ℝ) ^ 3 *
      (Ideal.absNorm H : ℝ) ^ 3 / X) ≠ 0 := fun h => hF0 (hwindow I J H h)
  have hsize := (div_le_iff₀ hX).mp (hbound _ hw)
  have hb := triple_scale_bounds _ _ _ (norm_at_least_one I hI)
    (norm_at_least_one J hJ) (norm_at_least_one H hH)
  have hIM : Ideal.absNorm I ≤ M := by exact_mod_cast (hb.1.trans hsize).trans hM.le
  have hJM : Ideal.absNorm J ≤ M := by exact_mod_cast (hb.2.1.trans hsize).trans hM.le
  have hHM : Ideal.absNorm H ≤ M := by exact_mod_cast (hb.2.2.trans hsize).trans hM.le
  exact ⟨hIM, hJM, hHM⟩

end

open ActualEisensteinCubic
open IdealMobiusDivisorSum (idealDivisors mem_idealDivisors sum_moebius_divisors)

end CompletedGauss

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.CompletedExpansion
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

open ActualEisensteinCubic

theorem finite_support_expandedTerm (Ψ : O →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) :
    (Function.support (fun p : Ideal O × Ideal O × Ideal O =>
      expandedTerm Ψ W X p.1 p.2.1 p.2.2)).Finite := by
  apply finite_support_norm_triple W hW X hX
  · intro I H J hz
    rcases hz with rfl | rfl | rfl <;> simp [expandedTerm]
  · intro I H J hw
    simp [expandedTerm, Vstar, hw]

theorem expandedTerm_one (Ψ : O →* ℂ) (W : ℝ → ℂ) (X : ℝ) (I J : Ideal O) :
    expandedTerm Ψ W X I 1 J = summand Ψ W X I J := by
  simp only [expandedTerm, summand, UniqueFactorizationMonoid.moebius_one, Int.cast_one,
    one_mul, map_one, Nat.cast_one, one_pow, mul_one]
  ring

theorem completedT_finite_support (Ψ : O →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) :
    (Function.support (fun p : Ideal O × Ideal O => summand Ψ W X p.1 p.2)).Finite := by
  have hf := finite_support_expandedTerm Ψ W hW X hX
  have hinj : Function.Injective (fun p : Ideal O × Ideal O => (p.1, (1 : Ideal O), p.2)) := by
    intro a b hab
    exact Prod.ext (Prod.mk.inj hab).1 (Prod.mk.inj (Prod.mk.inj hab).2).2
  have hp := Set.Finite.preimage hinj.injOn hf
  change (Function.support (fun p : Ideal O × Ideal O => expandedTerm Ψ W X p.1 1 p.2)).Finite at hp
  simpa only [expandedTerm_one] using hp

open ActualEisensteinCubic ConcreteTraceCRT

end CompletedGauss

namespace FiniteRayExpansion

variable {R : Type*} [CommRing R] [Fintype R]

attribute [local instance] OAI.FiniteRayExpansion.instFintypeMulCharComplex_definitions
theorem zeroExtendUnits_fourier (f : Rˣ → ℂ) (r : R) :
    zeroExtendUnits f r = ∑ χ : MulChar R ℂ, unitFourierCoeff f χ * χ r := by
  by_cases hr : IsUnit r
  · obtain ⟨u, rfl⟩ := hr
    rw [zeroExtendUnits_unit]
    exact (unit_fourier_inversion f u).symm
  · rw [zeroExtendUnits_nonunit f r hr]
    simp only [MulChar.map_nonunit _ hr, mul_zero, Finset.sum_const_zero]

end FiniteRayExpansion

open scoped BigOperators Classical

namespace RayFourExpansion
open ActualEisensteinCubic ConcreteTraceCRT ActualEisensteinCoordinates QuadraticGaussRay
open FiniteRayExpansion

theorem phase_expansion (f : RayRing → ℂ) (a : O) :
    rayMask a * f (Ideal.Quotient.mk (Ideal.span {(4 : O)}) a) =
      ∑ χ : RayCharacter, phaseCoeff f χ * rayCharacter χ a := by
  rw [rayMask, ← zeroExtendUnits_restrict]
  exact zeroExtendUnits_fourier _ _

end RayFourExpansion

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

end CompletedGauss

open Filter MeasureTheory
open scoped Classical BigOperators Topology

open scoped BigOperators Classical
open Finset AddChar MulChar EisensteinEmbedding

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Cusp.ResiduePhases
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

open scoped Classical BigOperators

namespace CompletedGauss
open ActualEisensteinCubic CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O

variable (Ψ Φ:Eis→*ℂ) (h:∀n:Eis,lambda^2∣n-1→Ψ n=Φ n)
include h

lemma columnWeight_congr_primary (I:Ideal Eis) : columnWeight Ψ I=columnWeight Φ I := by
  by_cases hi:primaryGenerator I=0
  · simp only [columnWeight,squarefreeGaussCoefficient,hi,ne_eq,not_true_eq_false,and_false,
      dite_false,zero_mul]
  · rw [columnWeight,columnWeight,h _ (primaryGenerator_spec I hi).2]

lemma cubeWeight_congr_primary (I:Ideal Eis) : cubeWeight Ψ I=cubeWeight Φ I := by
  change star (FiniteGaussPhase.angularFactor (primaryGenerator I))^3*Ψ (primaryGenerator I)^3/
      (Ideal.absNorm I:ℂ)=star (FiniteGaussPhase.angularFactor (primaryGenerator I))^3*Φ (primaryGenerator I)^3/
      (Ideal.absNorm I:ℂ)
  by_cases hi:primaryGenerator I=0
  · simp only [hi,FiniteGaussPhase.angularFactor,map_zero,norm_zero,Complex.ofReal_zero,
      div_zero,star_zero,zero_pow (by decide : (3:ℕ)≠0),zero_mul,zero_div]
  · rw [h _ (primaryGenerator_spec I hi).2]

end CompletedGauss

open scoped Classical BigOperators

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.FixedFrequencyExpansion
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
open ActualEisensteinCubic CompletedGauss
open CubicEisenstein hiding summand
local notation "Eis" => ActualEisensteinCubic.O

lemma summand_mul_fixed_twist (φ χ:Eis→*ℂ) (W:ℝ→ℂ) (X:ℝ) (I J:Ideal Eis) :
    summand (φ*χ) W X I J=
      φ (primaryGenerator I*(primaryGenerator J)^3)*summand χ W X I J := by
  have he (η:Eis→*ℂ) : cubeWeight η J=
      star (FiniteGaussPhase.angularFactor (primaryGenerator J))^3*
        η (primaryGenerator J)^3/(Ideal.absNorm J:ℂ):=rfl
  rw [summand,summand,he,he]
  simp only [columnWeight,MonoidHom.mul_apply,map_mul,map_pow,mul_pow]
  ring

end

open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve
open CubicEisenstein hiding summand
local notation "Eis" => ActualEisensteinCubic.O

end CanonicalRowCompletion

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.Completion
namespace OAI

namespace SevenEighths.InverseMoment

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss

local notation "Eis" => ActualEisensteinCubic.O

theorem markedCompletedT_summable (Ψ : Eis →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) (d : Ideal Eis → ℂ) :
    Summable (fun p : Ideal Eis × Ideal Eis =>
      summand Ψ W X p.1 p.2 * d (p.1 * p.2 ^ 3)) := by
  apply summable_of_hasFiniteSupport
  apply (completedT_finite_support Ψ W hW X hX).subset
  intro p hp hz
  exact hp (by simp only [hz, zero_mul])

theorem markedCompletedT_eq_tsum (Ψ : Eis →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) (d : Ideal Eis → ℂ) :
    markedCompletedT Ψ W X d = ∑' p : Ideal Eis × Ideal Eis,
      summand Ψ W X p.1 p.2 * d (p.1 * p.2 ^ 3) :=
  (markedCompletedT_summable Ψ W hW X hX d).tsum_prod.symm

end

end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.Completed
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.ProbeCompleted
open ActualEisensteinCubic CompletedGauss
open RayFourExpansion QuadraticGaussRay SecondPassArithmetic

local notation "O" => ActualEisensteinCubic.O

theorem completedIndex_eq_primaryGenerator (I J : Ideal O) :
    completedIndex I J = primaryGenerator (I * J ^ 3) := by
  simp only [completedIndex, primaryGenerator_mul, CubicEisenstein.primaryGenerator_pow]

theorem completedCorrection_expansion (I J : Ideal O) :
    completedCorrection I J =
      ∑ χ : RayCharacter, correctionCoeff χ * rayCharacter χ (completedIndex I J) := by
  exact phase_expansion (fun r => star (fixedGQuotientValue r)) (completedIndex I J)

theorem correctedSummand_ray_expansion (S : Finset (Ideal O)) (D I J : Ideal O)
    (Ψ : O →* ℂ) (W : ℝ → ℂ) (X : ℝ) :
    correctedSummand S D Ψ W X I J =
      ∑ χ : RayCharacter, correctionCoeff χ *
        markedSummand S D (rayMonoid χ * Ψ) W X I J := by
  unfold correctedSummand
  rw [completedCorrection_expansion, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro χ _
  unfold markedSummand
  rw [CanonicalRowCompletion.summand_mul_fixed_twist]
  simp only [rayMonoid_apply, completedIndex]
  ring

theorem markedSummand_summable (S : Finset (Ideal O)) (D : Ideal O)
    (Ψ : O →* ℂ) (W : ℝ → ℂ) (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) :
    Summable (fun p : Ideal O × Ideal O => markedSummand S D Ψ W X p.1 p.2) := by
  apply summable_of_hasFiniteSupport
  apply (completedT_finite_support Ψ W hW X hX).subset
  intro p hp
  exact fun hz => hp (by simp only [markedSummand, hz, mul_zero])

theorem correctedCompletedT_ray_expansion (S : Finset (Ideal O)) (D : Ideal O)
    (Ψ : O →* ℂ) (W : ℝ → ℂ) (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) :
    correctedCompletedT S D Ψ W X =
      ∑ χ : RayCharacter, correctionCoeff χ *
        markedCompletedT S D (rayMonoid χ * Ψ) W X := by
  unfold correctedCompletedT
  simp_rw [correctedSummand_ray_expansion]
  rw [Summable.tsum_finsetSum (fun χ _ =>
    (markedSummand_summable S D (rayMonoid χ * Ψ) W hW X hX).mul_left (correctionCoeff χ))]
  simp only [tsum_mul_left, markedCompletedT]

end SevenEighths.ProbeCompleted
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.Row
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.ProbeRow
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion
open CanonicalQuadraticSieve InitialMeanSquare ProbeCompleted

local notation "O" => ActualEisensteinCubic.O

theorem rowCoefficient_apply (η : HeckeFamily.Character) (Xi : O →* ℂ)
    (s : O) (hs : Supported (Ideal.span {s})) (m a : O) :
    rowCoefficient η Xi s hs m a = HeckeFamily.elementCoeff η a * star (Xi a) *
      sexticReciprocityPhase s a * idealRowHom m (Ideal.span {a}) := rfl

end SevenEighths.ProbeRow
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.Calibration
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

theorem calibrationForSet_excluded (S : Finset (Ideal O)) (hS : ∀ P ∈ S, P.IsMaximal) :
    (calibrationForSet S hS).excluded = S := by
  change Finset.univ.image (fun P : S => P.val) = S
  ext P
  simp

theorem calibrationForSet_span (S : Finset (Ideal O)) (hS : ∀ P ∈ S, P.IsMaximal) :
    Ideal.span {(calibrationForSet S hS).generator} = ∏ P ∈ S, P := by
  change Ideal.span {finitePrimeModulus (fun P : S => P.val)} = _
  rw [span_finitePrimeModulus]
  exact Finset.prod_coe_sort S (fun P : Ideal O => P)

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.CalibrationSupport
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve ProbeRow
local notation "O" => ActualEisensteinCubic.O

theorem calibrationForSet_coprime_iff (S : Finset (Ideal O)) (hS : ∀ P ∈ S, P.IsMaximal)
    (a : O) : IsCoprime (calibrationForSet S hS).generator a ↔ ∀ P ∈ S, a ∉ P := by
  rw [← Ideal.isCoprime_span_singleton_iff, calibrationForSet_span, IsCoprime.prod_left_iff]
  constructor
  · intro h P hP
    let : P.IsMaximal := hS P hP
    exact (SixthPowerAverage.prime_coprime_span_iff P a).mp (h P hP)
  · intro h P hP
    let : P.IsMaximal := hS P hP
    exact (SixthPowerAverage.prime_coprime_span_iff P a).mpr (h P hP)

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.GaussianPartition
namespace OAI

noncomputable section
open scoped Classical Topology ContDiff
namespace SevenEighths.ProbePhysical
open DyadicTransfer

lemma gaussianCutoff_small (y : ℝ) (hy : y≤1) : gaussianCutoff y=1 := by
  simp only [gaussianCutoff,Real.smoothTransition.one_of_one_le (by linarith : 1≤2-y),Complex.ofReal_one]
lemma gaussianCutoff_large (y : ℝ) (hy : 2≤y) : gaussianCutoff y=0 := by
  simp only [gaussianCutoff,Real.smoothTransition.zero_of_nonpos (by linarith : 2-y≤0),Complex.ofReal_zero]
lemma gaussianAnnulus_small (y : ℝ) (hy : y≤1/2) : gaussianAnnulus y=0 :=
  annularCutoff_eq_zero_of_le_half gaussianCutoff gaussianCutoff_small hy
lemma gaussianAnnulus_large (y : ℝ) (hy : 2≤y) : gaussianAnnulus y=0 :=
  annularCutoff_eq_zero_of_two_le gaussianCutoff gaussianCutoff_large hy

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.LowPeriod
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ProbeRow CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss
open RayFourExpansion InitialMeanSquare SecondPassArithmetic CanonicalCoefficientClass
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

lemma periodicCalibrationXi_eq_primary (C : CalibrationData) (B : O)
    (D : GoodMaskRowData B 1 C.generator) (hBL : λ₀∣B) (hB2 : (2:O)∣B)
    (n : O) (hn : Supported (Ideal.span {n})) (hpn : λ₀^2∣n-1) (hc : IsCoprime B n) :
    periodicCalibrationXi C B D n=C.Xi n := by
  have he := rowTwist_eq_actualPeriodicRow_primary (1:O→*ℂ) B 1 C.generator hBL hB2
    D.numeratorUnit D.numeratorLambda D.numeratorTwo D.numeratorGood D.numeratorSupported
    D.numeratorPrimary D.numeratorFactor n hpn
  rw [rowTwist_extract_sixth_mask _ _ _ _ _ hn] at he
  have hmask : coprimalityMask B n=(1:ℂ) := by
    change (if IsCoprime B n then (1:ℂ) else 0)=1
    rw [if_pos hc]
  simp only [MonoidHom.one_apply,hmask,one_mul,one_pow] at he
  change C.residueMonoid n*_ = C.residueMonoid n*idealRowHom C.generator (Ideal.span {n})
  rw [←he]

lemma lowPeriodicBase_eq_primary (η : HeckeFamily.Character) (C : CalibrationData) (B : O)
    (D : GoodMaskRowData B 1 C.generator) (hBL : λ₀∣B) (hB2 : (2:O)∣B)
    (s : O) (hs : Supported (Ideal.span {s})) (χ : RayCharacter)
    (n : O) (hn : Supported (Ideal.span {n})) (hpn : λ₀^2∣n-1) (hc : IsCoprime B n) :
    lowPeriodicBase η C B D s hs χ n=(rayMonoid χ*physicalRowBase η C.Xi s hs) n := by
  change ((rayMonoid χ n*targetMonoid η n)*star (periodicCalibrationXi C B D n))*sexticReciprocityPhase s n=
    rayMonoid χ n*((targetMonoid η n*star (C.Xi n))*sexticReciprocityPhase s n)
  rw [periodicCalibrationXi_eq_primary C B D hBL hB2 n hn hpn hc]
  ring

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.LowPuncture
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ProbeRow ProbeCompleted CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss
open RayFourExpansion InitialMeanSquare SecondPassArithmetic CanonicalCoefficientClass ActualEisensteinCubic
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

lemma calibration_generator_dvd (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (a : O) (ha : Ideal.span {a}∈S) : a∣(calibrationForSet S hS).generator := by
  apply Ideal.span_singleton_dvd_span_singleton_iff_dvd.mp
  rw [calibrationForSet_span]
  exact Finset.dvd_prod_of_mem (fun P : Id=>P) ha

lemma calibration_generator_bad (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S) :
    λ₀∣(calibrationForSet S hS).generator ∧ (2:O)∣(calibrationForSet S hS).generator := by
  constructor
  · apply calibration_generator_dvd S hS
    apply hbad
    simp only [fixedBadPrimes,Finset.mem_insert,Finset.mem_singleton]
    exact Or.inl rfl
  · apply calibration_generator_dvd S hS
    apply hbad
    simp only [fixedBadPrimes,Finset.mem_insert,Finset.mem_singleton]
    exact Or.inr trivial

lemma supported_of_coprime_bad (B n : O) (hBL : λ₀∣B) (hB2 : (2:O)∣B)
    (hc : IsCoprime B n) : Supported (Ideal.span {n}) := by
  apply supported_span_iff n |>.mpr
  constructor
  · exact PrimaryIdealUnitReindex.lambda_prime_actual.irreducible.coprime_iff_not_dvd.mp
      (hc.of_isCoprime_of_dvd_left hBL)
  · have h2 : IsCoprime (-2:O) n := (hc.of_isCoprime_of_dvd_left hB2).neg_left
    have hn := negative_two_prime.irreducible.coprime_iff_not_dvd.mp h2
    simpa only [neg_dvd] using hn

lemma lowPeriodicBase_zero_of_not_coprime (η : HeckeFamily.Character) (C : CalibrationData) (B : O)
    (D : GoodMaskRowData B 1 C.generator) (s : O) (hs : Supported (Ideal.span {s}))
    (χ : RayCharacter) (n : O) (hc : ¬IsCoprime B n) : lowPeriodicBase η C B D s hs χ n=0 := by
  have hm : coprimalityMask B n=(0:ℂ) := by change (if IsCoprime B n then (1:ℂ) else 0)=0;rw [if_neg hc]
  change ((rayMonoid χ n*targetMonoid η n)*star (C.residueMonoid n*
      ((((1:O→*ℂ) n*coprimalityMask B n)*
        numeratorBadTwist D.numeratorUnit D.numeratorLambda D.numeratorTwo D.numeratorGood D.numeratorSupported n)*
        movingNumeratorRow D.numeratorGood D.numeratorSupported n)))*sexticReciprocityPhase s n=0
  rw [hm]
  simp only [mul_zero,zero_mul,star_zero]

lemma lowPeriodicRow_eq_primary (η : HeckeFamily.Character) (C : CalibrationData) (B : O)
    (D : GoodMaskRowData B 1 C.generator) (hBL : λ₀∣B) (hB2 : (2:O)∣B)
    (s : O) (hs : Supported (Ideal.span {s})) (χ : RayCharacter) (z n : O) (hpn : λ₀^2∣n-1) :
    rowTwist (lowPeriodicBase η C B D s hs χ) B 1 z n=
      (coprimalityMask B*(rayMonoid χ*rowCoefficient η C.Xi s hs z)) n := by
  by_cases hc : IsCoprime B n
  · have hn := supported_of_coprime_bad B n hBL hB2 hc
    have hm : coprimalityMask B n=(1:ℂ) := by change (if IsCoprime B n then (1:ℂ) else 0)=1;rw [if_pos hc]
    rw [rowTwist_extract_sixth_mask _ _ _ _ _ hn,lowPeriodicBase_eq_primary η C B D hBL hB2 s hs χ n hn hpn hc]
    simp only [MonoidHom.mul_apply,hm,mul_one,one_pow,one_mul]
    change (rayMonoid χ n*((targetMonoid η n*star (C.Xi n))*sexticReciprocityPhase s n))*
      idealRowHom z (Ideal.span {n})=rayMonoid χ n*
        (((targetMonoid η n*star (C.Xi n))*sexticReciprocityPhase s n)*idealRowHom z (Ideal.span {n}))
    ring
  · have hm : coprimalityMask B n=(0:ℂ) := by change (if IsCoprime B n then (1:ℂ) else 0)=0;rw [if_neg hc]
    change lowPeriodicBase η C B D s hs χ n*idealRowHom (B^6*1^4*z) (Ideal.span {n})=
      coprimalityMask B n*(rayMonoid χ n*rowCoefficient η C.Xi s hs z n)
    rw [lowPeriodicBase_zero_of_not_coprime η C B D s hs χ n hc,hm,zero_mul,zero_mul]

lemma calibration_coprime_iff_excluded_span (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (a : O) :
    IsCoprime (calibrationForSet S hS).generator a ↔ ∀P∈S,¬P∣Ideal.span {a} := by
  rw [calibrationForSet_coprime_iff]
  constructor
  · intro h P hP hd
    exact h P hP (Ideal.dvd_iff_le.mp hd (Ideal.subset_span (by simp)))
  · intro h P hP ha
    apply h P hP
    exact Ideal.dvd_iff_le.mpr (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr ha))

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.LowCompletion
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ProbeRow ProbeCompleted CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss
open RayFourExpansion InitialMeanSquare SecondPassArithmetic ActualEisensteinCubic
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma summand_zero_completedIndex (Ψ : O→*ℂ) (W : ℝ→ℂ) (X : ℝ) (I J : Id)
    (h : completedIndex I J=0) : summand Ψ W X I J=0 := by
  have hprod : primaryGenerator I*primaryGenerator J^3=0 := h
  rcases mul_eq_zero.mp hprod with hI|hJ
  · simp only [summand,columnWeight,squarefreeGaussCoefficient,hI,ne_eq,not_true_eq_false,
      and_false,dite_false,zero_mul,zero_div]
  · have hj : primaryGenerator J=0 := (pow_eq_zero_iff (by decide : 3≠0)).mp hJ
    have hc : cubeWeight Ψ J=0 := by
      change star (FiniteGaussPhase.angularFactor (primaryGenerator J))^3*
        Ψ (primaryGenerator J)^3/(Ideal.absNorm J:ℂ)=0
      simp only [hj,FiniteGaussPhase.angularFactor,map_zero,norm_zero,Complex.ofReal_zero,
        div_zero,star_zero,zero_pow (by decide : (3:ℕ)≠0),zero_mul,zero_div]
    simp only [summand,hc,mul_zero,zero_mul]

lemma markedSummand_eq_punctured (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (D : Id) (Ψ : O→*ℂ) (W : ℝ→ℂ) (X : ℝ) (I J : Id) :
    markedSummand S D Ψ W X I J=
      summand (coprimalityMask (calibrationForSet S hS).generator*Ψ) W X I J*
        (if D∣I*J^3 then (1:ℂ) else 0) := by
  rw [summand_mul_fixed_twist]
  change completedMask S D I J*summand Ψ W X I J=
    coprimalityMask (calibrationForSet S hS).generator (completedIndex I J)*summand Ψ W X I J*
      (if D∣I*J^3 then (1:ℂ) else 0)
  by_cases hA : completedIndex I J=0
  · rw [summand_zero_completedIndex Ψ W X I J hA]
    simp only [mul_zero,zero_mul]
  · have he := calibration_coprime_iff_excluded_span S hS (completedIndex I J)
    rw [completedIndex_eq_primaryGenerator] at he hA
    rw [(primaryGenerator_spec (I*J^3) hA).1] at he
    change _=(if IsCoprime (calibrationForSet S hS).generator (completedIndex I J) then (1:ℂ) else 0)*_ * _
    rw [completedIndex_eq_primaryGenerator,he]
    unfold completedMask
    by_cases hd : D∣I*J^3 <;> by_cases hx : ∀P∈S,¬P∣I*J^3 <;>
      simp only [hd,hx,and_self,and_false,true_and,false_and,ite_true,ite_false,mul_one,mul_zero,zero_mul] ; simp_all

lemma markedCompletedT_eq_punctured (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (D : Id) (Ψ : O→*ℂ) (W : ℝ→ℂ) (hW : HasCompactSupport W) (X : ℝ) (hX : 0<X) :
    ProbeCompleted.markedCompletedT S D Ψ W X=
      InverseMoment.markedCompletedT (coprimalityMask (calibrationForSet S hS).generator*Ψ) W X
        (fun A=>if D∣A then (1:ℂ) else 0) := by
  rw [InverseMoment.markedCompletedT_eq_tsum _ W hW X hX]
  unfold ProbeCompleted.markedCompletedT
  apply tsum_congr
  intro p
  exact markedSummand_eq_punctured S hS D Ψ W X p.1 p.2

lemma inverseMarkedCompletedT_congr_primary (Ψ Φ : O→*ℂ)
    (h : ∀n : O,ConcretePrimeRowBridge.goodLambda^2∣n-1→Ψ n=Φ n)
    (W : ℝ→ℂ) (X : ℝ) (d : Id→ℂ) :
    InverseMoment.markedCompletedT Ψ W X d=InverseMoment.markedCompletedT Φ W X d := by
  unfold InverseMoment.markedCompletedT
  apply tsum_congr
  intro I
  apply tsum_congr
  intro J
  rw [summand,summand,columnWeight_congr_primary Ψ Φ h,cubeWeight_congr_primary Ψ Φ h]

theorem correctedPhysicalRow_eq_periodic_inverse (η : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    (s : O) (hs : Supported (Ideal.span {s})) (z : O) (D : Id)
    (W : ℝ→ℂ) (hW : HasCompactSupport W) (X : ℝ) (hX : 0<X)
    (E : GoodMaskRowData (calibrationForSet S hS).generator 1 (calibrationForSet S hS).generator) :
    correctedCompletedT S D (rowCoefficient η (calibrationForSet S hS).Xi s hs z) W X=
      ∑χ : RayCharacter,correctionCoeff χ*InverseMoment.markedCompletedT
        (rowTwist (lowPeriodicBase η (calibrationForSet S hS) (calibrationForSet S hS).generator E s hs χ)
          (calibrationForSet S hS).generator 1 z) W X (fun A=>if D∣A then (1:ℂ) else 0) := by
  rw [correctedCompletedT_ray_expansion S D _ W hW X hX]
  apply Finset.sum_congr rfl
  intro χ _
  rw [markedCompletedT_eq_punctured S hS D _ W hW X hX]
  congr 1
  apply inverseMarkedCompletedT_congr_primary
  intro n hn
  exact (lowPeriodicRow_eq_primary η (calibrationForSet S hS) (calibrationForSet S hS).generator E
    (calibration_generator_bad S hS hbad).1 (calibration_generator_bad S hS hbad).2 s hs χ z n hn).symm

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.GaussianSeminorm
namespace OAI

noncomputable section
open scoped Classical ContDiff Topology SchwartzMap
open Filter Set
namespace SevenEighths.ProbePhysical

lemma gaussianFixedWindow_small (y : ℝ) (hy : y≤1/2) : gaussianFixedWindow y=0 := by
  simp only [gaussianFixedWindow,gaussianAnnulus_small y hy,zero_div]
lemma gaussianFixedWindow_large (y : ℝ) (hy : 2≤y) : gaussianFixedWindow y=0 := by
  simp only [gaussianFixedWindow,gaussianAnnulus_large y hy,zero_div]
lemma gaussianFixedWindow_compact : HasCompactSupport gaussianFixedWindow := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a:=(1/2:ℝ)) (b:=2))
  intro y hy
  change gaussianFixedWindow y≠0 at hy
  constructor
  · by_contra h; exact hy (gaussianFixedWindow_small y (le_of_lt (lt_of_not_ge h)))
  · by_contra h; exact hy (gaussianFixedWindow_large y (le_of_lt (lt_of_not_ge h)))

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.GaussianTuple
namespace OAI

noncomputable section
open scoped Classical ContDiff Topology SchwartzMap
open MeasureTheory FourierBridge CompletedGauss
namespace SevenEighths.ProbePhysical
open ProbeCompleted ProbeRow CanonicalQuadraticSieve RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma gaussianFixedWindow_twist_compact (t : ℝ) :
    HasCompactSupport (CompletedHeight.normTwistedSource gaussianFixedWindow t) := by
  exact gaussianFixedWindow_compact.mul_left

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.PhysicalRows
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ProbeCompleted ProbeRow CanonicalQuadraticSieve CompletedGauss
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma physicalRowWeight_outer_zero (C : CalibrationData) (W0 W1 : ℝ→ℂ)
    (X Y : ℝ) (r : PhysicalRowIndex) (h : W1 ((Ideal.absNorm r.1.val:ℝ)/Y)=0) :
    physicalRowWeight C W0 W1 X Y r=0 := by
  unfold physicalRowWeight
  split_ifs <;> simp [h]

lemma physicalRowWeight_inner_zero (C : CalibrationData) (W0 W1 : ℝ→ℂ)
    (X Y : ℝ) (r : PhysicalRowIndex)
    (h : W0 (elementNorm r.2/(elementNorm C.generator*(Ideal.absNorm r.1.val:ℝ)*X))=0) :
    physicalRowWeight C W0 W1 X Y r=0 := by
  unfold physicalRowWeight
  split_ifs <;> simp [h]

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.SpectralWeights
namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler

lemma cpow_half_eq_sqrt (Q : ℝ) (hQ : 0≤Q) :
    (Q:ℂ)^(1/2:ℂ) = (Real.sqrt Q:ℂ) := by
  rw [Real.sqrt_eq_rpow]
  simpa using (Complex.ofReal_cpow hQ (1/2:ℝ)).symm

open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O

end SevenEighths.ProbeEuler
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.GaussianCompensation
namespace OAI

noncomputable section
open scoped Classical SchwartzMap
open MeasureTheory FourierBridge CompletedGauss
namespace SevenEighths.ProbePhysical
open ProbeCompleted ProbeRow
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma slotProduct_nonzero {K : ℕ} (p : Fin K→O) (hp : ∀i,p i≠0) (J : Finset (Fin K)) :
    slotProduct p J≠0 := Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)

lemma slotProduct_norm_pos {K : ℕ} (p : Fin K→O) (hp : ∀i,p i≠0) (J : Finset (Fin K)) :
    0<elementNorm (slotProduct p J) := physicalElementNorm_pos _ (slotProduct_nonzero p hp J)

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.LowRay
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ProbeCompleted ProbeRow CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion
open RayFourExpansion CanonicalCoefficientClass
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma physicalRayRepresentative_spec (s : PhysicalRayElement) :
    physicalRay (physicalRayRepresentative (physicalRay s.val)).val=physicalRay s.val := by
  have hh : ∃r : PhysicalRayElement,physicalRay r.val=physicalRay s.val := ⟨s,rfl⟩
  simp only [physicalRayRepresentative,dif_pos hh]
  exact Classical.choose_spec hh

lemma rowCoefficient_congr_ray (η : HeckeFamily.Character) (Xi : O→*ℂ)
    (s r : PhysicalRayElement) (h : physicalRay s.val=physicalRay r.val) (m : O) :
    rowCoefficient η Xi s.val s.property m=rowCoefficient η Xi r.val r.property m := by
  apply MonoidHom.ext
  intro n
  rw [rowCoefficient_apply,rowCoefficient_apply]
  have hd : (4:O)∣s.val-r.val := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp h)
  have he : sexticReciprocityPhase s.val n=sexticReciprocityPhase r.val n := by
    unfold sexticReciprocityPhase
    rw [QuadraticGaussRay.residue_eq_of_four_dvd_sub s.val r.val hd]
  rw [he]

lemma physicalRowMonoid_eq_ray (η : HeckeFamily.Character) (C : CalibrationData) (r : PhysicalRowIndex) :
    physicalRowMonoid η C r=physicalRayRowMonoid η C (physicalIdealRay r.1) r.2 := by
  let s : PhysicalRayElement :=
    ⟨primaryGenerator r.1.val,(supported_span_primaryGenerator_iff r.1.val).mpr r.1.property⟩
  exact rowCoefficient_congr_ray η C.Xi s (physicalRayRepresentative (physicalRay s.val))
    (physicalRayRepresentative_spec s).symm r.2

theorem physicalRayRow_eq_periodic_inverse (η : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    (σ : RayRing) (m : O) (D : Id) (W : ℝ→ℂ) (hW : HasCompactSupport W)
    (T : ℝ) (hT : 0<T) :
    correctedCompletedT S D (physicalRayRowMonoid η (calibrationForSet S hS) σ m) W T=
      ∑χ : RayCharacter,correctionCoeff χ*
        InverseMoment.markedCompletedT
          (rowTwist (physicalRayPeriodicBase η S hS σ χ) (calibrationForSet S hS).generator 1 m)
          W T (fun A=>if D∣A then (1:ℂ) else 0) :=
  correctedPhysicalRow_eq_periodic_inverse η S hS hbad
    (physicalRayRepresentative σ).val (physicalRayRepresentative σ).property m D W hW T hT
      (calibrationLowData S hS)

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.LowCutoff
namespace OAI

noncomputable section
open scoped Classical ContDiff
namespace SevenEighths.ProbePhysical
local notation "O" => ActualEisensteinCubic.O

lemma lowOuterCutoff_one (a b : ℝ) (ha : 0<a) (hb : 0<b) (x : ℝ) (hlo : a≤x) (hhi : x≤b) :
    lowOuterCutoff a b x=1 := by
  have hl : 1≤2*x/a-1 := by
    have hh : 2≤2*x/a := (le_div_iff₀ ha).mpr (by linarith)
    linarith
  have hr : 1≤2-x/b := by
    have hh : x/b≤1 := (div_le_iff₀ hb).mpr (by simpa using hhi)
    linarith
  simp only [lowOuterCutoff,Real.smoothTransition.one_of_one_le hl,
    Real.smoothTransition.one_of_one_le hr,Complex.ofReal_one,mul_one]

lemma physical_ratio_factor (B q X Y m : ℝ) (hq : 0<q) (hY : 0<Y) :
    m/(B*X*Y)=(q/Y)*(m/(B*q*X)) := by
  field_simp

lemma physical_window_cutoff_one (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 : ℝ)
    (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (B q X Y m : ℝ) (hq : 0<q) (hY : 0<Y)
    (h0 : W0 (m/(B*q*X))≠0) (h1 : W1 (q/Y)≠0) :
    lowOuterCutoff (a0*a1) (max 1 (b0*b1)) (m/(B*X*Y))=1 := by
  have h0b := hW0 h0
  have h1b := hW1 h1
  apply lowOuterCutoff_one _ _ (mul_pos ha0 ha1) (lt_of_lt_of_le (by norm_num) (le_max_left _ _))
  · rw [physical_ratio_factor B q X Y m hq hY]
    have hh := mul_le_mul h0b.1 h1b.1 ha1.le (le_trans ha0.le h0b.1)
    simpa only [mul_comm] using hh
  · rw [physical_ratio_factor B q X Y m hq hY]
    have hh := mul_le_mul h0b.2 h1b.2 (le_trans ha1.le h1b.1) (le_trans ha0.le (h0b.1.trans h0b.2))
    have hd : (q/Y)*(m/(B*q*X))≤b0*b1 := by simpa only [mul_comm] using hh
    exact hd.trans (le_max_right _ _)

theorem physicalRowWeight_insert_cutoff (C : CalibrationData) (W0 W1 : ℝ→ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y : ℝ) (hY : 0<Y) (r : PhysicalRowIndex) :
    physicalRowWeight C W0 W1 X Y r=
      lowOuterCutoff (a0*a1) (max 1 (b0*b1)) (elementNorm r.2/(elementNorm C.generator*X*Y))*
        physicalRowWeight C W0 W1 X Y r := by
  by_cases hz : physicalRowWeight C W0 W1 X Y r=0
  · simp only [hz,mul_zero]
  have h0 : W0 (elementNorm r.2/(elementNorm C.generator*(Ideal.absNorm r.1.val:ℝ)*X))≠0 :=
    fun h=>hz (physicalRowWeight_inner_zero C W0 W1 X Y r h)
  have h1 : W1 ((Ideal.absNorm r.1.val:ℝ)/Y)≠0 :=
    fun h=>hz (physicalRowWeight_outer_zero C W0 W1 X Y r h)
  have hq : (0:ℝ)<Ideal.absNorm r.1.val := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr r.1.property.1)
  rw [physical_window_cutoff_one W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    (elementNorm C.generator) (Ideal.absNorm r.1.val) X Y (elementNorm r.2) hq hY h0 h1,one_mul]

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.LowMellin
namespace OAI

noncomputable section
open scoped Classical ContDiff
open MeasureTheory CompletedGauss
namespace SevenEighths.ProbePhysical

lemma low_mellin_ratio_integrable (W : ℝ→ℂ) (a0 b0 : ℝ) (ha0 : 0<a0)
    (hW : Function.support W⊆Set.Icc a0 b0) (hWs : ContDiff ℝ ∞ W)
    (a b : ℝ) (ha : 0<a) (hb : 0<b) :
    Integrable (fun v : ℝ=>(a:ℂ)^(-((v:ℂ)*Complex.I))*(b:ℂ)^((v:ℂ)*Complex.I)*
      mellin W ((v:ℂ)*Complex.I)) := by
  have hm : Integrable (fun v : ℝ=>mellin W ((v:ℂ)*Complex.I)) := by
    have hh := compactMellin_vertical_integrable W a0 b0 ha0 hW hWs 0
    change Integrable (fun v : ℝ=>mellin W ((0:ℂ)+v*Complex.I)) at hh
    simpa using hh
  have hc : Continuous (fun v : ℝ=>(a:ℂ)^(-((v:ℂ)*Complex.I))*(b:ℂ)^((v:ℂ)*Complex.I)) :=
    (Continuous.const_cpow (by fun_prop) (Or.inl (Complex.ofReal_ne_zero.mpr ha.ne'))).mul
      (Continuous.const_cpow (by fun_prop) (Or.inl (Complex.ofReal_ne_zero.mpr hb.ne')))
  have hp : ∀v : ℝ,‖(a:ℂ)^(-((v:ℂ)*Complex.I))*(b:ℂ)^((v:ℂ)*Complex.I)‖≤1 := by
    intro v
    rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos ha,Complex.norm_cpow_eq_rpow_re_of_pos hb]
    simp
  simpa only [mul_comm] using hm.mul_bdd hc.aestronglyMeasurable (Filter.Eventually.of_forall hp)

lemma low_mellin_ratio (W : ℝ→ℂ) (a0 b0 : ℝ) (ha0 : 0<a0)
    (hW : Function.support W⊆Set.Icc a0 b0) (hWs : ContDiff ℝ ∞ W)
    (a b : ℝ) (ha : 0<a) (hb : 0<b) :
    W (a/b)=(1/(2*Real.pi):ℂ)*∫v : ℝ,
      (a:ℂ)^(-((v:ℂ)*Complex.I))*(b:ℂ)^((v:ℂ)*Complex.I)*mellin W ((v:ℂ)*Complex.I) := by
  rw [compactMellin_inversion W a0 b0 ha0 hW hWs 0 _ (div_pos ha hb)]
  congr 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro v
  dsimp only
  rw [Complex.ofReal_zero,zero_add,Complex.ofReal_div,Complex.div_cpow_ofReal_nonneg ha.le hb.le]
  simp only [div_eq_mul_inv,←Complex.cpow_neg,neg_neg]

lemma low_sqrt_ratio (B q X Y : ℝ) (hB : 0<B) (hq : 0<q) (hX : 0<X) (hY : 0<Y) :
    (Real.sqrt (B*q*X):ℂ)⁻¹=
      (Real.sqrt (B*X*Y):ℂ)⁻¹*((q/Y:ℝ):ℂ)^(-(1/2:ℂ)) := by
  have hQ : 0<B*X*Y := by positivity
  have hb : 0<q/Y := div_pos hq hY
  have he : B*q*X=(B*X*Y)*(q/Y) := by field_simp
  rw [he,Real.sqrt_mul hQ.le,Complex.ofReal_mul,Complex.cpow_neg,ProbeEuler.cpow_half_eq_sqrt _ hb.le]
  simp only [mul_inv_rev,mul_comm]

theorem physical_radial_low_mellin (W : ℝ→ℂ) (a0 b0 : ℝ) (ha0 : 0<a0)
    (hW : Function.support W⊆Set.Icc a0 b0) (hWs : ContDiff ℝ ∞ W)
    (B q X Y m : ℝ) (hB : 0<B) (hq : 0<q) (hX : 0<X) (hY : 0<Y) (hm : 0< m) :
    (Real.sqrt (B*q*X):ℂ)⁻¹*W (m/(B*q*X))=
      (Real.sqrt (B*X*Y):ℂ)⁻¹*(1/(2*Real.pi):ℂ)*
        ∫v : ℝ,((m/(B*X*Y):ℝ):ℂ)^(-((v:ℂ)*Complex.I))*
          ((q/Y:ℝ):ℂ)^(-(1/2:ℂ)+(v:ℂ)*Complex.I)*mellin W ((v:ℂ)*Complex.I) := by
  have hQ : 0<B*X*Y := by positivity
  have ha : 0< m/(B*X*Y) := div_pos hm hQ
  have hb : 0<q/Y := div_pos hq hY
  have hbc : ((q/Y:ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr hb.ne'
  have he : m/(B*q*X)=(m/(B*X*Y))/(q/Y) := by field_simp
  rw [he,low_mellin_ratio W a0 b0 ha0 hW hWs _ _ ha hb,low_sqrt_ratio B q X Y hB hq hX hY]
  simp_rw [Complex.cpow_add _ _ hbc]
  rw [show (fun v : ℝ=>((m/(B*X*Y):ℝ):ℂ)^(-((v:ℂ)*Complex.I))*
    (((q/Y:ℝ):ℂ)^(-(1/2:ℂ))*((q/Y:ℝ):ℂ)^((v:ℂ)*Complex.I))*mellin W ((v:ℂ)*Complex.I))=
    (fun v : ℝ=>((q/Y:ℝ):ℂ)^(-(1/2:ℂ))*
      (((m/(B*X*Y):ℝ):ℂ)^(-((v:ℂ)*Complex.I))*((q/Y:ℝ):ℂ)^((v:ℂ)*Complex.I)*mellin W ((v:ℂ)*Complex.I))) by funext v; ring]
  rw [integral_const_mul]
  ring

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.LowRowMellin
namespace OAI

noncomputable section
open scoped Classical ContDiff
open MeasureTheory CompletedGauss
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve CanonicalRowCompletion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma lowAdditiveCoefficient_outer_zero (C : CalibrationData) (W1 : ℝ→ℂ) (Y : ℝ)
    (s : {I : Id // Supported I}) (m : O) (v : ℝ) (h : W1 ((Ideal.absNorm s.val:ℝ)/Y)=0) :
    lowAdditiveCoefficient C W1 Y s m v=0 := by
  unfold lowAdditiveCoefficient
  split_ifs <;> simp [h]

lemma lowRowMellinIntegrand_nonzero_form (C : CalibrationData) (W0 W1 Ω : ℝ→ℂ)
    (X Y : ℝ) (hY : 0<Y) (r : PhysicalRowIndex) (v : ℝ)
    (hc : ∀P∈C.excluded,¬P∣r.1.val) :
    lowRowMellinIntegrand C W0 W1 Ω X Y r v=
      ((Y:ℂ)⁻¹*W1 ((Ideal.absNorm r.1.val:ℝ)/Y)*idealRowHom C.generator r.1.val/
        (C.tau*C.residueMonoid (primaryGenerator r.1.val))*
          (((Ideal.absNorm r.1.val:ℝ)/Y:ℝ):ℂ)^(-(1/2:ℂ))*
          (Real.sqrt (Ideal.absNorm r.1.val):ℂ)⁻¹*
          sexticGauss (primaryGenerator r.1.val) (supported_primaryGenerator_ne_zero r.1.val r.1.property) (-r.2)*
          Ω (elementNorm r.2/lowPhysicalScale C X Y)*C.residueMonoid r.2)*
        (((elementNorm r.2/lowPhysicalScale C X Y:ℝ):ℂ)^(-((v:ℂ)*Complex.I))*
          (((Ideal.absNorm r.1.val:ℝ)/Y:ℝ):ℂ)^((v:ℂ)*Complex.I)*mellin W0 ((v:ℂ)*Complex.I)) := by
  have hq : (0:ℝ)<Ideal.absNorm r.1.val := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr r.1.property.1)
  have hqc : (((Ideal.absNorm r.1.val:ℝ)/Y:ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr (div_pos hq hY).ne'
  unfold lowRowMellinIntegrand lowAdditiveCoefficient
  rw [if_pos hc]
  dsimp only
  rw [Complex.cpow_add _ _ hqc]
  ring

lemma lowRowMellinIntegrand_integrable (C : CalibrationData) (W0 W1 Ω : ℝ→ℂ)
    (a0 b0 : ℝ) (ha0 : 0<a0) (hW0 : Function.support W0⊆Set.Icc a0 b0)
    (hWs : ContDiff ℝ ∞ W0) (hΩ : Ω 0=0) (X Y : ℝ) (hX : 0<X) (hY : 0<Y)
    (r : PhysicalRowIndex) : Integrable (lowRowMellinIntegrand C W0 W1 Ω X Y r) := by
  by_cases hm : r.2=0
  · have he : lowRowMellinIntegrand C W0 W1 Ω X Y r=0 := by
      funext v
      simp [lowRowMellinIntegrand,hm,elementNorm,hΩ]
    rw [he]
    exact integrable_zero _ _ _
  by_cases hc : ∀P∈C.excluded,¬P∣r.1.val
  · have hq : (0:ℝ)<Ideal.absNorm r.1.val := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr r.1.property.1)
    have hmpos : 0<elementNorm r.2 := by
      unfold elementNorm
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hm))
    change Integrable (fun v : ℝ=>lowRowMellinIntegrand C W0 W1 Ω X Y r v)
    simp_rw [lowRowMellinIntegrand_nonzero_form C W0 W1 Ω X Y hY r _ hc]
    exact (low_mellin_ratio_integrable W0 a0 b0 ha0 hW0 hWs _ _
      (div_pos hmpos (lowPhysicalScale_pos C X Y hX hY)) (div_pos hq hY)).const_mul _
  · have he : lowRowMellinIntegrand C W0 W1 Ω X Y r=0 := by
      funext v
      simp [lowRowMellinIntegrand,lowAdditiveCoefficient,hc]
    rw [he]
    exact integrable_zero _ _ _

theorem physicalRowWeight_low_mellin (C : CalibrationData) (W0 W1 : ℝ→ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hWs : ContDiff ℝ ∞ W0) (X Y : ℝ) (hX : 0<X) (hY : 0<Y) (r : PhysicalRowIndex) :
    physicalRowWeight C W0 W1 X Y r=
      (Real.sqrt (lowPhysicalScale C X Y):ℂ)⁻¹*(1/(2*Real.pi):ℂ)*
        ∫v : ℝ,lowRowMellinIntegrand C W0 W1 (lowOuterCutoff (a0*a1) (max 1 (b0*b1))) X Y r v := by
  let Ω := lowOuterCutoff (a0*a1) (max 1 (b0*b1))
  have hΩ : Ω 0=0 := lowOuterCutoff_small _ _ (mul_pos ha0 ha1) 0 (by positivity)
  by_cases hm : r.2=0
  · have hw : W0 0=0 := by
      by_contra hh
      have hx := (hW0 hh).1
      linarith
    simp [physicalRowWeight,lowRowMellinIntegrand,hm,elementNorm,hw,hΩ,Ω]
  by_cases hc : ∀P∈C.excluded,¬P∣r.1.val
  · have hq : (0:ℝ)<Ideal.absNorm r.1.val := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr r.1.property.1)
    have hmpos : 0<elementNorm r.2 := by
      unfold elementNorm
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hm))
    rw [physicalRowWeight_insert_cutoff C W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y hY r]
    unfold physicalRowWeight lowRowMellinIntegrand lowAdditiveCoefficient lowPhysicalScale
    dsimp only
    simp only [if_pos hc]
    have hh := physical_radial_low_mellin W0 a0 b0 ha0 hW0 hWs
      (elementNorm C.generator) (Ideal.absNorm r.1.val) X Y (elementNorm r.2)
      (calibration_elementNorm_pos C) hq hX hY hmpos

    calc
      _ = (Ω (elementNorm r.2/(elementNorm C.generator*X*Y))*(Y:ℂ)⁻¹*
        W1 ((Ideal.absNorm r.1.val:ℝ)/Y)*idealRowHom C.generator r.1.val*
        (C.tau*C.residueMonoid (primaryGenerator r.1.val))⁻¹*C.residueMonoid r.2*
        (Real.sqrt (Ideal.absNorm r.1.val):ℂ)⁻¹*
        sexticGauss (primaryGenerator r.1.val) (supported_primaryGenerator_ne_zero r.1.val r.1.property) (-r.2))*
        ((Real.sqrt (elementNorm C.generator*(Ideal.absNorm r.1.val:ℝ)*X):ℂ)⁻¹*
          W0 (elementNorm r.2/(elementNorm C.generator*(Ideal.absNorm r.1.val:ℝ)*X))) := by dsimp only [Ω]; simp only [div_eq_mul_inv,mul_inv_rev]; ring
      _ = _ := by
        rw [hh]
        repeat rw [←integral_const_mul]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun v=>by dsimp only [Ω]; ring)
  · simp [physicalRowWeight,lowRowMellinIntegrand,lowAdditiveCoefficient,hc]

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.LowMellinFubini
namespace OAI

noncomputable section
open scoped Classical ContDiff
open MeasureTheory CompletedGauss
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma lowRowMellinIntegrand_common_support (C : CalibrationData) (W0 W1 Ω : ℝ→ℂ)
    (hW1 : HasCompactSupport W1) (hΩ : HasCompactSupport Ω)
    (X Y : ℝ) (hX : 0<X) (hY : 0<Y) :
    ∃R : Finset PhysicalRowIndex,∀v : ℝ,∀r∉R,
      lowRowMellinIntegrand C W0 W1 Ω X Y r v=0 := by
  have hs := (idealWindow_finite_support W1 hW1 Y hY).preimage
    (f:=fun s : {I : Id // Supported I}=>s.val) Subtype.val_injective.injOn
  have hm := elementWindow_finite_support Ω hΩ _ (lowPhysicalScale_pos C X Y hX hY)
  refine ⟨hs.toFinset×ˢhm.toFinset,?_⟩
  intro v r hr
  simp only [Finset.mem_product,Set.Finite.mem_toFinset,Set.mem_preimage,Function.mem_support] at hr
  by_cases h : W1 ((Ideal.absNorm r.1.val:ℝ)/Y)=0
  · unfold lowRowMellinIntegrand
    rw [lowAdditiveCoefficient_outer_zero C W1 Y r.1 r.2 v h,mul_zero]
  · have ho : Ω (elementNorm r.2/lowPhysicalScale C X Y)=0 := by
      by_contra ho
      exact hr ⟨h,ho⟩
    simp [lowRowMellinIntegrand,ho]

lemma lowRowMellinIntegrand_mul_summable (C : CalibrationData) (W0 W1 Ω : ℝ→ℂ)
    (hW1 : HasCompactSupport W1) (hΩ : HasCompactSupport Ω)
    (X Y : ℝ) (hX : 0<X) (hY : 0<Y) (v : ℝ) (B : PhysicalRowIndex→ℂ) :
    Summable (fun r=>lowRowMellinIntegrand C W0 W1 Ω X Y r v*B r) := by
  obtain ⟨R,hR⟩ := lowRowMellinIntegrand_common_support C W0 W1 Ω hW1 hΩ X Y hX hY
  apply summable_of_ne_finset_zero (s:=R)
  intro r hr
  rw [hR v r hr,zero_mul]

lemma lowRowMellinIntegrand_sum_integrable (C : CalibrationData) (W0 W1 Ω : ℝ→ℂ)
    (a0 b0 : ℝ) (ha0 : 0<a0) (hW0 : Function.support W0⊆Set.Icc a0 b0)
    (hWs : ContDiff ℝ ∞ W0) (hW1 : HasCompactSupport W1)
    (hΩ : HasCompactSupport Ω) (hΩ0 : Ω 0=0)
    (X Y : ℝ) (hX : 0<X) (hY : 0<Y) (B : PhysicalRowIndex→ℂ) :
    Integrable (fun v : ℝ=>∑'r : PhysicalRowIndex,lowRowMellinIntegrand C W0 W1 Ω X Y r v*B r) := by
  obtain ⟨R,hR⟩ := lowRowMellinIntegrand_common_support C W0 W1 Ω hW1 hΩ X Y hX hY
  have he (v : ℝ) : (∑'r : PhysicalRowIndex,lowRowMellinIntegrand C W0 W1 Ω X Y r v*B r)=
      ∑r∈R,lowRowMellinIntegrand C W0 W1 Ω X Y r v*B r := by
    apply tsum_eq_sum
    intro r hr
    rw [hR v r hr,zero_mul]
  simp_rw [he]
  exact integrable_finsetSum R (fun r _=>(lowRowMellinIntegrand_integrable C W0 W1 Ω a0 b0 ha0 hW0 hWs hΩ0 X Y hX hY r).mul_const _)

lemma lowRowMellinIntegrand_tsum_integral (C : CalibrationData) (W0 W1 Ω : ℝ→ℂ)
    (a0 b0 : ℝ) (ha0 : 0<a0) (hW0 : Function.support W0⊆Set.Icc a0 b0)
    (hWs : ContDiff ℝ ∞ W0) (hW1 : HasCompactSupport W1)
    (hΩ : HasCompactSupport Ω) (hΩ0 : Ω 0=0)
    (X Y : ℝ) (hX : 0<X) (hY : 0<Y) (B : PhysicalRowIndex→ℂ) :
    (∑'r : PhysicalRowIndex,∫v : ℝ,lowRowMellinIntegrand C W0 W1 Ω X Y r v*B r)=
      ∫v : ℝ,∑'r : PhysicalRowIndex,lowRowMellinIntegrand C W0 W1 Ω X Y r v*B r := by
  obtain ⟨R,hR⟩ := lowRowMellinIntegrand_common_support C W0 W1 Ω hW1 hΩ X Y hX hY
  have he (v : ℝ) : (∑'r : PhysicalRowIndex,lowRowMellinIntegrand C W0 W1 Ω X Y r v*B r)=
      ∑r∈R,lowRowMellinIntegrand C W0 W1 Ω X Y r v*B r := by
    apply tsum_eq_sum
    intro r hr
    rw [hR v r hr,zero_mul]
  rw [tsum_eq_sum (s:=R) (fun r hr=>by simp only [hR _ r hr,zero_mul,integral_zero])]
  simp_rw [he]
  exact (integral_finsetSum R (fun r _=>(lowRowMellinIntegrand_integrable C W0 W1 Ω a0 b0 ha0 hW0 hWs hΩ0 X Y hX hY r).mul_const _)).symm

theorem physicalRowWeight_tsum_low_mellin (C : CalibrationData) (W0 W1 : ℝ→ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hWs : ContDiff ℝ ∞ W0) (X Y : ℝ) (hX : 0<X) (hY : 0<Y) (B : PhysicalRowIndex→ℂ) :
    (∑'r : PhysicalRowIndex,physicalRowWeight C W0 W1 X Y r*B r)=
      (Real.sqrt (lowPhysicalScale C X Y):ℂ)⁻¹*(1/(2*Real.pi):ℂ)*
        ∫v : ℝ,∑'r : PhysicalRowIndex,
          lowRowMellinIntegrand C W0 W1 (lowOuterCutoff (a0*a1) (max 1 (b0*b1))) X Y r v*B r := by
  let Ω := lowOuterCutoff (a0*a1) (max 1 (b0*b1))
  have hΩ : HasCompactSupport Ω := lowOuterCutoff_compact _ _ (mul_pos ha0 ha1) (lt_of_lt_of_le (by norm_num) (le_max_left _ _))
  have hΩ0 : Ω 0=0 := lowOuterCutoff_small _ _ (mul_pos ha0 ha1) 0 (by positivity)
  have hW1c : HasCompactSupport W1 := HasCompactSupport.of_support_subset_isCompact isCompact_Icc hW1
  simp_rw [physicalRowWeight_low_mellin C W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hWs X Y hX hY]
  simp_rw [mul_assoc,←integral_mul_const]
  repeat rw [tsum_mul_left]
  congr 2
  exact lowRowMellinIntegrand_tsum_integral C W0 W1 Ω a0 b0 ha0 hW0 hWs hW1c hΩ hΩ0 X Y hX hY B

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.LowRayAmplitude
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma lowAdditiveCoefficient_common_support (C : CalibrationData) (W1 : ℝ→ℂ)
    (hW1 : HasCompactSupport W1) (Y : ℝ) (hY : 0<Y) :
    ∃F : Finset {I : Id // Supported I},∀m : O,∀v : ℝ,∀s∉F,
      lowAdditiveCoefficient C W1 Y s m v=0 := by
  have ho := (idealWindow_finite_support W1 hW1 Y hY).preimage
    (f:=fun s : {I : Id // Supported I}=>s.val) Subtype.val_injective.injOn
  refine ⟨ho.toFinset,?_⟩
  intro m v s hs
  apply lowAdditiveCoefficient_outer_zero
  simpa only [Set.Finite.mem_toFinset,Set.mem_preimage,Function.mem_support,not_not] using hs

lemma lowRayAmplitude_group (C : CalibrationData) (W1 : ℝ→ℂ)
    (hW1 : HasCompactSupport W1) (Y : ℝ) (hY : 0<Y) (m : O) (v : ℝ)
    (B : RayRing→ℂ) :
    (∑'s : {I : Id // Supported I},lowAdditiveCoefficient C W1 Y s m v*B (physicalIdealRay s))=
      ∑σ : RayRing,lowRayAmplitude C W1 Y σ m v*B σ := by
  obtain ⟨F,hF⟩ := lowAdditiveCoefficient_common_support C W1 hW1 Y hY
  have hleft : (∑'s : {I : Id // Supported I},lowAdditiveCoefficient C W1 Y s m v*B (physicalIdealRay s))=
      ∑s∈F,lowAdditiveCoefficient C W1 Y s m v*B (physicalIdealRay s) := by
    apply tsum_eq_sum
    intro s hs
    rw [hF m v s hs,zero_mul]
  have hr (σ : RayRing) : lowRayAmplitude C W1 Y σ m v=
      ∑s∈F,if physicalIdealRay s=σ then lowAdditiveCoefficient C W1 Y s m v else 0 := by
    apply tsum_eq_sum
    intro s hs
    simp only [hF m v s hs,ite_self]
  rw [hleft]
  simp_rw [hr,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s hs
  simp only [ite_mul,zero_mul]
  simp

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.LowSeparated
namespace OAI

noncomputable section
open scoped Classical ContDiff
open MeasureTheory CompletedGauss
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve RayFourExpansion ProbeCompleted
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma lowSeparatedIntegrand_eq (C : CalibrationData) (W0 W1 Ω : ℝ→ℂ)
    (hW1 : HasCompactSupport W1) (hΩ : HasCompactSupport Ω)
    (X Y : ℝ) (hX : 0<X) (hY : 0<Y) (B : RayRing→O→ℂ) (v : ℝ) :
    (∑'r : PhysicalRowIndex,lowRowMellinIntegrand C W0 W1 Ω X Y r v*B (physicalIdealRay r.1) r.2)=
      lowSeparatedIntegrand C W0 W1 Ω X Y B v := by
  have hs := lowRowMellinIntegrand_mul_summable C W0 W1 Ω hW1 hΩ X Y hX hY v
    (fun r=>B (physicalIdealRay r.1) r.2)
  rw [hs.tsum_prod,←hs.tsum_comm]
  unfold lowSeparatedIntegrand
  rw [←tsum_mul_left]
  apply tsum_congr
  intro m
  rw [←lowRayAmplitude_group C W1 hW1 Y hY m v (fun σ=>B σ m)]
  repeat rw [←tsum_mul_left]
  apply tsum_congr
  intro s
  unfold lowRowMellinIntegrand
  ring

lemma lowSeparatedIntegrand_integrable (C : CalibrationData) (W0 W1 Ω : ℝ→ℂ)
    (a0 b0 : ℝ) (ha0 : 0<a0) (hW0 : Function.support W0⊆Set.Icc a0 b0)
    (hWs : ContDiff ℝ ∞ W0) (hW1 : HasCompactSupport W1)
    (hΩ : HasCompactSupport Ω) (hΩ0 : Ω 0=0)
    (X Y : ℝ) (hX : 0<X) (hY : 0<Y) (B : RayRing→O→ℂ) :
    Integrable (lowSeparatedIntegrand C W0 W1 Ω X Y B) := by
  have hh := lowRowMellinIntegrand_sum_integrable C W0 W1 Ω a0 b0 ha0 hW0 hWs hW1 hΩ hΩ0 X Y hX hY
    (fun r=>B (physicalIdealRay r.1) r.2)
  simpa only [lowSeparatedIntegrand_eq C W0 W1 Ω hW1 hΩ X Y hX hY B] using hh

theorem physicalRowWeight_low_separated (C : CalibrationData) (W0 W1 : ℝ→ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hWs : ContDiff ℝ ∞ W0) (X Y : ℝ) (hX : 0<X) (hY : 0<Y) (B : RayRing→O→ℂ) :
    (∑'r : PhysicalRowIndex,physicalRowWeight C W0 W1 X Y r*B (physicalIdealRay r.1) r.2)=
      (Real.sqrt (lowPhysicalScale C X Y):ℂ)⁻¹*(1/(2*Real.pi):ℂ)*
        ∫v : ℝ,lowSeparatedIntegrand C W0 W1 (lowOuterCutoff (a0*a1) (max 1 (b0*b1))) X Y B v := by
  have hW1c : HasCompactSupport W1 := HasCompactSupport.of_support_subset_isCompact isCompact_Icc hW1
  have hΩ := lowOuterCutoff_compact (a0*a1) (max 1 (b0*b1)) (mul_pos ha0 ha1)
    (lt_of_lt_of_le (by norm_num) (le_max_left _ _))
  rw [physicalRowWeight_tsum_low_mellin C W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hWs X Y hX hY]
  simp_rw [lowSeparatedIntegrand_eq C W0 W1 _ hW1c hΩ X Y hX hY B]

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.LowCompensation
namespace OAI

noncomputable section
open scoped Classical ContDiff
open MeasureTheory CompletedGauss
namespace SevenEighths.ProbePhysical
open ProbeCompleted CanonicalRowCompletion RayFourExpansion ProbeRow CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma lowMarkedInverseRow_eq (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S) (D : Id) (T t : ℝ) (hT : 0<T)
    (σ : RayRing) (m : O) :
    correctedCompletedT S D (physicalRayRowMonoid η (calibrationForSet S hS) σ m)
      (CompletedHeight.normTwistedSource gaussianFixedWindow t) T=
        lowMarkedInverseRow η S hS D T t σ m :=
  physicalRayRow_eq_periodic_inverse η S hS hbad σ m D _ (gaussianFixedWindow_twist_compact t) T hT

theorem compensationRowTest_low_separated {K : ℕ} (η : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hWs : ContDiff ℝ ∞ W0) (p : Fin K→O) (hp : ∀i,p i≠0) (J : Finset (Fin K))
    (X Y T t : ℝ) (hX : 0<X) (hY : 0<Y) (hT : 0<T) :
    compensationRowTest η (calibrationForSet S hS) W0 W1 p J X Y T t=
      (Real.sqrt (lowPhysicalScale (calibrationForSet S hS)
        (X/elementNorm (slotProduct p J)) (Y/elementNorm (slotProduct p J))):ℂ)⁻¹*(1/(2*Real.pi):ℂ)*
        ∫v : ℝ,lowSeparatedIntegrand (calibrationForSet S hS) W0 W1
          (lowOuterCutoff (a0*a1) (max 1 (b0*b1)))
          (X/elementNorm (slotProduct p J)) (Y/elementNorm (slotProduct p J))
          (lowMarkedInverseRow η S hS (Ideal.span {slotProduct p (Finset.univ\J)}) T t) v := by
  unfold compensationRowTest
  simp_rw [physicalRowMonoid_eq_ray]
  have hC : (calibrationForSet S hS).excluded=S := calibrationForSet_excluded S hS
  rw [hC]
  simp_rw [lowMarkedInverseRow_eq η S hS hbad _ T t hT]
  exact physicalRowWeight_low_separated (calibrationForSet S hS) W0 W1 a0 b0 a1 b1 ha0 ha1
    hW0 hW1 hWs _ _ (div_pos hX (slotProduct_norm_pos p hp J))
      (div_pos hY (slotProduct_norm_pos p hp J))
      (lowMarkedInverseRow η S hS (Ideal.span {slotProduct p (Finset.univ\J)}) T t)

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.LowSelectedSum
namespace OAI

noncomputable section
open scoped Classical ContDiff
open MeasureTheory CompletedGauss
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma lowSeparatedIntegrand_finite_sum {α : Type*} (F : Finset α) (c : α→ℂ)
    (C : CalibrationData) (W0 W1 Ω : ℝ→ℂ) (hW1 : HasCompactSupport W1) (hΩ : HasCompactSupport Ω)
    (X Y : ℝ) (hX : 0<X) (hY : 0<Y) (B : α→RayRing→O→ℂ) (v : ℝ) :
    (∑k∈F,c k*lowSeparatedIntegrand C W0 W1 Ω X Y (B k) v)=
      lowSeparatedIntegrand C W0 W1 Ω X Y (fun σ m=>∑k∈F,c k*B k σ m) v := by
  simp_rw [←lowSeparatedIntegrand_eq C W0 W1 Ω hW1 hΩ X Y hX hY]
  simp_rw [←tsum_mul_left]
  rw [←Summable.tsum_finsetSum (fun k _=>
    (lowRowMellinIntegrand_mul_summable C W0 W1 Ω hW1 hΩ X Y hX hY v
      (fun r=>B k (physicalIdealRay r.1) r.2)).mul_left (c k))]
  apply tsum_congr
  intro r
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

lemma lowSeparatedIntegral_finite_sum {α : Type*} (F : Finset α) (c : α→ℂ)
    (C : CalibrationData) (W0 W1 Ω : ℝ→ℂ)
    (a0 b0 : ℝ) (ha0 : 0<a0) (hW0 : Function.support W0⊆Set.Icc a0 b0)
    (hWs : ContDiff ℝ ∞ W0) (hW1 : HasCompactSupport W1)
    (hΩ : HasCompactSupport Ω) (hΩ0 : Ω 0=0)
    (X Y : ℝ) (hX : 0<X) (hY : 0<Y) (B : α→RayRing→O→ℂ) :
    (∑k∈F,c k*∫v : ℝ,lowSeparatedIntegrand C W0 W1 Ω X Y (B k) v)=
      ∫v : ℝ,lowSeparatedIntegrand C W0 W1 Ω X Y (fun σ m=>∑k∈F,c k*B k σ m) v := by
  simp_rw [←integral_const_mul]
  rw [←integral_finsetSum F (fun k _=>(lowSeparatedIntegrand_integrable C W0 W1 Ω
    a0 b0 ha0 hW0 hWs hW1 hΩ hΩ0 X Y hX hY (B k)).const_mul (c k))]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun v=>lowSeparatedIntegrand_finite_sum F c C W0 W1 Ω hW1 hΩ X Y hX hY B v)

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.LowSlotSplit
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
local notation "O" => ActualEisensteinCubic.O

lemma lowSlotJoin_nonzero {K : ℕ} (slots : Fin K→Finset O)
    (hslots : ∀i x,x∈slots i→x≠0) (J : Finset (Fin K))
    (a : LowUnselectedTuple slots J) (b : LowSelectedTuple slots J) (i : Fin K) :
    lowSlotJoin slots J a b i≠0 := hslots i _ ((lowSlotTupleEquiv slots J).symm (a,b) i).property

lemma lowSlotJoin_unselected {K : ℕ} (slots : Fin K→Finset O) (J : Finset (Fin K))
    (a : LowUnselectedTuple slots J) (b : LowSelectedTuple slots J) (i : J) :
    lowSlotJoin slots J a b i.val=(a i).val := by
  simp only [lowSlotJoin,lowSlotTupleEquiv,Equiv.coe_fn_symm_mk,dif_pos i.property]

lemma lowSlotJoin_selected {K : ℕ} (slots : Fin K→Finset O) (J : Finset (Fin K))
    (a : LowUnselectedTuple slots J) (b : LowSelectedTuple slots J) (i : SelectedSlot J) :
    lowSlotJoin slots J a b i.val=(b i).val := by
  have hi : i.val∉J := (Finset.mem_sdiff.mp i.property).2
  simp only [lowSlotJoin,lowSlotTupleEquiv,Equiv.coe_fn_symm_mk,dif_neg hi]

lemma lowSlotJoin_unselectedProduct {K : ℕ} (slots : Fin K→Finset O) (J : Finset (Fin K))
    (a : LowUnselectedTuple slots J) (b : LowSelectedTuple slots J) :
    slotProduct (lowSlotJoin slots J a b) J=∏i : J,(a i).val := by
  unfold slotProduct
  rw [←Finset.prod_coe_sort J]
  simp only [lowSlotJoin_unselected]

lemma lowSlotJoin_selectedProduct {K : ℕ} (slots : Fin K→Finset O) (J : Finset (Fin K))
    (a : LowUnselectedTuple slots J) (b : LowSelectedTuple slots J) :
    slotProduct (lowSlotJoin slots J a b) (Finset.univ\J)=∏i : SelectedSlot J,(b i).val := by
  unfold slotProduct
  rw [←Finset.prod_coe_sort (Finset.univ\J)]
  simp only [lowSlotJoin_selected]

lemma lowSlotJoin_selectedFactor {K : ℕ} (slots : Fin K→Finset O) (J : Finset (Fin K))
    (a : LowUnselectedTuple slots J) (b : LowSelectedTuple slots J)
    (W : Fin K→ℝ→ℂ) (P : Fin K→ℝ) (t : ℝ) :
    selectedSlotFactor W P (lowSlotJoin slots J a b) J t=
      ∏i : SelectedSlot J,W i.val (elementNorm (b i).val/P i.val)*
        FourierBridge.logPhase (-t) (Real.log (elementNorm (b i).val/P i.val)) := by
  unfold selectedSlotFactor
  simp only [lowSlotJoin_selected]

theorem sum_lowSlotJoin {K : ℕ} (slots : Fin K→Finset O) (J : Finset (Fin K))
    (F : (Fin K→O)→ℂ) :
    (∑p : (∀i,↥(slots i)),F (fun i=>(p i).val))=
      ∑a : LowUnselectedTuple slots J,∑b : LowSelectedTuple slots J,F (lowSlotJoin slots J a b) := by
  calc
    _ = ∑p : LowUnselectedTuple slots J×LowSelectedTuple slots J,F (lowSlotJoin slots J p.1 p.2) :=
      (Equiv.sum_comp (lowSlotTupleEquiv slots J).symm (fun p=>F (fun i=>(p i).val))).symm
    _ = _ := Fintype.sum_prod_type _

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.LowSlotPolynomial
namespace OAI

noncomputable section
open scoped Classical ContDiff
open MeasureTheory CompletedGauss
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma lowSlotJoin_weight {K : ℕ} (η : HeckeFamily.Character) (slots : Fin K→Finset O)
    (J : Finset (Fin K)) (W : Fin K→ℝ→ℂ) (P : Fin K→ℝ) (t : ℝ)
    (a : LowUnselectedTuple slots J) (b : LowSelectedTuple slots J) :
    compensationSubsetWeight η W P (lowSlotJoin slots J a b) J*
      selectedSlotFactor W P (lowSlotJoin slots J a b) J t=
        lowUnselectedWeight slots J W P a*lowSelectedWeight η slots J W P t b := by
  unfold compensationSubsetWeight compensationSubsetCoefficient
  rw [lowSlotJoin_unselectedProduct,lowSlotJoin_selectedProduct,lowSlotJoin_selectedFactor]
  rw [←Finset.prod_coe_sort J (fun i=>W i (elementNorm (lowSlotJoin slots J a b i)/P i))]
  simp only [lowSlotJoin_unselected]
  unfold lowUnselectedWeight lowSelectedWeight
  ring

lemma compensationRowTest_join_low {K : ℕ} (η : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hWs : ContDiff ℝ ∞ W0) (slots : Fin K→Finset O) (hslots : ∀i x,x∈slots i→x≠0)
    (J : Finset (Fin K)) (a : LowUnselectedTuple slots J) (b : LowSelectedTuple slots J)
    (X Y T t : ℝ) (hX : 0<X) (hY : 0<Y) (hT : 0<T) :
    compensationRowTest η (calibrationForSet S hS) W0 W1 (lowSlotJoin slots J a b) J X Y T t=
      (Real.sqrt (lowPhysicalScale (calibrationForSet S hS)
        (X/elementNorm (∏i : J,(a i).val)) (Y/elementNorm (∏i : J,(a i).val))):ℂ)⁻¹*(1/(2*Real.pi):ℂ)*
        ∫v : ℝ,lowSeparatedIntegrand (calibrationForSet S hS) W0 W1
          (lowOuterCutoff (a0*a1) (max 1 (b0*b1)))
          (X/elementNorm (∏i : J,(a i).val)) (Y/elementNorm (∏i : J,(a i).val))
          (lowMarkedInverseRow η S hS (lowSelectedIdeal slots J b) T t) v := by
  simpa only [lowSlotJoin_unselectedProduct,lowSlotJoin_selectedProduct,lowSelectedIdeal] using
    compensationRowTest_low_separated η S hS hbad W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hWs
      (lowSlotJoin slots J a b) (lowSlotJoin_nonzero slots hslots J a b) J X Y T t hX hY hT

theorem compensation_tuple_low_polynomial_oai {K : ℕ} (η : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hWs : ContDiff ℝ ∞ W0) (slots : Fin K→Finset O) (hslots : ∀i x,x∈slots i→x≠0)
    (J : Finset (Fin K)) (W : Fin K→ℝ→ℂ) (P : Fin K→ℝ)
    (X Y T t : ℝ) (hX : 0<X) (hY : 0<Y) (hT : 0<T) :
    (∑p : (∀i,↥(slots i)),compensationSubsetWeight η W P (fun i=>(p i).val) J*
      compensationRowTest η (calibrationForSet S hS) W0 W1 (fun i=>(p i).val) J X Y T t*
        selectedSlotFactor W P (fun i=>(p i).val) J t)=
      ∑a : LowUnselectedTuple slots J,lowUnselectedWeight slots J W P a*
        ((Real.sqrt (lowPhysicalScale (calibrationForSet S hS)
          (X/elementNorm (∏i : J,(a i).val)) (Y/elementNorm (∏i : J,(a i).val))):ℂ)⁻¹*(1/(2*Real.pi):ℂ))*
          ∫v : ℝ,lowSeparatedIntegrand (calibrationForSet S hS) W0 W1
            (lowOuterCutoff (a0*a1) (max 1 (b0*b1)))
            (X/elementNorm (∏i : J,(a i).val)) (Y/elementNorm (∏i : J,(a i).val))
            (lowSelectedInverseRow Finset.univ (lowSelectedWeight η slots J W P t)
              η S hS (lowSelectedIdeal slots J) T t) v := by
  rw [sum_lowSlotJoin slots J (fun p=>compensationSubsetWeight η W P p J*
    compensationRowTest η (calibrationForSet S hS) W0 W1 p J X Y T t*selectedSlotFactor W P p J t)]
  apply Finset.sum_congr rfl
  intro a ha
  let L := elementNorm (∏i : J,(a i).val)
  have hL : 0<L := lowUnselectedProduct_norm_pos slots hslots J a
  let C := calibrationForSet S hS
  let Ω := lowOuterCutoff (a0*a1) (max 1 (b0*b1))
  let N : ℂ := (Real.sqrt (lowPhysicalScale C (X/L) (Y/L)):ℂ)⁻¹*(1/(2*Real.pi):ℂ)
  have hW1c : HasCompactSupport W1 := HasCompactSupport.of_support_subset_isCompact isCompact_Icc hW1
  have hΩc : HasCompactSupport Ω := lowOuterCutoff_compact _ _ (mul_pos ha0 ha1)
    (lt_of_lt_of_le (by norm_num) (le_max_left _ _))
  have hΩ0 : Ω 0=0 := lowOuterCutoff_small _ _ (mul_pos ha0 ha1) 0 (by positivity)
  calc
    _ = lowUnselectedWeight slots J W P a*N*
        ∑b : LowSelectedTuple slots J,lowSelectedWeight η slots J W P t b*
          ∫v : ℝ,lowSeparatedIntegrand C W0 W1 Ω (X/L) (Y/L)
            (lowMarkedInverseRow η S hS (lowSelectedIdeal slots J b) T t) v := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      rw [compensationRowTest_join_low η S hS hbad W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hWs
        slots hslots J a b X Y T t hX hY hT]
      have hw := lowSlotJoin_weight η slots J W P t a b
      dsimp only [C,Ω,L,N]
      linear_combination (Real.sqrt (lowPhysicalScale (calibrationForSet S hS)
        (X/elementNorm (∏i : J,(a i).val)) (Y/elementNorm (∏i : J,(a i).val))):ℂ)⁻¹*
        (1/(2*Real.pi):ℂ)*(∫v : ℝ,lowSeparatedIntegrand (calibrationForSet S hS) W0 W1
          (lowOuterCutoff (a0*a1) (max 1 (b0*b1)))
          (X/elementNorm (∏i : J,(a i).val)) (Y/elementNorm (∏i : J,(a i).val))
          (lowMarkedInverseRow η S hS (lowSelectedIdeal slots J b) T t) v)*hw
    _ = _ := by
      rw [lowSeparatedIntegral_finite_sum Finset.univ (lowSelectedWeight η slots J W P t)
        C W0 W1 Ω a0 b0 ha0 hW0 hWs hW1c hΩc hΩ0 (X/L) (Y/L)
        (div_pos hX hL) (div_pos hY hL)]
      rfl

end SevenEighths.ProbePhysical
end

end OAI
end

theorem solution : type_of% @OAI.SevenEighths.ProbePhysical.compensation_tuple_low_polynomial_oai := @OAI.SevenEighths.ProbePhysical.compensation_tuple_low_polynomial_oai
