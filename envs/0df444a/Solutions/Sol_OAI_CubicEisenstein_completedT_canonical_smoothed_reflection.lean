-- Prove2me | solution 1 for OAI.CubicEisenstein.completedT_canonical_smoothed_reflection
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T02:30:43.924643+00:00
-- url     : https://prove2.me/submissions/349e6896-5ba6-4639-90e0-21b9581ae3e5

import Mathlib
import Definitions.Def_OAIHecke78B021
import Theorems.Thm_OAI_CubicEisenstein_completedBesselProfile_eq_finite_cuspProfiles
import Theorems.Thm_OAI_CubicEisenstein_completedBesselProfile_mellin_entire_of_periodic

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

theorem primaryGenerator_norm_sq (I : Ideal O) (h : primaryGenerator I ≠ 0) :
    ‖ConcreteTraceCRT.eisEmbedding (primaryGenerator I)‖ ^ 2 = (Ideal.absNorm I : ℝ) := by
  rw [eisEmbedding_norm_sq_eq_absNorm_span, (primaryGenerator_spec I h).1]

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
section

open ActualEisensteinCubic ConcreteTraceCRT

theorem squarefreeGaussCoefficient_eq (I : Ideal O) (hs : Squarefree I)
    (hI : primaryGenerator I ≠ 0) :
    squarefreeGaussCoefficient I =
      star (FiniteGaussPhase.angularFactor (primaryGenerator I)) * gaussTwo I hI := by
  rw [squarefreeGaussCoefficient, dif_pos ⟨hs, hI⟩]

theorem summand_zero_left (Ψ : O →* ℂ) (W : ℝ → ℂ) (X : ℝ) (J : Ideal O) :
    summand Ψ W X 0 J = 0 := by simp [summand]

theorem summand_zero_right (Ψ : O →* ℂ) (W : ℝ → ℂ) (X : ℝ) (I : Ideal O) :
    summand Ψ W X I 0 = 0 := by simp [summand]

theorem primaryGenerator_norm (I : Ideal O) (hI : primaryGenerator I ≠ 0) :
    ‖eisEmbedding (primaryGenerator I)‖ = Real.sqrt (Ideal.absNorm I : ℝ) := by
  rw [← primaryGenerator_norm_sq I hI, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]

theorem columnWeight_eq (Ψ : O →* ℂ) (I : Ideal O) (hs : Squarefree I)
    (hI : primaryGenerator I ≠ 0) :
    columnWeight Ψ I = star (FiniteGaussPhase.angularFactor (primaryGenerator I)) *
      gaussTwo I hI * Ψ (primaryGenerator I) := by
  rw [columnWeight, squarefreeGaussCoefficient_eq I hs hI]

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

theorem completedT_summable (Ψ : O →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) :
    Summable (fun p : Ideal O × Ideal O => summand Ψ W X p.1 p.2) :=
  summable_of_hasFiniteSupport (completedT_finite_support Ψ W hW X hX)

open ActualEisensteinCubic ConcreteTraceCRT

end CompletedGauss

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.QuadraticSieve.InitialBound
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

open scoped Classical FourierTransform SchwartzMap ContDiff
open MeasureTheory

namespace CubicReflectionKernel

theorem Gamma_vertical_conj (a u : ℝ) :
    Complex.Gamma ((a : ℂ) - u * Complex.I) =
      star (Complex.Gamma ((a : ℂ) + u * Complex.I)) := by
  change _ = (starRingEnd ℂ) (Complex.Gamma ((a : ℂ) + u * Complex.I))
  rw [← Complex.Gamma_conj]
  congr 1
  simp [sub_eq_add_neg]

end CubicReflectionKernel

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

theorem paperScale_pos : 0 < paperScale := by
  unfold paperScale
  positivity

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

theorem Gamma_differentiableAt_of_re_pos (z : ℂ) (hz : 0 < z.re) :
    DifferentiableAt ℂ Complex.Gamma z := by
  apply Complex.differentiableAt_Gamma
  intro m hm
  have hr := congrArg Complex.re hm
  simp only [Complex.neg_re, Complex.natCast_re] at hr
  have hn : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  linarith

theorem gammaMultiplier_differentiableAt (s : ℂ) (hs : -(5 / 6 : ℝ) < s.re) :
    DifferentiableAt ℂ gammaMultiplier s := by
  have h1 := (Gamma_differentiableAt_of_re_pos ((7 / 6 : ℂ) + s) (by
    norm_num [Complex.add_re, Complex.div_re]
    linarith)).comp s (differentiableAt_const _ |>.add differentiableAt_id)
  have h2 := (Gamma_differentiableAt_of_re_pos ((5 / 6 : ℂ) + s) (by
    norm_num [Complex.add_re, Complex.div_re]
    linarith)).comp s (differentiableAt_const _ |>.add differentiableAt_id)
  have h3 := (Complex.differentiable_one_div_Gamma ((7 / 6 : ℂ) - s)).comp s
    (differentiableAt_const _ |>.sub differentiableAt_id)
  have h4 := (Complex.differentiable_one_div_Gamma ((5 / 6 : ℂ) - s)).comp s
    (differentiableAt_const _ |>.sub differentiableAt_id)
  convert (preTransparency := .instances) ((h1.mul h2).mul (h3.mul h4)) using 1
  ext z
  simp only [gammaMultiplier, Function.comp_def, div_eq_mul_inv, mul_inv_rev, Pi.mul_apply]
  ring

theorem kernelMellinIntegrand_differentiableAt
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (s : ℂ) (hs : -(5 / 6 : ℝ) < s.re) :
    DifferentiableAt ℂ (fun t => mellin V (-t) * gammaMultiplier t) s := by
  exact ((compact_source_mellin_differentiable V a b ha hsupp hV (-s)).comp s
    differentiableAt_id.neg).mul (gammaMultiplier_differentiableAt s hs)

end CubicReflectionKernel

open scoped BigOperators Classical

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

namespace VerticalContourShift
open MeasureTheory Filter Set
open scoped Topology

theorem horizontal_integral_tendsto_zero
    (f : ℂ → ℂ) (a b C : ℝ) (hab : a ≤ b)
    (hbound : ∀ σ ∈ Icc a b, ∀ t : ℝ,
      ‖f ((σ : ℂ) + t * Complex.I)‖ ≤ C / (1 + t ^ 2)) :
    Tendsto (fun t : ℝ => ∫ σ : ℝ in a..b, f ((σ : ℂ) + t * Complex.I))
      atTop (𝓝 0) := by
  have ht : Tendsto (fun t : ℝ => 1 + t ^ 2) atTop atTop :=
    tendsto_atTop_add_const_left atTop 1 (tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0))
  have hz : Tendsto (fun t : ℝ => C / (1 + t ^ 2) * |b - a|) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.div_atTop ht).mul_const |b - a|
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) _ hz
  intro t
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro σ hσ
  exact hbound σ (Ioc_subset_Icc_self (by simpa [uIoc_of_le hab] using hσ)) t

theorem integral_eq_of_strip_decay
    (f : ℂ → ℂ) (a b C : ℝ) (hab : a ≤ b)
    (hdiff : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → DifferentiableAt ℂ f z)
    (ha : Integrable (fun t : ℝ => f ((a : ℂ) + t * Complex.I)))
    (hb : Integrable (fun t : ℝ => f ((b : ℂ) + t * Complex.I)))
    (hbound : ∀ σ ∈ Icc a b, ∀ t : ℝ,
      ‖f ((σ : ℂ) + t * Complex.I)‖ ≤ C / (1 + t ^ 2)) :
    (∫ t : ℝ, f ((a : ℂ) + t * Complex.I)) =
      ∫ t : ℝ, f ((b : ℂ) + t * Complex.I) := by
  let H (t : ℝ) : ℂ := ∫ σ : ℝ in a..b, f ((σ : ℂ) + t * Complex.I)
  let V (σ t : ℝ) : ℂ := ∫ u : ℝ in -t..t, f ((σ : ℂ) + u * Complex.I)
  have htop : Tendsto H atTop (𝓝 0) := horizontal_integral_tendsto_zero f a b C hab hbound
  have hbottom : Tendsto (fun t : ℝ => H (-t)) atTop (𝓝 0) := by
    let g (z : ℂ) := f (star z)
    have hg : ∀ σ ∈ Icc a b, ∀ t : ℝ,
        ‖g ((σ : ℂ) + t * Complex.I)‖ ≤ C / (1 + t ^ 2) := by
      intro σ hσ t
      simpa [g] using hbound σ hσ (-t)
    convert (preTransparency := .instances) horizontal_integral_tendsto_zero g a b C hab hg using 1 ;
      simp [g, H]
  have hVa : Tendsto (V a) atTop
      (𝓝 (∫ t : ℝ, f ((a : ℂ) + t * Complex.I))) :=
    intervalIntegral_tendsto_integral ha tendsto_neg_atTop_atBot tendsto_id
  have hVb : Tendsto (V b) atTop
      (𝓝 (∫ t : ℝ, f ((b : ℂ) + t * Complex.I))) :=
    intervalIntegral_tendsto_integral hb tendsto_neg_atTop_atBot tendsto_id
  have hrect (t : ℝ) : H (-t) - H t + Complex.I * V b t - Complex.I * V a t = 0 := by
    have hd : DifferentiableOn ℂ f
        (uIcc (((a : ℂ) - t * Complex.I).re) (((b : ℂ) + t * Complex.I).re) ×ℂ
         uIcc (((a : ℂ) - t * Complex.I).im) (((b : ℂ) + t * Complex.I).im)) := by
      intro z hz
      apply (hdiff z ?_ ?_).differentiableWithinAt
      · have hz' : z.re ∈ Icc a b := by
          simpa [uIcc_of_le hab] using hz.1
        exact hz'.1
      · have hz' : z.re ∈ Icc a b := by
          simpa [uIcc_of_le hab] using hz.1
        exact hz'.2
    have hr := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f
      ((a : ℂ) - t * Complex.I) ((b : ℂ) + t * Complex.I) hd
    simpa [H, V, smul_eq_mul] using hr
  have hlim : Tendsto
      (fun t : ℝ => H (-t) - H t + Complex.I * V b t - Complex.I * V a t)
      atTop (𝓝 (0 - 0 + Complex.I * (∫ t : ℝ, f ((b : ℂ) + t * Complex.I)) -
        Complex.I * (∫ t : ℝ, f ((a : ℂ) + t * Complex.I)))) :=
    ((hbottom.sub htop).add (tendsto_const_nhds.mul hVb)).sub
      (tendsto_const_nhds.mul hVa)
  have heq : Complex.I * (∫ t : ℝ, f ((b : ℂ) + t * Complex.I)) -
      Complex.I * (∫ t : ℝ, f ((a : ℂ) + t * Complex.I)) = 0 := by
    have hzero : Tendsto (fun t : ℝ => H (-t) - H t + Complex.I * V b t - Complex.I * V a t)
        atTop (𝓝 0) := by
      simpa only [hrect] using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℂ)) atTop (𝓝 0))
    simpa using tendsto_nhds_unique hlim hzero
  exact (mul_left_cancel₀ Complex.I_ne_zero (sub_eq_zero.mp heq)).symm

end VerticalContourShift

open scoped BigOperators Classical

open scoped BigOperators Classical SchwartzMap

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
namespace CubicReflectionKernel

theorem betaIntegral_ofReal (a b : ℝ) :
    Complex.betaIntegral (a : ℂ) (b : ℂ) = (realBeta a b : ℂ) := by
  rw [Complex.betaIntegral, realBeta, ← intervalIntegral.integral_ofReal]
  apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
  intro x hx
  dsimp only
  rw [Complex.ofReal_mul, Complex.ofReal_cpow hx.1.le,
    Complex.ofReal_cpow (sub_pos.mpr hx.2).le]
  push_cast
  rfl

theorem norm_betaIntegral_le (u v : ℂ) :
    ‖Complex.betaIntegral u v‖ ≤ realBeta u.re v.re := by
  apply (intervalIntegral.norm_integral_le_integral_norm (by norm_num : (0 : ℝ) ≤ 1)).trans_eq
  apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
  intro x hx
  dsimp only
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx.1]
  have hcast : (1 - (x : ℂ)) = ((1 - x : ℝ) : ℂ) := by push_cast; rfl
  rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos (sub_pos.mpr hx.2)]
  simp

theorem realBeta_eq_Gamma (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    realBeta a b = Real.Gamma a * Real.Gamma b / Real.Gamma (a + b) := by
  apply Complex.ofReal_injective
  rw [← betaIntegral_ofReal]
  rw [Complex.betaIntegral_eq_Gamma_mul_div _ _ (by simpa using ha) (by simpa using hb)]
  rw [← Complex.ofReal_add]
  simp only [Complex.Gamma_ofReal, Complex.ofReal_div, Complex.ofReal_mul]

theorem Gamma_ratio_eq_beta (z : ℂ) (d : ℝ) (hz : 0 < z.re) (hd : 0 < d) :
    Complex.Gamma z / Complex.Gamma (z + d) =
      Complex.betaIntegral z d / Complex.Gamma d := by
  rw [Complex.betaIntegral_eq_Gamma_mul_div _ _ hz (by simpa using hd)]
  have hdn : Complex.Gamma (d : ℂ) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simpa using hd)
  field_simp

theorem Gamma_vertical_ratio_bound (a d t : ℝ) (ha : 0 < a) (hd : 0 < d) :
    ‖Complex.Gamma ((a : ℂ) + t * Complex.I) /
      Complex.Gamma ((a : ℂ) + t * Complex.I + d)‖ ≤
      Real.Gamma a / Real.Gamma (a + d) := by
  rw [Gamma_ratio_eq_beta _ d (by simpa using ha) hd, norm_div]
  have hg := Real.Gamma_pos_of_pos hd
  have hb := norm_betaIntegral_le ((a : ℂ) + t * Complex.I) (d : ℂ)
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, mul_zero, zero_mul, sub_zero, add_zero] at hb
  rw [Complex.Gamma_ofReal, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hg]
  calc
    _ ≤ realBeta a d / Real.Gamma d := div_le_div_of_nonneg_right hb hg.le
    _ = _ := by rw [realBeta_eq_Gamma a d ha hd]; field_simp

theorem inverse_Gamma_shift (z : ℂ) (n : ℕ) :
    (Complex.Gamma z)⁻¹ =
      (∏ k ∈ Finset.range n, (z + k)) * (Complex.Gamma (z + n))⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ih, Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (z + n),
      Finset.prod_range_succ]
    push_cast
    ring_nf

theorem Gamma_shifted_pair_bound (a σ t : ℝ) (n : ℕ)
    (ha : 0 < a + σ) (hd : 0 < (n : ℝ) - 2 * σ) :
    ‖Complex.Gamma ((a : ℂ) + (σ + t * Complex.I)) /
      Complex.Gamma ((a : ℂ) - (σ + t * Complex.I) + n)‖ ≤
      Real.Gamma (a + σ) / Real.Gamma (a - σ + n) := by
  have hb := Gamma_vertical_ratio_bound (a + σ) ((n : ℝ) - 2 * σ) t ha hd
  have hn : ((a + σ : ℝ) : ℂ) + t * Complex.I =
      (a : ℂ) + (σ + t * Complex.I) := by push_cast; ring
  have hdp : ((a + σ : ℝ) : ℂ) + t * Complex.I + ((n : ℝ) - 2 * σ : ℝ) =
      ((a - σ + n : ℝ) : ℂ) + t * Complex.I := by push_cast; ring
  have hdm : (a : ℂ) - (σ + t * Complex.I) + n =
      ((a - σ + n : ℝ) : ℂ) - t * Complex.I := by push_cast; ring
  have hr : a + σ + ((n : ℝ) - 2 * σ) = a - σ + n := by ring
  rw [hdp, hn, hr] at hb
  rw [hdm, Gamma_vertical_conj, norm_div, norm_star]
  simpa only [norm_div] using hb

theorem norm_Gamma_shift_factor (z : ℂ) (n : ℕ) :
    ‖∏ k ∈ Finset.range n, (z + k)‖ ≤ (‖z‖ + n) ^ n := by
  rw [norm_prod]
  calc
    _ ≤ ∏ _k ∈ Finset.range n, (‖z‖ + n) := by
      apply Finset.prod_le_prod
      · intro k hk
        exact norm_nonneg _
      · intro k hk
        have hk' : (k : ℝ) ≤ n := by exact_mod_cast (Finset.mem_range.mp hk).le
        exact (norm_add_le _ _).trans (by simpa using add_le_add_left hk' ‖z‖)
    _ = _ := by simp

end CubicReflectionKernel

open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter Set
namespace CubicReflectionKernel

theorem Gamma_pair_strip_bound (a : ℝ) (ha : 1 / 4 < a) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ), ∀ t : ℝ,
      ‖Complex.Gamma ((a : ℂ) + (σ + t * Complex.I)) /
        Complex.Gamma ((a : ℂ) - (σ + t * Complex.I))‖ ≤
        C * (1 + |t|) ^ (2 * A + 2) := by
  let n : ℕ := 2 * A + 2
  let I : Set ℝ := Set.Icc (-(1 / 4 : ℝ)) (A : ℝ)
  have hapos (σ : ℝ) (hσ : σ ∈ I) : 0 < a + σ := by
    have := hσ.1
    linarith
  have hdpos (σ : ℝ) (hσ : σ ∈ I) : 0 < (n : ℝ) - 2 * σ := by
    have := hσ.2
    dsimp [n]
    push_cast
    linarith
  have hdenpos (σ : ℝ) (hσ : σ ∈ I) : 0 < a - σ + n := by
    have h1 := hapos σ hσ
    have h2 := hdpos σ hσ
    linarith
  have hc1 : ContinuousOn (fun σ : ℝ => Real.Gamma (a + σ)) I :=
    Real.differentiableOn_Gamma_Ioi.continuousOn.comp
      (continuous_const.add continuous_id).continuousOn hapos
  have hc2 : ContinuousOn (fun σ : ℝ => Real.Gamma (a - σ + n)) I :=
    Real.differentiableOn_Gamma_Ioi.continuousOn.comp
      ((continuous_const.sub continuous_id).add continuous_const).continuousOn hdenpos
  have hc : ContinuousOn (fun σ : ℝ => Real.Gamma (a + σ) / Real.Gamma (a - σ + n)) I :=
    hc1.div hc2 (fun σ hσ => (Real.Gamma_pos_of_pos (hdenpos σ hσ)).ne')
  obtain ⟨C₀, hC₀⟩ := (isCompact_Icc : IsCompact I).bddAbove_image hc
  let C₁ : ℝ := |C₀| + 1
  have hC₁ : 0 < C₁ := by dsimp [C₁]; positivity
  have hreal (σ : ℝ) (hσ : σ ∈ I) :
      Real.Gamma (a + σ) / Real.Gamma (a - σ + n) ≤ C₁ := by
    exact (hC₀ (Set.mem_image_of_mem _ hσ)).trans (by dsimp [C₁]; linarith [le_abs_self C₀])
  let B : ℝ := |a| + A + 1 + n + 1
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨B ^ n * C₁, mul_pos (pow_pos hB n) hC₁, ?_⟩
  intro σ hσ t
  have hσ' : σ ∈ I := hσ
  have hσabs : |σ| ≤ (A : ℝ) + 1 := by
    apply abs_le.mpr
    constructor <;> linarith [hσ.1, hσ.2, (Nat.cast_nonneg A : (0 : ℝ) ≤ A)]
  have hz : ‖(a : ℂ) - (σ + t * Complex.I)‖ ≤ |a| + A + 1 + |t| := by
    calc
      _ ≤ ‖(a : ℂ)‖ + ‖(σ : ℂ) + t * Complex.I‖ := norm_sub_le _ _
      _ ≤ ‖(a : ℂ)‖ + (‖(σ : ℂ)‖ + ‖(t : ℂ) * Complex.I‖) :=
        add_le_add le_rfl (norm_add_le _ _)
      _ = |a| + (|σ| + |t|) := by simp
      _ ≤ _ := by linarith
  have hzB : ‖(a : ℂ) - (σ + t * Complex.I)‖ + n ≤ B * (1 + |t|) := by
    dsimp [B]
    nlinarith [abs_nonneg a, abs_nonneg t, (Nat.cast_nonneg A : (0 : ℝ) ≤ A), (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hprod : ‖∏ k ∈ Finset.range n, ((a : ℂ) - (σ + t * Complex.I) + k)‖ ≤
      B ^ n * (1 + |t|) ^ n := by
    apply (norm_Gamma_shift_factor _ n).trans
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hzB n
  have hratio := (Gamma_shifted_pair_bound a σ t n (hapos σ hσ') (hdpos σ hσ')).trans
    (hreal σ hσ')
  have heq : Complex.Gamma ((a : ℂ) + (σ + t * Complex.I)) /
      Complex.Gamma ((a : ℂ) - (σ + t * Complex.I)) =
      (∏ k ∈ Finset.range n, ((a : ℂ) - (σ + t * Complex.I) + k)) *
      (Complex.Gamma ((a : ℂ) + (σ + t * Complex.I)) /
       Complex.Gamma ((a : ℂ) - (σ + t * Complex.I) + n)) := by
    rw [div_eq_mul_inv, inverse_Gamma_shift _ n, div_eq_mul_inv]
    ring
  rw [heq, norm_mul]
  calc
    _ ≤ (B ^ n * (1 + |t|) ^ n) * C₁ :=
      mul_le_mul hprod hratio (norm_nonneg _) (by positivity)
    _ = _ := by dsimp [n]; ring

theorem gammaMultiplier_strip_bound (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ), ∀ t : ℝ,
      ‖gammaMultiplier ((σ : ℂ) + t * Complex.I)‖ ≤
        C * (1 + |t|) ^ (4 * A + 4) := by
  obtain ⟨C₁, hC₁, h1⟩ := Gamma_pair_strip_bound (7 / 6) (by norm_num) A
  obtain ⟨C₂, hC₂, h2⟩ := Gamma_pair_strip_bound (5 / 6) (by norm_num) A
  refine ⟨C₁ * C₂, mul_pos hC₁ hC₂, ?_⟩
  intro σ hσ t
  have heq : gammaMultiplier ((σ : ℂ) + t * Complex.I) =
      (Complex.Gamma (((7 / 6 : ℝ) : ℂ) + (σ + t * Complex.I)) /
       Complex.Gamma (((7 / 6 : ℝ) : ℂ) - (σ + t * Complex.I))) *
      (Complex.Gamma (((5 / 6 : ℝ) : ℂ) + (σ + t * Complex.I)) /
       Complex.Gamma (((5 / 6 : ℝ) : ℂ) - (σ + t * Complex.I))) := by
    simp only [gammaMultiplier, Complex.ofReal_div, Complex.ofReal_ofNat]
    exact div_mul_div_comm _ _ _ _ |>.symm
  rw [heq, norm_mul]
  calc
    _ ≤ (C₁ * (1 + |t|) ^ (2 * A + 2)) * (C₂ * (1 + |t|) ^ (2 * A + 2)) :=
      mul_le_mul (h1 σ hσ t) (h2 σ hσ t) (norm_nonneg _) (by positivity)
    _ = _ := by
      rw [mul_mul_mul_comm, ← pow_add]
      congr 2
      omega

theorem section_deriv_smooth (F : ℝ → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => deriv (F p.1) p.2) := by
  have hFp : ContDiff ℝ ∞
      (Function.uncurry (fun p : ℝ × ℝ => F p.1)) :=
    hF.comp (contDiff_fst.fst.prodMk contDiff_snd)
  have hd := hFp.fderiv contDiff_snd (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞)
  simpa only [deriv] using hd.clm_apply (contDiff_const (c := (1 : ℝ)))

theorem section_iteratedDeriv_smooth (F : ℝ → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (j : ℕ) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => iteratedDeriv j (F p.1) p.2) := by
  induction j with
  | zero => simpa only [iteratedDeriv_zero, Function.uncurry_def] using hF
  | succ j ih =>
    simpa only [iteratedDeriv_succ] using
      section_deriv_smooth (fun σ => iteratedDeriv j (F σ)) ih

theorem tsupport_iteratedDeriv_subset (f : ℝ → ℂ) (j : ℕ) :
    tsupport (iteratedDeriv j f) ⊆ tsupport f := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [iteratedDeriv_succ]
    exact tsupport_deriv_subset.trans ih

theorem compact_family_deriv_integrable (F : ℝ → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (K : Set ℝ) (hK : IsCompact K)
    (hsupp : ∀ σ, Function.support (F σ) ⊆ K) (σ : ℝ) (j : ℕ) :
    Integrable (iteratedDeriv j (F σ)) := by
  have hs : ContDiff ℝ ∞ (F σ) := hF.comp (contDiff_const.prodMk contDiff_id)
  have hc : HasCompactSupport (iteratedDeriv j (F σ)) := by
    apply HasCompactSupport.of_support_subset_isCompact hK
    exact (subset_tsupport _).trans ((tsupport_iteratedDeriv_subset (F σ) j).trans
      (closure_minimal (hsupp σ) hK.isClosed))
  exact (hs.continuous_iteratedDeriv j (by simp)).integrable_of_hasCompactSupport hc

theorem compact_family_deriv_L1_bound (F : ℝ → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (K : Set ℝ) (hK : IsCompact K)
    (hsupp : ∀ σ, Function.support (F σ) ⊆ K) (J : Set ℝ) (hJ : IsCompact J)
    (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ J, (∫ u : ℝ, ‖iteratedDeriv j (F σ) u‖) ≤ C := by
  have hc := (section_iteratedDeriv_smooth F hF j).continuous.norm
  obtain ⟨M, hM⟩ := (hJ.prod hK).bddAbove_image hc.continuousOn
  let C : ℝ := (|M| + 1) * (volume.real K + 1)
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro σ hσ
  have hbound : ∀ u ∈ K, ‖iteratedDeriv j (F σ) u‖ ≤ |M| + 1 := by
    intro u hu
    exact (hM (Set.mem_image_of_mem _ (show (σ, u) ∈ J ×ˢ K from ⟨hσ, hu⟩))).trans (by linarith [le_abs_self M])
  have hs : Function.support (iteratedDeriv j (F σ)) ⊆ K :=
    (subset_tsupport _).trans ((tsupport_iteratedDeriv_subset (F σ) j).trans
      (closure_minimal (hsupp σ) hK.isClosed))
  have hzero : ∀ u, u ∉ K → ‖iteratedDeriv j (F σ) u‖ = 0 := by
    intro u hu
    have hz : iteratedDeriv j (F σ) u = 0 := by
      by_contra hn
      exact hu (hs hn)
    simp [hz]
  have hi := norm_setIntegral_le_of_norm_le_const («μ» := volume) (f := fun u => ‖iteratedDeriv j (F σ) u‖)
    hK.measure_lt_top (C := |M| + 1) (fun u hu => by simpa using hbound u hu)
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero] at hi
  rw [Real.norm_of_nonneg (integral_nonneg (fun u => norm_nonneg _))] at hi
  exact hi.trans (by dsimp [C]; nlinarith [abs_nonneg M])

theorem compact_family_fourier_power_bound (F : ℝ → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (K : Set ℝ) (hK : IsCompact K)
    (hsupp : ∀ σ, Function.support (F σ) ⊆ K) (J : Set ℝ) (hJ : IsCompact J)
    (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ J, ∀ w : ℝ,
      |w| ^ j * ‖𝓕 (F σ) w‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := compact_family_deriv_L1_bound F hF K hK hsupp J hJ j
  refine ⟨C / (2 * Real.pi) ^ j, by positivity, ?_⟩
  intro σ hσ w
  have hs : ContDiff ℝ ∞ (F σ) := hF.comp (contDiff_const.prodMk contDiff_id)
  have hfour := Real.fourier_iteratedDeriv (N := (⊤ : ℕ∞)) hs
    (fun k _ => compact_family_deriv_integrable F hF K hK hsupp σ k)
    (by simp : (j : ℕ∞) ≤ ⊤)
  have hid : (2 * Real.pi) ^ j * (|w| ^ j * ‖𝓕 (F σ) w‖) =
      ‖𝓕 (iteratedDeriv j (F σ)) w‖ := by
    rw [hfour]
    simp only [norm_smul, norm_pow, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    norm_num
    ring
  have hn : ‖𝓕 (iteratedDeriv j (F σ)) w‖ ≤ C := by
    apply (VectorFourier.norm_fourierIntegral_le_integral_norm
      Real.fourierChar volume (innerₗ ℝ) (iteratedDeriv j (F σ)) w).trans
    exact hb σ hσ
  apply (le_div_iff₀ (by positivity : 0 < (2 * Real.pi) ^ j)).mpr
  rw [← hid] at hn
  calc
    _ = (2 * Real.pi) ^ j * (|w| ^ j * ‖𝓕 (F σ) w‖) := mul_comm _ _
    _ ≤ C := hn

theorem compact_family_fourier_weighted_bound (F : ℝ → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (K : Set ℝ) (hK : IsCompact K)
    (hsupp : ∀ σ, Function.support (F σ) ⊆ K) (J : Set ℝ) (hJ : IsCompact J)
    (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ J, ∀ w : ℝ,
      (1 + |w|) ^ j * ‖𝓕 (F σ) w‖ ≤ C := by
  obtain ⟨C₀, hC₀, h0⟩ := compact_family_fourier_power_bound F hF K hK hsupp J hJ 0
  obtain ⟨Cj, hCj, hj⟩ := compact_family_fourier_power_bound F hF K hK hsupp J hJ j
  refine ⟨2 ^ j * (C₀ + Cj), by positivity, ?_⟩
  intro σ hσ w
  have hbase : ‖𝓕 (F σ) w‖ ≤ C₀ := by simpa using h0 σ hσ w
  by_cases hw : |w| ≤ 1
  · calc
      _ ≤ 2 ^ j * ‖𝓕 (F σ) w‖ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (by linarith) j) (norm_nonneg _)
      _ ≤ 2 ^ j * C₀ := mul_le_mul_of_nonneg_left hbase (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  · have hw' : 1 ≤ |w| := le_of_lt (lt_of_not_ge hw)
    calc
      _ ≤ (2 * |w|) ^ j * ‖𝓕 (F σ) w‖ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (by linarith) j) (norm_nonneg _)
      _ = 2 ^ j * (|w| ^ j * ‖𝓕 (F σ) w‖) := by rw [mul_pow, mul_assoc]
      _ ≤ 2 ^ j * Cj := mul_le_mul_of_nonneg_left (hj σ hσ w) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

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

theorem compact_source_mellin_strip_decay (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (lo hi : ℝ) (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Set.Icc lo hi, ∀ t : ℝ,
      (1 + |t|) ^ j * ‖mellin V ((σ : ℂ) + t * Complex.I)‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := compact_family_fourier_weighted_bound
    (mellinLogFamily V) (mellinLogFamily_smooth V hV)
    (Set.Icc (-Real.log b) (-Real.log a)) isCompact_Icc
    (mellinLogFamily_support V a b ha hsupp) (Set.Icc lo hi) isCompact_Icc j
  refine ⟨(1 + 2 * Real.pi) ^ j * C, by positivity, ?_⟩
  intro σ hσ t
  rw [mellin_eq_logFamily_fourier]
  have ht : |t| = (2 * Real.pi) * |t / (2 * Real.pi)| := by
    rw [abs_div, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
    field_simp
  have hbase : 1 + |t| ≤ (1 + 2 * Real.pi) * (1 + |t / (2 * Real.pi)|) := by
    rw [ht]
    nlinarith [Real.pi_pos, abs_nonneg (t / (2 * Real.pi))]
  calc
    _ ≤ ((1 + 2 * Real.pi) * (1 + |t / (2 * Real.pi)|)) ^ j *
        ‖𝓕 (mellinLogFamily V σ) (t / (2 * Real.pi))‖ :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hbase j) (norm_nonneg _)
    _ = (1 + 2 * Real.pi) ^ j * ((1 + |t / (2 * Real.pi)|) ^ j *
        ‖𝓕 (mellinLogFamily V σ) (t / (2 * Real.pi))‖) := by rw [mul_pow, mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_left (hb σ hσ _) (by positivity)

end CubicReflectionKernel

open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter Set
namespace CubicReflectionKernel

theorem mellinData_strip_decay (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (A j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ), ∀ t : ℝ,
      (1 + |t|) ^ j * ‖mellinData V ((σ : ℂ) + t * Complex.I)‖ ≤ C := by
  let g : ℕ := 4 * A + 4
  obtain ⟨Cγ, hCγ, hγ⟩ := gammaMultiplier_strip_bound A
  obtain ⟨CV, hCV, hVb⟩ := compact_source_mellin_strip_decay V a b ha hsupp hV
    (-(A : ℝ)) (1 / 4) (g + j)
  refine ⟨Cγ * CV, mul_pos hCγ hCV, ?_⟩
  intro σ hσ t
  have hσ' : -σ ∈ Set.Icc (-(A : ℝ)) (1 / 4) := by constructor <;> linarith [hσ.1, hσ.2]
  have hmb := hVb (-σ) hσ' (-t)
  have heq : (-σ : ℝ) + (-t : ℝ) * Complex.I = -((σ : ℂ) + t * Complex.I) := by
    push_cast
    ring
  rw [heq, abs_neg] at hmb
  have hgb : ‖gammaMultiplier ((σ : ℂ) + t * Complex.I)‖ ≤ Cγ * (1 + |t|) ^ g := hγ σ hσ t
  rw [mellinData, norm_mul]
  calc
    _ = ((1 + |t|) ^ j * ‖mellin V (-((σ : ℂ) + t * Complex.I))‖) *
        ‖gammaMultiplier ((σ : ℂ) + t * Complex.I)‖ := by ring
    _ ≤ ((1 + |t|) ^ j * ‖mellin V (-((σ : ℂ) + t * Complex.I))‖) *
        (Cγ * (1 + |t|) ^ g) := mul_le_mul_of_nonneg_left hgb (by positivity)
    _ = Cγ * ((1 + |t|) ^ (g + j) * ‖mellin V (-((σ : ℂ) + t * Complex.I))‖) := by
      rw [pow_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hmb hCγ.le

theorem weighted_two_to_cauchy {C B : ℝ} (hB : 0 ≤ B) (t : ℝ)
    (h : (1 + |t|) ^ 2 * B ≤ C) : B ≤ C / (1 + t ^ 2) := by
  apply (le_div_iff₀ (by positivity : 0 < 1 + t ^ 2)).mpr
  have hpow : 1 + t ^ 2 ≤ (1 + |t|) ^ 2 := by nlinarith [abs_nonneg t, sq_abs t]
  exact (mul_le_mul_of_nonneg_left hpow hB).trans (by simpa only [mul_comm] using h)

theorem mellinEulerData_strip_bound (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (A j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ), ∀ t : ℝ,
      ‖mellinEulerData V j ((σ : ℂ) + t * Complex.I)‖ ≤ C / (1 + t ^ 2) := by
  obtain ⟨C, hC, hb⟩ := mellinData_strip_decay V a b ha hsupp hV A (j + 2)
  refine ⟨((A : ℝ) + 2) ^ j * C, by positivity, ?_⟩
  intro σ hσ t
  apply weighted_two_to_cauchy (norm_nonneg _) t
  have hσabs : |σ| ≤ (A : ℝ) + 1 := by
    apply abs_le.mpr
    constructor <;> linarith [hσ.1, hσ.2, (Nat.cast_nonneg A : (0 : ℝ) ≤ A)]
  have hz : ‖(σ : ℂ) + t * Complex.I‖ ≤ ((A : ℝ) + 2) * (1 + |t|) := by
    have hnorm := norm_add_le (σ : ℂ) ((t : ℂ) * Complex.I)
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one] at hnorm
    nlinarith [abs_nonneg t, (Nat.cast_nonneg A : (0 : ℝ) ≤ A)]
  rw [mellinEulerData, norm_mul, norm_pow, norm_neg]
  calc
    _ ≤ (1 + |t|) ^ 2 * ((((A : ℝ) + 2) * (1 + |t|)) ^ j *
        ‖mellinData V ((σ : ℂ) + t * Complex.I)‖) := by
      gcongr
    _ = ((A : ℝ) + 2) ^ j * ((1 + |t|) ^ (j + 2) *
        ‖mellinData V ((σ : ℂ) + t * Complex.I)‖) := by rw [mul_pow, pow_add]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hb σ hσ t) (by positivity)

theorem mellinEulerData_differentiableAt (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (j : ℕ) (s : ℂ) (hs : -(5 / 6 : ℝ) < s.re) :
    DifferentiableAt ℂ (mellinEulerData V j) s :=
  (differentiableAt_id.neg.pow j).mul
    (kernelMellinIntegrand_differentiableAt V a b ha hsupp hV s hs)

theorem mellinEulerData_vertical_integrable (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (A j : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ)) :
    Integrable (fun t : ℝ => mellinEulerData V j ((σ : ℂ) + t * Complex.I)) := by
  obtain ⟨C, hC, hb⟩ := mellinEulerData_strip_bound V a b ha hsupp hV A j
  have hc : Continuous (fun t : ℝ => mellinEulerData V j ((σ : ℂ) + t * Complex.I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply (mellinEulerData_differentiableAt V a b ha hsupp hV j _ ?_).continuousAt.comp
    · fun_prop
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, mul_zero, zero_mul, sub_zero, add_zero]
      linarith [hσ.1]
  apply (integrable_inv_one_add_sq.const_mul C).mono' hc.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun t => by simpa only [div_eq_mul_inv] using hb σ hσ t)

end CubicReflectionKernel

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Mellin.InverseContour
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
open MeasureTheory Filter Set

theorem inverseMellinIntegrand_differentiableAt
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (j : ℕ) (y : ℝ) (hy : 0 < y) (s : ℂ) (hs : -(5 / 6 : ℝ) < s.re) :
    DifferentiableAt ℂ (inverseMellinIntegrand V j y) s := by
  exact (differentiableAt_id.neg.const_cpow
    (Or.inl (Complex.ofReal_ne_zero.mpr hy.ne'))).mul
    (mellinEulerData_differentiableAt V a b ha hsupp hV j s hs)

theorem inverseMellinIntegrand_vertical_integrable
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (A j : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ))
    (y : ℝ) (hy : 0 < y) :
    Integrable (fun t : ℝ => inverseMellinIntegrand V j y ((σ : ℂ) + t * Complex.I)) := by
  apply (mellinEulerData_vertical_integrable V a b ha hsupp hV A j σ hσ).bdd_mul
    (c := y ^ (-σ))
  · exact ((show Continuous (fun t : ℝ => -((σ : ℂ) + t * Complex.I)) by fun_prop).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hy.ne'))).aestronglyMeasurable
  · filter_upwards [] with t
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hy]
    simp

theorem inverseMellinIntegrand_strip_bound
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (A j : ℕ) (y : ℝ) (hy : 0 < y) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ), ∀ t : ℝ,
      ‖inverseMellinIntegrand V j y ((σ : ℂ) + t * Complex.I)‖ ≤ C / (1 + t ^ 2) := by
  obtain ⟨C, hC, hb⟩ := mellinEulerData_strip_bound V a b ha hsupp hV A j
  have hc : Continuous (fun σ : ℝ => y ^ (-σ)) :=
    (Real.continuous_const_rpow hy.ne').comp continuous_neg
  obtain ⟨B, hB⟩ := (isCompact_Icc : IsCompact (Set.Icc (-(1 / 4 : ℝ)) (A : ℝ))).bddAbove_image hc.continuousOn
  refine ⟨(|B| + 1) * C, by positivity, ?_⟩
  intro σ hσ t
  have hby : y ^ (-σ) ≤ |B| + 1 :=
    (hB (Set.mem_image_of_mem _ hσ)).trans (by linarith [le_abs_self B])
  rw [inverseMellinIntegrand, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy]
  simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, Complex.I_re, mul_zero, zero_mul, sub_zero, add_zero]
  calc
    _ ≤ (|B| + 1) * (C / (1 + t ^ 2)) :=
      mul_le_mul hby (hb σ hσ t) (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem mellinInv_euler_shift
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (A j : ℕ) (σ : ℝ) (hσ : σ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ))
    (y : ℝ) (hy : 0 < y) :
    mellinInv 0 (mellinEulerData V j) y = mellinInv σ (mellinEulerData V j) y := by
  obtain ⟨C, hC, hb⟩ := inverseMellinIntegrand_strip_bound V a b ha hsupp hV A j y hy
  have h0 : (0 : ℝ) ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ) := by
    constructor
    · norm_num
    · exact Nat.cast_nonneg A
  have hshift (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ)) :
      (∫ t : ℝ, inverseMellinIntegrand V j y ((-(1 / 4) : ℝ) + t * Complex.I)) =
      ∫ t : ℝ, inverseMellinIntegrand V j y ((ρ : ℂ) + t * Complex.I) := by
    apply VerticalContourShift.integral_eq_of_strip_decay
      (inverseMellinIntegrand V j y) (-(1 / 4)) ρ C hρ.1
    · intro z hzlo hzhi
      apply inverseMellinIntegrand_differentiableAt V a b ha hsupp hV j y hy z
      linarith
    · apply inverseMellinIntegrand_vertical_integrable V a b ha hsupp hV A j
        (-(1 / 4)) ⟨le_rfl, hρ.1.trans hρ.2⟩ y hy
    · exact inverseMellinIntegrand_vertical_integrable V a b ha hsupp hV A j ρ hρ y hy
    · intro r hr t
      exact hb r ⟨hr.1, hr.2.trans hρ.2⟩ t
  have heq := (hshift 0 h0).symm.trans (hshift σ hσ)
  simpa only [mellinInv, smul_eq_mul, inverseMellinIntegrand] using
    congrArg (fun z : ℂ => (1 / (2 * Real.pi) : ℝ) • z) heq

end CubicReflectionKernel

open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter Set

open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter Set

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.RowCaps
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

open scoped BigOperators Classical

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Matrix ContDiff

namespace CubicEisenstein

lemma mobiusSpatial_positive (g : SL(2,ℂ)) (p : SpatialCoordinates) (hp : 0<p 2) :
    0< mobiusSpatial g p 2 := div_pos hp (mobiusSpatialDenominator_pos g p hp)

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Matrix ContDiff Manifold

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.CuspAverage
namespace OAI

noncomputable section

namespace CubicEisenstein

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

open Filter MeasureTheory
open scoped BigOperators Classical Topology

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology

section

lemma complex_gaussian_power_integrable (s : ℂ) (r : ℝ)
    (hs : 0<s.re) (hr : 0< r) :
    IntegrableOn (fun x : ℝ => (x:ℂ)^(s-1)*Complex.exp (-(r:ℂ)*(x:ℂ)^2))
      (Set.Ioi 0) volume := by
  have hs2 : 0<(s/(2:ℂ)).re := by simpa using half_pos hs
  have hbase : MellinConvergent (fun t : ℝ => Complex.exp (-(t:ℂ))) (s/2) := by
    simpa only [MellinConvergent,smul_eq_mul,Complex.ofReal_exp,Complex.ofReal_neg,mul_comm]
      using Complex.GammaIntegral_convergent hs2
  have hlinear := (MellinConvergent.comp_mul_left
    (f := fun t : ℝ => Complex.exp (-(t:ℂ))) (s := s/2) hr).mpr hbase
  have hgaussian := (MellinConvergent.comp_rpow
    (f := fun t : ℝ => Complex.exp (-((r*t:ℝ):ℂ))) (s := s) (a := 2)
      (by norm_num)).mpr hlinear
  simpa only [MellinConvergent,smul_eq_mul,Real.rpow_two,
    Complex.ofReal_mul,Complex.ofReal_pow,neg_mul] using hgaussian

lemma complex_gaussian_power_integral (s : ℂ) (r : ℝ)
    (hs : 0<s.re) (hr : 0< r) :
    (∫x : ℝ in Set.Ioi 0,(x:ℂ)^(s-1)*Complex.exp (-(r:ℂ)*(x:ℂ)^2)) =
      (1/2:ℂ)*((1/(r:ℂ))^(s/2)*Complex.Gamma (s/2)) := by
  have hs2 : 0<(s/(2:ℂ)).re := by simpa using half_pos hs
  have he := mellin_comp_rpow (fun t : ℝ => Complex.exp (-((r*t:ℝ):ℂ))) s 2
  simp only [mellin,smul_eq_mul,Real.rpow_two,Complex.ofReal_mul,
    Complex.ofReal_pow,Complex.real_smul] at he
  norm_num only [Complex.ofReal_ofNat] at he
  rw [Complex.integral_cpow_mul_exp_neg_mul_Ioi hs2 hr] at he
  simpa [neg_mul] using he

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

lemma cubicMellinMixture_slice_integrable (s : ℂ) (hs : 1/3<s.re)
    (t : ℝ) (ht : 0<t) :
    IntegrableOn (cubicMellinMixture s t) (Set.Ioi 0) volume := by
  apply (complex_gaussian_power_integrable (s-1/3) (1/(4*t))
    (by norm_num; linarith) (by positivity)).const_mul

lemma cubicMellinMixture_integral_x (s : ℂ) (hs : 1/3<s.re)
    (t : ℝ) (ht : 0<t) :
    (∫x : ℝ in Set.Ioi 0,cubicMellinMixture s t x) =
      ((1/2:ℂ)*(4:ℂ)^((s-1/3)/2)*Complex.Gamma ((s-1/3)/2))*
        ((t:ℂ)^((s+1/3)/2-1)*Complex.exp (-(t:ℂ))) := by
  simp only [cubicMellinMixture,integral_const_mul]
  rw [complex_gaussian_power_integral (s-1/3) (1/(4*t))
    (by norm_num; linarith) (by positivity)]
  have hb : (1/(((1/(4*t):ℝ):ℂ)))=(4:ℂ)*(t:ℂ) := by
    push_cast
    field_simp
  have hm : ((4:ℂ)*(t:ℂ))^((s-1/3)/2)=
      (4:ℂ)^((s-1/3)/2)*(t:ℂ)^((s-1/3)/2) := by
    simpa only [Complex.ofReal_ofNat] using
      Complex.mul_cpow_ofReal_nonneg (by norm_num : 0≤(4:ℝ)) ht.le ((s-1/3)/2)
  rw [hb,hm]
  have hp : (t:ℂ)^(-(2:ℂ)/3)*(t:ℂ)^((s-1/3)/2)=
      (t:ℂ)^((s+1/3)/2-1) := by
    rw [←Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr ht.ne')]
    congr 1
    ring
  calc
    _ = ((1/2:ℂ)*(4:ℂ)^((s-1/3)/2)*Complex.Gamma ((s-1/3)/2))*
        (((t:ℂ)^(-(2:ℂ)/3)*(t:ℂ)^((s-1/3)/2))*Complex.exp (-(t:ℂ))) := by ring
    _ = _ := by rw [hp]

lemma cubicMellinMixture_norm (s : ℂ) (t x : ℝ) (ht : 0<t) (hx : 0<x) :
    ‖cubicMellinMixture s t x‖ =
      (t^(-(2:ℝ)/3)*Real.exp (-t))*
        (x^((s.re-1/3)-1)*Real.exp (-(1/(4*t))*x^2)) := by
  have he : -((1/(4*t):ℝ):ℂ)*(x:ℂ)^2=(-(1/(4*t))*x^2:ℝ) := by
    push_cast
    rfl
  simp only [cubicMellinMixture,norm_mul,he,
    Complex.norm_cpow_eq_rpow_re_of_pos ht,Complex.norm_cpow_eq_rpow_re_of_pos hx,
    Complex.norm_exp,Complex.ofReal_re,Complex.neg_re]
  norm_num

lemma real_gaussian_power_integral (sigma r : ℝ) (hs : 0<sigma) (hr : 0< r) :
    (∫x : ℝ in Set.Ioi 0,x^(sigma-1)*Real.exp (-r*x^2)) =
      r^(-sigma/2)*(1/2)*Real.Gamma (sigma/2) := by
  simpa only [Real.rpow_two,sub_add_cancel] using
    (_root_.integral_rpow_mul_exp_neg_mul_rpow (p:=2) (q:=sigma-1) (b:=r)
      (by norm_num) (by linarith) hr)

lemma cubicMellinMixture_integral_norm (s : ℂ) (hs : 1/3<s.re)
    (t : ℝ) (ht : 0<t) :
    (∫x : ℝ in Set.Ioi 0,‖cubicMellinMixture s t x‖) =
      ((1/2:ℝ)*(4:ℝ)^((s.re-1/3)/2)*Real.Gamma ((s.re-1/3)/2))*
        (t^((s.re+1/3)/2-1)*Real.exp (-t)) := by
  calc
    _ = ∫x : ℝ in Set.Ioi 0,(t^(-(2:ℝ)/3)*Real.exp (-t))*
        (x^((s.re-1/3)-1)*Real.exp (-(1/(4*t))*x^2)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      exact cubicMellinMixture_norm s t x ht hx
    _ = _ := by
      rw [integral_const_mul,real_gaussian_power_integral (s.re-1/3) (1/(4*t))
        (by linarith) (by positivity)]
      have hpow : (1/(4*t):ℝ)^(-(s.re-1/3)/2)=(4:ℝ)^((s.re-1/3)/2)*t^((s.re-1/3)/2) := by
        rw [show -(s.re-1/3)/2=-((s.re-1/3)/2) by ring,
          Real.rpow_neg_eq_inv_rpow,one_div,inv_inv,
          Real.mul_rpow (by norm_num : 0≤(4:ℝ)) ht.le]
      rw [hpow]
      have hp : t^(-(2:ℝ)/3)*t^((s.re-1/3)/2)=t^((s.re+1/3)/2-1) := by
        rw [←Real.rpow_add ht]
        congr 1
        ring
      calc
        _ = ((1/2:ℝ)*(4:ℝ)^((s.re-1/3)/2)*Real.Gamma ((s.re-1/3)/2))*
            ((t^(-(2:ℝ)/3)*t^((s.re-1/3)/2))*Real.exp (-t)) := by ring
        _ = _ := by rw [hp]

lemma cubicMellinMixture_integrable (s : ℂ) (hs : 1/3<s.re) :
    Integrable (fun p : ℝ × ℝ => cubicMellinMixture s p.1 p.2)
      ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioi 0))) := by
  have hm : AEStronglyMeasurable (fun p : ℝ × ℝ => cubicMellinMixture s p.1 p.2)
      ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioi 0))) := by
    unfold cubicMellinMixture
    fun_prop
  apply (integrable_prod_iff hm).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact cubicMellinMixture_slice_integrable s hs t ht
  · have hg := (Real.GammaIntegral_convergent
        (show 0<(s.re+1/3)/2 by linarith)).const_mul
        ((1/2:ℝ)*(4:ℝ)^((s.re-1/3)/2)*Real.Gamma ((s.re-1/3)/2))
    apply hg.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [cubicMellinMixture_integral_norm s hs t ht]
    ring

lemma cubicMellinMixture_integral_t (s : ℂ) (x : ℝ) :
    (∫t : ℝ in Set.Ioi 0,cubicMellinMixture s t x) =
      (x:ℂ)^((s-1/3)-1)*schlafliIntegral (1/3) x := by
  rw [schlafliIntegral,←integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  have ht0 : (t:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht)
  have he : Complex.exp (-(t:ℂ))*Complex.exp (-((1/(4*t):ℝ):ℂ)*(x:ℂ)^2)=
      Complex.exp (-(t:ℂ)-(x:ℂ)^2/(4*t)) := by
    rw [←Complex.exp_add]
    congr 1
    push_cast
    field_simp
    ring
  rw [show (1/3:ℂ)-1=-(2:ℂ)/3 by ring]
  unfold cubicMellinMixture
  linear_combination (t:ℂ)^(-(2:ℂ)/3)*(x:ℂ)^((s-1/3)-1)*he

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

lemma schlafliBesselK_cubic_mellin_mixture (s : ℂ) (x : ℝ) (hx : 0<x) :
    (x:ℂ)^(s-1)*schlafliBesselK (1/3) x =
      ((1/2:ℂ)*(2:ℂ)^(1/3:ℂ))*(∫t : ℝ in Set.Ioi 0,cubicMellinMixture s t x) := by
  rw [schlafliBesselK,cubicMellinMixture_integral_t]
  have hdiv : (x/2:ℂ)^(-(1/3:ℂ))=(x:ℂ)^(-(1/3:ℂ))/(2:ℂ)^(-(1/3:ℂ)) := by
    simpa only [Complex.ofReal_ofNat] using
      Complex.div_cpow_ofReal_nonneg hx.le (by norm_num : 0≤(2:ℝ)) (-(1/3:ℂ))
  rw [hdiv,Complex.cpow_neg (2:ℂ) (1/3),div_inv_eq_mul]
  have hp : (x:ℂ)^(s-1)*(x:ℂ)^(-(1/3:ℂ))=(x:ℂ)^((s-1/3)-1) := by
    rw [←Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hx.ne')]
    congr 1
    ring
  linear_combination (1/2:ℂ)*(2:ℂ)^(1/3:ℂ)*schlafliIntegral (1/3) x*hp

lemma schlafliBesselK_cubic_mellin_integrable (s : ℂ) (hs : 1/3<s.re) :
    IntegrableOn (fun x : ℝ => (x:ℂ)^(s-1)*schlafliBesselK (1/3) x)
      (Set.Ioi 0) volume := by
  apply ((cubicMellinMixture_integrable s hs).integral_prod_right.const_mul
    ((1/2:ℂ)*(2:ℂ)^(1/3:ℂ))).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact (schlafliBesselK_cubic_mellin_mixture s x hx).symm

lemma cubicMellinMixture_double_integral (s : ℂ) (hs : 1/3<s.re) :
    (∫t : ℝ in Set.Ioi 0,∫x : ℝ in Set.Ioi 0,cubicMellinMixture s t x) =
      ((1/2:ℂ)*(4:ℂ)^((s-1/3)/2)*Complex.Gamma ((s-1/3)/2))*
        Complex.Gamma ((s+1/3)/2) := by
  have hB : 0<((s+1/3)/2).re := by norm_num; linarith
  calc
    _ = ∫t : ℝ in Set.Ioi 0,
        ((1/2:ℂ)*(4:ℂ)^((s-1/3)/2)*Complex.Gamma ((s-1/3)/2))*
          ((t:ℂ)^((s+1/3)/2-1)*Complex.exp (-(t:ℂ))) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      exact cubicMellinMixture_integral_x s hs t ht
    _ = _ := by
      rw [integral_const_mul]
      congr 1
      simpa only [Complex.GammaIntegral,Complex.ofReal_exp,Complex.ofReal_neg,mul_comm] using
        (Complex.Gamma_eq_integral hB).symm

theorem schlafliBesselK_cubic_mellin (s : ℂ) (hs : 1/3<s.re) :
    (∫x : ℝ in Set.Ioi 0,(x:ℂ)^(s-1)*schlafliBesselK (1/3) x) =
      (2:ℂ)^(s-2)*Complex.Gamma ((s-1/3)/2)*Complex.Gamma ((s+1/3)/2) := by
  have hmix : Integrable (Function.uncurry (cubicMellinMixture s))
      ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioi 0))) := by
    convert (preTransparency := .instances) cubicMellinMixture_integrable s hs using 1
    funext p
    rcases p with ⟨t,x⟩
    rfl
  have hswap := (integral_integral_swap hmix).symm
  have h4 : (4:ℂ)^((s-1/3)/2)=(2:ℂ)^(2*((s-1/3)/2)) := by
    have hh := (Complex.natCast_cpow_natCast_mul 2 2 ((s-1/3)/2)).symm
    norm_num at hh
    exact hh
  have hprod : (2:ℂ)^(1/3:ℂ)*(4:ℂ)^((s-1/3)/2)=(2:ℂ)^s := by
    rw [h4,←Complex.cpow_add _ _ (by norm_num : (2:ℂ)≠0)]
    congr 1
    ring
  have hscale : (1/4:ℂ)*(2:ℂ)^s=(2:ℂ)^(s-2) := by
    rw [Complex.cpow_sub _ _ (by norm_num : (2:ℂ)≠0)]
    norm_num
    ring
  calc
    _ = ((1/2:ℂ)*(2:ℂ)^(1/3:ℂ))*
        (∫x : ℝ in Set.Ioi 0,∫t : ℝ in Set.Ioi 0,cubicMellinMixture s t x) := by
      rw [←integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      exact schlafliBesselK_cubic_mellin_mixture s x hx
    _ = ((1/2:ℂ)*(2:ℂ)^(1/3:ℂ))*
        (((1/2:ℂ)*(4:ℂ)^((s-1/3)/2)*Complex.Gamma ((s-1/3)/2))*
          Complex.Gamma ((s+1/3)/2)) := by
      rw [hswap,cubicMellinMixture_double_integral s hs]
    _ = ((1/4:ℂ)*((2:ℂ)^(1/3:ℂ)*(4:ℂ)^((s-1/3)/2)))*
        Complex.Gamma ((s-1/3)/2)*Complex.Gamma ((s+1/3)/2) := by ring
    _ = _ := by rw [hprod,hscale]

end CubicEisenstein

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.BesselMellinTransform
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

namespace CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

lemma schlafliBesselK_cubic_scaled_mellin_integrable (s : ℂ) (c : ℝ)
    (hs : 1/3<s.re) (hc : 0<c) :
    IntegrableOn (fun v : ℝ => (v:ℂ)^(s-1)*schlafliBesselK (1/3) (c*v))
      (Set.Ioi 0) volume := by
  have hb : MellinConvergent (fun v => schlafliBesselK (1/3) v) s := by
    simpa only [MellinConvergent,smul_eq_mul] using schlafliBesselK_cubic_mellin_integrable s hs
  have hh := (MellinConvergent.comp_mul_left
    (f := fun v => schlafliBesselK (1/3) v) (s := s) hc).mpr hb
  simpa only [MellinConvergent,smul_eq_mul] using hh

lemma schlafliBesselK_cubic_scaled_mellin (s : ℂ) (c : ℝ)
    (hs : 1/3<s.re) (hc : 0<c) :
    (∫v : ℝ in Set.Ioi 0,(v:ℂ)^(s-1)*schlafliBesselK (1/3) (c*v)) =
      (c:ℂ)^(-s)*((2:ℂ)^(s-2)*Complex.Gamma ((s-1/3)/2)*Complex.Gamma ((s+1/3)/2)) := by
  have hh := mellin_comp_mul_left (fun v => schlafliBesselK (1/3) v) s hc
  simp only [mellin,smul_eq_mul] at hh
  rw [schlafliBesselK_cubic_mellin s hs] at hh
  exact hh

lemma source_cubic_bessel_mellin_integrable (s freq : ℂ)
    (hs : -(1/3)<s.re) (hfreq : freq≠0) :
    IntegrableOn (fun v : ℝ => (v:ℂ)^(2*s)*
      schlafliBesselK (1/3) (4*Real.pi*‖freq‖*v)) (Set.Ioi 0) volume := by
  have hc : 0<4*Real.pi*‖freq‖ := by positivity
  have ht : 1/3<(2*s+1).re := by norm_num; linarith
  simpa only [show (2*s+1:ℂ)-1=2*s by ring] using
    schlafliBesselK_cubic_scaled_mellin_integrable (2*s+1) (4*Real.pi*‖freq‖) ht hc

theorem source_cubic_bessel_mellin (s freq : ℂ)
    (hs : -(1/3)<s.re) (hfreq : freq≠0) :
    (∫v : ℝ in Set.Ioi 0,(v:ℂ)^(2*s)*schlafliBesselK (1/3) (4*Real.pi*‖freq‖*v)) =
      ((2:ℂ)^(2*s-1)*Complex.Gamma (s+1/3)*Complex.Gamma (s+2/3))/
        ((4*Real.pi*‖freq‖:ℝ):ℂ)^(2*s+1) := by
  have hc : 0<4*Real.pi*‖freq‖ := by positivity
  have ht : 1/3<(2*s+1).re := by norm_num; linarith
  have hh := schlafliBesselK_cubic_scaled_mellin (2*s+1) (4*Real.pi*‖freq‖) ht hc
  rw [show (2*s+1:ℂ)-1=2*s by ring,
    show (2*s+1:ℂ)-2=2*s-1 by ring,
    show ((2*s+1:ℂ)-1/3)/2=s+1/3 by ring,
    show ((2*s+1:ℂ)+1/3)/2=s+2/3 by ring,Complex.cpow_neg] at hh
  rw [hh]
  ring

end CubicEisenstein

open scoped BigOperators Classical

open scoped BigOperators Classical
namespace CubicEisenstein

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

theorem primeCubicGauss_trivial_nonzero (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1)
    (e:ℕ) (he:3∣e) (h:Eis) (hph:¬p∣h):
    primeCubicGauss p hp hprimary e h=-1:=by
  let:(Ideal.span {p}:Ideal Eis).IsMaximal:=
    PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  let:Field (Eis⧸Ideal.span {p}):=Ideal.Quotient.field _
  let:Fintype (Eis⧸Ideal.span {p}):=Fintype.ofFinite _
  have hh:Ideal.Quotient.mk (Ideal.span {p}) h≠0:=by
    intro hh
    exact hph (Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hh))
  rw [primeCubicGauss_eq_gaussSum,(primeCubicMulChar_pow_eq_one p hp hprimary e).mpr he]
  exact gaussSum_one_left (GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive p hp.ne_zero hh)

end CubicEisenstein

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.TranslatedFourierResidues
namespace OAI

noncomputable section

namespace CubicEisenstein

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

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

lemma brevePhase_hasDerivAt (freq z direction : ℂ) (t : ℝ) :
    HasDerivAt (fun x : ℝ => ShortDraftTrace.breveE (freq*(z+(x:ℂ)*direction)))
      (horizontalPhaseMultiplier freq direction*
        ShortDraftTrace.breveE (freq*(z+(t:ℂ)*direction))) t := by
  have hz : HasDerivAt (fun x : ℝ => freq*(z+(x:ℂ)*direction)) (freq*direction) t := by
    convert (preTransparency := .instances) (((Complex.ofRealCLM.hasDerivAt (x:=t)).mul_const direction).const_add z).const_mul freq using 1 <;>
      simp
  have he := ((hz.add hz.star).const_mul (2*Real.pi*Complex.I)).cexp
  change HasDerivAt (fun x : ℝ => Complex.exp ((2*Real.pi*Complex.I)*
    (freq*(z+(x:ℂ)*direction)+star (freq*(z+(x:ℂ)*direction)))))
    ((2*Real.pi*Complex.I)*(freq*direction+star (freq*direction))*
      Complex.exp ((2*Real.pi*Complex.I)*
        (freq*(z+(t:ℂ)*direction)+star (freq*(z+(t:ℂ)*direction))))) t
  simpa only [Pi.add_apply,mul_comm] using he

lemma horizontalPhaseMultiplier_norm (freq direction : ℂ) :
    ‖horizontalPhaseMultiplier freq direction‖≤4*Real.pi*‖freq‖*‖direction‖ := by
  have hc : ‖(2*Real.pi*Complex.I:ℂ)‖=2*Real.pi := by
    norm_num [norm_mul,abs_of_pos Real.pi_pos]
  unfold horizontalPhaseMultiplier
  rw [norm_mul,hc]
  calc
    _ ≤ (2*Real.pi)*(‖freq*direction‖+‖star (freq*direction)‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
    _ = _ := by rw [norm_star,norm_mul];ring

lemma summable_norm_mul_exp_neg_cuspFrequency (a : ℝ) (ha : 0<a) :
    Summable (fun h : ActualEisensteinCubic.O => ‖cuspFrequency h‖*Real.exp (-a*‖cuspFrequency h‖)) := by
  apply Summable.of_nonneg_of_le (fun h => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)
    (fun h => norm_mul_exp_neg_bound a _ ha)
  exact (summable_exp_neg_cuspFrequency_norm (a/2) (half_pos ha)).mul_left (2/a)

local notation "O" => ActualEisensteinCubic.O

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O

end CubicEisenstein

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.BesselDerivatives
namespace OAI

noncomputable section

namespace CubicEisenstein

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

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

lemma cubicBesselDensity_hasDerivAt (x t : ℝ) :
    HasDerivAt (fun y : ℝ => cubicBesselDensity y t) (cubicBesselDensityDeriv x t) x := by
  have he := ((((hasDerivAt_id x).pow 2).div_const (4*t)).const_sub (-t)).exp.const_mul (t^(-(2:ℝ)/3))
  simp only [Pi.pow_apply,id_eq,Nat.cast_ofNat,mul_one] at he
  convert (preTransparency := .instances) he using 1
  · funext y
    rfl
  · unfold cubicBesselDensityDeriv cubicBesselDensity
    ring

lemma cubic_exp_damping (y : ℝ) : y*Real.exp (-y)≤1 := by
  have hy : y≤Real.exp y := by linarith [Real.add_one_le_exp y]
  calc
    _ ≤ Real.exp y*Real.exp (-y) := mul_le_mul_of_nonneg_right hy (Real.exp_pos _).le
    _ = 1 := by rw [←Real.exp_add,add_neg_cancel,Real.exp_zero]

lemma cubicBesselDensityDeriv_bound (delta x t : ℝ)
    (hdelta : 0<delta) (hx : delta≤x) (ht : 0<t) :
    ‖cubicBesselDensityDeriv x t‖≤
      (4/delta)*Real.exp (-x/2)*(t^(-(2:ℝ)/3)*Real.exp (-t/2)) := by
  have hxp : 0<x := hdelta.trans_le hx
  have hdamp : (x/(2*t))*Real.exp (-(x^2/(8*t)))≤4/x := by
    have hrewrite : x/(2*t)=(4/x)*(x^2/(8*t)) := by field_simp;ring
    rw [hrewrite,mul_assoc]
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (cubic_exp_damping (x^2/(8*t))) (by positivity : 0≤4/x)
  have hyoung : x/2-t/2≤x^2/(8*t) :=
    (le_div_iff₀ (show 0<8*t by positivity)).mpr (by nlinarith [sq_nonneg (x-2*t)])
  have he : Real.exp (-t-x^2/(4*t))≤
      Real.exp (-x/2)*Real.exp (-t/2)*Real.exp (-(x^2/(8*t))) := by
    rw [←Real.exp_add,←Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hsplit : x^2/(4*t)=2*(x^2/(8*t)) := by ring
    rw [hsplit]
    linarith
  have hnorm : ‖cubicBesselDensityDeriv x t‖=
      (x/(2*t))*t^(-(2:ℝ)/3)*Real.exp (-t-x^2/(4*t)) := by
    unfold cubicBesselDensityDeriv cubicBesselDensity
    rw [norm_mul,norm_neg,Real.norm_of_nonneg (by positivity),
      Real.norm_of_nonneg (by positivity)]
    ring
  rw [hnorm]
  calc
    _ ≤ (x/(2*t))*t^(-(2:ℝ)/3)*
        (Real.exp (-x/2)*Real.exp (-t/2)*Real.exp (-(x^2/(8*t)))) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = ((x/(2*t))*Real.exp (-(x^2/(8*t))))*
        Real.exp (-x/2)*(t^(-(2:ℝ)/3)*Real.exp (-t/2)) := by ring
    _ ≤ (4/x)*Real.exp (-x/2)*(t^(-(2:ℝ)/3)*Real.exp (-t/2)) := by
      gcongr
    _ ≤ _ := by
      gcongr

lemma cubicBesselDerivativeMajorant_integrable :
    IntegrableOn (fun t : ℝ => t^(-(2:ℝ)/3)*Real.exp (-t/2)) (Set.Ioi 0) volume := by
  have hh := integrableOn_rpow_mul_exp_neg_mul_rpow (s:=-(2:ℝ)/3) (p:=1) (b:=1/2)
    (by norm_num) (by norm_num) (by norm_num)
  apply hh.congr
  filter_upwards with t
  rw [Real.rpow_one]
  congr 1
  congr 1
  ring

lemma cubicBesselDensityDeriv_integrable (x : ℝ) (hx : 0<x) :
    IntegrableOn (cubicBesselDensityDeriv x) (Set.Ioi 0) volume := by
  apply (cubicBesselDerivativeMajorant_integrable.const_mul ((4/x)*Real.exp (-x/2))).mono'
  · unfold cubicBesselDensityDeriv cubicBesselDensity
    fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact cubicBesselDensityDeriv_bound x x t hx le_rfl ht

lemma cubicBesselIntegral_hasDerivAt (x : ℝ) (hx : 0<x) :
    HasDerivAt (fun y : ℝ => ∫t in Set.Ioi (0:ℝ),cubicBesselDensity y t)
      (∫t in Set.Ioi (0:ℝ),cubicBesselDensityDeriv x t) x := by
  let delta := x/2
  have hdelta : 0<delta := half_pos hx
  have hU : Set.Ioi delta∈𝓝 x := isOpen_Ioi.mem_nhds (by
    change delta<x
    dsimp [delta]
    linarith)
  have hbound : ∀ᵐt ∂volume.restrict (Set.Ioi (0:ℝ)),∀y∈Set.Ioi delta,
      ‖cubicBesselDensityDeriv y t‖≤(4/delta)*(t^(-(2:ℝ)/3)*Real.exp (-t/2)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htp : 0<t := ht
    intro y hy
    have hyp : 0<y := hdelta.trans hy
    calc
      _ ≤ (4/delta)*Real.exp (-y/2)*(t^(-(2:ℝ)/3)*Real.exp (-t/2)) :=
        cubicBesselDensityDeriv_bound delta y t hdelta hy.le ht
      _ ≤ _ := by
        have he : Real.exp (-y/2)≤1 := Real.exp_le_one_iff.mpr (by linarith)
        calc
          _ ≤ (4/delta)*1*(t^(-(2:ℝ)/3)*Real.exp (-t/2)) := by gcongr
          _ = _ := by ring
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    («μ» := volume.restrict (Set.Ioi (0:ℝ)))
    (F := cubicBesselDensity) (F' := cubicBesselDensityDeriv)
    (bound := fun t => (4/delta)*(t^(-(2:ℝ)/3)*Real.exp (-t/2))) hU
    (Eventually.of_forall (fun y => by unfold cubicBesselDensity;fun_prop))
    (cubicBesselDensity_integrable x)
    (by unfold cubicBesselDensityDeriv cubicBesselDensity;fun_prop)
    hbound (cubicBesselDerivativeMajorant_integrable.const_mul (4/delta))
    (Eventually.of_forall (fun t y _ => cubicBesselDensity_hasDerivAt y t))
  exact h.2

lemma schlafliBesselK_cubic_hasDerivAt (x : ℝ) (hx : 0<x) :
    HasDerivAt (fun y : ℝ => schlafliBesselK (1/3) y)
      (schlafliBesselK_cubic_derivative x) x := by
  have hp : HasDerivAt (fun y : ℝ => (1/2:ℝ)*(y/2)^(-(1:ℝ)/3))
      ((-(1:ℝ)/12)*(x/2)^(-(4:ℝ)/3)) x := by
    have hh := (((hasDerivAt_id x).div_const 2).rpow_const
      (p:=-(1:ℝ)/3) (Or.inl (by positivity : x/2≠0))).const_mul (1/2:ℝ)
    convert (preTransparency := .instances) hh using 1 <;> norm_num ; ring
  have hr := hp.mul (cubicBesselIntegral_hasDerivAt x hx)
  have hreal : HasDerivAt (fun y : ℝ => (1/2:ℝ)*(y/2)^(-(1:ℝ)/3)*
      (∫t in Set.Ioi (0:ℝ),cubicBesselDensity y t)) (cubicBesselRealDeriv x) x := by
    exact hr
  apply hreal.ofReal_comp.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hx] with y hy
  exact schlafliBesselK_cubic_real y hy

lemma cubicBesselDerivativeMajorant_integral :
    (∫t in Set.Ioi (0:ℝ),t^(-(2:ℝ)/3)*Real.exp (-t/2))=
      (2:ℝ)^(1/3:ℝ)*Real.Gamma (1/3) := by
  have hh := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (1/3:ℝ)) (r := (1/2:ℝ)) (by norm_num) (by norm_num)
  convert (preTransparency := .instances) hh using 1 <;> norm_num ; congr 2 ; funext t ; ring_nf

lemma cubicBesselIntegral_norm_bound (x : ℝ) :
    ‖∫t in Set.Ioi (0:ℝ),cubicBesselDensity x t‖≤
      Real.exp (-x/2)*((2:ℝ)^(1/3:ℝ)*Real.Gamma (1/3)) := by
  have hpos : 0≤∫t in Set.Ioi (0:ℝ),cubicBesselDensity x t := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact cubicBesselDensity_nonneg x t ht.le
  rw [Real.norm_of_nonneg hpos]
  exact cubicBesselIntegral_upper x

lemma cubicBesselIntegralDeriv_norm_bound (delta x : ℝ) (hdelta : 0<delta) (hx : delta≤x) :
    ‖∫t in Set.Ioi (0:ℝ),cubicBesselDensityDeriv x t‖≤
      (4/delta)*Real.exp (-x/2)*((2:ℝ)^(1/3:ℝ)*Real.Gamma (1/3)) := by
  have hi := cubicBesselDensityDeriv_integrable x (hdelta.trans_le hx)
  have hb := integral_mono_ae hi.norm
    (cubicBesselDerivativeMajorant_integrable.const_mul ((4/delta)*Real.exp (-x/2)))
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact cubicBesselDensityDeriv_bound delta x t hdelta hx ht)
  rw [integral_const_mul,cubicBesselDerivativeMajorant_integral] at hb
  exact (norm_integral_le_integral_norm _).trans hb

lemma cubicBesselDerivativeUpper_nonneg (delta : ℝ) (hdelta : 0<delta) :
    0≤ cubicBesselDerivativeUpper delta := by
  unfold cubicBesselDerivativeUpper
  positivity

lemma schlafliBesselK_cubic_derivative_bound (delta x : ℝ) (hdelta : 0<delta) (hx : delta≤x) :
    ‖schlafliBesselK_cubic_derivative x‖≤ cubicBesselDerivativeUpper delta*Real.exp (-x/2) := by
  have hxp : 0<x := hdelta.trans_le hx
  have hp1 : (x/2)^(-(1:ℝ)/3)≤(delta/2)^(-(1:ℝ)/3) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)
  have hp4 : (x/2)^(-(4:ℝ)/3)≤(delta/2)^(-(4:ℝ)/3) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)
  rw [schlafliBesselK_cubic_derivative,Complex.norm_real,cubicBesselRealDeriv]
  calc
    _ ≤ ‖(-(1:ℝ)/12)*(x/2)^(-(4:ℝ)/3)*(∫t in Set.Ioi (0:ℝ),cubicBesselDensity x t)‖+
        ‖(1/2:ℝ)*(x/2)^(-(1:ℝ)/3)*(∫t in Set.Ioi (0:ℝ),cubicBesselDensityDeriv x t)‖ := norm_add_le _ _
    _ = (1/12:ℝ)*(x/2)^(-(4:ℝ)/3)*‖∫t in Set.Ioi (0:ℝ),cubicBesselDensity x t‖+
        (1/2:ℝ)*(x/2)^(-(1:ℝ)/3)*‖∫t in Set.Ioi (0:ℝ),cubicBesselDensityDeriv x t‖ := by
      have hn4 : ‖(x/2)^(-(4:ℝ)/3)‖=(x/2)^(-(4:ℝ)/3) :=
        Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _)
      have hn1 : ‖(x/2)^(-(1:ℝ)/3)‖=(x/2)^(-(1:ℝ)/3) :=
        Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _)
      simp only [norm_mul,hn4,hn1]
      norm_num
    _ ≤ (1/12:ℝ)*(delta/2)^(-(4:ℝ)/3)*
          (Real.exp (-x/2)*((2:ℝ)^(1/3:ℝ)*Real.Gamma (1/3)))+
        (1/2:ℝ)*(delta/2)^(-(1:ℝ)/3)*
          ((4/delta)*Real.exp (-x/2)*((2:ℝ)^(1/3:ℝ)*Real.Gamma (1/3))) := by
      gcongr
      · exact cubicBesselIntegral_norm_bound x
      · exact cubicBesselIntegralDeriv_norm_bound delta x hdelta hx
    _ = _ := by unfold cubicBesselDerivativeUpper;ring

end

section

open scoped BigOperators Classical
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

lemma primeCubicGauss_add_three (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1)
    (e:ℕ) (h:Eis):primeCubicGauss p hp hprimary (e+3) h=primeCubicGauss p hp hprimary e h:=by
  unfold primeCubicGauss
  rw [pow_add,primeCubicMulChar_cube,mul_one]

lemma cubicUnitGaussSum_prime_cube_shift_pos (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (n:ℕ) (h:Eis):
    cubicUnitGaussSum (h*p^3) (p^(n+4))=
      (Ideal.absNorm (Ideal.span {p}):ℂ)^3*cubicUnitGaussSum h (p^(n+1)):=by
  by_cases hd:p^n∣h
  · obtain ⟨r,rfl⟩:=hd
    have harg:p^n*r*p^3=p^(n+3)*r:=by rw [pow_add];ring
    rw [harg,show n+4=(n+3)+1 by omega,
      cubicUnitGaussSum_prime_power_lift p hp hprimary (n+3) r,
      cubicUnitGaussSum_prime_power_lift p hp hprimary n r]
    rw [show n+3+1=(n+1)+3 by omega,primeCubicGauss_add_three,pow_add]
    ring
  · have hlow:cubicUnitGaussSum h (p^(n+1))=0:=by
      by_contra hh
      exact hd (cubicUnitGaussSum_prime_power_support p hp hprimary n h hh)
    have hhigh:cubicUnitGaussSum (h*p^3) (p^(n+4))=0:=by
      by_contra hh
      have hh':cubicUnitGaussSum (h*p^3) (p^((n+3)+1))≠0:=by convert (preTransparency := .instances) hh using 1
      have hd':p^(n+3)∣h*p^3:=cubicUnitGaussSum_prime_power_support p hp hprimary (n+3) (h*p^3) hh'
      have hd'':p^3*p^n∣p^3*h:=by simpa only [pow_add,mul_comm,mul_left_comm,mul_assoc] using hd'
      exact hd ((mul_dvd_mul_iff_left (pow_ne_zero 3 hp.ne_zero)).mp hd'')
    rw [hhigh,hlow,mul_zero]

lemma cubicUnitGaussSum_prime_cube_shift (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (k:ℕ) (h:Eis):
    cubicUnitGaussSum (h*p^3) (p^(k+3))=
      (Ideal.absNorm (Ideal.span {p}):ℂ)^3*cubicUnitGaussSum h (p^k)-
        if k=0 then (Ideal.absNorm (Ideal.span {p}):ℂ)^2 else 0:=by
  cases k with
  | zero=>
    rw [Nat.zero_add,cubicUnitGaussSum_frequency_dvd _ _ (pow_ne_zero _ hp.ne_zero)
      (dvd_mul_left (p^3) h)]
    have he:=cubicUnitGaussSum_prime_power_zero p hp hprimary 2
    norm_num at he ⊢
    rw [he]
    ring
  | succ n=>
    simpa only [show n+1+3=n+4 by omega,Nat.succ_ne_zero,ite_false,sub_zero] using
      cubicUnitGaussSum_prime_cube_shift_pos p hp hprimary n h

private lemma primeExpansionTerm_cube_shift (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (s:ℂ) (h:Eis) (k:ℕ):
    primeExpansionTerm p s (h*p^3) (k+3)=
      (Ideal.absNorm (Ideal.span {p}):ℂ)^3*((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^3*
        primeExpansionTerm p s h k-
      if k=0 then (Ideal.absNorm (Ideal.span {p}):ℂ)^2*
        ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^3*unramifiedPrimeDeletedSeries p s h else 0:=by
  have hv:unramifiedPrimeDeletedSeries p s (h*p^3*p^(k+3))=
      unramifiedPrimeDeletedSeries p s (h*p^k):=by
    have he:h*p^3*p^(k+3)=(h*p^k*p^3)*p^3:=by rw [pow_add];ring
    rw [he,unramifiedPrimeDeletedSeries_cube_shift p hp,
      unramifiedPrimeDeletedSeries_cube_shift p hp]
  unfold primeExpansionTerm
  rw [cubicUnitGaussSum_prime_cube_shift p hp hprimary k h,hv,pow_add]
  split_ifs with hk
  · subst k
    simp only [pow_zero,mul_one,cubicUnitGaussSum_one]
    ring
  · ring

theorem unramifiedCubicGaussSeries_cube_step (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (s:ℂ) (hs:2<s.re) (h:Eis) (hph:¬p∣h) (a:ℕ):
    unramifiedCubicGaussSeries s (h*p^(a+3))=
      (1-(Ideal.absNorm (Ideal.span {p}):ℂ)^2*((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^3)*
        unramifiedPrimeDeletedSeries p s (h*p^a)+
      (Ideal.absNorm (Ideal.span {p}):ℂ)^3*((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^3*
        unramifiedCubicGaussSeries s (h*p^a):=by
  have he:=unramifiedCubicGaussSeries_prime_finite p hp hprimary s hs h hph (a+3)
  have hold:=unramifiedCubicGaussSeries_prime_finite p hp hprimary s hs h hph a
  change unramifiedCubicGaussSeries s (h*p^a)=
    ∑k∈Finset.range (a+2),primeExpansionTerm p s (h*p^a) k at hold
  have harg:h*p^(a+3)=(h*p^a)*p^3:=by rw [pow_add,mul_assoc]
  change unramifiedCubicGaussSeries s (h*p^(a+3))=
    ∑k∈Finset.range (a+3+2),primeExpansionTerm p s (h*p^(a+3)) k at he
  rw [show a+3+2=3+(a+2) by omega,Finset.sum_range_add,harg] at he
  have hsmall:∑k∈Finset.range 3,primeExpansionTerm p s (h*p^a*p^3) k=
      unramifiedPrimeDeletedSeries p s (h*p^a):=by
    have hg1:cubicUnitGaussSum (h*p^a*p^3) p=0:=by
      rw [cubicUnitGaussSum_frequency_dvd _ _ hp.ne_zero
        ((dvd_pow_self p (by decide:3≠0)).trans (dvd_mul_left (p^3) (h*p^a)))]
      simpa using cubicUnitGaussSum_prime_power_zero p hp hprimary 0
    have hg2:cubicUnitGaussSum (h*p^a*p^3) (p^2)=0:=by
      rw [cubicUnitGaussSum_frequency_dvd _ _ (pow_ne_zero _ hp.ne_zero)
        ((pow_dvd_pow p (by omega:2≤3)).trans (dvd_mul_left (p^3) (h*p^a)))]
      simpa using cubicUnitGaussSum_prime_power_zero p hp hprimary 1
    simp only [Finset.sum_range_succ,Finset.sum_range_zero,primeExpansionTerm,
      pow_zero,pow_one,cubicUnitGaussSum_one,mul_one,one_mul,zero_add,hg1,hg2,
      mul_zero,zero_mul,add_zero]
    rw [unramifiedPrimeDeletedSeries_cube_shift p hp]
  rw [hsmall] at he
  have htail:∑k∈Finset.range (a+2),primeExpansionTerm p s (h*p^a*p^3) (3+k)=
      (Ideal.absNorm (Ideal.span {p}):ℂ)^3*((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^3*
        unramifiedCubicGaussSeries s (h*p^a)-
      (Ideal.absNorm (Ideal.span {p}):ℂ)^2*((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^3*
        unramifiedPrimeDeletedSeries p s (h*p^a):=by
    simp_rw [show ∀k:ℕ,3+k=k+3 by omega,primeExpansionTerm_cube_shift p hp hprimary]
    rw [Finset.sum_sub_distrib,←Finset.mul_sum,←hold]
    simp
  rw [htail,←harg] at he
  exact he.trans (by ring)

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology ComplexConjugate

lemma inverseCuspPath_zero (c d : ℂ) (v : ℝ) (direction : ℂ)
    (hc : c≠0) (hv : 0<v) :
    inverseCuspPath c d v direction 0=(-d/c,1/(‖c‖^2*v)) := by
  unfold inverseCuspPath
  simp only [Complex.ofReal_zero,zero_pow (by decide : 2≠0),zero_mul,add_zero,zero_div,sub_zero]
  congr 1
  field_simp [norm_ne_zero_iff.mpr hc,hv.ne']

theorem inverseCuspPath_hasDerivAt (c d : ℂ) (v : ℝ) (direction : ℂ)
    (hc : c≠0) (hv : 0<v) :
    HasDerivAt (inverseCuspPath c d v direction)
      (-(star direction)/(c^2*(v:ℂ)^2),0) 0 := by
  have hn : ‖c‖≠0 := norm_ne_zero_iff.mpr hc
  have hvc : (v:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hv.ne'
  have hden : HasDerivAt (fun t : ℝ=>v^2+t^2*‖direction‖^2) 0 0 := by
    convert (preTransparency := .instances) (((hasDerivAt_id (0:ℝ)).pow 2).mul_const (‖direction‖^2)).const_add (v^2) using 1 <;> norm_num
  have hnum : HasDerivAt (fun t : ℝ=>(t:ℂ)*star direction) (star direction) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).ofReal_comp.mul_const (star direction))
  have hdenC := hden.ofReal_comp.const_mul (c^2)
  have hdenR := hden.const_mul (‖c‖^2)
  have hcz : c^2*((v^2+(0:ℝ)^2*‖direction‖^2:ℝ):ℂ)≠0 := by
    simpa using mul_ne_zero (pow_ne_zero 2 hc) (pow_ne_zero 2 hvc)
  have hrz : ‖c‖^2*(v^2+(0:ℝ)^2*‖direction‖^2)≠0 := by positivity
  have hz : HasDerivAt
      (fun t : ℝ=>-d/c-(t:ℂ)*star direction/(c^2*((v^2+t^2*‖direction‖^2:ℝ):ℂ)))
      (-(star direction)/(c^2*(v:ℂ)^2)) 0 := by
    convert (preTransparency := .instances) (hnum.div hdenC hcz).const_sub (-d/c) using 1 ;
      simp only [zero_pow (by decide : 2≠0),zero_mul,add_zero,Complex.ofReal_pow,
        Complex.ofReal_zero,mul_zero,sub_zero]
    field_simp

  have hvd : HasDerivAt (fun t : ℝ=>v/(‖c‖^2*(v^2+t^2*‖direction‖^2))) 0 0 := by
    convert (preTransparency := .instances) (hasDerivAt_const (0:ℝ) v).div hdenR hrz using 1 ; simp
  exact hz.prodMk hvd

theorem inverseCuspPath_comp_hasDerivAt (c d : ℂ) (v : ℝ) (direction : ℂ)
    (hc : c≠0) (hv : 0<v) (F : ℂ×ℝ→ℂ) (A : (ℂ×ℝ)→L[ℝ]ℂ)
    (hF : HasFDerivAt F A (-d/c,1/(‖c‖^2*v))) :
    HasDerivAt (fun t=>F (inverseCuspPath c d v direction t))
      (A (-(star direction)/(c^2*(v:ℂ)^2),0)) 0 := by
  have hf : HasFDerivAt F A (inverseCuspPath c d v direction 0) := by
    rwa [inverseCuspPath_zero c d v direction hc hv]
  exact hf.comp_hasDerivAt 0 (inverseCuspPath_hasDerivAt c d v direction hc hv)

end CubicEisenstein

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.InverseCuspCoordinates
namespace OAI

noncomputable section

namespace CubicEisenstein

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

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ComplexConjugate MatrixGroups Matrix

lemma inverseCuspCoordinates_line (c d : ℂ) (v : ℝ) (direction : ℂ) (t : ℝ) :
    inverseCuspCoordinates c d v ((t:ℂ)*direction)=inverseCuspPath c d v direction t := by
  simp only [inverseCuspCoordinates,inverseCuspPath,star_mul,Complex.star_def,
    Complex.conj_ofReal,norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs,mul_comm]

theorem inverse_cusp_action (g : SL(2,ℂ)) (hc : g 1 0≠0)
    (v : ℝ) (hv : 0<v) (z : ℂ) :
    g⁻¹ • upperPoint (z+g 0 0/g 1 0) v hv =
      upperPoint (inverseCuspCoordinates (g 1 0) (g 1 1) v z).1
        (inverseCuspCoordinates (g 1 0) (g 1 1) v z).2
        (inverseCuspCoordinates_height_pos _ _ _ _ hc hv) := by
  have hdet : g 0 0*g 1 1-g 0 1*g 1 0=1 := by
    simpa only [Matrix.det_fin_two] using g.property
  have h00 : (g⁻¹) 0 0=g 1 1 := by
    simp [Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two]
  have h01 : (g⁻¹) 0 1= -g 0 1 := by
    simp [Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two]
  have h10 : (g⁻¹) 1 0= -g 1 0 := by
    simp [Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two]
  have h11 : (g⁻¹) 1 1=g 0 0 := by
    simp [Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two]
  have hl : (-g 1 0)*(z+g 0 0/g 1 0)+g 0 0= -(g 1 0*z) := by
    field_simp
    ; ring
  have ht : g 1 1*(z+g 0 0/g 1 0)+(-g 0 1)=g 1 1*z+1/g 1 0 := by
    field_simp
    linear_combination hdet
  have hden : ‖-(g 1 0*z)‖^2+‖-g 1 0‖^2*v^2=
      ‖g 1 0‖^2*(v^2+‖z‖^2) := by rw [norm_neg,norm_neg,norm_mul,mul_pow];ring
  have hnormc : ((‖g 1 0‖^2:ℝ):ℂ)=g 1 0*star (g 1 0) := by
    simpa [Complex.normSq_eq_norm_sq,Complex.star_def] using (Complex.mul_conj (g 1 0)).symm
  have hnormz : ((‖z‖^2:ℝ):ℂ)=z*star z := by
    simpa [Complex.normSq_eq_norm_sq,Complex.star_def] using (Complex.mul_conj z).symm
  have hT : v^2+‖z‖^2≠0 := by positivity
  have hTc : ((v^2+‖z‖^2:ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr hT
  have hcc : star (g 1 0)≠0 := star_ne_zero.mpr hc
  rw [mobius_upperPoint]
  apply upperPoint_congr
  · rw [h00,h01,h10,h11,hl,ht,hden]
    dsimp [inverseCuspCoordinates]
    rw [Complex.ofReal_mul,hnormc]
    simp only [Complex.star_def,map_neg,map_mul]
    simp only [Complex.star_def] at hcc
    field_simp [hc,hcc,hTc]
    rw [Complex.ofReal_add,Complex.ofReal_pow,hnormz]
    simp only [Complex.star_def,]
    ; ring
  · rw [h10,h11,hl,hden]
    rfl

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ComplexConjugate

lemma real_linear_horizontal_decompose (A : (ℂ×ℝ)→L[ℝ]ℂ) (z : ℂ) :
    A (z,0)=(z.re:ℂ)*A (1,0)+(z.im:ℂ)*A (Complex.I,0) := by
  have hz : ((z,0):ℂ×ℝ)=z.re • (1,0)+z.im • (Complex.I,0) := by
    apply Prod.ext
    · simpa only [Prod.fst_add,Prod.smul_fst,Complex.real_smul,mul_one] using z.re_add_im.symm
    · simp
  rw [hz,map_add,map_smul,map_smul]
  simp only [Complex.real_smul]

lemma real_linear_wirtinger_swap (A : (ℂ×ℝ)→L[ℝ]ℂ) (k : ℂ) :
    (1/2:ℂ)*(A (k,0)+Complex.I*A (-Complex.I*k,0))=
      k*((1/2:ℂ)*(A (1,0)-Complex.I*A (Complex.I,0))) := by
  rw [real_linear_horizontal_decompose A k,real_linear_horizontal_decompose A (-Complex.I*k)]
  simp only [Complex.mul_re,Complex.mul_im,Complex.neg_re,Complex.neg_im,
    Complex.I_re,Complex.I_im,zero_mul,neg_mul,one_mul,
    zero_add,zero_sub,Complex.ofReal_neg]
  conv_rhs => lhs; rw [←k.re_add_im]
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem inverse_cusp_wirtingerBar (c d : ℂ) (v : ℝ) (hc : c≠0) (hv : 0<v)
    (F : ℂ×ℝ→ℂ) (A : (ℂ×ℝ)→L[ℝ]ℂ)
    (hF : HasFDerivAt F A (-d/c,1/(‖c‖^2*v))) :
    horizontalWirtingerBar (fun z=>F (inverseCuspCoordinates c d v z)) 0=
      (-1/(c^2*(v:ℂ)^2))*((1/2:ℂ)*(A (1,0)-Complex.I*A (Complex.I,0))) := by
  have h1 := (inverseCuspPath_comp_hasDerivAt c d v 1 hc hv F A hF).deriv
  have hI := (inverseCuspPath_comp_hasDerivAt c d v Complex.I hc hv F A hF).deriv
  have he1 : (fun t : ℝ=>F (inverseCuspCoordinates c d v (t:ℂ)))=
      (fun t : ℝ=>F (inverseCuspPath c d v 1 t)) := by
    funext t
    rw [←inverseCuspCoordinates_line]
    simp only [mul_one]
  have heI : (fun t : ℝ=>F (inverseCuspCoordinates c d v ((t:ℂ)*Complex.I)))=
      (fun t : ℝ=>F (inverseCuspPath c d v Complex.I t)) := by
    funext t
    rw [inverseCuspCoordinates_line]
  rw [horizontalWirtingerBar]
  simp only [zero_add]
  rw [he1,heI,h1,hI]
  simp only [star_one,Complex.star_def,Complex.conj_I,neg_neg]
  convert (preTransparency := .instances) real_linear_wirtinger_swap A (-1/(c^2*(v:ℂ)^2)) using 1 ;
    congr 2 ; ring_nf

lemma horizontalWirtingerZ_eq_fderiv (F : ℂ×ℝ→ℂ) (A : (ℂ×ℝ)→L[ℝ]ℂ)
    (z : ℂ) (v : ℝ) (hF : HasFDerivAt F A (z,v)) :
    horizontalWirtingerZ (fun w=>F (w,v)) z=
      (1/2:ℂ)*(A (1,0)-Complex.I*A (Complex.I,0)) := by
  have hline (direction : ℂ) :
      HasDerivAt (fun t : ℝ=>F (z+(t:ℂ)*direction,v)) (A (direction,0)) 0 := by
    have hz : HasDerivAt (fun t : ℝ=>z+(t:ℂ)*direction) direction 0 := by
      simpa using (((hasDerivAt_id (0:ℝ)).ofReal_comp.mul_const direction).const_add z)
    have hp := hz.prodMk (hasDerivAt_const (0:ℝ) v)
    have hf : HasFDerivAt F A (z+(0:ℂ)*direction,v) := by simpa using hF
    exact hf.comp_hasDerivAt 0 hp
  have h1 := (hline 1).deriv
  have hI := (hline Complex.I).deriv
  simp only [mul_one] at h1
  rw [horizontalWirtingerZ,h1,hI]

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology

section

theorem cusp_mellin_reflection (g : ℝ→ℂ) (A s : ℂ) (Q : ℝ) (hQ : 0<Q) :
    mellin (fun v : ℝ=>A*((v:ℂ)^(-2:ℂ)*g ((Q*v)⁻¹))) (2*s)=
      A*(Q:ℂ)^(2-2*s)*mellin g (2-2*s) := by
  have he : (fun v : ℝ=>A*((v:ℂ)^(-2:ℂ)*g ((Q*v)⁻¹)))=
      (fun v : ℝ=>A • ((v:ℂ)^(-2:ℂ) • g ((Q*v)⁻¹))) := by
    funext v; simp only [smul_eq_mul]
  rw [he,mellin_const_smul,mellin_cpow_smul]
  have hm := mellin_comp_mul_left (fun v : ℝ=>g v⁻¹) (2*s+(-2:ℂ)) hQ
  rw [mellin_comp_inv] at hm
  rw [hm]
  simp only [smul_eq_mul]
  rw [show -(2*s+(-2:ℂ))=2-2*s by ring]
  ring

theorem cusp_mellin_reflection_of_identity (f g : ℝ→ℂ) (A s : ℂ)
    (Q : ℝ) (hQ : 0<Q)
    (hfg : ∀v : ℝ,0<v→f v=A*((v:ℂ)^(-2:ℂ)*g ((Q*v)⁻¹))) :
    mellin f (2*s)=A*(Q:ℂ)^(2-2*s)*mellin g (2-2*s) := by
  rw [←cusp_mellin_reflection g A s Q hQ]
  unfold mellin
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  rw [hfg v hv]

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O

lemma horizontalPhaseCLM_apply (freq direction : ℂ) :
    horizontalPhaseCLM freq direction = horizontalPhaseMultiplier freq direction := by
  simp [horizontalPhaseCLM,horizontalPhaseMultiplier]
  ring

lemma brevePhase_hasFDerivAt (freq z : ℂ) :
    HasFDerivAt (fun w : ℂ => ShortDraftTrace.breveE (freq*w))
      (ShortDraftTrace.breveE (freq*z) • horizontalPhaseCLM freq) z := by
  have hh := (horizontalPhaseCLM freq).hasFDerivAt.cexp (x:=z)
  convert! (preTransparency := .instances) hh using 1

namespace SubexponentialBesselCoefficients
variable (coeff : SubexponentialBesselCoefficients)

lemma amplitude_hasDerivAt (v : ℝ) (hv : 0<v) (h : ActualEisensteinCubic.O) :
    HasDerivAt (fun y : ℝ => coeff.amplitude y h) (coeff.amplitudeDeriv v h) v := by
  by_cases hh : h=0
  · simp only [amplitude,amplitudeDeriv,if_pos hh]
    exact hasDerivAt_const v 0
  have hr : 0<‖cuspFrequency h‖ := norm_pos_iff.mpr (cuspFrequency_ne_zero h hh)
  have hslope : HasDerivAt (fun y : ℝ => 4*Real.pi*‖cuspFrequency h‖*y)
      (4*Real.pi*‖cuspFrequency h‖) v := by
    simpa only [id_eq,mul_one] using (hasDerivAt_id v).const_mul (4*Real.pi*‖cuspFrequency h‖)
  have hk := (schlafliBesselK_cubic_hasDerivAt (4*Real.pi*‖cuspFrequency h‖*v)
    (by positivity)).scomp v hslope
  have hvd := (Complex.ofRealCLM.hasDerivAt (x:=v)).mul hk
  have hfull := hvd.const_mul (coeff.value h)
  simp only [amplitude,amplitudeDeriv,if_neg hh]
  convert! (preTransparency := .instances) hfull using 1 <;> simp [Function.comp_def,Pi.mul_apply,Complex.ofRealCLM_apply,Complex.real_smul,mul_assoc]

lemma term_hasFDerivAt (h : ActualEisensteinCubic.O) (p : ℝ × ℂ) (hp : 0<p.1) :
    HasFDerivAt (coeff.term h) (coeff.termFDeriv h p) p := by
  by_cases hh : h=0
  · have hzero : coeff.term h=(fun _ : ℝ × ℂ => (0:ℂ)) := by
      funext q
      simp only [term,if_pos hh]
    rw [hzero,termFDeriv,if_pos hh]
    exact hasFDerivAt_const (𝕜:=ℝ) (0:ℂ) p
  have hvd := (coeff.amplitude_hasDerivAt p.1 hp h).hasFDerivAt.comp p
    (hasFDerivAt_fst (𝕜:=ℝ) (p:=p))
  have hzd := (brevePhase_hasFDerivAt (cuspFrequency h) p.2).comp p
    (hasFDerivAt_snd (𝕜:=ℝ) (p:=p))
  have hprod : HasFDerivAt (fun q : ℝ × ℂ => coeff.amplitude q.1 h*
      ShortDraftTrace.breveE (cuspFrequency h*q.2)) (coeff.termFDeriv h p) p := by
    convert! (preTransparency := .instances) hvd.mul hzd using 1
    apply ContinuousLinearMap.ext
    intro direction
    simp only [termFDeriv,if_neg hh]
    change (direction.1:ℂ)*(coeff.amplitudeDeriv p.1 h*
        ShortDraftTrace.breveE (cuspFrequency h*p.2))+
      coeff.term h p*horizontalPhaseCLM (cuspFrequency h) direction.2 =
      coeff.amplitude p.1 h*(ShortDraftTrace.breveE (cuspFrequency h*p.2)*
        horizontalPhaseCLM (cuspFrequency h) direction.2)+
      ShortDraftTrace.breveE (cuspFrequency h*p.2)*
        ((direction.1:ℂ)*coeff.amplitudeDeriv p.1 h)
    rw [coeff.term_eq_amplitude p.1 hp h p.2]
    ring
  apply hprod.congr_of_eventuallyEq
  filter_upwards [continuousAt_fst.tendsto.eventually (Ioi_mem_nhds hp)] with q hq
  exact coeff.term_eq_amplitude q.1 hq h q.2

end SubexponentialBesselCoefficients
end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

section
local notation "O" => ActualEisensteinCubic.O
namespace SubexponentialBesselCoefficients
variable (coeff : SubexponentialBesselCoefficients)

lemma weighted_bessel_bounds (a : ℝ) (ha : 0<a) :
    ∃A B : ℝ,0≤A ∧ 0≤B ∧ ∀(h : ActualEisensteinCubic.O),h≠0 → ∀v : ℝ,a≤v →
      ‖coeff.value h‖*‖schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)‖≤
        A*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖) ∧
      ‖coeff.value h‖*‖schlafliBesselK_cubic_derivative (4*Real.pi*‖cuspFrequency h‖*v)‖≤
        B*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖) := by
  have hd : 0<‖(3:ℂ)*ConcreteTraceCRT.eisLam‖ := norm_pos_iff.mpr
    (mul_ne_zero (by norm_num) ConcreteTraceCRT.eisLam_ne_zero)
  let delta : ℝ := 4*Real.pi*a*‖(3:ℂ)*ConcreteTraceCRT.eisLam‖⁻¹
  have hdelta : 0<delta := by dsimp [delta];positivity
  have hKu := (cubicBesselUpperAway_pos delta hdelta).le
  have hKd := cubicBesselDerivativeUpper_nonneg delta hdelta
  obtain ⟨C,hC,hcoeff⟩ := coeff.growth (Real.pi*a) (mul_pos Real.pi_pos ha)
  refine ⟨C*cubicBesselUpperAway delta,C*cubicBesselDerivativeUpper delta,
    mul_nonneg hC hKu,mul_nonneg hC hKd,?_⟩
  intro h hh v hv
  have hr : 0<‖cuspFrequency h‖ := norm_pos_iff.mpr (cuspFrequency_ne_zero h hh)
  have hx : delta≤4*Real.pi*‖cuspFrequency h‖*v := by
    have hmul := mul_le_mul (cuspFrequency_norm_lower h hh) hv ha.le (norm_nonneg _)
    dsimp [delta]
    nlinarith [mul_le_mul_of_nonneg_left hmul (by positivity : 0≤4*Real.pi)]
  have hcombine (y D : ℝ) (hy : 0≤y) (hD : 0≤D)
      (hbound : y≤D*Real.exp (-(4*Real.pi*‖cuspFrequency h‖*v)/2)) :
      ‖coeff.value h‖*y≤(C*D)*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖) := by
    calc
      _ ≤ (C*Real.exp ((Real.pi*a)*‖cuspFrequency h‖))*
          (D*Real.exp (-(4*Real.pi*‖cuspFrequency h‖*v)/2)) :=
        mul_le_mul (hcoeff h hh) hbound hy (by positivity)
      _ = (C*D)*Real.exp ((Real.pi*a)*‖cuspFrequency h‖-
          (4*Real.pi*‖cuspFrequency h‖*v)/2) := by
        rw [show (Real.pi*a)*‖cuspFrequency h‖-(4*Real.pi*‖cuspFrequency h‖*v)/2=
          (Real.pi*a)*‖cuspFrequency h‖+(-(4*Real.pi*‖cuspFrequency h‖*v)/2) by ring,
          Real.exp_add]
        ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC hD)
        apply Real.exp_le_exp.mpr
        nlinarith [mul_le_mul_of_nonneg_left hv (mul_pos Real.pi_pos hr).le]
  exact ⟨hcombine _ _ (norm_nonneg _) hKu
    (schlafliBesselK_cubic_upper_away delta _ hdelta hx),
    hcombine _ _ (norm_nonneg _) hKd
    (schlafliBesselK_cubic_derivative_bound delta _ hdelta hx)⟩

lemma amplitudeDeriv_norm_le (v : ℝ) (hv : 0<v) (h : ActualEisensteinCubic.O) (hh : h≠0) :
    ‖coeff.amplitudeDeriv v h‖≤
      ‖coeff.value h‖*‖schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)‖+
      (v*(4*Real.pi*‖cuspFrequency h‖))*
        (‖coeff.value h‖*‖schlafliBesselK_cubic_derivative (4*Real.pi*‖cuspFrequency h‖*v)‖) := by
  rw [amplitudeDeriv,if_neg hh,norm_mul]
  calc
    _ ≤ ‖coeff.value h‖*(‖schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)‖+
      ‖(v:ℂ)*(4*Real.pi*‖cuspFrequency h‖:ℝ)*
        schlafliBesselK_cubic_derivative (4*Real.pi*‖cuspFrequency h‖*v)‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)
    _ = _ := by
      rw [norm_mul,norm_mul,Complex.norm_of_nonneg hv.le,
        Complex.norm_of_nonneg (by positivity : 0≤4*Real.pi*‖cuspFrequency h‖)]
      ring

lemma termFDeriv_norm_le (h : ActualEisensteinCubic.O) (p : ℝ × ℂ) :
    ‖coeff.termFDeriv h p‖≤‖coeff.amplitudeDeriv p.1 h‖+
      ‖coeff.term h p‖*(4*Real.pi*‖cuspFrequency h‖) := by
  by_cases hh : h=0
  · simp only [termFDeriv,if_pos hh,norm_zero]
    positivity
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro direction
  simp only [termFDeriv,if_neg hh]
  change ‖(direction.1:ℂ)*(coeff.amplitudeDeriv p.1 h*
      ShortDraftTrace.breveE (cuspFrequency h*p.2))+
    coeff.term h p*horizontalPhaseCLM (cuspFrequency h) direction.2‖≤_
  calc
    _ ≤ ‖(direction.1:ℂ)*(coeff.amplitudeDeriv p.1 h*
        ShortDraftTrace.breveE (cuspFrequency h*p.2))‖+
      ‖coeff.term h p*horizontalPhaseCLM (cuspFrequency h) direction.2‖ := norm_add_le _ _
    _ = ‖direction.1‖*‖coeff.amplitudeDeriv p.1 h‖+
        ‖coeff.term h p‖*‖horizontalPhaseMultiplier (cuspFrequency h) direction.2‖ := by
      rw [norm_mul,norm_mul,Complex.norm_real,breveE_norm,mul_one,norm_mul,
        horizontalPhaseCLM_apply]
    _ ≤ ‖direction‖*‖coeff.amplitudeDeriv p.1 h‖+
        ‖coeff.term h p‖*((4*Real.pi*‖cuspFrequency h‖)*‖direction‖) := by
      gcongr
      · exact norm_fst_le direction
      · exact (horizontalPhaseMultiplier_norm _ _).trans (by
          gcongr
          exact norm_snd_le direction)
    _ = _ := by ring

lemma termFDeriv_slab_bound (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    ∃C : ℝ,0≤C ∧ ∀(h : ActualEisensteinCubic.O)(p : ℝ × ℂ),p.1∈Set.Icc a b →
      ‖coeff.termFDeriv h p‖≤C*((1+‖cuspFrequency h‖)*
        Real.exp (-(Real.pi*a)*‖cuspFrequency h‖)) := by
  obtain ⟨A,B,hA,hB,hweighted⟩ := coeff.weighted_bessel_bounds a ha
  obtain ⟨T,hT,hterm⟩ := coeff.slab_bound a b ha hab
  let D := B*b*(4*Real.pi)+T*(4*Real.pi)
  have hb : 0<b := ha.trans_le hab
  have hD : 0≤D := by dsimp [D];positivity
  refine ⟨A+D,add_nonneg hA hD,?_⟩
  intro h p hp
  by_cases hh : h=0
  · simp only [termFDeriv,if_pos hh,norm_zero]
    positivity
  have hv : 0<p.1 := ha.trans_le hp.1
  obtain ⟨hKu,hKd⟩ := hweighted h hh p.1 hp.1
  have hamp : ‖coeff.amplitudeDeriv p.1 h‖≤
      A*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖)+
      (b*(4*Real.pi*‖cuspFrequency h‖))*
        (B*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖)) := by
    apply (coeff.amplitudeDeriv_norm_le p.1 hv h hh).trans
    gcongr
    exact hp.2
  calc
    _ ≤ ‖coeff.amplitudeDeriv p.1 h‖+
        ‖coeff.term h p‖*(4*Real.pi*‖cuspFrequency h‖) := coeff.termFDeriv_norm_le h p
    _ ≤ (A*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖)+
        (b*(4*Real.pi*‖cuspFrequency h‖))*(B*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖)))+
        (T*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖))*(4*Real.pi*‖cuspFrequency h‖) := by
      gcongr
      exact hterm h p hp
    _ = (A+D*‖cuspFrequency h‖)*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖) := by
      dsimp [D]
      ring
    _ ≤ _ := by
      rw [←mul_assoc]
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      nlinarith [mul_nonneg hA (norm_nonneg (cuspFrequency h))]

end SubexponentialBesselCoefficients
end

local notation "O" => ActualEisensteinCubic.O

lemma summable_one_add_norm_exp_neg_cuspFrequency (a : ℝ) (ha : 0<a) :
    Summable (fun h : ActualEisensteinCubic.O => (1+‖cuspFrequency h‖)*Real.exp (-a*‖cuspFrequency h‖)) := by
  simpa only [add_mul,one_mul] using
    (summable_exp_neg_cuspFrequency_norm a ha).add (summable_norm_mul_exp_neg_cuspFrequency a ha)

namespace SubexponentialBesselCoefficients
variable (coeff : SubexponentialBesselCoefficients)

lemma series_hasFDerivAt (p : ℝ × ℂ) (hp : 0<p.1) :
    HasFDerivAt coeff.series (∑'h : ActualEisensteinCubic.O,coeff.termFDeriv h p) p := by
  let a := p.1/2
  let b := 2*p.1
  have ha : 0<a := by dsimp [a];linarith
  have hab : a≤b := by dsimp [a,b];linarith
  have hap : a<p.1 := by dsimp [a];linarith
  have hpb : p.1<b := by dsimp [b];linarith
  obtain ⟨C,hC,hbound⟩ := coeff.termFDeriv_slab_bound a b ha hab
  have hsum := (summable_one_add_norm_exp_neg_cuspFrequency (Real.pi*a)
    (mul_pos Real.pi_pos ha)).mul_left C
  let slab : Set (ℝ × ℂ) := Set.Ioo a b ×ˢ Set.univ
  have hslab : IsOpen slab := isOpen_Ioo.prod isOpen_univ
  have hconn : IsPreconnected slab := isPreconnected_Ioo.prod isPreconnected_univ
  have hpSlab : p∈slab := ⟨⟨hap,hpb⟩,Set.mem_univ _⟩
  exact hasFDerivAt_tsum_of_isPreconnected hsum hslab hconn
    (fun h q hq => coeff.term_hasFDerivAt h q (ha.trans hq.1.1))
    (fun h q hq => hbound h q ⟨hq.1.1.le,hq.1.2.le⟩)
    hpSlab (coeff.summable p hp) hpSlab

lemma series_differentiableAt (p : ℝ × ℂ) (hp : 0<p.1) :
    DifferentiableAt ℝ coeff.series p := (coeff.series_hasFDerivAt p hp).differentiableAt

lemma fullFunction_cusp_eq (constant : ℂ) (p : ℝ × ℂ) (hp : 0<p.1) :
    coeff.fullFunction constant (cuspCoordinateLift p)=
      constant*(p.1:ℂ)^(2/3:ℂ)+coeff.series p := by
  rw [show p=(p.1,p.2) from rfl,cuspCoordinateLift_positive p.1 p.2 hp]
  simp only [fullFunction,function,hyperbolicHeight_upperPoint,hyperbolicHorizontal_upperPoint]

lemma fullFunction_cusp_differentiableAt (constant : ℂ) (p : ℝ × ℂ) (hp : 0<p.1) :
    DifferentiableAt ℝ (fun q : ℝ × ℂ => coeff.fullFunction constant (cuspCoordinateLift q)) p := by
  have hc := ((hasDerivAt_ofReal_cpow_const hp.ne' (r:=(2/3:ℂ))
    (by norm_num)).const_mul constant).differentiableAt.comp p
      (differentiableAt_fst (𝕜:=ℝ) (p:=p))
  have ht : DifferentiableAt ℝ (fun q : ℝ × ℂ =>
      constant*(q.1:ℂ)^(2/3:ℂ)+coeff.series q) p := by
    convert! (preTransparency := .instances) hc.add (coeff.series_differentiableAt p hp) using 1
  apply ht.congr_of_eventuallyEq
  filter_upwards [continuousAt_fst.tendsto.eventually (Ioi_mem_nhds hp)] with q hq
  exact coeff.fullFunction_cusp_eq constant q hq

end SubexponentialBesselCoefficients
end

open Filter MeasureTheory Asymptotics
open scoped BigOperators Classical Topology

lemma truncatedCuspProfile_eventually_top (c : ℝ) (f : ℝ→ℂ) :
    truncatedCuspProfile c f =ᶠ[atTop] f := by
  filter_upwards [eventually_gt_atTop c] with x hx
  simp only [truncatedCuspProfile,if_pos hx]

lemma truncatedCuspProfile_eventually_zero (c : ℝ) (hc : 0<c) (f : ℝ→ℂ) :
    truncatedCuspProfile c f =ᶠ[𝓝[>] 0] 0 := by
  have he : ∀ᶠx : ℝ in 𝓝[>] 0,x<c := (eventually_lt_nhds hc).filter_mono nhdsWithin_le_nhds
  filter_upwards [he] with x hx
  simp only [truncatedCuspProfile,if_neg (not_lt_of_ge hx.le),Pi.zero_apply]

lemma truncatedCuspProfile_locallyIntegrable (c : ℝ) (hc : 0<c) (f : ℝ→ℂ)
    (hf : ContinuousOn f (Set.Ioi 0)) :
    LocallyIntegrable (truncatedCuspProfile c f) volume := by
  have hcont : Continuous (fun x : ℝ=>f (max (c/2) x)) :=
    hf.comp_continuous (continuous_const.max continuous_id)
      (fun x=>lt_of_lt_of_le (by linarith : 0<c/2) (le_max_left _ _))
  have he : truncatedCuspProfile c f=
      (Set.Ioi c).indicator (fun x : ℝ=>f (max (c/2) x)) := by
    funext x
    by_cases hx : c<x
    · have hm : max (c/2) x=x := max_eq_right (by linarith)
      simp [truncatedCuspProfile,Set.indicator,hx,hm]
    · simp [truncatedCuspProfile,Set.indicator,hx]
  rw [he]
  exact hcont.locallyIntegrable.indicator measurableSet_Ioi

theorem truncatedCuspProfile_mellin_entire (c decay : ℝ) (hc : 0<c) (hdecay : 0<decay)
    (f : ℝ→ℂ) (hf : ContinuousOn f (Set.Ioi 0))
    (hbound : f =O[atTop] (fun x : ℝ=>Real.exp (-decay*x))) :
    (∀s : ℂ,MellinConvergent (truncatedCuspProfile c f) s) ∧
      Differentiable ℂ (mellin (truncatedCuspProfile c f)) := by
  have hlocal := (truncatedCuspProfile_locallyIntegrable c hc f hf).locallyIntegrableOn (Set.Ioi 0)
  have htop : truncatedCuspProfile c f =O[atTop] (fun x : ℝ=>Real.exp (-decay*x)) :=
    hbound.congr' (truncatedCuspProfile_eventually_top c f).symm Filter.EventuallyEq.rfl
  have hzero (b : ℝ) : truncatedCuspProfile c f =O[𝓝[>] 0] (fun x : ℝ=>x^(-b)) :=
    (Asymptotics.isBigO_zero (fun x : ℝ=>x^(-b)) (𝓝[>] 0)).congr'
      (truncatedCuspProfile_eventually_zero c hc f).symm Filter.EventuallyEq.rfl
  constructor
  · intro s
    exact mellinConvergent_of_isBigO_rpow_exp hdecay hlocal htop (hzero (s.re-1)) (by linarith)
  · intro s
    exact mellin_differentiableAt_of_isBigO_rpow_exp hdecay hlocal htop (hzero (s.re-1)) (by linarith)

end CubicEisenstein

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.ReflectedCuspMellin
namespace OAI

noncomputable section

namespace CubicEisenstein

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

section
open Filter MeasureTheory Asymptotics
open scoped BigOperators Classical Topology

lemma reflectedCuspProfile_mellin (g : ℝ→ℂ) (A s : ℂ) (Q : ℝ) (hQ : 0<Q) :
    mellin (reflectedCuspProfile A Q g) s=
      A*(Q:ℂ)^(2-s)*mellin g (2-s) := by
  unfold reflectedCuspProfile
  have hh := cusp_mellin_reflection g A (s/2) Q hQ
  simpa only [show (2*(s/2):ℂ)=s by ring,reflectedCuspProfile] using hh

lemma reflectedCuspProfile_mellinConvergent (g : ℝ→ℂ) (A s : ℂ) (Q : ℝ)
    (hQ : 0<Q) (hg : MellinConvergent g (2-s)) :
    MellinConvergent (reflectedCuspProfile A Q g) s := by
  unfold reflectedCuspProfile
  have hinv : MellinConvergent (fun t : ℝ=>g t⁻¹) (s-2) := by
    have hh := (MellinConvergent.comp_rpow (f := g) (s := s-2)
      (a := -1) (by norm_num : (-1:ℝ)≠0)).mpr
        (show MellinConvergent g ((s-2)/(-1:ℝ)) by
          simpa only [show ((s-2)/(-1:ℝ):ℂ)=2-s by push_cast;ring] using hg)
    simpa only [Real.rpow_neg_one] using hh
  have hscale := (MellinConvergent.comp_mul_left (f := fun t : ℝ=>g t⁻¹)
    (s := s-2) hQ).mpr hinv
  have hpow := (MellinConvergent.cpow_smul (f := fun t : ℝ=>g (Q*t)⁻¹)
    (s := s) (a := -2)).mpr (by simpa only [sub_eq_add_neg] using hscale)
  simpa only [reflectedCuspProfile,smul_eq_mul] using hpow.const_smul A

lemma cusp_truncation_reflection_ae (f g : ℝ→ℂ) (A : ℂ) (Q : ℝ) (hQ : 0<Q)
    (hfg : ∀v : ℝ,0<v→f v=reflectedCuspProfile A Q g v) :
    f =ᵐ[volume.restrict (Set.Ioi 0)]
      (fun v=>truncatedCuspProfile 1 f v+
        reflectedCuspProfile A Q (truncatedCuspProfile (1/Q) g) v) := by
  have hne : ∀ᵐv : ℝ ∂volume.restrict (Set.Ioi 0),v≠1 :=
    ae_restrict_of_ae (Measure.ae_ne volume 1)
  filter_upwards [ae_restrict_mem measurableSet_Ioi,hne] with v hv hv1
  have hrel : 1/Q<(Q*v)⁻¹ ↔ v<1 := by
    rw [inv_eq_one_div,div_lt_div_iff₀ hQ (mul_pos hQ hv)]
    constructor <;> intro hh <;> nlinarith
  by_cases hhi : 1<v
  · have hlo : ¬1/Q<(Q*v)⁻¹ := fun hh=>not_lt_of_ge hhi.le (hrel.mp hh)
    simp only [truncatedCuspProfile,if_pos hhi,reflectedCuspProfile,if_neg hlo,
      mul_zero,add_zero]
  · have hlo : 1/Q<(Q*v)⁻¹ := hrel.mpr (lt_of_le_of_ne (le_of_not_gt hhi) hv1)
    simp only [truncatedCuspProfile,if_neg hhi,reflectedCuspProfile,if_pos hlo,zero_add]
    exact hfg v hv

theorem cusp_mellin_entire (f g : ℝ→ℂ) (A : ℂ) (Q decayF decayG : ℝ)
    (hQ : 0<Q) (hdecayF : 0<decayF) (hdecayG : 0<decayG)
    (hf : ContinuousOn f (Set.Ioi 0)) (hg : ContinuousOn g (Set.Ioi 0))
    (hfbound : f =O[atTop] (fun v : ℝ=>Real.exp (-decayF*v)))
    (hgbound : g =O[atTop] (fun v : ℝ=>Real.exp (-decayG*v)))
    (hfg : ∀v : ℝ,0<v→f v=reflectedCuspProfile A Q g v) :
    (∀s : ℂ,MellinConvergent f s) ∧ Differentiable ℂ (mellin f) := by
  obtain ⟨hfc,hfd⟩ := truncatedCuspProfile_mellin_entire 1 decayF (by norm_num) hdecayF f hf hfbound
  obtain ⟨hgc,hgd⟩ := truncatedCuspProfile_mellin_entire (1/Q) decayG
    (by positivity) hdecayG g hg hgbound
  have hae := cusp_truncation_reflection_ae f g A Q hQ hfg
  have hresult (s : ℂ) : HasMellin f s
      (mellin (truncatedCuspProfile 1 f) s+
        A*(Q:ℂ)^(2-s)*mellin (truncatedCuspProfile (1/Q) g) (2-s)) := by
    have hr := reflectedCuspProfile_mellinConvergent
      (truncatedCuspProfile (1/Q) g) A s Q hQ (hgc (2-s))
    have hsum := hasMellin_add (hfc s) hr
    constructor
    · apply hsum.1.congr
      filter_upwards [hae] with v hv
      exact congrArg (fun z : ℂ=>(v:ℂ)^(s-1) • z) hv.symm
    · have he : mellin f s=mellin (fun v=>truncatedCuspProfile 1 f v+
          reflectedCuspProfile A Q (truncatedCuspProfile (1/Q) g) v) s := by
        unfold mellin
        apply integral_congr_ae
        filter_upwards [hae] with v hv
        rw [hv]
      rw [he,hsum.2,reflectedCuspProfile_mellin _ _ _ _ hQ]
  refine ⟨fun s=>(hresult s).1,?_⟩
  have he : mellin f=(fun s : ℂ=>mellin (truncatedCuspProfile 1 f) s+
      A*(Q:ℂ)^(2-s)*mellin (truncatedCuspProfile (1/Q) g) (2-s)) :=
    funext (fun s=>(hresult s).2)
  rw [he]
  let : NeZero (Q:ℂ) := ⟨Complex.ofReal_ne_zero.mpr hQ.ne'⟩
  have hp := (differentiable_const_cpow_of_neZero (Q:ℂ)).comp
    ((differentiable_const (2:ℂ)).sub differentiable_id)
  exact hfd.add (((differentiable_const A).mul hp).mul
    (hgd.comp ((differentiable_const (2:ℂ)).sub differentiable_id)))

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

section
local notation "O" => ActualEisensteinCubic.O
namespace SubexponentialBesselCoefficients
variable (coeff : SubexponentialBesselCoefficients)

lemma term_horizontal_hasDerivAt (h : ActualEisensteinCubic.O) (v : ℝ) (hv : 0<v)
    (z direction : ℂ) (t : ℝ) :
    HasDerivAt (fun x : ℝ => coeff.term h (v,z+(x:ℂ)*direction))
      (coeff.directionalTerm h v (z+(t:ℂ)*direction) direction) t := by
  have hh := (brevePhase_hasDerivAt (cuspFrequency h) z direction t).const_mul
    (coeff.amplitude v h)
  have hf : (fun x : ℝ => coeff.term h (v,z+(x:ℂ)*direction))=
      (fun x : ℝ => coeff.amplitude v h*
        ShortDraftTrace.breveE (cuspFrequency h*(z+(x:ℂ)*direction))) := by
    funext x
    exact coeff.term_eq_amplitude v hv h _
  rw [hf]
  convert (preTransparency := .instances) hh using 1
  rw [directionalTerm,coeff.term_eq_amplitude v hv h]
  ring

lemma directionalTerm_slab_bound (a b : ℝ) (ha : 0<a) (hab : a≤b)
    (direction : ℂ) :
    ∃C : ℝ,0≤C ∧ ∀(h : ActualEisensteinCubic.O)(v : ℝ)(z : ℂ),v∈Set.Icc a b →
      ‖coeff.directionalTerm h v z direction‖≤
        C*(‖cuspFrequency h‖*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖)) := by
  obtain ⟨C,hC,hbound⟩ := coeff.slab_bound a b ha hab
  refine ⟨4*Real.pi*‖direction‖*C,by positivity,?_⟩
  intro h v z hv
  rw [directionalTerm,norm_mul]
  calc
    _ ≤ (4*Real.pi*‖cuspFrequency h‖*‖direction‖)*
        (C*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖)) :=
      mul_le_mul (horizontalPhaseMultiplier_norm _ _) (hbound h (v,z) hv)
        (norm_nonneg _) (by positivity)
    _ = _ := by ring

lemma directionalTerm_summable (v : ℝ) (hv : 0<v) (z direction : ℂ) :
    Summable (fun h : ActualEisensteinCubic.O => coeff.directionalTerm h v z direction) := by
  obtain ⟨C,hC,hbound⟩ := coeff.directionalTerm_slab_bound v v hv le_rfl direction
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun h => norm_nonneg _) (fun h => hbound h v z ⟨le_rfl,le_rfl⟩)
  exact (summable_norm_mul_exp_neg_cuspFrequency (Real.pi*v) (mul_pos Real.pi_pos hv)).mul_left C

lemma series_horizontal_hasDerivAt (v : ℝ) (hv : 0<v)
    (z direction : ℂ) (t : ℝ) :
    HasDerivAt (fun x : ℝ => coeff.series (v,z+(x:ℂ)*direction))
      (∑'h : ActualEisensteinCubic.O,coeff.directionalTerm h v (z+(t:ℂ)*direction) direction) t := by
  obtain ⟨C,hC,hbound⟩ := coeff.directionalTerm_slab_bound v v hv le_rfl direction
  have hs := (summable_norm_mul_exp_neg_cuspFrequency (Real.pi*v) (mul_pos Real.pi_pos hv)).mul_left C
  have hz : Summable (fun h : ActualEisensteinCubic.O => coeff.term h (v,z+(0:ℂ)*direction)) := by
    simpa only [zero_mul,add_zero] using coeff.summable (v,z) hv
  exact hasDerivAt_tsum hs (fun h x => coeff.term_horizontal_hasDerivAt h v hv z direction x)
    (fun h x => hbound h v (z+(x:ℂ)*direction) ⟨le_rfl,le_rfl⟩) hz t

lemma fullFunction_horizontal_hasDerivAt (constant : ℂ) (v : ℝ) (hv : 0<v)
    (z direction : ℂ) (t : ℝ) :
    HasDerivAt (fun x : ℝ => coeff.fullFunction constant (upperPoint (z+(x:ℂ)*direction) v hv))
      (∑'h : ActualEisensteinCubic.O,coeff.directionalTerm h v (z+(t:ℂ)*direction) direction) t := by
  have hh := (coeff.series_horizontal_hasDerivAt v hv z direction t).const_add
    (constant*(v:ℂ)^(2/3:ℂ))
  simpa only [fullFunction,function,
    hyperbolicHeight_upperPoint,hyperbolicHorizontal_upperPoint] using hh

end SubexponentialBesselCoefficients
end

local notation "O" => ActualEisensteinCubic.O
namespace SubexponentialBesselCoefficients
variable (coeff : SubexponentialBesselCoefficients)

lemma directionalTerm_cusp_majorant (a : ℝ) (ha : 0<a) (direction : ℂ) :
    ∃D : ℝ,0≤D ∧ ∀(h : ActualEisensteinCubic.O)(v : ℝ)(z : ℂ),a≤v →
      ‖coeff.directionalTerm h v z direction‖≤
        (D*v*Real.exp (-(2*residualCuspDecayRate)*v))*
          (‖cuspFrequency h‖*Real.exp (-(Real.pi*a/2)*‖cuspFrequency h‖)) := by
  obtain ⟨C,hC,hbound⟩ := coeff.term_cusp_bound a ha
  refine ⟨4*Real.pi*‖direction‖*C,by positivity,?_⟩
  intro h v z hav
  have hv : 0<v := ha.trans_le hav
  by_cases hh : h=0
  · subst h
    simp only [directionalTerm,term,ite_true,mul_zero,norm_zero]
    positivity
  have hr : 0<‖cuspFrequency h‖ := norm_pos_iff.mpr (cuspFrequency_ne_zero h hh)
  have he : Real.exp (-(Real.pi*v)*‖cuspFrequency h‖)≤
      Real.exp (-(2*residualCuspDecayRate)*v)*Real.exp (-(Real.pi*a/2)*‖cuspFrequency h‖) := by
    rw [←Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h1 := mul_le_mul_of_nonneg_left (cuspFrequency_norm_lower h hh)
      (show 0≤Real.pi*v/2 by positivity)
    have h2 := mul_le_mul_of_nonneg_left hav (show 0≤Real.pi*‖cuspFrequency h‖/2 by positivity)
    unfold residualCuspDecayRate
    nlinarith
  rw [directionalTerm,norm_mul]
  calc
    _ ≤ (4*Real.pi*‖cuspFrequency h‖*‖direction‖)*
        (C*v*Real.exp (-(Real.pi*v)*‖cuspFrequency h‖)) :=
      mul_le_mul (horizontalPhaseMultiplier_norm _ _) (hbound h v z hav)
        (norm_nonneg _) (by positivity)
    _ ≤ (4*Real.pi*‖cuspFrequency h‖*‖direction‖)*
        (C*v*(Real.exp (-(2*residualCuspDecayRate)*v)*
          Real.exp (-(Real.pi*a/2)*‖cuspFrequency h‖))) := by
      gcongr
    _ = _ := by ring

lemma directionalSeries_cusp_decay (a : ℝ) (ha : 0<a) (direction : ℂ) :
    ∃C : ℝ,0≤C ∧ ∀(v : ℝ)(z : ℂ),a≤v →
      ‖∑'h : ActualEisensteinCubic.O,coeff.directionalTerm h v z direction‖≤
        C*Real.exp (-residualCuspDecayRate*v) := by
  obtain ⟨D,hD,hbound⟩ := coeff.directionalTerm_cusp_majorant a ha direction
  have hc := residualCuspDecayRate_pos
  let S : ℝ := ∑'h : ActualEisensteinCubic.O,‖cuspFrequency h‖*Real.exp (-(Real.pi*a/2)*‖cuspFrequency h‖)
  have hS : 0≤S := tsum_nonneg (fun h => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)
  have hs := summable_norm_mul_exp_neg_cuspFrequency (Real.pi*a/2) (by positivity)
  refine ⟨D*S*(2/(2*residualCuspDecayRate)),by positivity,?_⟩
  intro v z hav
  have hsum := tsum_of_norm_bounded
    (hs.hasSum.mul_left (D*v*Real.exp (-(2*residualCuspDecayRate)*v)))
    (fun h => hbound h v z hav)
  calc
    _ ≤ (D*v*Real.exp (-(2*residualCuspDecayRate)*v))*S := hsum
    _ = (D*S)*(v*Real.exp (-(2*residualCuspDecayRate)*v)) := by ring
    _ ≤ (D*S)*((2/(2*residualCuspDecayRate))*
        Real.exp (-((2*residualCuspDecayRate)/2)*v)) :=
      mul_le_mul_of_nonneg_left (norm_mul_exp_neg_bound (2*residualCuspDecayRate) v
        (mul_pos (by norm_num) residualCuspDecayRate_pos)) (mul_nonneg hD hS)
    _ = _ := by
      rw [show -((2*residualCuspDecayRate)/2)*v=-residualCuspDecayRate*v by ring]
      ring

theorem fullFunction_wirtingerBar_cusp_decay (constant : ℂ) (a : ℝ) (ha : 0<a) :
    ∃C : ℝ,0≤C ∧ ∀(v : ℝ)(hv : 0<v)(z : ℂ),a≤v →
      ‖horizontalWirtingerBar (fun w => coeff.fullFunction constant (upperPoint w v hv)) z‖≤
        C*Real.exp (-residualCuspDecayRate*v) := by
  obtain ⟨C1,hC1,hbound1⟩ := coeff.directionalSeries_cusp_decay a ha 1
  obtain ⟨CI,hCI,hboundI⟩ := coeff.directionalSeries_cusp_decay a ha Complex.I
  refine ⟨(C1+CI)/2,by positivity,?_⟩
  intro v hv z hav
  have h1 := (coeff.fullFunction_horizontal_hasDerivAt constant v hv z 1 0).deriv
  have hI := (coeff.fullFunction_horizontal_hasDerivAt constant v hv z Complex.I 0).deriv
  simp only [mul_one,Complex.ofReal_zero,zero_mul,add_zero] at h1 hI
  rw [horizontalWirtingerBar,h1,hI,norm_mul]
  have hhalf : ‖(1/2:ℂ)‖=(1/2:ℝ) := by norm_num
  rw [hhalf]
  calc
    _ ≤ (1/2:ℝ)*(‖∑'h : ActualEisensteinCubic.O,coeff.directionalTerm h v z 1‖+
        ‖Complex.I*(∑'h : ActualEisensteinCubic.O,coeff.directionalTerm h v z Complex.I)‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
    _ = (1/2:ℝ)*(‖∑'h : ActualEisensteinCubic.O,coeff.directionalTerm h v z 1‖+
        ‖∑'h : ActualEisensteinCubic.O,coeff.directionalTerm h v z Complex.I‖) := by
      rw [norm_mul,Complex.norm_I,one_mul]
    _ ≤ (1/2:ℝ)*(C1*Real.exp (-residualCuspDecayRate*v)+CI*Real.exp (-residualCuspDecayRate*v)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact add_le_add (hbound1 v z hav) (hboundI v z hav)
    _ = _ := by ring

end SubexponentialBesselCoefficients
end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups
open Finset AddChar MulChar EisensteinEmbedding

section
local notation "O" => ActualEisensteinCubic.O

lemma spatialComplexSplit_differentiable : Differentiable ℝ spatialComplexSplit := by
  change Differentiable ℝ (fun p : EuclideanSpatial => (p 2,(p 0:ℂ)+(p 1:ℂ)*Complex.I))
  fun_prop

lemma spatialComplexSplit_symm_differentiable : Differentiable ℝ spatialComplexSplit.symm := by
  change Differentiable ℝ (fun q : ℝ × ℂ => spatialComplexSplit.symm q)
  simp_rw [spatialComplexSplit_symm_eq]
  have hlin := (WithLp.linearEquiv 2 ℝ (Fin 3→ℝ)).symm.toContinuousLinearMap.differentiable
  have hcoords : Differentiable ℝ (fun q : ℝ × ℂ => ![q.2.re,q.2.im,q.1]) := by
    apply differentiable_pi.mpr
    intro j
    fin_cases j
    · change Differentiable ℝ (fun q : ℝ × ℂ => q.2.re)
      fun_prop
    · change Differentiable ℝ (fun q : ℝ × ℂ => q.2.im)
      fun_prop
    · change Differentiable ℝ (fun q : ℝ × ℂ => q.1)
      fun_prop
  exact hlin.comp hcoords

namespace SubexponentialBesselCoefficients
variable (coeff : SubexponentialBesselCoefficients)

lemma fullFunction_euclidean_differentiableAt (constant : ℂ) (p : EuclideanSpatial) (hp : 0<p 2) :
    DifferentiableAt ℝ (fun q : EuclideanSpatial => coeff.fullFunction constant (euclideanToHyperbolic q)) p := by
  have hh := (coeff.fullFunction_cusp_differentiableAt constant (spatialComplexSplit p) hp).comp p
    spatialComplexSplit_differentiable.differentiableAt
  simpa only [Function.comp_def,cuspCoordinateLift,spatialComplexSplit.symm_apply_apply] using hh

lemma fullFunction_translate_cusp_differentiableAt (constant : ℂ) (g : SL(2,ℂ))
    (p : ℝ × ℂ) (hp : 0<p.1) :
    DifferentiableAt ℝ (fun q : ℝ × ℂ => coeff.fullFunction constant (g • cuspCoordinateLift q)) p := by
  have hx : 0<(spatialComplexSplit.symm p) 2 := by
    rw [spatialComplexSplit_symm_eq]
    exact hp
  obtain ⟨A,hA,hAn⟩ := hyperbolicDifferentialIsometry g (spatialComplexSplit.symm p) hx
  have hh := ((coeff.fullFunction_euclidean_differentiableAt constant
    (euclideanAction g (spatialComplexSplit.symm p)) (euclideanAction_positive _ _)).comp _
      hA.differentiableAt).comp p spatialComplexSplit_symm_differentiable.differentiableAt
  simpa only [Function.comp_def,euclideanAction,euclideanToHyperbolic_coordinates,cuspCoordinateLift] using hh

lemma fullFunction_translate_split_differentiableAt (constant : ℂ) (g : SL(2,ℂ))
    (p : ℂ × ℝ) (hp : 0<p.2) :
    DifferentiableAt ℝ
      (fun q : ℂ × ℝ => coeff.fullFunction constant (g • cuspCoordinateLift (q.2,q.1))) p := by
  have hswap : DifferentiableAt ℝ (fun q : ℂ × ℝ => (q.2,q.1)) p :=
    differentiableAt_snd.prodMk differentiableAt_fst
  exact (coeff.fullFunction_translate_cusp_differentiableAt constant g (p.2,p.1) hp).comp p hswap

end SubexponentialBesselCoefficients

lemma cubicSourceResidualFunction_translate_split_differentiableAt (g : SL(2,ℂ))
    (p : ℂ × ℝ) (hp : 0<p.2) :
    DifferentiableAt ℝ
      (fun q : ℂ × ℝ => cubicSourceResidualFunction (g • cuspCoordinateLift (q.2,q.1))) p := by
  rw [cubicSourceResidualFunction_eq_bessel]
  exact sourceBesselCoefficients.fullFunction_translate_split_differentiableAt
    ((3*(Real.pi:ℂ))*constantArithmeticResidue) g p hp

lemma cubicSourceResidualFunction_wirtingerBar_cusp_decay (a : ℝ) (ha : 0<a) :
    ∃C : ℝ,0≤C ∧ ∀(v : ℝ)(hv : 0<v)(z : ℂ),a≤v →
      ‖horizontalWirtingerBar (fun w => cubicSourceResidualFunction (upperPoint w v hv)) z‖≤
        C*Real.exp (-residualCuspDecayRate*v) := by
  rw [cubicSourceResidualFunction_eq_bessel]
  exact sourceBesselCoefficients.fullFunction_wirtingerBar_cusp_decay _ a ha

end

local notation "O" => ActualEisensteinCubic.O

lemma horizontalWirtingerBar_star (f : ℂ→ℂ) (z : ℂ) :
    horizontalWirtingerBar (fun w => star (f w)) z=star (horizontalWirtingerZ f z) := by
  unfold horizontalWirtingerBar horizontalWirtingerZ
  rw [deriv.star,deriv.star]
  simp []

namespace SubexponentialBesselCoefficients
variable (coeff : SubexponentialBesselCoefficients)

lemma fullFunction_wirtingerZ_cusp_decay (constant : ℂ) (a : ℝ) (ha : 0<a) :
    ∃C : ℝ,0≤C ∧ ∀(v : ℝ)(hv : 0<v)(z : ℂ),a≤v →
      ‖horizontalWirtingerZ (fun w => coeff.fullFunction constant (upperPoint w v hv)) z‖≤
        C*Real.exp (-residualCuspDecayRate*v) := by
  obtain ⟨C1,hC1,hbound1⟩ := coeff.directionalSeries_cusp_decay a ha 1
  obtain ⟨CI,hCI,hboundI⟩ := coeff.directionalSeries_cusp_decay a ha Complex.I
  refine ⟨(C1+CI)/2,by positivity,?_⟩
  intro v hv z hav
  have h1 := (coeff.fullFunction_horizontal_hasDerivAt constant v hv z 1 0).deriv
  have hI := (coeff.fullFunction_horizontal_hasDerivAt constant v hv z Complex.I 0).deriv
  simp only [mul_one,Complex.ofReal_zero,zero_mul,add_zero] at h1 hI
  rw [horizontalWirtingerZ,h1,hI,norm_mul]
  have hhalf : ‖(1/2:ℂ)‖=(1/2:ℝ) := by norm_num
  rw [hhalf]
  calc
    _ ≤ (1/2:ℝ)*(‖∑'h : ActualEisensteinCubic.O,coeff.directionalTerm h v z 1‖+
        ‖Complex.I*(∑'h : ActualEisensteinCubic.O,coeff.directionalTerm h v z Complex.I)‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by norm_num)
    _ = (1/2:ℝ)*(‖∑'h : ActualEisensteinCubic.O,coeff.directionalTerm h v z 1‖+
        ‖∑'h : ActualEisensteinCubic.O,coeff.directionalTerm h v z Complex.I‖) := by
      rw [norm_mul,Complex.norm_I,one_mul]
    _ ≤ (1/2:ℝ)*(C1*Real.exp (-residualCuspDecayRate*v)+CI*Real.exp (-residualCuspDecayRate*v)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact add_le_add (hbound1 v z hav) (hboundI v z hav)
    _ = _ := by ring

end SubexponentialBesselCoefficients

lemma cubicSourceResidualFunction_wirtingerZ_cusp_decay (a : ℝ) (ha : 0<a) :
    ∃C : ℝ,0≤C ∧ ∀(v : ℝ)(hv : 0<v)(z : ℂ),a≤v →
      ‖horizontalWirtingerZ (fun w => cubicSourceResidualFunction (upperPoint w v hv)) z‖≤
        C*Real.exp (-residualCuspDecayRate*v) := by
  rw [cubicSourceResidualFunction_eq_bessel]
  exact sourceBesselCoefficients.fullFunction_wirtingerZ_cusp_decay _ a ha

lemma cubicSourceConjugateFunction_translate_split_differentiableAt (g : SL(2,ℂ))
    (p : ℂ × ℝ) (hp : 0<p.2) :
    DifferentiableAt ℝ
      (fun q : ℂ × ℝ => cubicSourceConjugateFunction (g • cuspCoordinateLift (q.2,q.1))) p :=
  (cubicSourceResidualFunction_translate_split_differentiableAt g p hp).star

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups
open Finset AddChar MulChar EisensteinEmbedding

lemma horizontalWirtingerBar_translate (f : ℂ→ℂ) (a : ℂ) :
    horizontalWirtingerBar (fun z=>f (z+a)) 0=horizontalWirtingerBar f a := by
  unfold horizontalWirtingerBar
  simp only [zero_add]
  have h1 : (fun t : ℝ=>f ((t:ℂ)+a))=(fun t : ℝ=>f (a+(t:ℂ))) := by
    funext t
    rw [add_comm]
  have hI : (fun t : ℝ=>f ((t:ℂ)*Complex.I+a))=(fun t : ℝ=>f (a+(t:ℂ)*Complex.I)) := by
    funext t
    rw [add_comm]
  rw [h1,hI]

lemma cuspDerivative_of_transform (f : HyperbolicSpace→ℂ) (g H : SL(2,ℂ))
    (κ : ℂ) (htransform : ∀w,f (g•w)=κ*f (H•w)) (hc : g 1 0≠0)
    (v : ℝ) (hv : 0<v)
    (hD : DifferentiableAt ℝ
      (fun q : ℂ × ℝ=>f (H•cuspCoordinateLift (q.2,q.1)))
      (-g 1 1/g 1 0,1/(‖g 1 0‖^2*v))) :
    horizontalWirtingerBar (fun z=>f (upperPoint z v hv)) (g 0 0/g 1 0)=
      (κ*(-1/((g 1 0)^2*(v:ℂ)^2)))*
        horizontalWirtingerZ
          (fun z=>f (H•upperPoint z (1/(‖g 1 0‖^2*v)) (by positivity)))
          (-g 1 1/g 1 0) := by
  let FH : ℂ × ℝ→ℂ := fun q=>f (H•cuspCoordinateLift (q.2,q.1))
  let base : ℂ × ℝ := (-g 1 1/g 1 0,1/(‖g 1 0‖^2*v))
  let D := fderiv ℝ FH base
  have hF : HasFDerivAt FH D base := hD.hasFDerivAt
  have hscaled : HasFDerivAt (fun q=>κ*FH q) (κ • D) base := hF.const_mul κ
  have he := inverse_cusp_wirtingerBar (g 1 0) (g 1 1) v hc hv
    (fun q=>κ*FH q) (κ • D) hscaled
  have hline : (fun z=>κ*FH (inverseCuspCoordinates (g 1 0) (g 1 1) v z))=
      (fun z=>f (upperPoint (z+g 0 0/g 1 0) v hv)) := by
    funext z
    have ht := htransform (g⁻¹•upperPoint (z+g 0 0/g 1 0) v hv)
    rw [smul_inv_smul,inverse_cusp_action g hc v hv z] at ht
    change κ*f (H•cuspCoordinateLift
      ((inverseCuspCoordinates (g 1 0) (g 1 1) v z).2,
       (inverseCuspCoordinates (g 1 0) (g 1 1) v z).1))=_
    rw [cuspCoordinateLift_positive _ _ (inverseCuspCoordinates_height_pos _ _ _ _ hc hv)]
    exact ht.symm
  rw [hline] at he
  have hshift := horizontalWirtingerBar_translate (fun z=>f (upperPoint z v hv)) (g 0 0/g 1 0)
  rw [hshift] at he
  have hz := horizontalWirtingerZ_eq_fderiv FH D (-g 1 1/g 1 0) (1/(‖g 1 0‖^2*v)) hF
  have hFH : (fun z=>FH (z,1/(‖g 1 0‖^2*v)))=
      (fun z=>f (H•upperPoint z (1/(‖g 1 0‖^2*v)) (by positivity))) := by
    funext z
    exact congrArg (fun w=>f (H•w)) (cuspCoordinateLift_positive _ _ (by positivity))
  rw [hFH] at hz
  rw [hz]
  rw [he]
  simp only [_root_.smul_apply,smul_eq_mul]
  ring

end CubicEisenstein

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reciprocity.CubeCorrespondence
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

open Filter MeasureTheory Asymptotics
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

namespace CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

lemma cuspBarProfile_positive (f : HyperbolicSpace→ℂ) (z : ℂ) (v : ℝ) (hv : 0<v) :
    cuspBarProfile f z v=horizontalWirtingerBar (fun w=>f (upperPoint w v hv)) z := by
  simp only [cuspBarProfile,cuspCoordinateLift_positive v _ hv]

lemma cuspZProfile_positive (f : HyperbolicSpace→ℂ) (z : ℂ) (v : ℝ) (hv : 0<v) :
    cuspZProfile f z v=horizontalWirtingerZ (fun w=>f (upperPoint w v hv)) z := by
  simp only [cuspZProfile,cuspCoordinateLift_positive v _ hv]

lemma horizontalWirtingerZ_star (f : ℂ→ℂ) (z : ℂ) :
    horizontalWirtingerZ (fun w=>star (f w)) z=star (horizontalWirtingerBar f z) := by
  unfold horizontalWirtingerBar horizontalWirtingerZ
  rw [deriv.star,deriv.star]
  simp [sub_eq_add_neg]

namespace SubexponentialBesselCoefficients
variable (coeff : SubexponentialBesselCoefficients)

lemma directionalSeries_continuousOn_slab (direction : ℂ) (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    ContinuousOn (coeff.directionalSeries direction) {p : ℝ × ℂ|p.1∈Set.Icc a b} := by
  obtain ⟨C,hC,hbound⟩ := coeff.directionalTerm_slab_bound a b ha hab direction
  apply continuousOn_tsum (u:=fun h : ActualEisensteinCubic.O=>C*(‖cuspFrequency h‖*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖)))
  · intro h
    have ht : ContinuousOn (coeff.term h) {p : ℝ × ℂ|p.1∈Set.Icc a b} :=
      (coeff.term_continuousOn h).mono (fun p hp=>ha.trans_le hp.1)
    exact ht.const_mul (horizontalPhaseMultiplier (cuspFrequency h) direction)
  · exact (summable_norm_mul_exp_neg_cuspFrequency (Real.pi*a) (mul_pos Real.pi_pos ha)).mul_left C
  · intro h p hp
    exact hbound h p.1 p.2 hp

lemma directionalSeries_continuousOn (direction : ℂ) :
    ContinuousOn (coeff.directionalSeries direction) {p : ℝ × ℂ|0<p.1} := by
  intro p hp
  have hclosed := coeff.directionalSeries_continuousOn_slab direction (p.1/2) (2*p.1)
    (by change 0<p.1 at hp;linarith) (by change 0<p.1 at hp;linarith)
  have hnb : {q : ℝ × ℂ|q.1∈Set.Icc (p.1/2) (2*p.1)}∈𝓝 p :=
    continuousAt_fst.tendsto.eventually (Icc_mem_nhds (by change 0<p.1 at hp;linarith)
      (by change 0<p.1 at hp;linarith))
  exact (hclosed.continuousAt hnb).continuousWithinAt

lemma cuspZProfile_full_eq (constant z : ℂ) (v : ℝ) (hv : 0<v) :
    cuspZProfile (coeff.fullFunction constant) z v=
      (1/2:ℂ)*(coeff.directionalSeries 1 (v,z)-Complex.I*coeff.directionalSeries Complex.I (v,z)) := by
  rw [cuspZProfile_positive _ _ _ hv,horizontalWirtingerZ]
  have h1 := (coeff.fullFunction_horizontal_hasDerivAt constant v hv z 1 0).deriv
  have hI := (coeff.fullFunction_horizontal_hasDerivAt constant v hv z Complex.I 0).deriv
  simp only [mul_one,Complex.ofReal_zero,zero_mul,add_zero] at h1 hI
  rw [h1,hI]
  rfl

lemma cuspZProfile_continuousOn (constant z : ℂ) :
    ContinuousOn (cuspZProfile (coeff.fullFunction constant) z) (Set.Ioi 0) := by
  have hd (direction : ℂ) : ContinuousOn (fun v : ℝ=>coeff.directionalSeries direction (v,z)) (Set.Ioi 0) :=
    (coeff.directionalSeries_continuousOn direction).comp
      (continuousOn_id.prodMk continuousOn_const) (fun v hv=>hv)
  apply (continuousOn_const.mul ((hd 1).sub (continuousOn_const.mul (hd Complex.I)))).congr
  intro v hv
  exact coeff.cuspZProfile_full_eq constant z v hv

end SubexponentialBesselCoefficients

lemma cuspZProfile_source_continuousOn (z : ℂ) :
    ContinuousOn (cuspZProfile cubicSourceResidualFunction z) (Set.Ioi 0) := by
  rw [cubicSourceResidualFunction_eq_bessel]
  exact sourceBesselCoefficients.cuspZProfile_continuousOn _ z

lemma cuspBarProfile_conjugate_eq (z : ℂ) :
    cuspBarProfile cubicSourceConjugateFunction z=fun v=>star (cuspZProfile cubicSourceResidualFunction z v) := by
  funext v
  exact horizontalWirtingerBar_star _ z

lemma cuspZProfile_conjugate_eq (z : ℂ) :
    cuspZProfile cubicSourceConjugateFunction z=fun v=>star (cuspBarProfile cubicSourceResidualFunction z v) := by
  funext v
  exact horizontalWirtingerZ_star _ z

lemma cuspBarProfile_conjugate_continuousOn (z : ℂ) :
    ContinuousOn (cuspBarProfile cubicSourceConjugateFunction z) (Set.Ioi 0) := by
  rw [cuspBarProfile_conjugate_eq]
  exact (cuspZProfile_source_continuousOn z).star

lemma cuspBarProfile_source_isBigO (z : ℂ) :
    cuspBarProfile cubicSourceResidualFunction z =O[atTop]
      (fun v : ℝ=>Real.exp (-residualCuspDecayRate*v)) := by
  obtain ⟨C,hC,hbound⟩ := cubicSourceResidualFunction_wirtingerBar_cusp_decay 1 (by norm_num)
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [eventually_ge_atTop (1:ℝ)] with v hv
  have hvp : 0<v := lt_of_lt_of_le (by norm_num) hv
  rw [cuspBarProfile_positive _ _ _ hvp,Real.norm_of_nonneg (Real.exp_pos _).le]
  exact hbound v hvp z hv

lemma cuspZProfile_source_isBigO (z : ℂ) :
    cuspZProfile cubicSourceResidualFunction z =O[atTop]
      (fun v : ℝ=>Real.exp (-residualCuspDecayRate*v)) := by
  obtain ⟨C,hC,hbound⟩ := cubicSourceResidualFunction_wirtingerZ_cusp_decay 1 (by norm_num)
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [eventually_ge_atTop (1:ℝ)] with v hv
  have hvp : 0<v := lt_of_lt_of_le (by norm_num) hv
  rw [cuspZProfile_positive _ _ _ hvp,Real.norm_of_nonneg (Real.exp_pos _).le]
  exact hbound v hvp z hv

lemma cuspBarProfile_conjugate_isBigO (z : ℂ) :
    cuspBarProfile cubicSourceConjugateFunction z =O[atTop]
      (fun v : ℝ=>Real.exp (-residualCuspDecayRate*v)) := by
  obtain ⟨C,hC⟩ := Asymptotics.isBigO_iff.mp (cuspZProfile_source_isBigO z)
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [hC] with v hv
  simpa only [cuspBarProfile_conjugate_eq,norm_star] using hv

lemma cuspZProfile_conjugate_isBigO (z : ℂ) :
    cuspZProfile cubicSourceConjugateFunction z =O[atTop]
      (fun v : ℝ=>Real.exp (-residualCuspDecayRate*v)) := by
  obtain ⟨C,hC⟩ := Asymptotics.isBigO_iff.mp (cuspBarProfile_source_isBigO z)
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [hC] with v hv
  simpa only [cuspZProfile_conjugate_eq,norm_star] using hv

end CubicEisenstein

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.ConjugateCuspProfiles
namespace OAI

noncomputable section

namespace CubicEisenstein

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

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O

lemma cubicBesselIntegralDeriv_continuousAt (x : ℝ) (hx : 0<x) :
    ContinuousAt (fun y : ℝ=>∫t in Set.Ioi (0:ℝ),cubicBesselDensityDeriv y t) x := by
  let delta := x/2
  have hdelta : 0<delta := half_pos hx
  apply continuousAt_of_dominated («μ» := volume.restrict (Set.Ioi (0:ℝ)))
    (bound:=fun t : ℝ=>(4/delta)*(t^(-(2:ℝ)/3)*Real.exp (-t/2)))
  · exact Eventually.of_forall (fun y=>by unfold cubicBesselDensityDeriv cubicBesselDensity;fun_prop)
  · filter_upwards [Ioi_mem_nhds (show delta<x by dsimp [delta];linarith)] with y hy
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hyp : 0<y := hdelta.trans hy
    have htp : 0<t := ht
    calc
      _ ≤ (4/delta)*Real.exp (-y/2)*(t^(-(2:ℝ)/3)*Real.exp (-t/2)) :=
        cubicBesselDensityDeriv_bound delta y t hdelta hy.le ht
      _ ≤ _ := by
        have he : Real.exp (-y/2)≤1 := Real.exp_le_one_iff.mpr (by linarith)
        calc
          _ ≤ (4/delta)*1*(t^(-(2:ℝ)/3)*Real.exp (-t/2)) := by gcongr
          _ = _ := by ring
  · exact cubicBesselDerivativeMajorant_integrable.const_mul (4/delta)
  · exact Eventually.of_forall (fun t=>by unfold cubicBesselDensityDeriv cubicBesselDensity;fun_prop)

lemma schlafliBesselK_cubic_derivative_continuousAt (x : ℝ) (hx : 0<x) :
    ContinuousAt schlafliBesselK_cubic_derivative x := by
  have hp4 : ContinuousAt (fun y : ℝ=>(y/2)^(-(4:ℝ)/3)) x :=
    (continuousAt_id.div_const 2).rpow_const (Or.inl (by positivity))
  have hp1 : ContinuousAt (fun y : ℝ=>(y/2)^(-(1:ℝ)/3)) x :=
    (continuousAt_id.div_const 2).rpow_const (Or.inl (by positivity))
  have hI := (cubicBesselIntegral_hasDerivAt x hx).continuousAt
  have hD := cubicBesselIntegralDeriv_continuousAt x hx
  apply Complex.continuous_ofReal.continuousAt.comp
  exact ((continuousAt_const.mul hp4).mul hI).add ((continuousAt_const.mul hp1).mul hD)

namespace SubexponentialBesselCoefficients
variable (coeff : SubexponentialBesselCoefficients)

lemma amplitudeDeriv_continuousAt (v : ℝ) (hv : 0<v) (h : ActualEisensteinCubic.O) :
    ContinuousAt (fun y : ℝ=>coeff.amplitudeDeriv y h) v := by
  by_cases hh : h=0
  · simpa only [amplitudeDeriv,if_pos hh] using (continuousAt_const (y:=(0:ℂ)) (x:=v))
  have hr : 0<‖cuspFrequency h‖ := norm_pos_iff.mpr (cuspFrequency_ne_zero h hh)
  have hK : ContinuousAt (fun y : ℝ=>schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*y)) v :=
    (schlafliBesselK_cubic_hasDerivAt _ (by positivity)).continuousAt.comp (by fun_prop)
  have hD : ContinuousAt (fun y : ℝ=>schlafliBesselK_cubic_derivative (4*Real.pi*‖cuspFrequency h‖*y)) v :=
    (schlafliBesselK_cubic_derivative_continuousAt _ (by positivity)).comp (by fun_prop)
  simp only [amplitudeDeriv,if_neg hh]
  exact continuousAt_const.mul (hK.add ((Complex.continuous_ofReal.continuousAt.mul continuousAt_const).mul hD))

lemma termFDeriv_continuousAt (h : ActualEisensteinCubic.O) (p : ℝ × ℂ) (hp : 0<p.1) :
    ContinuousAt (coeff.termFDeriv h) p := by
  by_cases hh : h=0
  · have he : coeff.termFDeriv h=fun _=>(0:(ℝ × ℂ)→L[ℝ]ℂ) := by
      funext q
      simp only [termFDeriv,if_pos hh]
    rw [he]
    exact continuousAt_const
  have hA := (coeff.amplitudeDeriv_continuousAt p.1 hp h).comp continuousAt_fst
  have hphase : ContinuousAt (fun q : ℝ × ℂ=>ShortDraftTrace.breveE (cuspFrequency h*q.2)) p := by
    change ContinuousAt (fun q : ℝ × ℂ=>Complex.exp (2*Real.pi*Complex.I*
      ((cuspFrequency h*q.2)+starRingEnd ℂ (cuspFrequency h*q.2)))) p
    fun_prop
  have hfirst := (ContinuousLinearMap.smulRightL ℝ (ℝ × ℂ) ℂ
    (ContinuousLinearMap.fst ℝ ℝ ℂ)).continuous.continuousAt.comp (hA.mul hphase)
  have hterm := (coeff.term_continuousOn h).continuousAt
    ((isOpen_lt continuous_const continuous_fst).mem_nhds hp)
  have hsecond := hterm.smul (continuousAt_const
    (y:=(horizontalPhaseCLM (cuspFrequency h)).comp (ContinuousLinearMap.snd ℝ ℝ ℂ)))
  have he : coeff.termFDeriv h=(fun q : ℝ × ℂ=>
      (ContinuousLinearMap.fst ℝ ℝ ℂ).smulRight
        (coeff.amplitudeDeriv q.1 h*ShortDraftTrace.breveE (cuspFrequency h*q.2))+
      coeff.term h q • (horizontalPhaseCLM (cuspFrequency h)).comp (ContinuousLinearMap.snd ℝ ℝ ℂ)) := by
    funext q
    simp only [termFDeriv,if_neg hh]
  rw [he]
  exact hfirst.add hsecond

lemma seriesFDeriv_continuousOn_slab (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    ContinuousOn (fun p : ℝ × ℂ=>∑'h : ActualEisensteinCubic.O,coeff.termFDeriv h p)
      {p : ℝ × ℂ|p.1∈Set.Icc a b} := by
  obtain ⟨C,hC,hbound⟩ := coeff.termFDeriv_slab_bound a b ha hab
  apply continuousOn_tsum (u:=fun h : ActualEisensteinCubic.O=>C*((1+‖cuspFrequency h‖)*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖)))
  · intro h p hp
    exact (coeff.termFDeriv_continuousAt h p (ha.trans_le hp.1)).continuousWithinAt
  · exact (summable_one_add_norm_exp_neg_cuspFrequency (Real.pi*a) (mul_pos Real.pi_pos ha)).mul_left C
  · exact hbound

lemma series_contDiffAt_one (p : ℝ × ℂ) (hp : 0<p.1) : ContDiffAt ℝ 1 coeff.series p := by
  apply contDiffAt_one_iff.mpr
  refine ⟨(fun q=>∑'h : ActualEisensteinCubic.O,coeff.termFDeriv h q),
    {q : ℝ × ℂ|q.1∈Set.Icc (p.1/2) (2*p.1)},?_,?_,?_⟩
  · exact continuousAt_fst.tendsto.eventually (Icc_mem_nhds (by linarith) (by linarith))
  · exact coeff.seriesFDeriv_continuousOn_slab _ _ (by linarith) (by linarith)
  · intro q hq
    exact coeff.series_hasFDerivAt q (by change p.1/2≤q.1 ∧ q.1≤2*p.1 at hq;linarith [hq.1])

end SubexponentialBesselCoefficients
end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups
open Finset AddChar MulChar EisensteinEmbedding

lemma cuspSpatialInput_contDiff : ContDiff ℝ 1 cuspSpatialInput := by
  apply contDiff_pi.mpr
  intro j
  fin_cases j
  · change ContDiff ℝ 1 (fun q : ℝ × ℂ=>q.2.re)
    exact Complex.reCLM.contDiff.comp contDiff_snd
  · change ContDiff ℝ 1 (fun q : ℝ × ℂ=>q.2.im)
    exact Complex.imCLM.contDiff.comp contDiff_snd
  · change ContDiff ℝ 1 (fun q : ℝ × ℂ=>q.1)
    fun_prop

lemma cuspSpatialOutput_contDiff : ContDiff ℝ 1 cuspSpatialOutput :=
  (contDiff_apply ℝ ℝ 2).prodMk (spatialHorizontal_contDiff.of_le (by simp))

lemma cuspSpatialAction_lift (g : SL(2,ℂ)) (q : ℝ × ℂ) (hq : 0<q.1) :
    cuspCoordinateLift (cuspSpatialOutput (mobiusSpatial g (cuspSpatialInput q)))=
      g•cuspCoordinateLift q := by
  have hin : hyperbolicSpatialCoordinates (cuspCoordinateLift q)=cuspSpatialInput q := by
    rw [show q=(q.1,q.2) from rfl,cuspCoordinateLift_positive q.1 q.2 hq]
    simp only [hyperbolicSpatialCoordinates,hyperbolicHorizontal_upperPoint,hyperbolicHeight_upperPoint,cuspSpatialInput]
  have he := mobiusSpatial_coordinates_global g (cuspCoordinateLift q)
  rw [hin] at he
  have hr := hyperbolicSpatialCoordinates_reconstruct (g•cuspCoordinateLift q)
  have hp : 0< mobiusSpatial g (cuspSpatialInput q) 2 := mobiusSpatial_positive g _ hq
  rw [cuspSpatialOutput,cuspCoordinateLift_positive _ _ hp]
  refine Eq.trans ?_ hr
  apply upperPoint_congr
  · rw [he]
    rfl
  · rw [he]

namespace SubexponentialBesselCoefficients
variable (coeff : SubexponentialBesselCoefficients)

lemma fullFunction_cusp_contDiffAt_one (constant : ℂ) (p : ℝ × ℂ) (hp : 0<p.1) :
    ContDiffAt ℝ 1 (fun q : ℝ × ℂ=>coeff.fullFunction constant (cuspCoordinateLift q)) p := by
  have hreal : ContDiffAt ℝ 1 (fun q : ℝ × ℂ=>q.1^(2/3:ℝ)) p :=
    contDiff_fst.contDiffAt.rpow_const_of_ne hp.ne'
  have hcast := Complex.ofRealCLM.contDiff.contDiffAt.comp p hreal
  have hpow : ContDiffAt ℝ 1 (fun q : ℝ × ℂ=>(q.1:ℂ)^(2/3:ℂ)) p := by
    apply hcast.congr_of_eventuallyEq
    filter_upwards [continuousAt_fst.tendsto.eventually (Ioi_mem_nhds hp)] with q hq
    have he := Complex.ofReal_cpow (le_of_lt hq) (2/3:ℝ)
    norm_num only [Complex.ofReal_div,Complex.ofReal_ofNat] at he
    exact he.symm
  have hfull : ContDiffAt ℝ 1 (fun q : ℝ × ℂ=>constant*(q.1:ℂ)^(2/3:ℂ)+coeff.series q) p :=
    (contDiffAt_const.mul hpow).add (coeff.series_contDiffAt_one p hp)
  apply hfull.congr_of_eventuallyEq
  filter_upwards [continuousAt_fst.tendsto.eventually (Ioi_mem_nhds hp)] with q hq
  exact coeff.fullFunction_cusp_eq constant q hq

lemma fullFunction_translate_cusp_contDiffAt_one (constant : ℂ) (g : SL(2,ℂ))
    (p : ℝ × ℂ) (hp : 0<p.1) :
    ContDiffAt ℝ 1 (fun q : ℝ × ℂ=>coeff.fullFunction constant (g•cuspCoordinateLift q)) p := by
  have hmid : ContDiffAt ℝ 1 (fun q=>mobiusSpatial g (cuspSpatialInput q)) p :=
    ((mobiusSpatial_contDiffAt g (cuspSpatialInput p) hp).of_le (by simp)).comp p
      cuspSpatialInput_contDiff.contDiffAt
  have hact := cuspSpatialOutput_contDiff.contDiffAt.comp p hmid
  have hpos : 0<(cuspSpatialOutput (mobiusSpatial g (cuspSpatialInput p))).1 :=
    mobiusSpatial_positive g _ hp
  have hfull := (coeff.fullFunction_cusp_contDiffAt_one constant _ hpos).comp p hact
  apply hfull.congr_of_eventuallyEq
  filter_upwards [continuousAt_fst.tendsto.eventually (Ioi_mem_nhds hp)] with q hq
  exact congrArg (coeff.fullFunction constant) (cuspSpatialAction_lift g q hq).symm

lemma fullFunction_translate_split_contDiffAt_one (constant : ℂ) (g : SL(2,ℂ))
    (p : ℂ × ℝ) (hp : 0<p.2) :
    ContDiffAt ℝ 1 (fun q : ℂ × ℝ=>coeff.fullFunction constant (g•cuspCoordinateLift (q.2,q.1))) p := by
  have hswap : ContDiffAt ℝ 1 (fun q : ℂ × ℝ=>(q.2,q.1)) p := by fun_prop
  exact (coeff.fullFunction_translate_cusp_contDiffAt_one constant g (p.2,p.1) hp).comp p hswap

end SubexponentialBesselCoefficients

lemma cubicSourceResidualFunction_translate_split_contDiffAt_one (g : SL(2,ℂ))
    (p : ℂ × ℝ) (hp : 0<p.2) :
    ContDiffAt ℝ 1 (fun q : ℂ × ℝ=>cubicSourceResidualFunction (g•cuspCoordinateLift (q.2,q.1))) p := by
  rw [cubicSourceResidualFunction_eq_bessel]
  exact sourceBesselCoefficients.fullFunction_translate_split_contDiffAt_one _ g p hp

lemma cubicSourceConjugateFunction_translate_split_contDiffAt_one (g : SL(2,ℂ))
    (p : ℂ × ℝ) (hp : 0<p.2) :
    ContDiffAt ℝ 1 (fun q : ℂ × ℝ=>cubicSourceConjugateFunction (g•cuspCoordinateLift (q.2,q.1))) p := by
  exact Complex.conjCLE.contDiff.contDiffAt.comp p
    (cubicSourceResidualFunction_translate_split_contDiffAt_one g p hp)

lemma cuspZProfile_continuousOn_of_contDiff (f : HyperbolicSpace→ℂ)
    (hreg : ∀p : ℂ × ℝ,0<p.2 → ContDiffAt ℝ 1
      (fun q : ℂ × ℝ=>f (cuspCoordinateLift (q.2,q.1))) p) (z : ℂ) :
    ContinuousOn (cuspZProfile f z) (Set.Ioi 0) := by
  let F : ℂ × ℝ→ℂ := fun q=>f (cuspCoordinateLift (q.2,q.1))
  intro v hv
  have hd : ContinuousAt (fderiv ℝ F) (z,v) :=
    (hreg (z,v) hv).continuousAt_fderiv (by norm_num)
  have hc : ContinuousAt (fun y : ℝ=>(z,y)) v := continuousAt_const.prodMk continuousAt_id
  have h1 := (hd.comp hc).clm_apply (continuousAt_const (y:=((1,0):ℂ × ℝ)))
  have hI := (hd.comp hc).clm_apply (continuousAt_const (y:=((Complex.I,0):ℂ × ℝ)))
  have hformula : ContinuousAt (fun y : ℝ=>(1/2:ℂ)*
      ((fderiv ℝ F (z,y)) (1,0)-Complex.I*(fderiv ℝ F (z,y)) (Complex.I,0))) v :=
    continuousAt_const.mul (h1.sub (continuousAt_const.mul hI))
  apply ContinuousAt.continuousWithinAt
  apply hformula.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds (show 0<v from hv)] with y hy
  exact horizontalWirtingerZ_eq_fderiv F (fderiv ℝ F (z,y)) z y
    ((hreg (z,y) hy).differentiableAt (by norm_num)).hasFDerivAt

lemma cuspZProfile_conjugate_translate_continuousOn (H : SL(2,ℂ)) (z : ℂ) :
    ContinuousOn (cuspZProfile (fun w=>cubicSourceConjugateFunction (H•w)) z) (Set.Ioi 0) :=
  cuspZProfile_continuousOn_of_contDiff _
    (cubicSourceConjugateFunction_translate_split_contDiffAt_one H) z

end

open scoped BigOperators Classical MatrixGroups Matrix

open ActualEisensteinCubic CubicKubota ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

end CubicEisenstein

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.CorrespondenceAdjoint
namespace OAI

noncomputable section

namespace CubicEisenstein

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

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

local notation "Eis" => ActualEisensteinCubic.O

lemma ramifiedSource_eq_series (side:Bool) (v:ℝ) (hv:0<v) (z:ℂ) :
    ramifiedSourceFunction (ramifiedCuspRoot side:Eis) (upperPoint z v hv)=
      (ramifiedBesselCoefficients side).series (v/3,z/3) := by
  have he:=ramifiedScaledRow_eq_bessel side (v/3) (by positivity) (z/3)
  have hv3:3*(v/3)=v:=by ring
  have hz3:(3:ℂ)*(z/3)=z:=by ring
  simpa only [ramifiedScaledRow,hv3,hz3,cuspCoordinateLift_positive v z hv,
    SubexponentialBesselCoefficients.fullFunction,zero_mul,zero_add,
    SubexponentialBesselCoefficients.function,hyperbolicHeight_upperPoint,
    hyperbolicHorizontal_upperPoint] using he

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Pointwise Manifold ContDiff ENNReal InnerProductSpace
open Finset AddChar MulChar EisensteinEmbedding

end CubicEisenstein

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.PrimeGaussFactors
namespace OAI

noncomputable section

namespace CubicEisenstein

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

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

local instance instFintypeUnitsO_3_r70e77c_1 : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units
lemma unramifiedCubicGaussSeries_prime_two_power (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (s:ℂ) (hs:2<s.re) (h:Eis) (hph:¬p∣h) :
    unramifiedCubicGaussSeries s (h*p^2)=
      (1-(Ideal.absNorm (Ideal.span {p}):ℂ)^2*
        ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^3)*
        unramifiedPrimeDeletedSeries p s (h*p^2) := by
  have he:=unramifiedCubicGaussSeries_prime_finite p hp hprimary s hs h hph 2
  have hg1:cubicUnitGaussSum (h*p^2) p=0:=by
    rw [cubicUnitGaussSum_frequency_dvd _ p hp.ne_zero
      ((dvd_pow_self p (by decide : (2:ℕ)≠0)).trans (dvd_mul_left (p^2) h))]
    simpa using cubicUnitGaussSum_prime_power_zero p hp hprimary 0
  have hg2:cubicUnitGaussSum (h*p^2) (p^2)=0:=by
    rw [cubicUnitGaussSum_frequency_dvd _ (p^2) (pow_ne_zero _ hp.ne_zero) (dvd_mul_left (p^2) h)]
    simpa using cubicUnitGaussSum_prime_power_zero p hp hprimary 1
  have hg3:cubicUnitGaussSum (h*p^2) (p^3)= -(Ideal.absNorm (Ideal.span {p}):ℂ)^2:=by
    have hh:=cubicUnitGaussSum_prime_power_lift p hp hprimary 2 h
    rw [primeCubicGauss_trivial_nonzero p hp hprimary 3 (dvd_refl 3) h hph] at hh
    simpa only [mul_comm (p^2) h,mul_neg_one] using hh
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,pow_zero,pow_one,
    cubicUnitGaussSum_one,mul_one,one_mul,hg1,hg2,hg3,mul_zero,zero_mul,add_zero] at he
  rw [unramifiedPrimeDeletedSeries_cube_shift p hp] at he
  exact he.trans (by ring)

lemma unramifiedCubicGaussSeries_square_cube (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (s:ℂ) (hs:2<s.re) (h:Eis) (hph:¬p∣h) :
    unramifiedCubicGaussSeries s (h*p^5)=
      (1+(Ideal.absNorm (Ideal.span {p}):ℂ)^3*
        ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^3)*
        unramifiedCubicGaussSeries s (h*p^2) := by
  have he:=unramifiedCubicGaussSeries_cube_step p hp hprimary s hs h hph 2
  rw [←unramifiedCubicGaussSeries_prime_two_power p hp hprimary s hs h hph] at he
  simpa only [show 2+3=5 from rfl,add_mul,one_mul] using he

theorem unramifiedGaussResidue_square_cube (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) :
    unramifiedGaussResidue (h*p^5)=
      (1+(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹)*unramifiedGaussResidue (h*p^2) := by
  let A:ℂ→ℂ:=fun s=>1+(Ideal.absNorm (Ideal.span {p}):ℂ)^3*
    ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^3
  have hA (s:ℂ):AnalyticAt ℂ A s:=analyticAt_const.add
    (analyticAt_const.mul ((gaussPrimeWeight_analytic p hp s).pow 3))
  have he:=unramifiedGaussResidue_of_initial_relation (h*p^5) (h*p^2) 0 A (fun _=>0)
    (fun s _=>hA s) (fun _ _=>analyticAt_const) (hA _).continuousAt continuousAt_const
    (fun s hs _=>by simpa only [A,zero_mul,add_zero] using
      unramifiedCubicGaussSeries_square_cube p hp hprimary s (by linarith) h hph)
  dsimp only [A] at he
  rw [gaussPrimeWeight_center p hp] at he
  simpa only [zero_mul,add_zero] using he

lemma principalResidueTerm_square_cube (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) (u:Eisˣ) (n:ℕ) :
    principalResidueTerm (h*p^5) u n=
      (1+(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹)*principalResidueTerm (h*p^2) u n := by
  let c:=u.val*lambda^(n+2)
  have hA:=arithmeticResidueSum_frequency_cube (h*p^2) c p
    (ramifiedElement_ne_zero u (n+2)) (ramifiedElement_level u (n+2) (by omega)) hprimary
    (ramified_primary_coprime u (n+2) p hprimary).of_mul_left_right
  have hfreq:¬p∣h*(9*c):=ramified_prime_frequency_not_dvd h p hp hprimary hph u (n+2)
  rw [show (h*p^2)*p^3=h*p^5 by ring] at hA
  change _*arithmeticResidueSum (h*p^5) c*unramifiedGaussResidue ((h*p^5)*(9*c))=_
  rw [hA,show (h*p^5)*(9*c)=(h*(9*c))*p^5 by ring,
    unramifiedGaussResidue_square_cube p hp hprimary (h*(9*c)) hfreq]
  change _=(1+(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹)*
    (((3^(n+2):ℕ):ℂ)^(-(4/3:ℂ))*arithmeticResidueSum (h*p^2) c*
      unramifiedGaussResidue ((h*p^2)*(9*c)))
  rw [show (h*p^2)*(9*c)=(h*(9*c))*p^2 by ring]
  ring

lemma principalArithmeticResidue_square_cube (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) :
    principalArithmeticResidue (h*p^5)=
      (1+(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹)*principalArithmeticResidue (h*p^2) := by
  have hh:h≠0:=fun he=>hph (he▸dvd_zero p)
  let N:=max (ramifiedFrequencyBound (h*p^5)+1) (ramifiedFrequencyBound (h*p^2)+1)
  rw [principalArithmeticResidue_eq_sum (h*p^5) (mul_ne_zero hh (pow_ne_zero _ hp.ne_zero)) N (le_max_left _ _),
    principalArithmeticResidue_eq_sum (h*p^2) (mul_ne_zero hh (pow_ne_zero _ hp.ne_zero)) N (le_max_right _ _)]
  simp_rw [principalResidueTerm_square_cube p hp hprimary h hph,←Finset.mul_sum]
  ring

theorem sourceArithmeticResidue_square_cube (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) :
    sourceArithmeticResidue (h*p^5)=
      (1+(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹)*sourceArithmeticResidue (h*p^2) := by
  have hm:ShortDraftTrace.breveE (cuspFrequency (h*p^5))=
      ShortDraftTrace.breveE (cuspFrequency (h*p^2)):=by
    rw [show h*p^5=(((h*p^2)*p)*p)*p by ring]
    rw [sourceRayPhase_mul_primary _ p hprimary,sourceRayPhase_mul_primary _ p hprimary,
      sourceRayPhase_mul_primary _ p hprimary]
  have hp9:¬p∣9*h:=by
    have hh:=ramified_prime_frequency_not_dvd h p hp hprimary hph (1:Eisˣ) 0
    simpa only [Units.val_one,pow_zero,one_mul,mul_one,mul_comm 9 h] using hh
  simp only [sourceArithmeticResidue,hm]
  split_ifs
  · rw [principalArithmeticResidue_square_cube p hp hprimary h hph,
      show 9*(h*p^5)=(9*h)*p^5 by ring,
      unramifiedGaussResidue_square_cube p hp hprimary (9*h) hp9,
      show 9*(h*p^2)=(9*h)*p^2 by ring]
    ring
  · ring

end

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

lemma sourceArithmeticResidue_prime_pow_mod (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (h:Eis) (hh:h≠0) (n:ℕ) :
    sourceArithmeticResidue (h*p^n)=sourceArithmeticResidue (h*p^(n%3)) := by
  induction n using Nat.strong_induction_on with
  | h n ih=>
    by_cases hn:n<3
    · rw [Nat.mod_eq_of_lt hn]
    · have hn3:3≤n:=by omega
      have he:h*p^n=(h*p^(n-3))*p^3:=by rw [mul_assoc,←pow_add,Nat.sub_add_cancel hn3]
      rw [he,sourceArithmeticResidue_prime_cube p hp hprimary _ (mul_ne_zero hh (pow_ne_zero _ hp.ne_zero)),
        ih (n-3) (by omega)]
      have hm:(n-3)%3=n%3:=by omega
      rw [hm]

theorem sourceArithmeticResidue_prime_square (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) :
    sourceArithmeticResidue (h*p^2)=0 := by
  have hh:h≠0:=fun he=>hph (he▸dvd_zero p)
  have he:=sourceArithmeticResidue_square_cube p hp hprimary h hph
  rw [show h*p^5=(h*p^2)*p^3 by ring,
    sourceArithmeticResidue_prime_cube p hp hprimary _ (mul_ne_zero hh (pow_ne_zero _ hp.ne_zero))] at he
  have hq:(Ideal.absNorm (Ideal.span {p}):ℂ)≠0:=Nat.cast_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))
  have hz:(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*sourceArithmeticResidue (h*p^2)=0:=by
    linear_combination -he
  exact (mul_eq_zero.mp hz).resolve_left (inv_ne_zero hq)

theorem sourceArithmeticResidue_prime_power_table (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) (n:ℕ) :
    sourceArithmeticResidue (h*p^n)=
      if n%3=0 then sourceArithmeticResidue h
      else if n%3=1 then
        (Ideal.absNorm (Ideal.span {p}):ℂ)^(-(2/3:ℂ))*
          primeCubicGauss p hp hprimary 2 (9*h)*sourceArithmeticResidue h
      else 0 := by
  have hh:h≠0:=fun he=>hph (he▸dvd_zero p)
  rw [sourceArithmeticResidue_prime_pow_mod p hp hprimary h hh n]
  split_ifs with h0 h1
  · simp only [h0,pow_zero,mul_one]
  · simp only [h1,pow_one]
    exact sourceArithmeticResidue_prime_factor p hp hprimary h hph
  · have hn:n%3=2:=by omega
    rw [hn,sourceArithmeticResidue_prime_square p hp hprimary h hph]

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

end CubicEisenstein

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.SquarefreeCoefficients
namespace OAI

noncomputable section

namespace CubicEisenstein

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

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss UniqueFactorizationMonoid
local notation "Eis" => ActualEisensteinCubic.O

lemma thetaSquarefreePart_squarefree (I:Ideal Eis) : Squarefree (thetaSquarefreePart I) := by
  apply IdealMobiusDivisorSum.squarefree_support_product
  exact Finset.filter_subset _ _

lemma thetaParts_mul_cube (I:Ideal Eis) (hI:I≠0)
    (he:∀P∈normalizedFactors I,(normalizedFactors I).count P%3≠2) :
    thetaSquarefreePart I*thetaCubePart I ^3=I := by
  rw [thetaSquarefreePart,Finset.prod_filter,thetaCubePart,←Finset.prod_pow,←Finset.prod_mul_distrib]
  calc
    _=∏P∈primeSupport I,P^((normalizedFactors I).count P):=by
      apply Finset.prod_congr rfl
      intro P hP
      have hp:=he P (Multiset.mem_toFinset.mp hP)
      have hm:(normalizedFactors I).count P%3=0 ∨ (normalizedFactors I).count P%3=1:=by omega
      rcases hm with hm|hm
      · rw [if_neg (by omega),one_mul,←pow_mul]
        congr 1
        omega
      · rw [if_pos hm,←pow_mul,←pow_succ']
        congr 1
        omega
    _=(normalizedFactors I).prod:=(Finset.prod_multiset_count (normalizedFactors I)).symm
    _=I:=Ideal.prod_normalizedFactors_eq_self hI

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

open ActualEisensteinCubic ConcreteTraceCRT CubicKubota CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

end CubicEisenstein

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

namespace CompletedGauss

section
open ActualEisensteinCubic ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

lemma angularFactor_norm_le_one (a : ActualEisensteinCubic.O) : ‖FiniteGaussPhase.angularFactor a‖≤1 := by
  by_cases ha : a=0
  · subst a; simp [FiniteGaussPhase.angularFactor]
  · exact (FiniteGaussPhase.norm_angularFactor a ha).le

lemma cubicRow_norm_le_one (I : Ideal ActualEisensteinCubic.O) (hI : primaryGenerator I≠0) (x : ActualEisensteinCubic.O⧸I) :
    ‖cubicRow I hI x‖≤1 := by
  unfold cubicRow
  rw [norm_prod]
  apply Finset.prod_le_one
  · intro i hi; exact norm_nonneg _
  · intro i hi
    exact FiniteRayExpansion.norm_char_le_one _ _

lemma gaussTwo_norm_le_sqrt (I : Ideal ActualEisensteinCubic.O) (hI : primaryGenerator I≠0) :
    ‖gaussTwo I hI‖≤Real.sqrt (Ideal.absNorm I:ℝ) := by
  let n := primaryGenerator I
  let : Finite (ActualEisensteinCubic.O⧸Ideal.span {n}) := finite_quotient_span hI
  let : Fintype (ActualEisensteinCubic.O⧸Ideal.span {n}) := Fintype.ofFinite _
  let e := Ideal.quotEquivOfEq (primaryGenerator_spec I hI).1
  let ψ := eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates n hI
  have hN : 0<(Ideal.absNorm I:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun h=>primaryGenerator_ne_zero_ideal I hI (Ideal.absNorm_eq_zero_iff.mp h))
  have hn : ‖eisEmbedding n‖=Real.sqrt (Ideal.absNorm I:ℝ) := primaryGenerator_norm I hI
  have hsum : ‖∑x : ActualEisensteinCubic.O⧸Ideal.span {n},cubicRow I hI (e x)*ψ x‖≤(Ideal.absNorm I:ℝ) := by
    calc
      _≤∑x : ActualEisensteinCubic.O⧸Ideal.span {n},‖cubicRow I hI (e x)*ψ x‖ := norm_sum_le _ _
      _≤∑_x : ActualEisensteinCubic.O⧸Ideal.span {n},(1:ℝ) := by
        apply Finset.sum_le_sum
        intro x hx
        rw [norm_mul,AddChar.norm_apply,mul_one]
        exact cubicRow_norm_le_one I hI (e x)
      _=(Ideal.absNorm I:ℝ) := by
        simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
        congr 1
        rw [←Nat.card_eq_fintype_card,←Submodule.cardQuot_apply,←Ideal.absNorm_apply,
          (primaryGenerator_spec I hI).1]
  change ‖(∑x : ActualEisensteinCubic.O⧸Ideal.span {n},cubicRow I hI (e x)*ψ x)/(‖eisEmbedding n‖:ℂ)‖≤_
  rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _),hn]
  apply (div_le_iff₀ (Real.sqrt_pos.mpr hN)).mpr
  simpa only [Real.mul_self_sqrt hN.le] using hsum

lemma columnWeight_div_sqrt_norm_le_one (Ψ : ActualEisensteinCubic.O→*ℂ) (hΨ : ∀a,‖Ψ a‖≤1) (I : Ideal ActualEisensteinCubic.O) :
    ‖columnWeight Ψ I/(Real.sqrt (Ideal.absNorm I:ℝ):ℂ)‖≤1 := by
  by_cases hI : Squarefree I ∧ primaryGenerator I≠0
  · have hN : 0<(Ideal.absNorm I:ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (fun h=>primaryGenerator_ne_zero_ideal I hI.2 (Ideal.absNorm_eq_zero_iff.mp h))
    rw [columnWeight_eq Ψ I hI.1 hI.2,norm_div,norm_mul,norm_mul,norm_star,
      FiniteGaussPhase.norm_angularFactor _ hI.2,one_mul,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
    apply (div_le_one (Real.sqrt_pos.mpr hN)).mpr
    exact (mul_le_of_le_one_right (norm_nonneg _) (hΨ _)).trans (gaussTwo_norm_le_sqrt I hI.2)
  · simp only [columnWeight,squarefreeGaussCoefficient,dif_neg hI,zero_mul,zero_div,norm_zero,zero_le_one]

lemma cubeWeight_norm_le_one (Ψ : ActualEisensteinCubic.O→*ℂ) (hΨ : ∀a,‖Ψ a‖≤1) (I : Ideal ActualEisensteinCubic.O) :
    ‖cubeWeight Ψ I‖≤1 := by
  by_cases hI : I=0
  · subst I; simp
  have hN : (1:ℝ)≤(Ideal.absNorm I:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun h=>hI (Ideal.absNorm_eq_zero_iff.mp h))
  have hn : 0<(Ideal.absNorm I:ℝ) := lt_of_lt_of_le zero_lt_one hN
  change ‖star (FiniteGaussPhase.angularFactor (primaryGenerator I))^3*
    Ψ (primaryGenerator I)^3/(Ideal.absNorm I:ℂ)‖≤1
  rw [norm_div,norm_mul,norm_pow,norm_star,norm_pow,Complex.norm_natCast]
  apply (div_le_one hn).mpr
  apply le_trans _ hN
  calc
    _≤(1:ℝ)*1 := mul_le_mul
      (pow_le_one₀ (norm_nonneg _) (angularFactor_norm_le_one _))
      (pow_le_one₀ (norm_nonneg _) (hΨ _)) (pow_nonneg (norm_nonneg _) _) zero_le_one
    _=1 := one_mul _

end

open Filter MeasureTheory
open scoped Classical BigOperators Topology ContDiff

section
open ActualEisensteinCubic CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

lemma completedMellinLength_pos (p : CompletedMellinIndex) : 0<completedMellinLength p :=
  mul_pos (nonzeroIdeal_norm_pos p.1) (pow_pos (nonzeroIdeal_norm_pos p.2) 3)

lemma completedMellinCoefficient_norm_le_one (Ψ : ActualEisensteinCubic.O→*ℂ) (hΨ : ∀a,‖Ψ a‖≤1)
    (p : CompletedMellinIndex) : ‖completedMellinCoefficient Ψ p‖≤1 := by
  rw [completedMellinCoefficient,norm_mul]
  exact (mul_le_mul_of_nonneg_right (columnWeight_div_sqrt_norm_le_one Ψ hΨ p.1.1)
    (norm_nonneg _)).trans (by simpa only [one_mul] using cubeWeight_norm_le_one Ψ hΨ p.2.1)

lemma nonzeroIdeal_norm_rpow_summable (σ : ℝ) (hσ : 1<σ) :
    Summable (fun I : NonzeroIdeal=>(Ideal.absNorm I.1:ℝ)^(-σ)) := by
  have h := (fullIdealWeight_summable_norm (σ:ℂ) (by simpa using hσ)).subtype (fun I=>I≠0)
  apply h.congr
  intro I
  change ‖fullIdealWeight (σ:ℂ) I.1‖=(Ideal.absNorm I.1:ℝ)^(-σ)
  rw [fullIdealWeight,if_neg I.2]
  simpa only [Complex.neg_re,Complex.ofReal_re,Complex.ofReal_natCast] using
    (Complex.norm_cpow_eq_rpow_re_of_pos (nonzeroIdeal_norm_pos I) (-(σ:ℂ)))

lemma completedMellinLength_rpow (p : CompletedMellinIndex) (σ : ℝ) :
    (completedMellinLength p)^(-σ)=
      (Ideal.absNorm p.1.1:ℝ)^(-σ)*(Ideal.absNorm p.2.1:ℝ)^(-(3*σ)) := by
  rw [completedMellinLength,Real.mul_rpow (nonzeroIdeal_norm_pos p.1).le
    (pow_nonneg (nonzeroIdeal_norm_pos p.2).le _),←Real.rpow_natCast_mul (nonzeroIdeal_norm_pos p.2).le]
  congr 1
  congr 1
  ring

theorem completedMellinCoefficient_summable (Ψ : ActualEisensteinCubic.O→*ℂ) (hΨ : ∀a,‖Ψ a‖≤1)
    (σ : ℝ) (hσ : 1<σ) :
    Summable (fun p=>‖completedMellinCoefficient Ψ p‖*(completedMellinLength p)^(-σ)) := by
  have hI := nonzeroIdeal_norm_rpow_summable σ hσ
  have hJ := nonzeroIdeal_norm_rpow_summable (3*σ) (by linarith)
  have hp := hI.mul_of_nonneg hJ (fun I=>Real.rpow_nonneg (nonzeroIdeal_norm_pos I).le _)
    (fun J=>Real.rpow_nonneg (nonzeroIdeal_norm_pos J).le _)
  apply hp.of_nonneg_of_le
  · intro p; exact mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (completedMellinLength_pos p).le _)
  · intro p
    rw [←completedMellinLength_rpow]
    exact mul_le_of_le_one_left (Real.rpow_nonneg (completedMellinLength_pos p).le _)
      (completedMellinCoefficient_norm_le_one Ψ hΨ p)

theorem completedT_eq_mellin_index (Ψ : ActualEisensteinCubic.O→*ℂ) (W : ℝ→ℂ)
    (hW : HasCompactSupport W) (X : ℝ) (hX : 0<X) :
    completedT Ψ W X=∑'p : CompletedMellinIndex,
      completedMellinCoefficient Ψ p*Vstar W (completedMellinLength p/X) := by
  have hfull := completedT_summable Ψ W hW X hX
  have hinj : Function.Injective (fun p : CompletedMellinIndex=>(p.1.1,p.2.1)) := by
    intro p q h
    apply Prod.ext <;> apply Subtype.ext
    · exact congrArg Prod.fst h
    · exact congrArg Prod.snd h
  have hsub := hfull.comp_injective hinj
  calc
    completedT Ψ W X=∑'I : NonzeroIdeal,∑'J : Ideal ActualEisensteinCubic.O,summand Ψ W X I.1 J := by
      symm
      unfold completedT
      apply tsum_subtype_eq_of_support_subset
        (s:={I:Ideal ActualEisensteinCubic.O|I≠0}) (f:=fun I:Ideal ActualEisensteinCubic.O=>∑'J:Ideal ActualEisensteinCubic.O,summand Ψ W X I J)
      intro I hI hz
      subst I
      exact hI (by simp only [summand_zero_left,tsum_zero])
    _=∑'I : NonzeroIdeal,∑'J : NonzeroIdeal,summand Ψ W X I.1 J.1 := by
      apply tsum_congr
      intro I
      symm
      apply tsum_subtype_eq_of_support_subset
        (s:={J:Ideal ActualEisensteinCubic.O|J≠0}) (f:=fun J:Ideal ActualEisensteinCubic.O=>summand Ψ W X I.1 J)
      intro J hJ hz
      subst J
      exact hJ (summand_zero_right Ψ W X I.1)
    _=∑'p : CompletedMellinIndex,summand Ψ W X p.1.1 p.2.1 := hsub.tsum_prod.symm
    _=_ := rfl

theorem completedT_initial_mellin (Ψ : ActualEisensteinCubic.O→*ℂ) (hΨ : ∀a,‖Ψ a‖≤1)
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (X : ℝ) (hX : 0<X) :
    completedT Ψ W X=(1/(2*Real.pi):ℂ)*∫t : ℝ,
      mellin (Vstar W) ((3/2:ℂ)+t*Complex.I)*(X:ℂ)^((3/2:ℂ)+t*Complex.I)*
        completedDirichletSeries Ψ ((2:ℂ)+t*Complex.I) := by
  let : Countable ActualEisensteinCubic.O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
  let : Countable (Ideal ActualEisensteinCubic.O) := ConcretePrimeRowBridge.idealGenerator_injective.countable
  have hWc : HasCompactSupport W :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsupp
  rw [completedT_eq_mellin_index Ψ W hWc X hX]
  have h := weightedMellin_inversion completedMellinLength completedMellinLength_pos
    (completedMellinCoefficient Ψ) (3/2)
    (completedMellinCoefficient_summable Ψ hΨ (3/2) (by norm_num))
    (Vstar W) a b ha (Vstar_support W a b hsupp) (Vstar_contDiff W a b ha hsupp hW) X hX
  have hd (t : ℝ) : completedDirichletSeries Ψ ((2:ℂ)+t*Complex.I)=
      ∑'p : CompletedMellinIndex,completedMellinCoefficient Ψ p*
        (completedMellinLength p:ℂ)^(-((3/2:ℂ)+t*Complex.I)) := by
    unfold completedDirichletSeries
    apply tsum_congr
    intro p
    congr 2
    ring
  simpa only [hd,Complex.ofReal_div,Complex.ofReal_ofNat] using h

end

open ActualEisensteinCubic
local notation "O" => ActualEisensteinCubic.O

lemma weighted_vertical_series_continuous {α : Type*}
    (r : α→ℝ) (hr : ∀i,0< r i) (c : α→ℂ) (σ : ℝ)
    (hc : Summable (fun i=>‖c i‖*(r i)^(-σ))) :
    Continuous (fun t : ℝ=>∑'i,c i*(r i:ℂ)^(-((σ:ℂ)+t*Complex.I))) := by
  apply continuous_tsum
    (fun i=>continuous_const.mul (positive_cpow_negative_vertical_continuous (r i) σ (hr i))) hc
  intro i t
  change ‖c i*(r i:ℂ)^(-((σ:ℂ)+t*Complex.I))‖≤‖c i‖*(r i)^(-σ)
  rw [norm_mul,positive_cpow_negative_vertical_norm _ _ _ (hr i)]

lemma weighted_vertical_series_norm {α : Type*}
    (r : α→ℝ) (hr : ∀i,0< r i) (c : α→ℂ) (σ : ℝ)
    (hc : Summable (fun i=>‖c i‖*(r i)^(-σ))) (t : ℝ) :
    ‖∑'i,c i*(r i:ℂ)^(-((σ:ℂ)+t*Complex.I))‖≤∑'i,‖c i‖*(r i)^(-σ) := by
  have he (i : α) : ‖c i*(r i:ℂ)^(-((σ:ℂ)+t*Complex.I))‖=‖c i‖*(r i)^(-σ) := by
    rw [norm_mul,positive_cpow_negative_vertical_norm _ _ _ (hr i)]
  simpa only [he] using norm_tsum_le_tsum_norm (hc.congr (fun i=>(he i).symm))

lemma completedDirichletSeries_initial (Ψ : ActualEisensteinCubic.O→*ℂ) (t : ℝ) :
    completedDirichletSeries Ψ ((2:ℂ)+t*Complex.I)=
      ∑'p : CompletedMellinIndex,completedMellinCoefficient Ψ p*
        (completedMellinLength p:ℂ)^(-((3/2:ℂ)+t*Complex.I)) := by
  unfold completedDirichletSeries
  apply tsum_congr
  intro p
  congr 2
  ring

theorem completedT_initial_mellin_integrable (Ψ : ActualEisensteinCubic.O→*ℂ) (hΨ : ∀a,‖Ψ a‖≤1)
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (X : ℝ) (hX : 0<X) :
    Integrable (fun t : ℝ=>mellin (Vstar W) ((3/2:ℂ)+t*Complex.I)*
      (X:ℂ)^((3/2:ℂ)+t*Complex.I)*completedDirichletSeries Ψ ((2:ℂ)+t*Complex.I)) := by
  have hsum := completedMellinCoefficient_summable Ψ hΨ (3/2) (by norm_num)
  have hc := weighted_vertical_series_continuous completedMellinLength completedMellinLength_pos
    (completedMellinCoefficient Ψ) (3/2) hsum
  have hb := weighted_vertical_series_norm completedMellinLength completedMellinLength_pos
    (completedMellinCoefficient Ψ) (3/2) hsum
  have hmi : Integrable (fun t : ℝ=>mellin (Vstar W) ((3/2:ℂ)+t*Complex.I)) := by
    simpa only [Complex.VerticalIntegrable,Complex.ofReal_div,Complex.ofReal_ofNat] using
      (compactMellin_vertical_integrable (Vstar W) a b ha (Vstar_support W a b hsupp)
        (Vstar_contDiff W a b ha hsupp hW) (3/2))
  have hbase := vertical_power_mul_integrable _ hmi X (3/2) hX
  have hi := hbase.mul_bdd hc.aestronglyMeasurable (Filter.Eventually.of_forall hb)
  simpa only [Complex.ofReal_div,Complex.ofReal_ofNat,completedDirichletSeries_initial,
    mul_comm (mellin (Vstar W) _)] using hi

end CompletedGauss

open scoped BigOperators Classical
open Finset AddChar MulChar EisensteinEmbedding

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Mellin.VerticalContourShift
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

namespace VerticalContourShift
open Filter MeasureTheory
open scoped Classical Topology

lemma gaussian_regulator_norm (ε σ t : ℝ) :
    ‖Complex.exp ((ε:ℂ)*((σ:ℂ)+t*Complex.I)^2)‖=Real.exp (ε*(σ^2-t^2)) := by
  rw [Complex.norm_exp]
  congr 1
  simp only [pow_two,Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im]
  ring

lemma gaussian_regulator_norm_le (ε σ t : ℝ) (hε0 : 0≤ε) (hε1 : ε≤1) :
    ‖Complex.exp ((ε:ℂ)*((σ:ℂ)+t*Complex.I)^2)‖≤Real.exp (σ^2) := by
  rw [gaussian_regulator_norm]
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg σ,sq_nonneg t,mul_nonneg hε0 (sq_nonneg t),
    mul_nonneg (sub_nonneg.mpr hε1) (sq_nonneg σ)]

lemma gaussianRegulatorSequence_pos (n : ℕ) : 0<gaussianRegulatorSequence n := by
  unfold gaussianRegulatorSequence
  positivity

lemma gaussianRegulatorSequence_le_one (n : ℕ) : gaussianRegulatorSequence n≤1 := by
  unfold gaussianRegulatorSequence
  apply (div_le_one (by positivity)).mpr
  linarith [Nat.cast_nonneg (α:=ℝ) n]

lemma gaussianRegulatorSequence_tendsto : Tendsto gaussianRegulatorSequence atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

theorem gaussian_regulator_integral_tendsto (g : ℝ→ℂ) (hg : Integrable g) (σ : ℝ) :
    Tendsto (fun n : ℕ=>∫t : ℝ,
      Complex.exp ((gaussianRegulatorSequence n:ℂ)*((σ:ℂ)+t*Complex.I)^2)*g t)
      atTop (𝓝 (∫t : ℝ,g t)) := by
  apply tendsto_integral_of_dominated_convergence
    (fun t : ℝ=>Real.exp (σ^2)*‖g t‖)
  · intro n
    have hc : Continuous (fun t : ℝ=>
        Complex.exp ((gaussianRegulatorSequence n:ℂ)*((σ:ℂ)+t*Complex.I)^2)) := by fun_prop
    exact hc.aestronglyMeasurable.mul hg.aestronglyMeasurable
  · exact hg.norm.const_mul _
  · intro n
    exact Filter.Eventually.of_forall (fun t=>by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right
        (gaussian_regulator_norm_le _ σ t (gaussianRegulatorSequence_pos n).le
          (gaussianRegulatorSequence_le_one n)) (norm_nonneg _))
  · filter_upwards with t
    have hε : Tendsto (fun n : ℕ=>(gaussianRegulatorSequence n:ℂ)) atTop (𝓝 0) :=
      by simpa only [Function.comp_def,Complex.ofReal_zero] using
        Complex.continuous_ofReal.continuousAt.tendsto.comp gaussianRegulatorSequence_tendsto
    have he := (Complex.continuous_exp.tendsto 0).comp
      (by simpa only [zero_mul] using hε.mul_const (((σ:ℂ)+t*Complex.I)^2))
    simpa only [Function.comp_def,Complex.exp_zero,one_mul] using he.mul_const (g t)

lemma rpow_between_endpoints (y a b σ : ℝ) (hy : 0<y) (ha : a≤σ) (hb : σ≤b) :
    y^σ≤y^a+y^b := by
  by_cases h1 : 1≤y
  · exact (Real.rpow_le_rpow_of_exponent_le h1 hb).trans
      (le_add_of_nonneg_left (Real.rpow_nonneg hy.le a))
  · exact (Real.rpow_le_rpow_of_exponent_ge hy (le_of_not_ge h1) ha).trans
      (le_add_of_nonneg_right (Real.rpow_nonneg hy.le b))

theorem mellin_uniform_strip_bound (f : ℝ→ℂ) (a b : ℝ)
    (ha : MellinConvergent f (a:ℂ)) (hb : MellinConvergent f (b:ℂ)) :
    ∃C : ℝ,0≤C ∧ ∀s : ℂ,a≤ s.re→s.re≤b→‖mellin f s‖≤C := by
  let B : ℝ→ℝ := fun y=>‖(y:ℂ)^((a:ℂ)-1)*f y‖+‖(y:ℂ)^((b:ℂ)-1)*f y‖
  have hB : IntegrableOn B (Set.Ioi 0) := by
    exact ha.norm.add hb.norm
  refine ⟨∫y in Set.Ioi 0,B y,integral_nonneg (fun y=>add_nonneg (norm_nonneg _) (norm_nonneg _)),?_⟩
  intro s hsa hsb
  unfold mellin
  apply norm_integral_le_of_norm_le hB
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  change 0<y at hy
  have hp := rpow_between_endpoints y (a-1) (b-1) (s.re-1) hy (by linarith) (by linarith)
  change ‖(y:ℂ)^(s-1)*f y‖≤B y
  dsimp only [B]
  simp only [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hy,Complex.sub_re,
    Complex.ofReal_re,Complex.one_re]
  simpa only [add_mul] using mul_le_mul_of_nonneg_right hp (norm_nonneg (f y))

end VerticalContourShift

namespace GaussianMoment

lemma gaussian_le_inverse_quadratic (c t:ℝ) (hc:0<c) :
    Real.exp (-c*t^2)≤(1+2/c)/(1+t^2) := by
  have h0:Real.exp (-c*t^2)≤1:=by
    apply Real.exp_le_one_iff.mpr
    nlinarith [sq_nonneg t]
  have h1:t^2*Real.exp (-c*t^2)≤2/c:=by
    have hm:=gaussian_moment_term_bound (t^2) c (sq_nonneg t) hc
    have he:Real.exp (-(c*t^2/2))≤1:=by
      apply Real.exp_le_one_iff.mpr
      nlinarith [sq_nonneg t]
    exact hm.trans (by simpa only [mul_one] using
      mul_le_mul_of_nonneg_left he (div_nonneg (by norm_num) hc.le))
  apply (le_div_iff₀ (by positivity : 0<1+t^2)).mpr
  nlinarith

lemma linear_height_young (A ε t:ℝ) (hε:0<ε) :
    A*|t|≤ε*t^2/2+A^2/(2*ε) := by
  have hs:0≤ε^2*t^2-2*ε*A*|t|+A^2:=by
    calc
      0≤(ε*|t|-A)^2:=sq_nonneg _
      _=ε^2*t^2-2*ε*A*|t|+A^2:=by rw [sub_sq,mul_pow,sq_abs];ring
  apply le_of_mul_le_mul_left (a := 2*ε) ?_
    (mul_pos (by norm_num : (0:ℝ)<2) hε)
  calc
    2*ε*(A*|t|)≤ε^2*t^2+A^2:=by nlinarith [hs]
    _=2*ε*(ε*t^2/2+A^2/(2*ε)):=by field_simp

theorem gaussian_regulator_strip_bound (a b A B ε:ℝ) (hB:0≤B) (hε:0<ε)
    (f:ℂ→ℂ)
    (hf:∀σ:ℝ,σ∈Set.Icc a b→∀t:ℝ,
      ‖f ((σ:ℂ)+(t:ℂ)*Complex.I)‖≤B*Real.exp (A*|t|))
    (σ t:ℝ) (hσ:σ∈Set.Icc a b) :
    ‖Complex.exp ((ε:ℂ)*((σ:ℂ)+(t:ℂ)*Complex.I)^2)*
        f ((σ:ℂ)+(t:ℂ)*Complex.I)‖≤
      (B*Real.exp (ε*(max |a| |b|)^2+A^2/(2*ε))*(1+4/ε))/(1+t^2) := by
  let R:ℝ:=max |a| |b|
  have hR:0≤R:=le_trans (abs_nonneg a) (le_max_left _ _)
  have hsabs:|σ|≤R:=abs_le_max_abs_abs hσ.1 hσ.2
  have hs:σ^2≤R^2:=by
    calc
      _=|σ|^2:=(sq_abs σ).symm
      _≤R^2:=pow_le_pow_left₀ (abs_nonneg σ) hsabs 2
  have hre:((ε:ℂ)*((σ:ℂ)+(t:ℂ)*Complex.I)^2).re=ε*(σ^2-t^2):=by
    simp [pow_two,Complex.mul_re,Complex.mul_im]

  have hE:ε*(σ^2-t^2)+A*|t|≤
      (ε*R^2+A^2/(2*ε))-(ε/2)*t^2:=by
    have hy:=linear_height_young A ε t hε
    nlinarith
  have hg:=gaussian_le_inverse_quadratic (ε/2) t (by positivity)
  have hg':Real.exp (-(ε/2)*t^2)≤(1+4/ε)/(1+t^2):=by
    convert (preTransparency := .instances) hg using 1 ;field_simp ;ring
  rw [norm_mul,Complex.norm_exp,hre]
  calc
    _≤Real.exp (ε*(σ^2-t^2))*(B*Real.exp (A*|t|)):=
      mul_le_mul_of_nonneg_left (hf σ hσ t) (Real.exp_pos _).le
    _=B*Real.exp (ε*(σ^2-t^2)+A*|t|):=by rw [Real.exp_add];ring
    _≤B*Real.exp ((ε*R^2+A^2/(2*ε))-(ε/2)*t^2):=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hE) hB
    _=(B*Real.exp (ε*R^2+A^2/(2*ε)))*Real.exp (-(ε/2)*t^2):=by
      rw [Real.exp_sub,div_eq_mul_inv,←Real.exp_neg,neg_mul]
      ring
    _≤(B*Real.exp (ε*R^2+A^2/(2*ε)))*((1+4/ε)/(1+t^2)):=
      mul_le_mul_of_nonneg_left hg' (mul_nonneg hB (Real.exp_pos _).le)
    _=_:=by dsimp only [R];ring

theorem gaussian_regulator_strip_decay (a b A B ε:ℝ) (_hab:a≤b) (_hA:0≤A)
    (hB:0≤B) (hε:0<ε) (f:ℂ→ℂ)
    (hf:∀σ:ℝ,σ∈Set.Icc a b→∀t:ℝ,
      ‖f ((σ:ℂ)+(t:ℂ)*Complex.I)‖≤B*Real.exp (A*|t|)) :
    ∃K:ℝ,0≤K ∧ ∀σ:ℝ,σ∈Set.Icc a b→∀t:ℝ,
      ‖Complex.exp ((ε:ℂ)*((σ:ℂ)+(t:ℂ)*Complex.I)^2)*
        f ((σ:ℂ)+(t:ℂ)*Complex.I)‖≤K/(1+t^2) := by
  refine ⟨B*Real.exp (ε*(max |a| |b|)^2+A^2/(2*ε))*(1+4/ε),by positivity,?_⟩
  intro σ hσ t
  exact gaussian_regulator_strip_bound a b A B ε hB hε f hf σ t hσ

end GaussianMoment

namespace VerticalContourShift
open Filter MeasureTheory
open scoped Classical Topology

theorem integral_eq_of_exponential_strip_growth
    (f : ℂ→ℂ) (a b A B : ℝ) (hab : a≤b) (hA : 0≤A) (hB : 0≤B)
    (hdiff : ∀z : ℂ,a≤z.re→z.re≤b→DifferentiableAt ℂ f z)
    (ha : Integrable (fun t : ℝ=>f ((a:ℂ)+t*Complex.I)))
    (hb : Integrable (fun t : ℝ=>f ((b:ℂ)+t*Complex.I)))
    (hbound : ∀σ∈Set.Icc a b,∀t : ℝ,‖f ((σ:ℂ)+t*Complex.I)‖≤B*Real.exp (A*|t|)) :
    (∫t : ℝ,f ((a:ℂ)+t*Complex.I))=∫t : ℝ,f ((b:ℂ)+t*Complex.I) := by
  let F : ℕ→ℂ→ℂ := fun n z=>Complex.exp ((gaussianRegulatorSequence n:ℂ)*z^2)*f z
  have hreg (n : ℕ) : Continuous (fun z : ℂ=>Complex.exp ((gaussianRegulatorSequence n:ℂ)*z^2)) := by
    fun_prop
  have hint (n : ℕ) (σ : ℝ) (hσ : Integrable (fun t : ℝ=>f ((σ:ℂ)+t*Complex.I))) :
      Integrable (fun t : ℝ=>F n ((σ:ℂ)+t*Complex.I)) := by
    apply hσ.bdd_mul (c:=Real.exp (σ^2))
    · exact ((hreg n).comp (by fun_prop)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun t=>gaussian_regulator_norm_le _ σ t
        (gaussianRegulatorSequence_pos n).le (gaussianRegulatorSequence_le_one n))
  have heq (n : ℕ) :
      (∫t : ℝ,F n ((a:ℂ)+t*Complex.I))=∫t : ℝ,F n ((b:ℂ)+t*Complex.I) := by
    obtain ⟨K,hK,hdec⟩ := GaussianMoment.gaussian_regulator_strip_decay a b A B
      (gaussianRegulatorSequence n) hab hA hB (gaussianRegulatorSequence_pos n) f hbound
    apply integral_eq_of_strip_decay (F n) a b K hab
    · intro z hza hzb
      have hg : Differentiable ℂ (fun w : ℂ=>Complex.exp ((gaussianRegulatorSequence n:ℂ)*w^2)) := by
        fun_prop
      exact hg.differentiableAt.mul (hdiff z hza hzb)
    · exact hint n a ha
    · exact hint n b hb
    · exact hdec
  have hleft := gaussian_regulator_integral_tendsto (fun t : ℝ=>f ((a:ℂ)+t*Complex.I)) ha a
  have hright := gaussian_regulator_integral_tendsto (fun t : ℝ=>f ((b:ℂ)+t*Complex.I)) hb b
  change Tendsto (fun n=>∫t : ℝ,F n ((a:ℂ)+t*Complex.I)) atTop
    (𝓝 (∫t : ℝ,f ((a:ℂ)+t*Complex.I))) at hleft
  change Tendsto (fun n=>∫t : ℝ,F n ((b:ℂ)+t*Complex.I)) atTop
    (𝓝 (∫t : ℝ,f ((b:ℂ)+t*Complex.I))) at hright
  simp only [heq] at hleft
  exact tendsto_nhds_unique hleft hright

end VerticalContourShift

namespace CubicGammaExponential
open scoped BigOperators Classical
open MeasureTheory
open Finset AddChar MulChar EisensteinEmbedding

lemma norm_Gamma_le_real (z : ℂ) (hz : 0<z.re) :
    ‖Complex.Gamma z‖≤Real.Gamma z.re := by
  rw [Complex.Gamma_eq_integral hz,Real.Gamma_eq_integral hz]
  unfold Complex.GammaIntegral
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  dsimp only
  rw [norm_mul,Complex.norm_of_nonneg (Real.exp_pos (-x)).le,
    Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp

lemma norm_sin_le_exp_abs_im (z : ℂ) :
    ‖Complex.sin z‖≤Real.exp |z.im| := by
  rw [Complex.sin,norm_div,norm_mul,Complex.norm_I,mul_one]
  norm_num only [Complex.norm_ofNat]
  apply (div_le_iff₀ (by norm_num : (0:ℝ)<2)).mpr
  calc
    _ ≤ ‖Complex.exp (-z*Complex.I)‖+‖Complex.exp (z*Complex.I)‖ := norm_sub_le _ _
    _ = Real.exp z.im+Real.exp (-z.im) := by simp [Complex.norm_exp]
    _ ≤ Real.exp |z.im|+Real.exp |z.im| :=
      add_le_add (Real.exp_le_exp.mpr (le_abs_self _)) (Real.exp_le_exp.mpr (neg_le_abs _))
    _ = _ := by ring

lemma Gamma_ne_zero_of_im_ne_zero (z : ℂ) (hz : z.im≠0) : Complex.Gamma z≠0 := by
  apply Complex.Gamma_ne_zero
  intro n he
  apply hz
  have h:=congrArg Complex.im he
  simpa using h

lemma inverse_Gamma_reflection (z : ℂ) (hz : z.im≠0) :
    (Complex.Gamma z)⁻¹=Complex.Gamma (1-z)*Complex.sin (Real.pi*z)/Real.pi := by
  have hg:=Gamma_ne_zero_of_im_ne_zero z hz
  have hh:=Gamma_ne_zero_of_im_ne_zero (1-z) (by simpa using hz)
  have hp : (Real.pi:ℂ)≠0:=Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hs : Complex.sin (Real.pi*z)≠0 := by
    intro hs
    have he:=Complex.Gamma_mul_Gamma_one_sub z
    rw [hs,div_zero] at he
    exact (mul_ne_zero hg hh) he
  apply mul_left_cancel₀ hg
  rw [mul_inv_cancel₀ hg]
  symm
  calc
    _ = (Complex.Gamma z*Complex.Gamma (1-z))*Complex.sin (Real.pi*z)/Real.pi := by ring
    _ = 1 := by
      rw [Complex.Gamma_mul_Gamma_one_sub,div_mul_cancel₀ _ hs,div_self hp]

lemma inverse_Gamma_norm_of_left (z : ℂ) (hz : z.re<1) (hi : z.im≠0) :
    ‖(Complex.Gamma z)⁻¹‖≤
      (Real.Gamma (1-z.re)/Real.pi)*Real.exp (Real.pi*|z.im|) := by
  rw [inverse_Gamma_reflection z hi,norm_div,norm_mul,
    Complex.norm_of_nonneg Real.pi_pos.le]
  have hgamma:=norm_Gamma_le_real (1-z) (by simp;linarith)
  have hsin:=norm_sin_le_exp_abs_im (Real.pi*z)
  simp only [Complex.sub_re,Complex.one_re] at hgamma
  have him : |((Real.pi:ℂ)*z).im|=Real.pi*|z.im| := by
    simp [abs_mul, Real.pi_nonneg]
  rw [him] at hsin
  calc
    _ ≤ (Real.Gamma (1-z.re)*Real.exp (Real.pi*|z.im|))/Real.pi :=
      div_le_div_of_nonneg_right
        (mul_le_mul hgamma hsin (norm_nonneg _) (Real.Gamma_pos_of_pos (by linarith)).le)
        Real.pi_pos.le
    _ = _ := by ring

lemma inverse_Gamma_norm_le_shift_left (z : ℂ) (n : ℕ) (hi : 1≤|z.im|) :
    ‖(Complex.Gamma z)⁻¹‖≤‖(Complex.Gamma (z-n))⁻¹‖ := by
  have he:=congrArg norm (CubicReflectionKernel.inverse_Gamma_shift (z-n) n)
  simp only [sub_add_cancel,norm_mul] at he
  have hprod : 1≤‖∏k∈Finset.range n,(z-(n:ℂ)+k)‖ := by
    rw [norm_prod]
    apply Finset.one_le_prod
    intro k hk
    calc
      1 ≤ |z.im| := hi
      _ = |(z-(n:ℂ)+k).im| := by simp
      _ ≤ _ := Complex.abs_im_le_norm _
  rw [he]
  exact le_mul_of_one_le_left (norm_nonneg _) hprod

lemma real_Gamma_compact_bound (a b : ℝ) (ha : 0<a) :
    ∃C : ℝ,0<C ∧ ∀x∈Set.Icc a b,Real.Gamma x≤C := by
  have hc : ContinuousOn Real.Gamma (Set.Icc a b) :=
    Real.differentiableOn_Gamma_Ioi.continuousOn.mono (fun x hx=>ha.trans_le hx.1)
  obtain ⟨C,hC⟩:=(isCompact_Icc : IsCompact (Set.Icc a b)).bddAbove_image hc
  refine ⟨|C|+1,by positivity,?_⟩
  intro x hx
  exact (hC (Set.mem_image_of_mem _ hx)).trans (by linarith [le_abs_self C])

lemma inverse_Gamma_compact_strip_bound (a b : ℝ) :
    ∃C : ℝ,0<C ∧ ∀σ∈Set.Icc a b,∀t∈Set.Icc (-1:ℝ) 1,
      ‖(Complex.Gamma ((σ:ℂ)+t*Complex.I))⁻¹‖≤C := by
  have hc : Continuous (fun p : ℝ×ℝ=>
      ‖(Complex.Gamma ((p.1:ℂ)+p.2*Complex.I))⁻¹‖) :=
    (Complex.differentiable_one_div_Gamma.continuous.comp (by fun_prop)).norm
  obtain ⟨C,hC⟩:=((isCompact_Icc : IsCompact (Set.Icc a b)).prod
    (isCompact_Icc : IsCompact (Set.Icc (-1:ℝ) 1))).bddAbove_image hc.continuousOn
  refine ⟨|C|+1,by positivity,?_⟩
  intro σ hσ t ht
  exact (hC ⟨(σ,t),⟨hσ,ht⟩,rfl⟩).trans (by linarith [le_abs_self C])

theorem inverse_Gamma_strip_exp_bound (a b : ℝ) :
    ∃C : ℝ,0<C ∧ ∀σ∈Set.Icc a b,∀t : ℝ,
      ‖(Complex.Gamma ((σ:ℂ)+t*Complex.I))⁻¹‖≤C*Real.exp (Real.pi*|t|) := by
  obtain ⟨n,hn⟩:=exists_nat_gt b
  obtain ⟨Cg,hCg,hg⟩:=real_Gamma_compact_bound ((n:ℝ)+1-b) ((n:ℝ)+1-a) (by linarith)
  obtain ⟨Cc,hCc,hc⟩:=inverse_Gamma_compact_strip_bound a b
  refine ⟨Cc+Cg/Real.pi,by positivity,?_⟩
  intro σ hσ t
  have hexp : 1≤Real.exp (Real.pi*|t|) := Real.one_le_exp (by positivity)
  by_cases ht:|t|≤1
  · have hsmall:=hc σ hσ t (abs_le.mp ht)
    calc
      _ ≤ Cc := hsmall
      _ ≤ Cc+Cg/Real.pi := le_add_of_nonneg_right (by positivity)
      _ ≤ (Cc+Cg/Real.pi)*Real.exp (Real.pi*|t|) :=
        le_mul_of_one_le_right (by positivity) hexp
  · have ht1 : 1 < |t| :=lt_of_not_ge ht
    have ht0 : t≠0 := by intro ht0;subst t;norm_num at ht1
    let z : ℂ := (σ:ℂ)+t*Complex.I
    let w : ℂ := z-n
    have hw : w.re<1 := by
      dsimp [w,z]
      simp only [Complex.ofReal_re,Complex.mul_re,
        Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,
        sub_zero,add_zero]
      linarith [hσ.2]
    have hwi : w.im≠0 := by simpa [w,z] using ht0
    have he : 1-w.re=(n:ℝ)+1-σ := by simp [w,z];ring
    have hi : w.im=t := by simp [w,z]
    have hbound:=inverse_Gamma_norm_of_left w hw hwi
    rw [he,hi] at hbound
    have hgbound:=hg ((n:ℝ)+1-σ) ⟨by linarith [hσ.2],by linarith [hσ.1]⟩
    calc
      _ ≤ ‖(Complex.Gamma w)⁻¹‖ :=
        inverse_Gamma_norm_le_shift_left z n (by simpa [z] using ht1.le)
      _ ≤ (Real.Gamma ((n:ℝ)+1-σ)/Real.pi)*Real.exp (Real.pi*|t|) := hbound
      _ ≤ (Cg/Real.pi)*Real.exp (Real.pi*|t|) := by gcongr
      _ ≤ (Cc+Cg/Real.pi)*Real.exp (Real.pi*|t|) :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCc.le) (Real.exp_pos _).le

theorem inverse_Gamma_strip_exp_bound_complex (a b : ℝ) :
    ∃C : ℝ,0<C ∧ ∀z : ℂ,z.re∈Set.Icc a b →
      ‖(Complex.Gamma z)⁻¹‖≤C*Real.exp (Real.pi*|z.im|) := by
  obtain ⟨C,hC,hb⟩:=inverse_Gamma_strip_exp_bound a b
  refine ⟨C,hC,?_⟩
  intro z hz
  simpa only [Complex.re_add_im] using hb z.re hz z.im

theorem inverse_cubic_Gamma_pair_strip_bound (a b : ℝ) :
    ∃C : ℝ,0<C ∧ ∀s : ℂ,s.re∈Set.Icc a b →
      ‖(Complex.Gamma (s+1/3)*Complex.Gamma (s+2/3))⁻¹‖≤
        C*Real.exp (2*Real.pi*|s.im|) := by
  obtain ⟨C1,hC1,h1⟩:=inverse_Gamma_strip_exp_bound_complex (a+1/3) (b+1/3)
  obtain ⟨C2,hC2,h2⟩:=inverse_Gamma_strip_exp_bound_complex (a+2/3) (b+2/3)
  refine ⟨C1*C2,mul_pos hC1 hC2,?_⟩
  intro s hs
  have hb1:=h1 (s+1/3) (by norm_num;constructor <;> linarith [hs.1,hs.2])
  have hb2:=h2 (s+2/3) (by norm_num;constructor <;> linarith [hs.1,hs.2])
  norm_num at hb1 hb2
  rw [mul_inv_rev,norm_mul,norm_inv,norm_inv]
  calc
    _ ≤ (C2*Real.exp (Real.pi*|s.im|))*(C1*Real.exp (Real.pi*|s.im|)) :=
      mul_le_mul hb2 hb1 (by positivity) (by positivity)
    _ = C1*C2*Real.exp (2*Real.pi*|s.im|) := by
      rw [show 2*Real.pi*|s.im|=Real.pi*|s.im|+Real.pi*|s.im| by ring,Real.exp_add]
      ring

end CubicGammaExponential

open Filter MeasureTheory
open scoped Classical BigOperators Topology

namespace CubicEisenstein

lemma cubic_bessel_mellin_norm_scale (s : ℂ) (r : ℝ) (hr : 0< r) :
    (∫v : ℝ in Set.Ioi 0,‖(v:ℂ)^(2*s)*
      schlafliBesselK (1/3) (4*Real.pi*r*v)‖)=
    r^(-(2*s.re+1))*(∫v : ℝ in Set.Ioi 0,
      ‖(v:ℂ)^(2*s)*schlafliBesselK (1/3) (4*Real.pi*v)‖) := by
  let g : ℝ→ℝ := fun v=>‖(v:ℂ)^(2*s)*schlafliBesselK (1/3) (4*Real.pi*v)‖
  have hp (v : ℝ) (hv : 0<v) :
      ‖(v:ℂ)^(2*s)*schlafliBesselK (1/3) (4*Real.pi*r*v)‖=
        r^(-(2*s.re))*g (r*v) := by
    dsimp only [g]
    rw [norm_mul,norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos hv,
      Complex.norm_cpow_eq_rpow_re_of_pos (mul_pos hr hv)]
    simp only [show (2*s).re=2*s.re by simp]
    rw [Real.mul_rpow hr.le hv.le]
    rw [show 4*Real.pi*r*v=4*Real.pi*(r*v) by ring]
    have hc : r^(-(2*s.re))*r^(2*s.re)=1 := by
      rw [←Real.rpow_add hr]
      simp
    linear_combination -(v^(2*s.re)*‖schlafliBesselK (1/3) (4*Real.pi*(r*v))‖)*hc
  calc
    _=∫v : ℝ in Set.Ioi 0,r^(-(2*s.re))*g (r*v) :=
      setIntegral_congr_fun measurableSet_Ioi hp
    _=r^(-(2*s.re))*(r⁻¹*(∫v : ℝ in Set.Ioi 0,g v)) := by
      rw [integral_const_mul,integral_comp_mul_left_Ioi g 0 hr]
      simp
    _=_ := by
      rw [←mul_assoc,←Real.rpow_neg_one,←Real.rpow_add hr]
      congr 2
      ring

lemma weighted_cubic_bessel_integral_norm (s : ℂ) (freq a : ℂ) (hf : freq≠0) :
    (∫v : ℝ in Set.Ioi 0,‖a*((v:ℂ)^(2*s)*
      schlafliBesselK (1/3) (4*Real.pi*‖freq‖*v))‖)=
    (‖a‖*‖freq‖^(-(2*s.re+1)))*(∫v : ℝ in Set.Ioi 0,
      ‖(v:ℂ)^(2*s)*schlafliBesselK (1/3) (4*Real.pi*v)‖) := by
  simp only [norm_mul,integral_const_mul]
  rw [←integral_const_mul]
  have h:=cubic_bessel_mellin_norm_scale s ‖freq‖ (norm_pos_iff.mpr hf)
  simp only [norm_mul] at h
  rw [integral_const_mul,h]
  ring

theorem cubic_bessel_series_mellin {α : Type*} [Countable α]
    (freq a : α→ℂ) (hf : ∀i,freq i≠0) (s : ℂ) (hs : -(1/3)<s.re)
    (ha : Summable (fun i=>‖a i‖*‖freq i‖^(-(2*s.re+1)))) :
    (∫v : ℝ in Set.Ioi 0,∑'i,a i*((v:ℂ)^(2*s)*
      schlafliBesselK (1/3) (4*Real.pi*‖freq i‖*v)))=
    ∑'i,a i*(((2:ℂ)^(2*s-1)*Complex.Gamma (s+1/3)*Complex.Gamma (s+2/3))/
      ((4*Real.pi*‖freq i‖:ℝ):ℂ)^(2*s+1)) := by
  have hi (i : α) := (source_cubic_bessel_mellin_integrable s (freq i) hs (hf i)).const_mul (a i)
  have hsum : Summable (fun i=>∫v : ℝ in Set.Ioi 0,
      ‖a i*((v:ℂ)^(2*s)*schlafliBesselK (1/3) (4*Real.pi*‖freq i‖*v))‖) := by
    simp only [weighted_cubic_bessel_integral_norm s _ _ (hf _)]
    exact ha.mul_right _
  rw [←integral_tsum_of_summable_integral_norm hi hsum]
  apply tsum_congr
  intro i
  rw [integral_const_mul,source_cubic_bessel_mellin s (freq i) hs (hf i)]

end CubicEisenstein

open Filter MeasureTheory
open scoped Classical BigOperators Topology

namespace CubicEisenstein

lemma positive_sqrt_cpow_twice (r : ℝ) (hr : 0< r) (s : ℂ) :
    (Real.sqrt r:ℂ)^(2*s+1)=(r:ℂ)^(s+1/2) := by
  have ha : Complex.arg (Real.sqrt r:ℂ)=0 :=
    Complex.arg_ofReal_of_nonneg (Real.sqrt_nonneg r)
  have h := Complex.cpow_nat_mul' (x:=(Real.sqrt r:ℂ)) (n:=2)
    (by simpa only [ha,mul_zero] using (neg_lt_zero.mpr Real.pi_pos))
    (by simpa only [ha,mul_zero] using Real.pi_pos.le) (s+1/2)
  have hs : (Real.sqrt r:ℂ)^2=(r:ℂ) := by
    rw [←Complex.ofReal_pow,Real.sq_sqrt hr.le]
  norm_num only at h
  simpa only [hs,show (2:ℂ)*(s+1/2)=2*s+1 by ring] using h

lemma radial_bessel_coefficient_norm (r q σ : ℝ) (hr : 0< r) (hq : 0<q) (a : ℂ) :
    ‖a*(r:ℂ)‖*‖((q*Real.sqrt r:ℝ):ℂ)‖^(-(2*σ+1))=
      q^(-(2*σ+1))*(‖a‖*r^(1/2-σ)) := by
  rw [norm_mul,Complex.norm_of_nonneg hr.le,
    Complex.norm_of_nonneg (mul_pos hq (Real.sqrt_pos.mpr hr)).le,
    Real.mul_rpow hq.le (Real.sqrt_nonneg r),Real.sqrt_eq_rpow,
    ←Real.rpow_mul hr.le]
  have hp : r*r^((1/2)*(-(2*σ+1)))=r^(1/2-σ) := by
    calc
      _=r^1*r^((1/2)*(-(2*σ+1))) := by rw [Real.rpow_one]
      _=r^(1+(1/2)*(-(2*σ+1))) := (Real.rpow_add hr _ _).symm
      _=_ := by congr 1;ring
  calc
    _=q^(-(2*σ+1))*(‖a‖*(r*r^((1/2)*(-(2*σ+1))))) := by ring
    _=_ := by rw [hp]

lemma radial_bessel_coefficient_identity (r q : ℝ) (hr : 0< r) (hq : 0<q)
    (a B s : ℂ) :
    (a*(r:ℂ))*(B/((q*Real.sqrt r:ℝ):ℂ)^(2*s+1))=
      (B/(q:ℂ)^(2*s+1))*(a*(r:ℂ)^(1/2-s)) := by
  rw [Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg hq.le (Real.sqrt_nonneg r),
    positive_sqrt_cpow_twice r hr s]
  have hp : (r:ℂ)/(r:ℂ)^(s+1/2)=(r:ℂ)^(1/2-s) := by
    have h := Complex.cpow_sub (1:ℂ) (s+1/2) (Complex.ofReal_ne_zero.mpr hr.ne')
    rw [Complex.cpow_one] at h
    simpa only [show (1:ℂ)-(s+1/2)=1/2-s by ring] using h.symm
  calc
    _=(B/(q:ℂ)^(2*s+1))*(a*((r:ℂ)/(r:ℂ)^(s+1/2))) := by ring
    _=_ := by rw [hp]

theorem radialBesselProfile_mellin {α : Type*} [Countable α]
    (r : α→ℝ) (hr : ∀i,0< r i) (a : α→ℂ) (q : ℝ) (hq : 0<q)
    (s : ℂ) (hs : -(1/3)<s.re)
    (ha : Summable (fun i=>‖a i‖*(r i)^(1/2-s.re))) :
    mellin (radialBesselProfile r a q) (2*s)=
      (((2:ℂ)^(2*s-1)*Complex.Gamma (s+1/3)*Complex.Gamma (s+2/3))/
        ((4*Real.pi*q:ℝ):ℂ)^(2*s+1))*(∑'i,a i*(r i:ℂ)^(1/2-s)) := by
  let f : α→ℂ := fun i=>((q*Real.sqrt (r i):ℝ):ℂ)
  have hf (i : α) : f i≠0 :=
    Complex.ofReal_ne_zero.mpr (mul_pos hq (Real.sqrt_pos.mpr (hr i))).ne'
  have has : Summable (fun i=>‖a i*(r i:ℂ)‖*‖f i‖^(-(2*s.re+1))) := by
    simp only [f,radial_bessel_coefficient_norm _ q s.re (hr _) hq]
    exact ha.mul_left _
  have hid := cubic_bessel_series_mellin f (fun i=>a i*(r i:ℂ)) hf s hs has
  calc
    _=(∫v : ℝ in Set.Ioi 0,∑'i,(a i*(r i:ℂ))*((v:ℂ)^(2*s)*
        schlafliBesselK (1/3) (4*Real.pi*‖f i‖*v))) := by
      unfold mellin
      apply setIntegral_congr_fun measurableSet_Ioi
      intro v hv
      dsimp only [radialBesselProfile]
      simp only [smul_eq_mul]
      rw [←tsum_mul_left]
      apply tsum_congr
      intro i
      have hp : (v:ℂ)^(2*s-1)*(v:ℂ)=(v:ℂ)^(2*s) := by
        calc
          _=(v:ℂ)^(2*s-1)*(v:ℂ)^1 := by rw [Complex.cpow_one]
          _=(v:ℂ)^((2*s-1)+1) :=
            (Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hv.ne')).symm
          _=_ := by rw [sub_add_cancel]
      have hn : ‖f i‖=q*Real.sqrt (r i) :=
        Complex.norm_of_nonneg (mul_pos hq (Real.sqrt_pos.mpr (hr i))).le
      rw [hn]
      have hk : 4*Real.pi*q*Real.sqrt (r i)*v=4*Real.pi*(q*Real.sqrt (r i))*v := by ring
      rw [hk]
      change (v:ℂ)^(2*s-1)*_=_
      linear_combination (a i*(r i:ℂ))*schlafliBesselK (1/3) (4*Real.pi*(q*Real.sqrt (r i))*v)*hp
    _=_ := by
      rw [hid,←tsum_mul_left]
      apply tsum_congr
      intro i
      have hn : ‖f i‖=q*Real.sqrt (r i) :=
        Complex.norm_of_nonneg (mul_pos hq (Real.sqrt_pos.mpr (hr i))).le
      rw [hn,show 4*Real.pi*(q*Real.sqrt (r i))=(4*Real.pi*q)*Real.sqrt (r i) by ring]
      exact radial_bessel_coefficient_identity (r i) (4*Real.pi*q) (hr i)
        (by positivity) (a i) _ s

end CubicEisenstein

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.BesselReflection
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
open Filter MeasureTheory
open scoped Classical BigOperators Topology

section
open CubicEisenstein

theorem completedBesselProfile_mellin (Ψ : ActualEisensteinCubic.O→*ℂ)
    (hΨ : ∀a,‖Ψ a‖≤1) (q : ℝ) (hq : 0<q) (s : ℂ) (hs : 3/2<s.re) :
    mellin (completedBesselProfile Ψ q) (2*s)=
      besselMellinFactor q s*completedDirichletSeries Ψ s := by
  let : Countable ActualEisensteinCubic.O :=
    ActualEisensteinCubic.latticeCoordEquiv.injective.countable
  let : Countable (Ideal ActualEisensteinCubic.O) :=
    ConcretePrimeRowBridge.idealGenerator_injective.countable
  have hsum := completedMellinCoefficient_summable Ψ hΨ (s.re-1/2) (by linarith)
  have he : -(s.re-1/2)=1/2-s.re := by ring
  simp only [he] at hsum
  exact radialBesselProfile_mellin completedMellinLength completedMellinLength_pos
    (completedMellinCoefficient Ψ) q hq s (by linarith) hsum

lemma inverseBesselMellinFactor_mul (q : ℝ) (hq : 0<q) (s : ℂ)
    (hs : -(1/3)<s.re) :
    inverseBesselMellinFactor q s*besselMellinFactor q s=1 := by
  have hq0 : (((4*Real.pi*q:ℝ):ℂ)^(2*s+1))≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr (by positivity)))
  have h1 : Complex.Gamma (s+1/3)≠0 := Complex.Gamma_ne_zero_of_re_pos (by simp;linarith)
  have h2 : Complex.Gamma (s+2/3)≠0 := Complex.Gamma_ne_zero_of_re_pos (by simp;linarith)
  have hp : (2:ℂ)^(1-2*s)*(2:ℂ)^(2*s-1)=1 := by
    rw [←Complex.cpow_add _ _ (by norm_num : (2:ℂ)≠0)]
    simp
  unfold inverseBesselMellinFactor besselMellinFactor
  calc
    _=((((4*Real.pi*q:ℝ):ℂ)^(2*s+1))/(((4*Real.pi*q:ℝ):ℂ)^(2*s+1)))*
        ((2:ℂ)^(1-2*s)*(2:ℂ)^(2*s-1))*
        ((Complex.Gamma (s+1/3)*Complex.Gamma (s+2/3))⁻¹*
          (Complex.Gamma (s+1/3)*Complex.Gamma (s+2/3))) := by ring
    _=1 := by rw [div_self hq0,hp,inv_mul_cancel₀ (mul_ne_zero h1 h2)];ring

theorem completedDirichletSeries_eq_mellin (Ψ : ActualEisensteinCubic.O→*ℂ)
    (hΨ : ∀a,‖Ψ a‖≤1) (q : ℝ) (hq : 0<q) (s : ℂ) (hs : 3/2<s.re) :
    completedDirichletSeries Ψ s=
      inverseBesselMellinFactor q s*mellin (completedBesselProfile Ψ q) (2*s) := by
  rw [completedBesselProfile_mellin Ψ hΨ q hq s hs,←mul_assoc,
    inverseBesselMellinFactor_mul q hq s (by linarith),one_mul]

end

theorem inverseBesselMellinFactor_differentiable (q : ℝ) (hq : 0<q) :
    Differentiable ℂ (inverseBesselMellinFactor q) := by
  have hq0 : ((4*Real.pi*q:ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr (by positivity)
  have h1 : Differentiable ℂ (fun s : ℂ=>((4*Real.pi*q:ℝ):ℂ)^(2*s+1)) :=
    (show Differentiable ℂ (fun s : ℂ=>2*s+1) from by fun_prop).const_cpow (Or.inl hq0)
  have h2 : Differentiable ℂ (fun s : ℂ=>(2:ℂ)^(1-2*s)) :=
    (show Differentiable ℂ (fun s : ℂ=>1-2*s) from by fun_prop).const_cpow
      (Or.inl (by norm_num : (2:ℂ)≠0))
  have h3 : Differentiable ℂ (fun s : ℂ=>(Complex.Gamma (s+1/3))⁻¹) :=
    Complex.differentiable_one_div_Gamma.comp (by fun_prop)
  have h4 : Differentiable ℂ (fun s : ℂ=>(Complex.Gamma (s+2/3))⁻¹) :=
    Complex.differentiable_one_div_Gamma.comp (by fun_prop)
  convert (preTransparency := .instances) (h1.mul h2).mul (h4.mul h3) using 1
  ext s
  simp only [inverseBesselMellinFactor,Pi.mul_apply,mul_inv_rev]

theorem inverseBesselMellinFactor_strip_bound (q : ℝ) (hq : 0<q) (a b : ℝ) :
    ∃C : ℝ,0≤C ∧ ∀s : ℂ,s.re∈Set.Icc a b →
      ‖inverseBesselMellinFactor q s‖≤C*Real.exp (2*Real.pi*|s.im|) := by
  obtain ⟨Cg,hCg,hg⟩ := CubicGammaExponential.inverse_cubic_Gamma_pair_strip_bound a b
  let Ca := (4*Real.pi*q)^(2*a+1)+(4*Real.pi*q)^(2*b+1)
  let Cb := (2:ℝ)^(1-2*b)+(2:ℝ)^(1-2*a)
  have hqpos : 0<4*Real.pi*q := by positivity
  have hCa : 0≤Ca := by dsimp [Ca];positivity
  have hCb : 0≤Cb := by dsimp [Cb];positivity
  refine ⟨Ca*Cb*Cg,by positivity,?_⟩
  intro s hs
  have hp1 : ‖((4*Real.pi*q:ℝ):ℂ)^(2*s+1)‖≤Ca := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hqpos]
    have hr : (2*s+1).re=2*s.re+1 := by simp
    rw [hr]
    exact VerticalContourShift.rpow_between_endpoints _ _ _ _ hqpos
      (by linarith [hs.1]) (by linarith [hs.2])
  have hp2 : ‖(2:ℂ)^(1-2*s)‖≤Cb := by
    change ‖((2:ℝ):ℂ)^(1-2*s)‖≤Cb
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : 0<(2:ℝ))]
    have hr : (1-2*s).re=1-2*s.re := by simp
    rw [hr]
    exact VerticalContourShift.rpow_between_endpoints _ _ _ _ (by norm_num)
      (by linarith [hs.2]) (by linarith [hs.1])
  simp only [inverseBesselMellinFactor,norm_mul]
  calc
    _≤(Ca*Cb)*(Cg*Real.exp (2*Real.pi*|s.im|)) :=
      mul_le_mul (mul_le_mul hp1 hp2 (norm_nonneg _) hCa) (hg s hs)
        (norm_nonneg _) (mul_nonneg hCa hCb)
    _=_ := by ring

theorem continuedBesselDirichlet_differentiable (F : ℝ→ℂ) (q : ℝ) (hq : 0<q)
    (hF : Differentiable ℂ (mellin F)) :
    Differentiable ℂ (continuedBesselDirichlet F q) :=
  (inverseBesselMellinFactor_differentiable q hq).mul (hF.comp (by fun_prop))

theorem continuedBesselDirichlet_strip_bound (F : ℝ→ℂ) (q : ℝ) (hq : 0<q)
    (a b : ℝ) (ha : MellinConvergent F ((2*a:ℝ):ℂ))
    (hb : MellinConvergent F ((2*b:ℝ):ℂ)) :
    ∃C : ℝ,0≤C ∧ ∀s : ℂ,s.re∈Set.Icc a b →
      ‖continuedBesselDirichlet F q s‖≤C*Real.exp (2*Real.pi*|s.im|) := by
  obtain ⟨Ci,hCi,hi⟩ := inverseBesselMellinFactor_strip_bound q hq a b
  obtain ⟨Cm,hCm,hm⟩ := VerticalContourShift.mellin_uniform_strip_bound F (2*a) (2*b) ha hb
  refine ⟨Ci*Cm,mul_nonneg hCi hCm,?_⟩
  intro s hs
  have hms : ‖mellin F (2*s)‖≤Cm := hm (2*s)
    (by simp;linarith [hs.1]) (by simp;linarith [hs.2])
  rw [continuedBesselDirichlet,norm_mul]
  calc
    _≤(Ci*Real.exp (2*Real.pi*|s.im|))*Cm :=
      mul_le_mul (hi s hs) hms (norm_nonneg _) (mul_nonneg hCi (Real.exp_pos _).le)
    _=_ := by ring

theorem continuedBesselDirichlet_eq_initial (Ψ : ActualEisensteinCubic.O→*ℂ)
    (hΨ : ∀a,‖Ψ a‖≤1) (q : ℝ) (hq : 0<q) (s : ℂ) (hs : 3/2<s.re) :
    continuedBesselDirichlet (completedBesselProfile Ψ q) q s=
      completedDirichletSeries Ψ s :=
  (completedDirichletSeries_eq_mellin Ψ hΨ q hq s hs).symm

end CompletedGauss

namespace CubicEisenstein
open Filter MeasureTheory Asymptotics
open scoped BigOperators Classical Topology MatrixGroups

section
local notation "Eis" => ActualEisensteinCubic.O

lemma ramifiedSource_horizontal_hasDerivAt (side:Bool) (v:ℝ) (hv:0<v)
    (z direction:ℂ) (t:ℝ) :
    HasDerivAt (fun x:ℝ => ramifiedSourceFunction (ramifiedCuspRoot side:Eis)
      (upperPoint (z+(x:ℂ)*direction) v hv))
      (∑'h:Eis,(ramifiedBesselCoefficients side).directionalTerm h (v/3)
        (z/3+(t:ℂ)*(direction/3)) (direction/3)) t := by
  have he : (fun x:ℝ => ramifiedSourceFunction (ramifiedCuspRoot side:Eis)
      (upperPoint (z+(x:ℂ)*direction) v hv)) =
      (fun x:ℝ => (ramifiedBesselCoefficients side).series
        (v/3,z/3+(x:ℂ)*(direction/3))) := by
    funext x
    rw [ramifiedSource_eq_series]
    congr 2
    ring
  rw [he]
  exact (ramifiedBesselCoefficients side).series_horizontal_hasDerivAt
    (v/3) (by positivity) (z/3) (direction/3) t

lemma ramifiedSource_wirtingerBar_cusp_decay (side:Bool) (a:ℝ) (ha:0<a) :
    ∃C:ℝ,0≤C ∧ ∀(v:ℝ)(hv:0<v)(z:ℂ),a≤v →
      ‖horizontalWirtingerBar (fun w => ramifiedSourceFunction (ramifiedCuspRoot side:Eis)
        (upperPoint w v hv)) z‖ ≤ C*Real.exp (-(residualCuspDecayRate/3)*v) := by
  obtain ⟨C1,hC1,h1b⟩ := (ramifiedBesselCoefficients side).directionalSeries_cusp_decay
    (a/3) (by positivity) (1/3)
  obtain ⟨CI,hCI,hIb⟩ := (ramifiedBesselCoefficients side).directionalSeries_cusp_decay
    (a/3) (by positivity) (Complex.I/3)
  refine ⟨(C1+CI)/2,by positivity,?_⟩
  intro v hv z hav
  have h1 := (ramifiedSource_horizontal_hasDerivAt side v hv z 1 0).deriv
  have hI := (ramifiedSource_horizontal_hasDerivAt side v hv z Complex.I 0).deriv
  simp only [mul_one,Complex.ofReal_zero,zero_mul,add_zero] at h1 hI
  have he : -residualCuspDecayRate*(v/3)=-(residualCuspDecayRate/3)*v := by ring
  have hb1 := h1b (v/3) (z/3) (by linarith)
  have hbI := hIb (v/3) (z/3) (by linarith)
  rw [he] at hb1 hbI
  rw [horizontalWirtingerBar,h1,hI,norm_mul]
  have hhalf : ‖(1/2:ℂ)‖=(1/2:ℝ) := by norm_num
  rw [hhalf]
  calc
    _ ≤ (1/2:ℝ)*(‖∑'h:Eis,(ramifiedBesselCoefficients side).directionalTerm h (v/3) (z/3) (1/3)‖+
      ‖Complex.I*(∑'h:Eis,(ramifiedBesselCoefficients side).directionalTerm h (v/3) (z/3) (Complex.I/3))‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
    _ = (1/2:ℝ)*(‖∑'h:Eis,(ramifiedBesselCoefficients side).directionalTerm h (v/3) (z/3) (1/3)‖+
      ‖∑'h:Eis,(ramifiedBesselCoefficients side).directionalTerm h (v/3) (z/3) (Complex.I/3)‖) := by
        rw [norm_mul,Complex.norm_I,one_mul]
    _ ≤ (1/2:ℝ)*(C1*Real.exp (-(residualCuspDecayRate/3)*v)+
      CI*Real.exp (-(residualCuspDecayRate/3)*v)) :=
        mul_le_mul_of_nonneg_left (add_le_add hb1 hbI) (by norm_num)
    _ = _ := by ring

lemma ramifiedConjugate_zProfile_isBigO (side:Bool) (z:ℂ) :
    cuspZProfile (fun w => cubicSourceConjugateFunction
      (integralComplexMatrix (lowerCuspMatrix (ramifiedCuspRoot side:Eis)) • w)) z
      =O[atTop] (fun v:ℝ => Real.exp (-(residualCuspDecayRate/3)*v)) := by
  obtain ⟨C,hC,hb⟩ := ramifiedSource_wirtingerBar_cusp_decay side 1 (by norm_num)
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [eventually_ge_atTop (1:ℝ)] with v hv
  have hvp:0<v := lt_of_lt_of_le (by norm_num) hv
  rw [cuspZProfile_positive _ _ _ hvp,Real.norm_of_nonneg (Real.exp_pos _).le]
  change ‖horizontalWirtingerZ (fun w => star (ramifiedSourceFunction
    (ramifiedCuspRoot side:Eis) (upperPoint w v hvp))) z‖ ≤ _
  rw [horizontalWirtingerZ_star,norm_star]
  exact hb v hvp z hv

end

local notation "Eis" => ActualEisensteinCubic.O

lemma reflectedCuspProfile_eq_inv_square (A:ℂ) (Q:ℝ) (g:ℝ→ℂ) (v:ℝ) :
    reflectedCuspProfile A Q g v=A/(v:ℂ)^2*g ((Q*v)⁻¹) := by
  unfold reflectedCuspProfile
  rw [Complex.cpow_neg,Complex.cpow_ofNat]
  ring

lemma reflectedCuspProfile_reverse (A:ℂ) (hA:A≠0) (Q:ℝ) (hQ:0<Q)
    (f g:ℝ→ℂ) (hfg:∀v:ℝ,0<v→f v=reflectedCuspProfile A Q g v)
    (v:ℝ) (hv:0<v) :
    g v=reflectedCuspProfile (A⁻¹/(Q:ℂ)^2) Q f v := by
  have he:=hfg (Q*v)⁻¹ (by positivity)
  have harg:(Q*(Q*v)⁻¹)⁻¹=v := by field_simp
  rw [reflectedCuspProfile_eq_inv_square,harg] at he
  rw [reflectedCuspProfile_eq_inv_square,he,Complex.ofReal_inv,Complex.ofReal_mul]
  have hcQ:(Q:ℂ)≠0:=Complex.ofReal_ne_zero.mpr hQ.ne'
  have hcv:(v:ℂ)≠0:=Complex.ofReal_ne_zero.mpr hv.ne'
  field_simp

theorem cusp_mellin_entire_both (f g:ℝ→ℂ) (A:ℂ) (hA:A≠0)
    (Q decayF decayG:ℝ) (hQ:0<Q) (hdecayF:0<decayF) (hdecayG:0<decayG)
    (hf:ContinuousOn f (Set.Ioi 0)) (hg:ContinuousOn g (Set.Ioi 0))
    (hfbound:f =O[atTop] (fun v:ℝ=>Real.exp (-decayF*v)))
    (hgbound:g =O[atTop] (fun v:ℝ=>Real.exp (-decayG*v)))
    (hfg:∀v:ℝ,0<v→f v=reflectedCuspProfile A Q g v) :
    ((∀s:ℂ,MellinConvergent f s) ∧ Differentiable ℂ (mellin f)) ∧
    ((∀s:ℂ,MellinConvergent g s) ∧ Differentiable ℂ (mellin g)) := by
  constructor
  · exact cusp_mellin_entire f g A Q decayF decayG hQ hdecayF hdecayG
      hf hg hfbound hgbound hfg
  · exact cusp_mellin_entire g f (A⁻¹/(Q:ℂ)^2) Q decayG decayF hQ hdecayG hdecayF
      hg hf hgbound hfbound (reflectedCuspProfile_reverse A hA Q hQ f g hfg)

end CubicEisenstein

open scoped BigOperators Classical

namespace CompletedGauss

open Filter MeasureTheory
open scoped Classical BigOperators Topology ContDiff

lemma besselSmoothingIntegrand_differentiable (F : ℝ→ℂ) (q : ℝ) (hq : 0<q)
    (hF : Differentiable ℂ (mellin F)) (V : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hVs : Function.support V⊆Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (X : ℝ) (hX : 0<X) : Differentiable ℂ (besselSmoothingIntegrand F q V X) := by
  have hm := (CubicReflectionKernel.compact_source_mellin_differentiable V a b ha hVs hV).comp
    (show Differentiable ℂ (fun s : ℂ=>s-1/2) from by fun_prop)
  have hp : Differentiable ℂ (fun s : ℂ=>(X:ℂ)^(s-1/2)) :=
    (show Differentiable ℂ (fun s : ℂ=>s-1/2) from by fun_prop).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hX.ne'))
  exact (hm.mul hp).mul (continuedBesselDirichlet_differentiable F q hq hF)

lemma besselSmoothingIntegrand_strip_bound (F : ℝ→ℂ) (q : ℝ) (hq : 0<q)
    (lo hi : ℝ) (hF : ∀s : ℂ,MellinConvergent F s)
    (V : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hVs : Function.support V⊆Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (X : ℝ) (hX : 0<X) :
    ∃C : ℝ,0≤C ∧ ∀s : ℂ,s.re∈Set.Icc lo hi →
      ‖besselSmoothingIntegrand F q V X s‖≤C*Real.exp (2*Real.pi*|s.im|) := by
  obtain ⟨Cd,hCd,hd⟩ := continuedBesselDirichlet_strip_bound F q hq lo hi (hF _) (hF _)
  have hVc (s : ℂ) := CubicReflectionKernel.compact_source_mellin_convergent V a b ha hVs hV s
  obtain ⟨Cv,hCv,hv⟩ := VerticalContourShift.mellin_uniform_strip_bound V (lo-1/2) (hi-1/2)
    (hVc _) (hVc _)
  let Cx : ℝ := X^(lo-1/2)+X^(hi-1/2)
  have hCx : 0≤Cx := by dsimp [Cx];positivity
  refine ⟨Cv*Cx*Cd,mul_nonneg (mul_nonneg hCv hCx) hCd,?_⟩
  intro s hs
  have hvb : ‖mellin V (s-1/2)‖≤Cv := hv (s-1/2)
    (by simp;linarith [hs.1]) (by simp;linarith [hs.2])
  have hxb : ‖(X:ℂ)^(s-1/2)‖≤Cx := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hX]
    have he : (s-1/2).re=s.re-1/2 := by simp
    rw [he]
    exact VerticalContourShift.rpow_between_endpoints X (lo-1/2) (hi-1/2) (s.re-1/2) hX
      (by linarith [hs.1]) (by linarith [hs.2])
  rw [besselSmoothingIntegrand,norm_mul,norm_mul]
  calc
    _≤(Cv*Cx)*(Cd*Real.exp (2*Real.pi*|s.im|)) :=
      mul_le_mul (mul_le_mul hvb hxb (norm_nonneg _) hCv) (hd s hs)
        (norm_nonneg _) (mul_nonneg hCv hCx)
    _=_ := by ring

theorem besselSmoothingIntegrand_contour_eq (F : ℝ→ℂ) (q : ℝ) (hq : 0<q)
    (hF : ∀s : ℂ,MellinConvergent F s) (hFe : Differentiable ℂ (mellin F))
    (V : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hVs : Function.support V⊆Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (X : ℝ) (hX : 0<X) (lo hi : ℝ) (hlh : lo≤hi)
    (hl : Integrable (fun t : ℝ=>besselSmoothingIntegrand F q V X ((lo:ℂ)+t*Complex.I)))
    (hh : Integrable (fun t : ℝ=>besselSmoothingIntegrand F q V X ((hi:ℂ)+t*Complex.I))) :
    (∫t : ℝ,besselSmoothingIntegrand F q V X ((lo:ℂ)+t*Complex.I))=
      ∫t : ℝ,besselSmoothingIntegrand F q V X ((hi:ℂ)+t*Complex.I) := by
  obtain ⟨C,hC,hb⟩ := besselSmoothingIntegrand_strip_bound F q hq lo hi hF V a b ha hVs hV X hX
  apply VerticalContourShift.integral_eq_of_exponential_strip_growth
    (besselSmoothingIntegrand F q V X) lo hi (2*Real.pi) C hlh (by positivity) hC
  · intro z hz1 hz2
    exact (besselSmoothingIntegrand_differentiable F q hq hFe V a b ha hVs hV X hX) z
  · exact hl
  · exact hh
  · intro σ hσ t
    simpa only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,
      Complex.I_re,Complex.I_im,zero_mul,mul_zero,sub_zero,add_zero,
      Complex.add_im,Complex.mul_im,mul_one,zero_add] using
      hb ((σ:ℂ)+t*Complex.I) (by simpa using hσ)

theorem completedT_mellin_shift (Ψ : ActualEisensteinCubic.O→*ℂ) (hΨ : ∀a,‖Ψ a‖≤1)
    (q : ℝ) (hq : 0<q)
    (hF : ∀s : ℂ,MellinConvergent (completedBesselProfile Ψ q) s)
    (hFe : Differentiable ℂ (mellin (completedBesselProfile Ψ q)))
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (X : ℝ) (hX : 0<X) (lo : ℝ) (hl : lo≤2)
    (hleft : Integrable (fun t : ℝ=>
      besselSmoothingIntegrand (completedBesselProfile Ψ q) q (Vstar W) X ((lo:ℂ)+t*Complex.I))) :
    completedT Ψ W X=(1/(2*Real.pi):ℂ)*∫t : ℝ,
      besselSmoothingIntegrand (completedBesselProfile Ψ q) q (Vstar W) X ((lo:ℂ)+t*Complex.I) := by
  have hid (t : ℝ) :
      besselSmoothingIntegrand (completedBesselProfile Ψ q) q (Vstar W) X ((2:ℂ)+t*Complex.I)=
      mellin (Vstar W) ((3/2:ℂ)+t*Complex.I)*(X:ℂ)^((3/2:ℂ)+t*Complex.I)*
        completedDirichletSeries Ψ ((2:ℂ)+t*Complex.I) := by
    rw [besselSmoothingIntegrand,continuedBesselDirichlet_eq_initial Ψ hΨ q hq _ (by norm_num)]
    rw [show (2:ℂ)+t*Complex.I-1/2=3/2+t*Complex.I by ring]
  have hr : Integrable (fun t : ℝ=>
      besselSmoothingIntegrand (completedBesselProfile Ψ q) q (Vstar W) X ((2:ℂ)+t*Complex.I)) := by
    simp only [hid]
    exact completedT_initial_mellin_integrable Ψ hΨ W a b ha hWs hW X hX
  have he := besselSmoothingIntegrand_contour_eq (completedBesselProfile Ψ q) q hq hF hFe
    (Vstar W) a b ha (Vstar_support W a b hWs) (Vstar_contDiff W a b ha hWs hW)
    X hX lo 2 hl hleft hr
  rw [he]
  simpa only [Complex.ofReal_ofNat,hid] using
    completedT_initial_mellin Ψ hΨ W a b ha hWs hW X hX

end CompletedGauss

open Filter MeasureTheory
open scoped Classical BigOperators Topology

namespace CompletedGauss
open CubicEisenstein

lemma besselMellinFactor_reflection (q d : ℝ) (s : ℂ) :
    inverseBesselMellinFactor q s*besselMellinFactor d (1-s)=
      besselReflectionFactor q d s*CubicReflectionKernel.gammaMultiplier (1/2-s) := by
  have hp : (2:ℂ)^(1-2*s)*(2:ℂ)^(1-2*s)=(2:ℂ)^(2-4*s) := by
    rw [←Complex.cpow_add _ _ (by norm_num : (2:ℂ)≠0)]
    congr 1
    ring
  unfold inverseBesselMellinFactor besselMellinFactor besselReflectionFactor
    CubicReflectionKernel.gammaMultiplier
  rw [show (2:ℂ)*(1-s)-1=1-2*s by ring,
    show (2:ℂ)*(1-s)+1=3-2*s by ring,
    show (1:ℂ)-s+1/3=4/3-s by ring,
    show (1:ℂ)-s+2/3=5/3-s by ring,
    show (7/6:ℂ)+(1/2-s)=5/3-s by ring,
    show (5/6:ℂ)+(1/2-s)=4/3-s by ring,
    show (7/6:ℂ)-(1/2-s)=s+2/3 by ring,
    show (5/6:ℂ)-(1/2-s)=s+1/3 by ring]
  have he := congrArg (fun z : ℂ=>
    (((4*Real.pi*q:ℝ):ℂ)^(2*s+1)*
      (Complex.Gamma (s+1/3))⁻¹*(Complex.Gamma (s+2/3))⁻¹*
      Complex.Gamma (4/3-s)*Complex.Gamma (5/3-s)*
      (((4*Real.pi*d:ℝ):ℂ)^(3-2*s))⁻¹)*z) hp
  simp only [div_eq_mul_inv,mul_inv_rev] at he ⊢
  linear_combination he

lemma besselReflectionFactor_norm (q d : ℝ) (hq : 0<q) (hd : 0<d) (s : ℂ) :
    ‖besselReflectionFactor q d s‖=
      (4*Real.pi*q)^(2*s.re+1)*(2:ℝ)^(2-4*s.re)/
        (4*Real.pi*d)^(3-2*s.re) := by
  unfold besselReflectionFactor
  have h2 : ‖(2:ℂ)^(2-4*s)‖=(2:ℝ)^(2-4*s.re) := by
    simpa only [Complex.ofReal_ofNat,show (2-4*s).re=2-4*s.re by simp] using
      Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : 0<(2:ℝ)) (2-4*s)
  rw [norm_div,norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : 0<4*Real.pi*q),
    h2,
    Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : 0<4*Real.pi*d)]
  norm_num

theorem continuedBesselDirichlet_reflection {α : Type*} [Countable α]
    (F : ℝ→ℂ) (r : α→ℝ) (hr : ∀i,0< r i) (a : α→ℂ)
    (q d Q : ℝ) (hd : 0<d) (hQ : 0<Q) (A : ℂ)
    (hreflect : ∀v : ℝ,0<v→F v=
      A*((v:ℂ)^(-2:ℂ)*radialBesselProfile r a d ((Q*v)⁻¹)))
    (s : ℂ) (hs : s.re<4/3)
    (ha : Summable (fun i=>‖a i‖*(r i)^(s.re-1/2))) :
    continuedBesselDirichlet F q s=
      (A*(Q:ℂ)^(2-2*s)*besselReflectionFactor q d s)*
        CubicReflectionKernel.gammaMultiplier (1/2-s)*
        (∑'i,a i*(r i:ℂ)^(s-1/2)) := by
  have hs' : -(1/3)<(1-s).re := by simp;linarith
  have ha' : Summable (fun i=>‖a i‖*(r i)^(1/2-(1-s).re)) := by
    convert (preTransparency := .instances) ha using 1
    funext i
    congr 2
    simp
    ring
  have hm := radialBesselProfile_mellin r hr a d hd (1-s) hs' ha'
  have hc := cusp_mellin_reflection_of_identity F (radialBesselProfile r a d) A s Q hQ hreflect
  have hm' : mellin (radialBesselProfile r a d) (2-2*s)=
      besselMellinFactor d (1-s)*(∑'i,a i*(r i:ℂ)^(s-1/2)) := by
    calc
      _=mellin (radialBesselProfile r a d) (2*(1-s)) := by congr 1;ring
      _=_ := by simpa only [besselMellinFactor,show (1/2:ℂ)-(1-s)=s-1/2 by ring] using hm
  rw [hm'] at hc
  rw [continuedBesselDirichlet,hc]
  calc
    _=A*(Q:ℂ)^(2-2*s)*(inverseBesselMellinFactor q s*besselMellinFactor d (1-s))*
        (∑'i,a i*(r i:ℂ)^(s-1/2)) := by ring
    _=_ := by rw [besselMellinFactor_reflection];ring

end CompletedGauss

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.FiniteTranslations
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
open Filter MeasureTheory
open scoped Classical BigOperators Topology ContDiff

open CubicEisenstein

lemma positive_cpow_comp_continuous (r : ℝ) (hr : 0< r)
    (f : ℝ→ℂ) (hf : Continuous f) : Continuous (fun t=>(r:ℂ)^(f t)) := by
  let : NeZero (r:ℂ) := ⟨Complex.ofReal_ne_zero.mpr hr.ne'⟩
  exact (_root_.continuous_const_cpow (r:ℂ)).comp hf

theorem besselSmoothingIntegrand_reflected_integrable {α : Type*} [Countable α]
    (F : ℝ→ℂ) (r : α→ℝ) (hr : ∀i,0< r i) (a : α→ℂ)
    (q d Q : ℝ) (hq : 0<q) (hd : 0<d) (hQ : 0<Q) (A : ℂ)
    (hreflect : ∀v : ℝ,0<v→F v=
      A*((v:ℂ)^(-2:ℂ)*radialBesselProfile r a d ((Q*v)⁻¹)))
    (has : Summable (fun i=>‖a i‖*(r i)^(-(3/2:ℝ))))
    (V : ℝ→ℂ) (v0 v1 : ℝ) (hv0 : 0<v0)
    (hVs : Function.support V⊆Set.Icc v0 v1) (hV : ContDiff ℝ ∞ V)
    (X : ℝ) (hX : 0<X) :
    Integrable (fun t : ℝ=>besselSmoothingIntegrand F q V X ((-1:ℂ)+t*Complex.I)) := by
  let P : ℝ→ℂ := fun t=>
    A*(Q:ℂ)^(2-2*((-1:ℂ)+t*Complex.I))*
      besselReflectionFactor q d ((-1:ℂ)+t*Complex.I)*
        (X:ℂ)^(((-1:ℂ)+t*Complex.I)-1/2)
  let D : ℝ→ℂ := fun t=>∑'i,a i*(r i:ℂ)^(-((3/2:ℂ)+(-t)*Complex.I))
  let K : ℝ→ℂ := fun t=>CubicReflectionKernel.mellinEulerData V 0 ((3/2:ℂ)+(-t)*Complex.I)
  have hK : Integrable K := by
    have hh := CubicReflectionKernel.mellinEulerData_vertical_integrable V v0 v1 hv0 hVs hV
      2 0 (3/2) (by norm_num)
    simpa only [K,Complex.ofReal_div,Complex.ofReal_ofNat,Complex.ofReal_neg] using hh.comp_neg
  have hD : Continuous D := by
    have hh := (weighted_vertical_series_continuous r hr a (3/2) has).comp continuous_neg
    simpa only [D,Function.comp_def,Complex.ofReal_div,Complex.ofReal_ofNat,Complex.ofReal_neg] using hh
  have hDb (t : ℝ) : ‖D t‖≤∑'i,‖a i‖*(r i)^(-(3/2:ℝ)) := by
    simpa only [D,Complex.ofReal_div,Complex.ofReal_ofNat,Complex.ofReal_neg] using
      weighted_vertical_series_norm r hr a (3/2) has (-t)
  have hP : Continuous P := by
    have h1 := positive_cpow_comp_continuous Q hQ
      (fun t : ℝ=>2-2*((-1:ℂ)+t*Complex.I)) (by fun_prop)
    have h2 := positive_cpow_comp_continuous (4*Real.pi*q) (by positivity)
      (fun t : ℝ=>2*((-1:ℂ)+t*Complex.I)+1) (by fun_prop)
    have h3 := positive_cpow_comp_continuous 2 (by norm_num)
      (fun t : ℝ=>2-4*((-1:ℂ)+t*Complex.I)) (by fun_prop)
    have h4 := positive_cpow_comp_continuous (4*Real.pi*d) (by positivity)
      (fun t : ℝ=>3-2*((-1:ℂ)+t*Complex.I)) (by fun_prop)
    have h5 := positive_cpow_comp_continuous X hX
      (fun t : ℝ=>((-1:ℂ)+t*Complex.I)-1/2) (by fun_prop)
    have hn (t : ℝ) : (((4*Real.pi*d:ℝ):ℂ)^(3-2*((-1:ℂ)+t*Complex.I)))≠0 :=
      Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr (by positivity)))
    convert (preTransparency := .instances) (((continuous_const (y:=A)).mul h1).mul ((h2.mul h3).div h4 hn)).mul h5 using 1 ;
      (ext t; simp only [P,besselReflectionFactor,Pi.mul_apply,Pi.div_apply,Complex.ofReal_ofNat])
  have hPn (t : ℝ) : ‖P t‖=‖P 0‖ := by
    simp only [P,norm_mul,besselReflectionFactor_norm q d hq hd,
      Complex.norm_cpow_eq_rpow_re_of_pos hQ,Complex.norm_cpow_eq_rpow_re_of_pos hX]
    norm_num
  have hi := (hK.mul_bdd hP.aestronglyMeasurable
    (Eventually.of_forall (fun t=>(hPn t).le))).mul_bdd hD.aestronglyMeasurable
      (Eventually.of_forall hDb)
  apply hi.congr
  filter_upwards with t
  have he : ((-1:ℂ)+t*Complex.I).re-1/2=-(3/2:ℝ) := by norm_num
  have hsum : Summable (fun i=>‖a i‖*(r i)^(((-1:ℂ)+t*Complex.I).re-1/2)) := by
    simpa only [he] using has
  have href := continuedBesselDirichlet_reflection F r hr a q d Q hd hQ A hreflect
    ((-1:ℂ)+t*Complex.I) (by norm_num) hsum
  change K t*P t*D t=besselSmoothingIntegrand F q V X ((-1:ℂ)+t*Complex.I)
  rw [besselSmoothingIntegrand,href]
  dsimp only [K,P,D]
  unfold CubicReflectionKernel.mellinEulerData CubicReflectionKernel.mellinData
  simp only [pow_zero,one_mul]
  have he1 : (1/2:ℂ)-((-1:ℂ)+t*Complex.I)=(3/2:ℂ)+(-t)*Complex.I := by ring
  have he2 : ((-1:ℂ)+t*Complex.I)-1/2=-((3/2:ℂ)+(-t)*Complex.I) := by ring
  rw [he1,he2]
  ring

end CompletedGauss

namespace CubicEisenstein

section
open scoped BigOperators Classical
open MeasureTheory
open Finset AddChar MulChar EisensteinEmbedding

section
local notation "Eis" => ActualEisensteinCubic.O

lemma breveE_star (z : ℂ) : star (ShortDraftTrace.breveE z)=ShortDraftTrace.breveE (-z) := by
  change (starRingEnd ℂ) (Complex.exp (2*Real.pi*Complex.I*(z+starRingEnd ℂ z)))=
    Complex.exp (2*Real.pi*Complex.I*((-z)+starRingEnd ℂ (-z)))
  rw [←Complex.exp_conj]
  congr 1
  simp only [map_mul,map_add,map_neg,map_ofNat,Complex.conj_ofReal,Complex.conj_I,
    starRingEnd_self_apply]
  ring

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

end

open ActualEisensteinCubic CompletedGauss CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

end CubicEisenstein

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.MellinSupport
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

namespace CubicEisenstein
open Filter MeasureTheory Asymptotics
open scoped BigOperators Classical Topology MatrixGroups

section
open CubicKubota EisensteinCuspModThree
local notation "Eis" => ActualEisensteinCubic.O

lemma cubicSourceConjugateFunction_levelTwo (G:levelTwo) (w:HyperbolicSpace) :
    cubicSourceConjugateFunction (integralComplexMatrix (G:SL(2,Eis)) • w)=
      star (levelTwoComplexCharacter G)*cubicSourceConjugateFunction w := by
  simp only [cubicSourceConjugateFunction,cubicSourceResidualFunction_automorphy,star_mul]
  ring

theorem cubicSourceConjugateFunction_cuspDerivative_levelTwo (G:levelTwo)
    (g H:SL(2,ℂ)) (hfactor:g=integralComplexMatrix (G:SL(2,Eis))*H)
    (hc:g 1 0≠0) (v:ℝ) (hv:0<v) :
    horizontalWirtingerBar (fun z=>cubicSourceConjugateFunction (upperPoint z v hv)) (g 0 0/g 1 0)=
      (star (levelTwoComplexCharacter G)*(-1/((g 1 0)^2*(v:ℂ)^2)))*
        horizontalWirtingerZ
          (fun z=>cubicSourceConjugateFunction (H • upperPoint z (1/(‖g 1 0‖^2*v)) (by positivity)))
          (-g 1 1/g 1 0) := by
  refine cuspDerivative_of_transform cubicSourceConjugateFunction g H
    (star (levelTwoComplexCharacter G)) ?_ hc v hv ?_
  · intro w
    rw [hfactor,mul_smul,cubicSourceConjugateFunction_levelTwo]
  · exact cubicSourceConjugateFunction_translate_split_differentiableAt H _ (by positivity)

lemma cuspBarProfile_conjugate_reflection_levelTwo (G:levelTwo)
    (g H:SL(2,ℂ)) (hfactor:g=integralComplexMatrix (G:SL(2,Eis))*H)
    (hc:g 1 0≠0) (v:ℝ) (hv:0<v) :
    cuspBarProfile cubicSourceConjugateFunction (g 0 0/g 1 0) v=
      reflectedCuspProfile (-star (levelTwoComplexCharacter G)/(g 1 0)^2)
        (‖g 1 0‖^2)
        (cuspZProfile (fun w=>cubicSourceConjugateFunction (H • w)) (-g 1 1/g 1 0)) v := by
  have hdual:0<(‖g 1 0‖^2*v)⁻¹ := by positivity
  rw [cuspBarProfile_positive _ _ _ hv,reflectedCuspProfile,cuspZProfile_positive _ _ _ hdual]
  have he:=cubicSourceConjugateFunction_cuspDerivative_levelTwo G g H hfactor hc v hv
  have hp:(v:ℂ)^(-2:ℂ)=((v:ℂ)^2)⁻¹ := by
    rw [Complex.cpow_neg,Complex.cpow_ofNat]
  rw [hp]
  simp only [one_div] at he
  rw [he]
  ring

lemma conjugateSource_cuspRepresentative_zProfile_decay (j:Fin 3) (z:ℂ) :
    ∃deltaLoss:ℝ,0<deltaLoss ∧ cuspZProfile (fun w=>cubicSourceConjugateFunction
      (integralComplexMatrix (cuspRepresentative j) • w)) z
        =O[atTop] (fun v:ℝ=>Real.exp (-deltaLoss*v)) := by
  fin_cases j
  · refine ⟨residualCuspDecayRate,residualCuspDecayRate_pos,?_⟩
    simpa [cuspRepresentative,cuspParameter,lowerCuspMatrix_zero]
      using cuspZProfile_conjugate_isBigO z
  · refine ⟨residualCuspDecayRate/3,div_pos residualCuspDecayRate_pos (by norm_num),?_⟩
    simpa [cuspRepresentative,cuspParameter,ramifiedCuspRoot,ramifiedOmegaUnit_val]
      using ramifiedConjugate_zProfile_isBigO false z
  · refine ⟨residualCuspDecayRate/3,div_pos residualCuspDecayRate_pos (by norm_num),?_⟩
    simpa [cuspRepresentative,cuspParameter,ramifiedCuspRoot,ramifiedOmegaUnit_val]
      using ramifiedConjugate_zProfile_isBigO true z

theorem conjugateSource_levelTwo_three_cusp_mellin_entire (G:levelTwo)
    (j:Fin 3) (g:SL(2,ℂ))
    (hfactor:g=integralComplexMatrix (G:SL(2,Eis))*integralComplexMatrix (cuspRepresentative j))
    (hc:g 1 0≠0) :
    ((∀s:ℂ,MellinConvergent
      (cuspBarProfile cubicSourceConjugateFunction (g 0 0/g 1 0)) s) ∧
      Differentiable ℂ (mellin (cuspBarProfile cubicSourceConjugateFunction (g 0 0/g 1 0)))) ∧
    ((∀s:ℂ,MellinConvergent
      (cuspZProfile (fun w=>cubicSourceConjugateFunction
        (integralComplexMatrix (cuspRepresentative j) • w)) (-g 1 1/g 1 0)) s) ∧
      Differentiable ℂ (mellin
        (cuspZProfile (fun w=>cubicSourceConjugateFunction
          (integralComplexMatrix (cuspRepresentative j) • w)) (-g 1 1/g 1 0)))) := by
  have hchar:levelTwoComplexCharacter G≠0 := by
    intro hz
    have hn:=norm_levelTwoComplexCharacter G
    rw [hz,norm_zero] at hn
    exact zero_ne_one hn
  have hscalar:-star (levelTwoComplexCharacter G)/(g 1 0)^2≠0 :=
    div_ne_zero (neg_ne_zero.mpr (star_ne_zero.mpr hchar)) (pow_ne_zero 2 hc)
  obtain ⟨deltaLoss,hδ,hb⟩:=conjugateSource_cuspRepresentative_zProfile_decay j (-g 1 1/g 1 0)
  exact cusp_mellin_entire_both
    (cuspBarProfile cubicSourceConjugateFunction (g 0 0/g 1 0))
    (cuspZProfile (fun w=>cubicSourceConjugateFunction
      (integralComplexMatrix (cuspRepresentative j) • w)) (-g 1 1/g 1 0))
    (-star (levelTwoComplexCharacter G)/(g 1 0)^2) hscalar (‖g 1 0‖^2)
    residualCuspDecayRate deltaLoss (sq_pos_of_pos (norm_pos_iff.mpr hc)) residualCuspDecayRate_pos hδ
    (cuspBarProfile_conjugate_continuousOn _) (cuspZProfile_conjugate_translate_continuousOn _ _)
    (cuspBarProfile_conjugate_isBigO _) hb
    (fun v hv=>cuspBarProfile_conjugate_reflection_levelTwo G g _ hfactor hc v hv)

end

open CubicKubota EisensteinCuspModThree ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.RamifiedTransform
namespace OAI

noncomputable section

namespace CubicEisenstein

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

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

lemma unramifiedGaussResidue_prime_pow_mod (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (h:Eis) (_hh:h≠0) (n:ℕ) :
    unramifiedGaussResidue (h*p^n)=unramifiedGaussResidue (h*p^(n%3)) := by
  induction n using Nat.strong_induction_on with
  | h n ih=>
    by_cases hn:n<3
    · rw [Nat.mod_eq_of_lt hn]
    · have hn3:3≤n:=by omega
      have he:h*p^n=(h*p^(n-3))*p^3:=by rw [mul_assoc,←pow_add,Nat.sub_add_cancel hn3]
      rw [he,unramifiedGaussResidue_prime_cube p hp hprimary _,
        ih (n-3) (by omega)]
      have hm:(n-3)%3=n%3:=by omega
      rw [hm]

theorem unramifiedGaussResidue_prime_square (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) :
    unramifiedGaussResidue (h*p^2)=0 := by
  have hh:h≠0:=fun he=>hph (he▸dvd_zero p)
  have he:=unramifiedGaussResidue_square_cube p hp hprimary h hph
  rw [show h*p^5=(h*p^2)*p^3 by ring,
    unramifiedGaussResidue_prime_cube p hp hprimary _] at he
  have hq:(Ideal.absNorm (Ideal.span {p}):ℂ)≠0:=Nat.cast_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))
  have hz:(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*unramifiedGaussResidue (h*p^2)=0:=by
    linear_combination -he
  exact (mul_eq_zero.mp hz).resolve_left (inv_ne_zero hq)

theorem unramifiedGaussResidue_prime_power_table (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) (n:ℕ) :
    unramifiedGaussResidue (h*p^n)=
      if n%3=0 then unramifiedGaussResidue h
      else if n%3=1 then
        (Ideal.absNorm (Ideal.span {p}):ℂ)^(-(2/3:ℂ))*
          primeCubicGauss p hp hprimary 2 h*unramifiedGaussResidue h
      else 0 := by
  have hh:h≠0:=fun he=>hph (he▸dvd_zero p)
  rw [unramifiedGaussResidue_prime_pow_mod p hp hprimary h hh n]
  split_ifs with h0 h1
  · simp only [h0,pow_zero,mul_one]
  · simp only [h1,pow_one]
    exact unramifiedGaussResidue_prime_factor p hp hprimary h hph
  · have hn:n%3=2:=by omega
    rw [hn,unramifiedGaussResidue_prime_square p hp hprimary h hph]

end

section
open scoped BigOperators Classical
open MeasureTheory
open Finset AddChar MulChar EisensteinEmbedding

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

lemma thetaFrequencyScale_ne_zero : thetaFrequencyScale≠0 := by
  exact one_div_ne_zero (mul_ne_zero (by norm_num) eisLam_ne_zero)

lemma thetaBesselScale_pos : 0<thetaBesselScale := norm_pos_iff.mpr thetaFrequencyScale_ne_zero

lemma cuspFrequency_eq_thetaFrequencyScale (h : Eis) :
    cuspFrequency h=thetaFrequencyScale*eisEmbedding h := by
  unfold cuspFrequency thetaFrequencyScale
  ring

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

end

open scoped BigOperators Classical
open MeasureTheory
open Finset AddChar MulChar EisensteinEmbedding

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

end CubicEisenstein

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.EntireMellinProfile
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
open Filter MeasureTheory
open scoped Classical BigOperators Topology ContDiff

lemma mellin_eq_of_positive_eq (F G : ℝ→ℂ) (hFG : ∀v : ℝ,0<v→F v=G v) (s : ℂ) :
    mellin F s=mellin G s := by
  unfold mellin
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v hv
  dsimp only
  rw [hFG v hv]

lemma continuedBesselDirichlet_finite_sum {ι : Type*} [Fintype ι]
    (F : ι→ℝ→ℂ) (w : ι→ℂ) (q : ℝ) (s : ℂ)
    (hF : ∀i,MellinConvergent (F i) (2*s)) :
    continuedBesselDirichlet (fun v=>∑i,w i*F i v) q s=
      ∑i,w i*continuedBesselDirichlet (F i) q s := by
  have hi (i : ι) : IntegrableOn (fun v : ℝ=>(v:ℂ)^(2*s-1)*(w i*F i v)) (Set.Ioi 0) := by
    simpa only [MellinConvergent,smul_eq_mul] using (hF i).const_smul (w i)
  have hm : mellin (fun v=>∑i,w i*F i v) (2*s)=∑i,w i*mellin (F i) (2*s) := by
    unfold mellin
    simp only [smul_eq_mul,Finset.mul_sum]
    rw [integral_finsetSum Finset.univ (fun i _=>hi i)]
    apply Finset.sum_congr rfl
    intro i _
    simpa only [mellin,smul_eq_mul] using mellin_const_smul (F i) (2*s) (w i)
  rw [continuedBesselDirichlet,hm,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  unfold continuedBesselDirichlet
  ring

lemma besselSmoothingIntegrand_finite_sum {ι : Type*} [Fintype ι]
    (F : ℝ→ℂ) (G : ι→ℝ→ℂ) (w : ι→ℂ)
    (hFG : ∀v : ℝ,0<v→F v=∑i,w i*G i v)
    (q : ℝ) (V : ℝ→ℂ) (X : ℝ) (s : ℂ)
    (hG : ∀i,MellinConvergent (G i) (2*s)) :
    besselSmoothingIntegrand F q V X s=
      ∑i,w i*besselSmoothingIntegrand (G i) q V X s := by
  have hm := mellin_eq_of_positive_eq F (fun v=>∑i,w i*G i v) hFG (2*s)
  have hd : continuedBesselDirichlet F q s=
      continuedBesselDirichlet (fun v=>∑i,w i*G i v) q s := by
    simp only [continuedBesselDirichlet,hm]
  rw [besselSmoothingIntegrand,hd,continuedBesselDirichlet_finite_sum G w q s hG,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  unfold besselSmoothingIntegrand
  ring

theorem besselSmoothingIntegrand_finite_integrable {ι : Type*} [Fintype ι]
    (F : ℝ→ℂ) (G : ι→ℝ→ℂ) (w : ι→ℂ)
    (hFG : ∀v : ℝ,0<v→F v=∑i,w i*G i v)
    (q : ℝ) (V : ℝ→ℂ) (X σ : ℝ)
    (hG : ∀i,∀t : ℝ,MellinConvergent (G i) (2*((σ:ℂ)+t*Complex.I)))
    (hi : ∀i,Integrable (fun t : ℝ=>besselSmoothingIntegrand (G i) q V X ((σ:ℂ)+t*Complex.I))) :
    Integrable (fun t : ℝ=>besselSmoothingIntegrand F q V X ((σ:ℂ)+t*Complex.I)) := by
  have hsum := integrable_finsetSum Finset.univ (fun i _=>(hi i).const_mul (w i))
  apply hsum.congr
  filter_upwards with t
  exact (besselSmoothingIntegrand_finite_sum F G w hFG q V X _ (fun i=>hG i t)).symm

end CompletedGauss

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

namespace CubicEisenstein

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

theorem ramifiedBesselValue_prime_power_vanish (side:Bool) (p:Eis) (hp:Prime p)
    (hpp:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) (k:ℕ) (hk:k%3=2) :
    ramifiedBesselValue side (h*p^k)=0 := by
  unfold ramifiedBesselValue
  split_ifs with hf
  · have hr:ramifiedArithmeticResidue side (h*p^k) hf=0:=by
      unfold ramifiedArithmeticResidue
      apply Finset.sum_eq_zero
      intro i hi
      rw [ramifiedSixIndex_multiplier]
      have hc:IsCoprime ((ramifiedSixUnit side i:Eis)*lambda^(ramifiedSixPower i)) p:=
        (ramified_primary_coprime (ramifiedSixUnit side i) (ramifiedSixPower i) p hpp).of_mul_left_right
      have hnot:¬p∣((ramifiedSixUnit side i:Eis)*lambda^(ramifiedSixPower i))*h:=by
        intro hd
        rcases hp.dvd_mul.mp hd with hd|hd
        · exact hp.not_isUnit (hc.symm.isUnit_of_dvd hd)
        · exact hph hd
      rw [←mul_assoc,unramifiedGaussResidue_prime_power_table p hp hpp _ hnot,hk]
      norm_num
    rw [hr,mul_zero,zero_div]
  · rfl

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.RamifiedValuation
namespace OAI

noncomputable section

namespace CubicEisenstein

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

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss UniqueFactorizationMonoid
local notation "Eis" => ActualEisensteinCubic.O

lemma ramifiedFunction_valuation_ne_two (F:Eis→ℂ)
    (hzero:∀(p:Eis),Prime p→lambda^2∣p-1→∀h:Eis,¬p∣h→∀k:ℕ,k%3=2→F (h*p^k)=0)
    (I P:Ideal Eis) (hI:primaryGenerator I≠0) (hP:P∈normalizedFactors I)
    (u:Eisˣ) (m:ℕ) (hF:F ((u.val*lambda^m)*primaryGenerator I)≠0) :
    (normalizedFactors I).count P%3≠2 := by
  have hI0:=primaryGenerator_ne_zero_ideal I hI
  have hprime:=prime_of_normalized_factor P hP
  let p:=primaryPrime P
  have hp0:p≠0:=primaryPrime_factor_ne_zero I P hI hP
  have hps:=primaryPrime_spec P hp0
  have hp:Prime p:=primaryPrime_isPrime_of_mem I P hI (Multiset.mem_toFinset.mpr hP)
  obtain ⟨J,hJ,hnot⟩:=(FiniteMultiplicity.of_prime_left hprime hI0).exists_eq_pow_mul_and_not_dvd
  have hgen:primaryGenerator I=p^(multiplicity P I)*primaryGenerator J:=by
    calc
      _=primaryGenerator (P^(multiplicity P I)*J):=congrArg primaryGenerator hJ
      _=p^(multiplicity P I)*primaryGenerator J:=by
        rw [primaryGenerator_mul,primaryGenerator_pow]
        have he:primaryGenerator P=p:=by
          rw [←hps.2.2.1,primaryGenerator_span p hp0 hps.2.2.2]
        rw [he]
  have hgJ:primaryGenerator J≠0:=by
    intro hz
    exact hI (by rw [hgen,hz,mul_zero])
  have hpd:¬p∣primaryGenerator J:=by
    intro hd
    apply hnot
    rw [Ideal.dvd_iff_le,←hps.2.2.1,←(primaryGenerator_spec J hgJ).1,
      Ideal.span_singleton_le_span_singleton]
    exact hd
  have hbase:¬p∣(u.val*lambda^m)*primaryGenerator J:=by
    intro hd
    rcases hp.dvd_mul.mp hd with hd|hd
    · exact hp.not_isUnit (((ramified_primary_coprime u m p hps.2.2.2).of_mul_left_right).symm.isUnit_of_dvd hd)
    · exact hpd hd
  have hcount:=multiplicity_eq_count_normalizedFactors hprime.irreducible hI0
  rw [normalize_normalized_factor P hP] at hcount
  intro hc
  have hm:(multiplicity P I)%3=2:=by rwa [hcount]
  apply hF
  rw [hgen,show (u.val*lambda^m)*(p^(multiplicity P I)*primaryGenerator J)=
    ((u.val*lambda^m)*primaryGenerator J)*p^(multiplicity P I) by ring]
  exact hzero p hp hps.2.2.2 _ hbase _ hm

theorem ramifiedBesselValue_squarefree_cube_support (side:Bool) (h:Eis) (hh:h≠0)
    (hB:ramifiedBesselValue side h≠0) :
    ∃(u:Eisˣ) (m:ℕ) (I J:Ideal Eis),Squarefree I ∧
      primaryGenerator I≠0 ∧ primaryGenerator J≠0 ∧
      h=(u.val*lambda^m)*primaryGenerator I*(primaryGenerator J)^3 := by
  obtain ⟨n,u,m,hn,he⟩:=exists_primary_unit_lambda_factor h hh
  let T:Ideal Eis:=Ideal.span {n}
  have hT:primaryGenerator T=n:=primaryGenerator_span n (primary_ne_zero n hn) hn
  have hT0:primaryGenerator T≠0:=by rw [hT]; exact primary_ne_zero n hn
  have hFT:ramifiedBesselValue side ((u.val*lambda^m)*primaryGenerator T)≠0:=by
    rw [hT,mul_comm]
    rwa [←he]
  have hv:∀P∈normalizedFactors T,(normalizedFactors T).count P%3≠2:=by
    intro P hP
    exact ramifiedFunction_valuation_ne_two (ramifiedBesselValue side)
      (fun p hp hpp h hph k hk=>ramifiedBesselValue_prime_power_vanish side p hp hpp h hph k hk)
      T P hT0 hP u m hFT
  have hparts:=thetaParts_mul_cube T (primaryGenerator_ne_zero_ideal T hT0) hv
  have hgen:primaryGenerator T=primaryGenerator (thetaSquarefreePart T)*
      (primaryGenerator (thetaCubePart T))^3:=by
    calc
      _=primaryGenerator (thetaSquarefreePart T*thetaCubePart T^3):=congrArg primaryGenerator hparts.symm
      _=_:=by rw [primaryGenerator_mul,primaryGenerator_pow]
  have hA:primaryGenerator (thetaSquarefreePart T)≠0:=by
    intro hz
    exact hT0 (by rw [hgen,hz,zero_mul])
  have hC:primaryGenerator (thetaCubePart T)≠0:=by
    intro hz
    exact hT0 (by rw [hgen,hz,zero_pow (by decide : (3:ℕ)≠0),mul_zero])
  refine ⟨u,m,thetaSquarefreePart T,thetaCubePart T,thetaSquarefreePart_squarefree T,hA,hC,?_⟩
  rw [he,←hT,hgen]
  ring

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss UniqueFactorizationMonoid
local notation "Eis" => ActualEisensteinCubic.O

lemma sourceResidualFourierCoefficient_prime_power_vanish (p:Eis) (hp:Prime p)
    (hpp:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) (k:ℕ) (hk:k%3=2) :
    sourceResidualFourierCoefficient (h*p^k)=0 := by
  rw [sourceResidualFourierCoefficient,sourceArithmeticResidue_prime_power_table p hp hpp h hph k,hk]
  norm_num

theorem sourceResidualFourierCoefficient_full_squarefree_cube_support (h:Eis) (hh:h≠0)
    (hB:sourceResidualFourierCoefficient h≠0) :
    ∃(u:Eisˣ) (m:ℕ) (I J:Ideal Eis),Squarefree I ∧
      primaryGenerator I≠0 ∧ primaryGenerator J≠0 ∧
      h=(u.val*lambda^m)*primaryGenerator I*(primaryGenerator J)^3 := by
  obtain ⟨n,u,m,hn,he⟩:=exists_primary_unit_lambda_factor h hh
  let T:Ideal Eis:=Ideal.span {n}
  have hT:primaryGenerator T=n:=primaryGenerator_span n (primary_ne_zero n hn) hn
  have hT0:primaryGenerator T≠0:=by rw [hT]; exact primary_ne_zero n hn
  have hFT:sourceResidualFourierCoefficient ((u.val*lambda^m)*primaryGenerator T)≠0:=by
    rw [hT,mul_comm]
    rwa [←he]
  have hv:∀P∈normalizedFactors T,(normalizedFactors T).count P%3≠2:=by
    intro P hP
    exact ramifiedFunction_valuation_ne_two (sourceResidualFourierCoefficient)
      (fun p hp hpp h hph k hk=>sourceResidualFourierCoefficient_prime_power_vanish p hp hpp h hph k hk)
      T P hT0 hP u m hFT
  have hparts:=thetaParts_mul_cube T (primaryGenerator_ne_zero_ideal T hT0) hv
  have hgen:primaryGenerator T=primaryGenerator (thetaSquarefreePart T)*
      (primaryGenerator (thetaCubePart T))^3:=by
    calc
      _=primaryGenerator (thetaSquarefreePart T*thetaCubePart T^3):=congrArg primaryGenerator hparts.symm
      _=_:=by rw [primaryGenerator_mul,primaryGenerator_pow]
  have hA:primaryGenerator (thetaSquarefreePart T)≠0:=by
    intro hz
    exact hT0 (by rw [hgen,hz,zero_mul])
  have hC:primaryGenerator (thetaCubePart T)≠0:=by
    intro hz
    exact hT0 (by rw [hgen,hz,zero_pow (by decide : (3:ℕ)≠0),mul_zero])
  refine ⟨u,m,thetaSquarefreePart T,thetaCubePart T,thetaSquarefreePart_squarefree T,hA,hC,?_⟩
  rw [he,←hT,hgen]
  ring

end

section
open scoped BigOperators Classical MatrixGroups
open MeasureTheory
open Finset AddChar MulChar EisensteinEmbedding

open CubicKubota EisensteinCuspModThree ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

namespace SourceCuspDatum

lemma heightScale_pos (d : SourceCuspDatum) : 0<d.heightScale :=
  sq_pos_of_pos (norm_pos_iff.mpr d.lower_ne_zero)

end SourceCuspDatum

lemma rationalSourceCusp_point (a c : Eis) (hc : c≠0) :
    (rationalSourceCusp a c hc).point=eisEmbedding a/eisEmbedding c :=
  (exists_sourceCuspDatum a c hc).choose_spec

theorem SourceCuspDatum.reflection (d : SourceCuspDatum) (v : ℝ) (hv : 0<v) :
    cuspBarProfile cubicSourceConjugateFunction d.point v=
      d.multiplier/(v:ℂ)^2*sourceCuspZFamily d.index d.dualPoint ((d.heightScale*v)⁻¹) := by
  have he:=cuspBarProfile_conjugate_reflection_levelTwo d.gamma d.matrix
    (integralComplexMatrix (cuspRepresentative d.index)) rfl d.lower_ne_zero v hv
  rw [reflectedCuspProfile_eq_inv_square] at he
  exact he

lemma finiteTwistCusp_point (c : Eis) (hc : c≠0) (h : Eis⧸Ideal.span {c}) :
    (finiteTwistCusp c hc h).point=thetaFourierTranslation c h := by
  rw [finiteTwistCusp,rationalSourceCusp_point,thetaFourierTranslation,TraceLambdaPhase.eisLam_sq]
  simp only [map_mul,map_neg,map_ofNat]

end

open scoped BigOperators Classical
open MeasureTheory
open Finset AddChar MulChar EisensteinEmbedding

local notation "Eis" => ActualEisensteinCubic.O

lemma horizontalPhaseMultiplier_scaled_bar (freq : ℂ) (r : ℝ) :
    (1/2:ℂ)*(horizontalPhaseMultiplier freq (1/(r:ℂ))+
      Complex.I*horizontalPhaseMultiplier freq (Complex.I/(r:ℂ)))=
      2*Real.pi*Complex.I*star freq/(r:ℂ) := by
  simp only [horizontalPhaseMultiplier,star_mul,
    Complex.star_def,map_div₀,map_one,Complex.conj_ofReal,Complex.conj_I]
  ring_nf
  norm_num [Complex.I_sq,Complex.I_pow_three]
  ; ring

namespace SubexponentialBesselCoefficients

lemma scaled_fullFunction_horizontal_hasDerivAt (coeff : SubexponentialBesselCoefficients)
    (constant : ℂ) (r : ℝ) (hr : 0< r) (v : ℝ) (hv : 0<v) (z direction : ℂ) :
    HasDerivAt (fun t:ℝ=>coeff.fullFunction constant
      (upperPoint ((z+(t:ℂ)*direction)/(r:ℂ)) (v/r) (div_pos hv hr)))
      (∑'h:Eis,coeff.directionalTerm h (v/r) (z/(r:ℂ)) (direction/(r:ℂ))) 0 := by
  have h:=coeff.fullFunction_horizontal_hasDerivAt constant (v/r) (div_pos hv hr)
    (z/(r:ℂ)) (direction/(r:ℂ)) 0
  simp only [Complex.ofReal_zero,zero_mul,add_zero] at h
  convert (preTransparency := .instances) h using 1
  funext t
  congr 2
  ring

lemma scaled_fullFunction_wirtingerBar (coeff : SubexponentialBesselCoefficients)
    (constant : ℂ) (r : ℝ) (hr : 0< r) (v : ℝ) (hv : 0<v) (z : ℂ) :
    horizontalWirtingerBar (fun w=>coeff.fullFunction constant
      (upperPoint (w/(r:ℂ)) (v/r) (div_pos hv hr))) z=
      ∑'h:Eis,(2*Real.pi*Complex.I*star (cuspFrequency h)/(r:ℂ))*coeff.term h (v/r,z/(r:ℂ)) := by
  have h1:=(coeff.scaled_fullFunction_horizontal_hasDerivAt constant r hr v hv z 1).deriv
  have hI:=(coeff.scaled_fullFunction_horizontal_hasDerivAt constant r hr v hv z Complex.I).deriv
  simp only [mul_one] at h1
  rw [horizontalWirtingerBar,h1,hI]
  have hs1:=coeff.directionalTerm_summable (v/r) (div_pos hv hr) (z/(r:ℂ)) (1/(r:ℂ))
  have hsI:=(coeff.directionalTerm_summable (v/r) (div_pos hv hr) (z/(r:ℂ)) (Complex.I/(r:ℂ))).mul_left Complex.I
  rw [←tsum_mul_left,←hs1.tsum_add hsI,←tsum_mul_left]
  apply tsum_congr
  intro h
  unfold directionalTerm
  linear_combination coeff.term h (v/r,z/(r:ℂ))*horizontalPhaseMultiplier_scaled_bar (cuspFrequency h) r

theorem scaledConjugate_wirtingerZ (coeff : SubexponentialBesselCoefficients)
    (constant : ℂ) (r : ℝ) (hr : 0< r) (v : ℝ) (hv : 0<v) (z : ℂ) :
    horizontalWirtingerZ (fun w=>star (coeff.fullFunction constant
      (upperPoint (w/(r:ℂ)) (v/r) (div_pos hv hr)))) z=
      ∑'h:Eis,coeff.scaledConjugateZTerm r v z h := by
  rw [horizontalWirtingerZ_star,coeff.scaled_fullFunction_wirtingerBar constant r hr v hv z,tsum_star]
  apply tsum_congr
  intro h
  unfold scaledConjugateZTerm
  simp only [star_mul,Complex.star_def,map_div₀,map_mul,
    map_ofNat,Complex.conj_ofReal,Complex.conj_I,starRingEnd_self_apply]
  ring

lemma scaledConjugateZTerm_zero (coeff : SubexponentialBesselCoefficients)
    (r v : ℝ) (z : ℂ) : coeff.scaledConjugateZTerm r v z 0=0 := by
  simp only [scaledConjugateZTerm,cuspFrequency,map_zero,zero_div,mul_zero,zero_mul]

lemma scaledConjugateZTerm_bessel (coeff : SubexponentialBesselCoefficients)
    (r : ℝ) (hr : 0< r) (v : ℝ) (hv : 0<v) (z : ℂ) (h : Eis) (hh : h≠0) :
    coeff.scaledConjugateZTerm r v z h=
      (-2*Real.pi*Complex.I*cuspFrequency h/(r:ℂ))*star (coeff.value h)*((v/r:ℝ):ℂ)*
        schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*(v/r))*
          ShortDraftTrace.breveE (-cuspFrequency h*(z/(r:ℂ))) := by
  rw [scaledConjugateZTerm,coeff.term_bessel h hh (v/r) (div_pos hv hr) (z/(r:ℂ))]
  have hx : 0<4*Real.pi*‖cuspFrequency h‖*(v/r) :=
    mul_pos (mul_pos (mul_pos (by norm_num) Real.pi_pos)
      (norm_pos_iff.mpr (cuspFrequency_ne_zero h hh))) (div_pos hv hr)
  rw [schlafliBesselK_cubic_real _ hx]
  simp only [star_mul,breveE_star,Complex.star_def,Complex.conj_ofReal,neg_mul]
  ring

end SubexponentialBesselCoefficients

end CubicEisenstein

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.SourceCuspKernels
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

namespace CubicEisenstein

section
open scoped BigOperators Classical MatrixGroups
open MeasureTheory
open Finset AddChar MulChar EisensteinEmbedding

open CubicKubota EisensteinCuspModThree ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma ramifiedSource_scaled_fullFunction (side : Bool) (v : ℝ) (hv : 0<v) (z : ℂ) :
    ramifiedSourceFunction (ramifiedCuspRoot side:Eis) (upperPoint z v hv)=
      (ramifiedBesselCoefficients side).fullFunction 0
        (upperPoint (z/3) (v/3) (by positivity)) := by
  rw [ramifiedSource_eq_series]
  simp only [SubexponentialBesselCoefficients.fullFunction,zero_mul,zero_add,
    SubexponentialBesselCoefficients.function,hyperbolicHeight_upperPoint,hyperbolicHorizontal_upperPoint]

theorem sourceCusp_bessel_expansion (j : Fin 3) (v : ℝ) (hv : 0<v) (z : ℂ) :
    cubicSourceResidualFunction (integralComplexMatrix (cuspRepresentative j) • upperPoint z v hv)=
      (sourceCuspCoefficients j).fullFunction (sourceCuspBesselConstant j)
        (upperPoint (z/(sourceCuspScale j:ℂ)) (v/sourceCuspScale j)
          (div_pos hv (sourceCuspScale_pos j))) := by
  fin_cases j
  · simpa [sourceCuspCoefficients,sourceCuspBesselConstant,sourceCuspScale,cuspRepresentative,cuspParameter,
      lowerCuspMatrix_zero,sourceBesselFunction] using congrFun cubicSourceResidualFunction_eq_bessel (upperPoint z v hv)
  · simpa [sourceCuspCoefficients,sourceCuspBesselConstant,sourceCuspScale,cuspRepresentative,cuspParameter,
      ramifiedSourceFunction,ramifiedCuspRoot,ramifiedOmegaUnit_val] using
      ramifiedSource_scaled_fullFunction false v hv z
  · simpa [sourceCuspCoefficients,sourceCuspBesselConstant,sourceCuspScale,cuspRepresentative,cuspParameter,
      ramifiedSourceFunction,ramifiedCuspRoot,ramifiedOmegaUnit_val] using
      ramifiedSource_scaled_fullFunction true v hv z

theorem sourceCuspZFamily_series (j : Fin 3) (z : ℂ) (v : ℝ) (hv : 0<v) :
    sourceCuspZFamily j z v=∑'h:Eis,sourceCuspZTerm j z v h := by
  rw [sourceCuspZFamily,cuspZProfile_positive _ _ _ hv]
  have he : (fun w=>cubicSourceConjugateFunction (integralComplexMatrix (cuspRepresentative j) • upperPoint w v hv))=
      fun w=>star ((sourceCuspCoefficients j).fullFunction (sourceCuspBesselConstant j)
        (upperPoint (w/(sourceCuspScale j:ℂ)) (v/sourceCuspScale j) (div_pos hv (sourceCuspScale_pos j)))) := by
    funext w
    exact congrArg star (sourceCusp_bessel_expansion j v hv w)
  rw [he]
  exact (sourceCuspCoefficients j).scaledConjugate_wirtingerZ (sourceCuspBesselConstant j)
    (sourceCuspScale j) (sourceCuspScale_pos j) v hv z

lemma sourceCuspZTerm_zero (j : Fin 3) (z : ℂ) (v : ℝ) : sourceCuspZTerm j z v 0=0 :=
  (sourceCuspCoefficients j).scaledConjugateZTerm_zero _ _ _

lemma sourceCuspZTerm_bessel (j : Fin 3) (z : ℂ) (v : ℝ) (hv : 0<v)
    (h : Eis) (hh : h≠0) :
    sourceCuspZTerm j z v h=
      (-2*Real.pi*Complex.I*cuspFrequency h/(sourceCuspScale j:ℂ))*
        star ((sourceCuspCoefficients j).value h)*((v/sourceCuspScale j:ℝ):ℂ)*
        schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*(v/sourceCuspScale j))*
          ShortDraftTrace.breveE (-cuspFrequency h*(z/(sourceCuspScale j:ℂ))) :=
  (sourceCuspCoefficients j).scaledConjugateZTerm_bessel _ (sourceCuspScale_pos j) v hv z h hh

end

open scoped BigOperators Classical
open MeasureTheory
open Finset AddChar MulChar EisensteinEmbedding

open ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma sourceCuspRadialLength_pos (h : Eis) : 0<sourceCuspRadialLength h := by
  by_cases hh:h=0
  · simp only [sourceCuspRadialLength,if_pos hh,zero_lt_one]
  · rw [sourceCuspRadialLength,if_neg hh]
    exact sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hh))

lemma sourceCuspRadialScale_pos (j : Fin 3) : 0<sourceCuspRadialScale j :=
  div_pos thetaBesselScale_pos (sourceCuspScale_pos j)

lemma sourceCuspRadialCoefficient_norm (j : Fin 3) (z : ℂ) (h : Eis) :
    ‖sourceCuspRadialCoefficient j z h‖=‖sourceCuspRadialBaseCoefficient j h‖ := by
  rw [sourceCuspRadialCoefficient,norm_mul,breveE_norm,mul_one]

lemma sourceCuspRadialCoefficient_zero (j : Fin 3) (z : ℂ) :
    sourceCuspRadialCoefficient j z 0=0 := by
  simp only [sourceCuspRadialCoefficient,sourceCuspRadialBaseCoefficient,cuspFrequency,
    map_zero,zero_div,mul_zero,zero_mul]

lemma sourceCuspRadialLength_frequency (h : Eis) (hh : h≠0) :
    ‖cuspFrequency h‖=thetaBesselScale*Real.sqrt (sourceCuspRadialLength h) := by
  rw [cuspFrequency_eq_thetaFrequencyScale,norm_mul,sourceCuspRadialLength,if_neg hh,
    Real.sqrt_sq (norm_nonneg _)]
  rfl

theorem sourceCuspZTerm_eq_radial (j : Fin 3) (z : ℂ) (v : ℝ) (hv : 0<v) (h : Eis) :
    sourceCuspZTerm j z v h=
      (sourceCuspRadialCoefficient j z h*(sourceCuspRadialLength h:ℂ))*(v:ℂ)*
        schlafliBesselK (1/3) (4*Real.pi*sourceCuspRadialScale j*Real.sqrt (sourceCuspRadialLength h)*v) := by
  by_cases hh:h=0
  · subst h
    rw [sourceCuspZTerm_zero,sourceCuspRadialCoefficient_zero]
    ring
  · rw [sourceCuspZTerm_bessel j z v hv h hh,sourceCuspRadialLength_frequency h hh]
    have ha : 4*Real.pi*(thetaBesselScale*Real.sqrt (sourceCuspRadialLength h))*(v/sourceCuspScale j)=
        4*Real.pi*sourceCuspRadialScale j*Real.sqrt (sourceCuspRadialLength h)*v := by
      unfold sourceCuspRadialScale
      ring
    rw [ha]
    have hs0 : (sourceCuspScale j:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (sourceCuspScale_pos j).ne'
    have hl0 : (sourceCuspRadialLength h:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (sourceCuspRadialLength_pos h).ne'
    simp only [sourceCuspRadialCoefficient,sourceCuspRadialBaseCoefficient,Complex.ofReal_div]
    field_simp [hs0,hl0]

theorem sourceCuspZFamily_eq_radialBesselProfile (j : Fin 3) (z : ℂ) (v : ℝ) (hv : 0<v) :
    sourceCuspZFamily j z v=
      radialBesselProfile sourceCuspRadialLength (sourceCuspRadialCoefficient j z) (sourceCuspRadialScale j) v := by
  rw [sourceCuspZFamily_series j z v hv]
  exact tsum_congr (sourceCuspZTerm_eq_radial j z v hv)

end CubicEisenstein

open Filter MeasureTheory
open scoped Classical BigOperators Topology

namespace CompletedGauss

lemma positive_nat_pow_cpow (x:ℝ) (hx:0≤x) (n:ℕ) (s:ℂ) :
    ((x^n:ℝ):ℂ)^s=((x:ℂ)^s)^n := by
  induction n with
  | zero => simp
  | succ n hn =>
      rw [pow_succ,Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (pow_nonneg hx n) hx,
        hn,pow_succ]

lemma positive_reflection_powers (Q u d X r:ℝ)
    (hQ:0<Q) (hu:0<u) (hd:0<d) (hX:0<X) (hr:0< r) (w:ℂ) :
    (Q:ℂ)^(1+2*w)*(u:ℂ)^(2-2*w)*(2:ℂ)^(4*w)/(d:ℂ)^(2+2*w)*
      (X:ℂ)^(-w)*(r:ℂ)^(-w)=
      ((Q*(u/d)^2:ℝ):ℂ)*((u^2*d^2*X*r/(16*Q^2):ℝ):ℂ)^(-w) := by
  have hQ0:(Q:ℂ)≠0:=Complex.ofReal_ne_zero.mpr hQ.ne'
  have hu0:(u:ℂ)≠0:=Complex.ofReal_ne_zero.mpr hu.ne'
  have hd0:(d:ℂ)≠0:=Complex.ofReal_ne_zero.mpr hd.ne'
  have hX0:(X:ℂ)≠0:=Complex.ofReal_ne_zero.mpr hX.ne'
  have hr0:(r:ℂ)≠0:=Complex.ofReal_ne_zero.mpr hr.ne'
  have hQp:(Q:ℂ)^w≠0:=Complex.cpow_ne_zero_iff.mpr (Or.inl hQ0)
  have hup:(u:ℂ)^w≠0:=Complex.cpow_ne_zero_iff.mpr (Or.inl hu0)
  have hdp:(d:ℂ)^w≠0:=Complex.cpow_ne_zero_iff.mpr (Or.inl hd0)
  have hXp:(X:ℂ)^w≠0:=Complex.cpow_ne_zero_iff.mpr (Or.inl hX0)
  have hrp:(r:ℂ)^w≠0:=Complex.cpow_ne_zero_iff.mpr (Or.inl hr0)
  have h2p:(2:ℂ)^w≠0:=Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
  have h16:((16:ℝ):ℂ)^w=((2:ℂ)^w)^4 := by
    have hh:=positive_nat_pow_cpow 2 (by norm_num) 4 w
    norm_num only [show (2:ℝ)^4=16 by norm_num] at hh
    exact hh
  have hy:((u^2*d^2*X*r/(16*Q^2):ℝ):ℂ)^w=
      (((u:ℂ)^w)^2*((d:ℂ)^w)^2*(X:ℂ)^w*(r:ℂ)^w)/
        (((2:ℂ)^w)^4*((Q:ℂ)^w)^2) := by
    rw [Complex.ofReal_div,Complex.div_cpow_ofReal_nonneg (by positivity) (by positivity)]
    rw [Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (by positivity) hr.le,
      Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (by positivity) hX.le,
      Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity),
      Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (by norm_num) (by positivity)]
    rw [positive_nat_pow_cpow u hu.le,positive_nat_pow_cpow d hd.le,
      positive_nat_pow_cpow Q hQ.le,h16]
  rw [Complex.cpow_add _ _ hQ0,Complex.cpow_one,
    Complex.cpow_sub _ _ hu0,Complex.cpow_add _ _ hd0]
  simp only [Complex.cpow_ofNat_mul,Complex.cpow_ofNat]
  rw [Complex.cpow_neg,Complex.cpow_neg,Complex.cpow_neg,hy]
  push_cast
  field_simp

theorem bessel_reflection_scale (q d Q X r:ℝ)
    (hq:0<q) (hd:0<d) (hQ:0<Q) (hX:0<X) (hr:0< r) (w:ℂ) :
    (Q:ℂ)^(2-2*(1/2-w))*besselReflectionFactor q d (1/2-w)*
      (X:ℂ)^(-w)*(r:ℂ)^(-w)=
      ((Q*(q/d)^2:ℝ):ℂ)*
        ((CubicReflectionKernel.paperScale*(27*q^2*d^2*X*r/Q^2):ℝ):ℂ)^(-w) := by
  have he:=positive_reflection_powers Q (4*Real.pi*q) (4*Real.pi*d) X r
    hQ (by positivity) (by positivity) hX hr w
  have hp:Q*((4*Real.pi*q)/(4*Real.pi*d))^2=Q*(q/d)^2 := by
    field_simp
  have hy:(4*Real.pi*q)^2*(4*Real.pi*d)^2*X*r/(16*Q^2)=
      CubicReflectionKernel.paperScale*(27*q^2*d^2*X*r/Q^2) := by
    unfold CubicReflectionKernel.paperScale
    ring
  rw [hp,hy] at he
  unfold besselReflectionFactor
  convert (preTransparency := .instances) he using 1 ; congr 2 ; ring_nf

end CompletedGauss

open Filter MeasureTheory
open scoped Classical BigOperators Topology ContDiff

namespace CubicReflectionKernel

lemma paperKernel_three_halves (V:ℝ→ℂ) (v0 v1:ℝ) (hv0:0<v0)
    (hVs:Function.support V⊆Set.Icc v0 v1) (hV:ContDiff ℝ ∞ V)
    (x:ℝ) (hx:0<x) :
    paperKernel V x=(1/(2*Real.pi):ℂ)*∫t:ℝ,
      ((paperScale*x:ℝ):ℂ)^(-((3/2:ℂ)+t*Complex.I))*
        mellinEulerData V 0 ((3/2:ℂ)+t*Complex.I) := by
  have he:=mellinInv_euler_shift V v0 v1 hv0 hVs hV 2 0 (3/2) (by norm_num)
    (paperScale*x) (mul_pos paperScale_pos hx)
  change paperKernel V x=_
  have hl:mellinInv 0 (mellinEulerData V 0) (paperScale*x)=paperKernel V x:=by
    have hf : mellinEulerData V 0=(fun s:ℂ=>mellin V (-s)*gammaMultiplier s) := by
      funext s
      simp only [mellinEulerData,pow_zero,one_mul,mellinData]
    rw [hf]
    rfl
  rw [hl] at he
  simpa only [mellinInv,smul_eq_mul,Complex.real_smul,Complex.ofReal_div,
    Complex.ofReal_one,Complex.ofReal_mul,Complex.ofReal_ofNat] using he

end CubicReflectionKernel
namespace CompletedGauss

section
open CubicReflectionKernel

theorem paperKernel_weighted_mellin {α:Type*} [Countable α]
    (r:α→ℝ) (hr:∀i,0< r i) (a:α→ℂ)
    (has:Summable (fun i=>‖a i‖*(r i)^(-(3/2:ℝ))))
    (V:ℝ→ℂ) (v0 v1:ℝ) (hv0:0<v0)
    (hVs:Function.support V⊆Set.Icc v0 v1) (hV:ContDiff ℝ ∞ V)
    (c:ℝ) (hc:0<c) :
    (∑'i,a i*paperKernel V (c*r i))=(1/(2*Real.pi):ℂ)*∫t:ℝ,
      (∑'i,a i*(r i:ℂ)^(-((3/2:ℂ)+t*Complex.I)))*
        (((paperScale*c:ℝ):ℂ)^(-((3/2:ℂ)+t*Complex.I))*
          mellinEulerData V 0 ((3/2:ℂ)+t*Complex.I)) := by
  let M:ℝ→ℂ:=fun t=>((paperScale*c:ℝ):ℂ)^(-((3/2:ℂ)+t*Complex.I))*
    mellinEulerData V 0 ((3/2:ℂ)+t*Complex.I)
  have hM:Integrable M:=by
    simpa only [M,inverseMellinIntegrand,Complex.ofReal_div,Complex.ofReal_ofNat] using
      inverseMellinIntegrand_vertical_integrable V v0 v1 hv0 hVs hV 2 0 (3/2)
        (by norm_num) (paperScale*c) (mul_pos paperScale_pos hc)
  have hi (i:α) : a i*paperKernel V (c*r i)=(1/(2*Real.pi):ℂ)*∫t:ℝ,
      a i*(r i:ℂ)^(-((3/2:ℂ)+t*Complex.I))*M t := by
    rw [paperKernel_three_halves V v0 v1 hv0 hVs hV _ (mul_pos hc (hr i))]
    rw [←mul_assoc,mul_comm (a i),mul_assoc,←integral_const_mul]
    congr 1
    apply integral_congr_ae
    filter_upwards with t
    rw [show paperScale*(c*r i)=(paperScale*c)*r i by ring,
      Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (mul_pos paperScale_pos hc).le (hr i).le]
    dsimp only [M]
    ring
  simp_rw [hi]
  rw [tsum_mul_left]
  congr 1
  simpa only [M,Complex.ofReal_div,Complex.ofReal_ofNat] using
    weighted_vertical_sum_integral r hr a (3/2) has M hM

end

open CubicEisenstein CubicReflectionKernel

lemma besselSmoothingIntegrand_reflected_kernel_line {α:Type*} [Countable α]
    (F:ℝ→ℂ) (r:α→ℝ) (hr:∀i,0< r i) (a:α→ℂ)
    (q d Q:ℝ) (hq:0<q) (hd:0<d) (hQ:0<Q) (A:ℂ)
    (hreflect:∀v:ℝ,0<v→F v=A*((v:ℂ)^(-2:ℂ)*radialBesselProfile r a d ((Q*v)⁻¹)))
    (has:Summable (fun i=>‖a i‖*(r i)^(-(3/2:ℝ))))
    (V:ℝ→ℂ) (X:ℝ) (hX:0<X) (t:ℝ) :
    besselSmoothingIntegrand F q V X ((-1:ℂ)+(-t)*Complex.I)=
      (A*((Q*(q/d)^2:ℝ):ℂ))*
        ((∑'i,a i*(r i:ℂ)^(-((3/2:ℂ)+t*Complex.I)))*
          (((paperScale*(27*q^2*d^2*X/Q^2):ℝ):ℂ)^(-((3/2:ℂ)+t*Complex.I))*
            mellinEulerData V 0 ((3/2:ℂ)+t*Complex.I))) := by
  let s:ℂ:=(-1:ℂ)+(-t)*Complex.I
  let w:ℂ:=(3/2:ℂ)+t*Complex.I
  have hs:s.re-1/2=-(3/2:ℝ):=by dsimp [s];norm_num
  have hslt:s.re<4/3:=by dsimp [s];norm_num
  have hsum:Summable (fun i=>‖a i‖*(r i)^(s.re-1/2)):=by simpa only [hs] using has
  have hsw:1/2-w=s:=by dsimp [s,w];ring
  have hw:1/2-s=w:=by rw [←hsw];ring
  have hsw':s-1/2=-w:=by rw [←hsw];ring
  have hp:=bessel_reflection_scale q d Q X 1 hq hd hQ hX (by norm_num) w
  simp only [hsw,Complex.ofReal_one,Complex.one_cpow,mul_one] at hp
  have he:=continuedBesselDirichlet_reflection F r hr a q d Q hd hQ A hreflect s hslt hsum
  change besselSmoothingIntegrand F q V X s=_
  rw [besselSmoothingIntegrand,he,hw,hsw']
  change _=(A*((Q*(q/d)^2:ℝ):ℂ))*
    ((∑'i,a i*(r i:ℂ)^(-w))*
      (((paperScale*(27*q^2*d^2*X/Q^2):ℝ):ℂ)^(-w)*mellinEulerData V 0 w))
  rw [mellinEulerData,pow_zero,one_mul,mellinData]
  calc
    _=(A*mellin V (-w)*gammaMultiplier w*(∑'i,a i*(r i:ℂ)^(-w)))*
      ((Q:ℂ)^(2-2*s)*besselReflectionFactor q d s*(X:ℂ)^(-w)):=by ring
    _=_:=by rw [hp];ring

end CompletedGauss

open Filter MeasureTheory
open scoped Classical BigOperators Topology ContDiff

namespace CompletedGauss
open CubicEisenstein CubicReflectionKernel

theorem besselSmoothingIntegral_reflected_kernel {α:Type*} [Countable α]
    (F:ℝ→ℂ) (r:α→ℝ) (hr:∀i,0< r i) (a:α→ℂ)
    (q d Q:ℝ) (hq:0<q) (hd:0<d) (hQ:0<Q) (A:ℂ)
    (hreflect:∀v:ℝ,0<v→F v=A*((v:ℂ)^(-2:ℂ)*radialBesselProfile r a d ((Q*v)⁻¹)))
    (has:Summable (fun i=>‖a i‖*(r i)^(-(3/2:ℝ))))
    (V:ℝ→ℂ) (v0 v1:ℝ) (hv0:0<v0)
    (hVs:Function.support V⊆Set.Icc v0 v1) (hV:ContDiff ℝ ∞ V)
    (X:ℝ) (hX:0<X) :
    (1/(2*Real.pi):ℂ)*∫t:ℝ,besselSmoothingIntegrand F q V X ((-1:ℂ)+t*Complex.I)=
      (A*(Q:ℂ)*((q/d:ℝ):ℂ)^2)*
        ∑'i,a i*paperKernel V (27*q^2*d^2*X*r i/Q^2) := by
  let c:ℝ:=27*q^2*d^2*X/Q^2
  have hc:0<c:=by dsimp [c];positivity
  let M:ℝ→ℂ:=fun t=>(∑'i,a i*(r i:ℂ)^(-((3/2:ℂ)+t*Complex.I)))*
    (((paperScale*c:ℝ):ℂ)^(-((3/2:ℂ)+t*Complex.I))*
      mellinEulerData V 0 ((3/2:ℂ)+t*Complex.I))
  have hk:=paperKernel_weighted_mellin r hr a has V v0 v1 hv0 hVs hV c hc
  have hpoint (t:ℝ) :
      besselSmoothingIntegrand F q V X ((-1:ℂ)+(-t)*Complex.I)=
        (A*((Q*(q/d)^2:ℝ):ℂ))*M t :=
    besselSmoothingIntegrand_reflected_kernel_line F
      r hr a q d Q hq hd hQ A hreflect has V X hX t
  calc
    _=(1/(2*Real.pi):ℂ)*∫t:ℝ,
        besselSmoothingIntegrand F q V X ((-1:ℂ)+(-t)*Complex.I):=by
      congr 1
      simpa only [Complex.ofReal_neg] using
        (integral_neg_eq_self (fun t:ℝ=>
          besselSmoothingIntegrand F q V X ((-1:ℂ)+t*Complex.I)) volume).symm
    _=(A*((Q*(q/d)^2:ℝ):ℂ))*((1/(2*Real.pi):ℂ)*∫t:ℝ,M t):=by
      simp_rw [hpoint]
      rw [integral_const_mul]
      ring
    _=(A*((Q*(q/d)^2:ℝ):ℂ))*(∑'i,a i*paperKernel V (c*r i)):=by rw [hk]
    _=_:=by
      push_cast
      congr 1
      · ring
      · apply tsum_congr
        intro i
        congr 2
        dsimp [c]
        ring

end CompletedGauss

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.FullFrequencyExpansion
namespace OAI

noncomputable section

namespace CubicEisenstein

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

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

lemma squarefreeCube_scale_le_norm_third (I J:Ideal Eis)
    (hI:primaryGenerator I≠0) (u:Eisˣ) (m:ℕ) :
    (3:ℝ)^((m:ℝ)/6)*‖eisEmbedding (primaryGenerator J)‖≤
      ‖eisEmbedding ((u.val*lambda^m)*primaryGenerator I*(primaryGenerator J)^3)‖^(1/3:ℝ) := by
  have hn:1≤‖eisEmbedding (primaryGenerator I)‖:=cubePrime_norm_ge_one _ hI
  have hn':1≤‖eisEmbedding (primaryGenerator I)‖^(1/3:ℝ):=
    Real.one_le_rpow hn (by norm_num)
  have hb:(‖eisEmbedding (primaryGenerator J)‖^3)^(1/3:ℝ)=‖eisEmbedding (primaryGenerator J)‖:=by
    rw [←Real.rpow_natCast_mul (norm_nonneg _)]
    norm_num
  have he:‖eisEmbedding ((u.val*lambda^m)*primaryGenerator I*(primaryGenerator J)^3)‖^(1/3:ℝ)=
      (3:ℝ)^((m:ℝ)/6)*‖eisEmbedding (primaryGenerator I)‖^(1/3:ℝ)*
        ‖eisEmbedding (primaryGenerator J)‖:=by
    rw [map_mul,map_mul,map_pow,norm_mul,norm_mul,norm_pow,
      Real.mul_rpow (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (pow_nonneg (norm_nonneg _) _),
      Real.mul_rpow (norm_nonneg _) (norm_nonneg _),ramified_norm_third,hb]
  rw [he]
  have hscale:0≤(3:ℝ)^((m:ℝ)/6):=Real.rpow_nonneg (by norm_num) _
  have hbn:0≤‖eisEmbedding (primaryGenerator J)‖:=norm_nonneg _
  exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hscale hn') hbn

lemma coefficient_polynomial_of_squarefree_cube_support (F:Eis→ℂ) (C:ℝ) (hC:0≤C)
    (hsupport:∀h:Eis,h≠0→F h≠0→∃(u:Eisˣ) (m:ℕ) (I J:Ideal Eis),Squarefree I ∧
      primaryGenerator I≠0 ∧ primaryGenerator J≠0 ∧
      h=(u.val*lambda^m)*primaryGenerator I*(primaryGenerator J)^3)
    (hbound:∀(I J:Ideal Eis),primaryGenerator I≠0→primaryGenerator J≠0→Squarefree I→
      ∀(u:Eisˣ) (m:ℕ),
      ‖F ((u.val*lambda^m)*primaryGenerator I*(primaryGenerator J)^3)‖≤
        C*(3:ℝ)^((m:ℝ)/6)*‖eisEmbedding (primaryGenerator J)‖)
    (h:Eis) (hh:h≠0) : ‖F h‖≤C*‖eisEmbedding h‖^(1/3:ℝ) := by
  by_cases hz:F h=0
  · rw [hz,norm_zero]
    positivity
  obtain ⟨u,m,I,J,hsq,hI,hJ,rfl⟩:=hsupport h hh hz
  refine (hbound I J hI hJ hsq u m).trans ?_
  have hb:=mul_le_mul_of_nonneg_left (squarefreeCube_scale_le_norm_third I J hI u m) hC
  exact (by simpa only [mul_assoc] using hb)

theorem three_cusp_coefficients_polynomial_bound :
    ∃C:ℝ,0<C ∧ ∀h:Eis,h≠0→
      ‖sourceResidualFourierCoefficient h‖≤C*‖eisEmbedding h‖^(1/3:ℝ) ∧
      ∀side:Bool,‖ramifiedBesselValue side h‖≤C*‖eisEmbedding h‖^(1/3:ℝ) := by
  obtain ⟨C,hC,hbound⟩:=three_cusp_coefficients_squarefree_cube_bound
  refine ⟨C,hC,?_⟩
  intro h hh
  constructor
  · exact coefficient_polynomial_of_squarefree_cube_support sourceResidualFourierCoefficient C hC.le
      sourceResidualFourierCoefficient_full_squarefree_cube_support
      (fun I J hI hJ hsq u m=>(hbound I J hI hJ hsq u m).1) h hh
  · intro side
    exact coefficient_polynomial_of_squarefree_cube_support (ramifiedBesselValue side) C hC.le
      (ramifiedBesselValue_squarefree_cube_support side)
      (fun I J hI hJ hsq u m=>(hbound I J hI hJ hsq u m).2 side) h hh

end

section
open ActualEisensteinCubic ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma coefficient_weighted_summable_of_polynomial (F:Eis→ℂ) (C:ℝ) (hC:0≤C)
    (hF:∀h:Eis,h≠0→‖F h‖≤C*‖eisEmbedding h‖^(1/3:ℝ)) :
    Summable (fun h:Eis=>if h=0 then (0:ℝ) else ‖F h‖*‖cuspFrequency h‖^(-4:ℝ)) := by
  let D:ℝ:=‖(3:ℂ)*eisLam‖
  have hD:0<D:=norm_pos_iff.mpr (mul_ne_zero (by norm_num) eisLam_ne_zero)
  have hDp:0<D^(-4:ℝ):=Real.rpow_pos_of_pos hD _
  have hs:Summable (fun h:Eis=>(C/D^(-4:ℝ))*‖eisEmbedding h‖^(-(11/3):ℝ)):=
    (summable_embedding_rpow (-(11/3):ℝ) (by norm_num)).mul_left _
  apply Summable.of_nonneg_of_le (fun h=>by split_ifs <;> positivity) _ hs
  intro h
  split_ifs with hh
  · exact mul_nonneg (div_nonneg hC hDp.le) (Real.rpow_nonneg (norm_nonneg _) _)
  · have hx:0<‖eisEmbedding h‖:=norm_pos_iff.mpr (eisEmbedding_ne_zero hh)
    have he:‖eisEmbedding h‖^(1/3:ℝ)*‖eisEmbedding h‖^(-4:ℝ)=
        ‖eisEmbedding h‖^(-(11/3):ℝ):=by
      rw [←Real.rpow_add hx]
      congr 1
      norm_num
    calc
      _≤(C*‖eisEmbedding h‖^(1/3:ℝ))*‖cuspFrequency h‖^(-4:ℝ):=
        mul_le_mul_of_nonneg_right (hF h hh) (Real.rpow_nonneg (norm_nonneg _) _)
      _=(C/D^(-4:ℝ))*(‖eisEmbedding h‖^(1/3:ℝ)*‖eisEmbedding h‖^(-4:ℝ)):=by
        rw [cuspFrequency,norm_div,Real.div_rpow (norm_nonneg _) (norm_nonneg _)]
        change (C*‖eisEmbedding h‖^(1/3:ℝ))*(‖eisEmbedding h‖^(-4:ℝ)/D^(-4:ℝ))=_
        ring
      _=_:=by rw [he]

theorem three_cusp_coefficients_weighted_summable :
    Summable (fun h:Eis=>if h=0 then (0:ℝ) else
      ‖sourceResidualFourierCoefficient h‖*‖cuspFrequency h‖^(-4:ℝ)) ∧
    ∀side:Bool,Summable (fun h:Eis=>if h=0 then (0:ℝ) else
      ‖ramifiedBesselValue side h‖*‖cuspFrequency h‖^(-4:ℝ)) := by
  obtain ⟨C,hC,hbound⟩:=three_cusp_coefficients_polynomial_bound
  constructor
  · exact coefficient_weighted_summable_of_polynomial _ C hC.le (fun h hh=>(hbound h hh).1)
  · intro side
    exact coefficient_weighted_summable_of_polynomial _ C hC.le (fun h hh=>(hbound h hh).2 side)

lemma derivative_coefficient_weighted_summable (F:Eis→ℂ) (A:ℂ)
    (hF:Summable (fun h:Eis=>if h=0 then (0:ℝ) else ‖F h‖*‖cuspFrequency h‖^(-4:ℝ))) :
    Summable (fun h:Eis=>if h=0 then (0:ℝ) else
      ‖A*cuspFrequency h*star (F h)‖*‖cuspFrequency h‖^(-5:ℝ)) := by
  apply (hF.mul_left ‖A‖).congr
  intro h
  split_ifs with hh
  · simp
  · have hx:0<‖cuspFrequency h‖:=norm_pos_iff.mpr (cuspFrequency_ne_zero h hh)
    have hp:‖cuspFrequency h‖*‖cuspFrequency h‖^(-5:ℝ)=‖cuspFrequency h‖^(-4:ℝ):=by
      conv_lhs => lhs; rw [←Real.rpow_one ‖cuspFrequency h‖]
      rw [←Real.rpow_add hx]
      norm_num
    rw [norm_mul,norm_mul,norm_star]
    calc
      _=‖A‖*‖F h‖*(‖cuspFrequency h‖*‖cuspFrequency h‖^(-5:ℝ)):=by rw [hp];ring
      _=_:=by ring

end

section
open ActualEisensteinCubic ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma radial_inverse_weight (x:ℝ) (hx:0<x) :
    (x^2)^(-(3/2):ℝ)/x^2=x^(-5:ℝ) := by
  calc
    _=(x^2)^(-(3/2):ℝ)*(x^2)^(-1:ℝ):=by rw [Real.rpow_neg_one];rfl
    _=(x^2)^(-(5/2):ℝ):=by
      rw [←Real.rpow_add (sq_pos_of_pos hx)]
      congr 1
      norm_num
    _=x^(-5:ℝ):=by
      rw [←Real.rpow_natCast_mul hx.le]
      congr 1
      norm_num

lemma radialCoefficient_weighted_summable_of_fourth (F:Eis→ℂ) (A:ℂ)
    (hF:Summable (fun h:Eis=>if h=0 then (0:ℝ) else ‖F h‖*‖cuspFrequency h‖^(-4:ℝ))) :
    Summable (fun h:Eis=>if h=0 then (0:ℝ) else
      ‖A*cuspFrequency h*star (F h)/((‖eisEmbedding h‖^2:ℝ):ℂ)‖*
        (‖eisEmbedding h‖^2)^(-(3/2):ℝ)) := by
  let D:ℝ:=‖(3:ℂ)*eisLam‖
  have hD:0<D:=norm_pos_iff.mpr (mul_ne_zero (by norm_num) eisLam_ne_zero)
  have hDp:D^(-5:ℝ)≠0:=(Real.rpow_pos_of_pos hD _).ne'
  apply ((derivative_coefficient_weighted_summable F A hF).mul_left (D^(-5:ℝ))).congr
  intro h
  split_ifs with hh
  · simp
  · have hx:0<‖eisEmbedding h‖:=norm_pos_iff.mpr (eisEmbedding_ne_zero hh)
    have hf:‖cuspFrequency h‖=‖eisEmbedding h‖/D:=by rw [cuspFrequency,norm_div]
    have hw:D^(-5:ℝ)*(‖eisEmbedding h‖/D)^(-5:ℝ)=‖eisEmbedding h‖^(-5:ℝ):=by
      rw [Real.div_rpow hx.le hD.le]
      field_simp [hDp]
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    calc
      _=‖A*cuspFrequency h*star (F h)‖*(D^(-5:ℝ)*(‖eisEmbedding h‖/D)^(-5:ℝ)):=by rw [hf];ring
      _=‖A*cuspFrequency h*star (F h)‖*‖eisEmbedding h‖^(-5:ℝ):=by rw [hw]
      _=_:=by rw [←radial_inverse_weight _ hx];ring

end

open ActualEisensteinCubic ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma sourceCuspCoefficients_weighted_summable (j:Fin 3) :
    Summable (fun h:Eis=>if h=0 then (0:ℝ) else
      ‖(sourceCuspCoefficients j).value h‖*‖cuspFrequency h‖^(-4:ℝ)) := by
  fin_cases j
  · exact three_cusp_coefficients_weighted_summable.1
  · exact three_cusp_coefficients_weighted_summable.2 false
  · exact three_cusp_coefficients_weighted_summable.2 true

theorem sourceCuspRadialCoefficient_weighted_summable (j:Fin 3) (z:ℂ) :
    Summable (fun h:Eis=>‖sourceCuspRadialCoefficient j z h‖*
      (sourceCuspRadialLength h)^(-(3/2):ℝ)) := by
  let A:ℂ:=(-2*Real.pi*Complex.I)/(sourceCuspScale j:ℂ)^2
  have hs:=radialCoefficient_weighted_summable_of_fourth (sourceCuspCoefficients j).value A
    (sourceCuspCoefficients_weighted_summable j)
  apply hs.congr
  intro h
  by_cases hh:h=0
  · subst h
    simp only [ite_true,sourceCuspRadialCoefficient_zero,norm_zero,zero_mul]
  · rw [if_neg hh,sourceCuspRadialCoefficient_norm,sourceCuspRadialBaseCoefficient,
      sourceCuspRadialLength,if_neg hh]
    congr 1
    apply congrArg norm
    dsimp only [A]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff MatrixGroups

section
open CompletedGauss ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma SourceCuspDatum.cuspBarProfile_mellin_entire (d : SourceCuspDatum) :
    (∀s:ℂ,MellinConvergent (cuspBarProfile cubicSourceConjugateFunction d.point) s) ∧
      Differentiable ℂ (mellin (cuspBarProfile cubicSourceConjugateFunction d.point)) :=
  (conjugateSource_levelTwo_three_cusp_mellin_entire d.gamma d.index d.matrix rfl d.lower_ne_zero).1

lemma SourceCuspDatum.reflection_radial (d : SourceCuspDatum) (v:ℝ) (hv:0<v) :
    cuspBarProfile cubicSourceConjugateFunction d.point v=
      d.multiplier*((v:ℂ)^(-2:ℂ)*
        radialBesselProfile sourceCuspRadialLength
          (sourceCuspRadialCoefficient d.index d.dualPoint)
          (sourceCuspRadialScale d.index) ((d.heightScale*v)⁻¹)) := by
  rw [d.reflection v hv,sourceCuspZFamily_eq_radialBesselProfile _ _ _
    (inv_pos.mpr (mul_pos d.heightScale_pos hv)),Complex.cpow_neg,Complex.cpow_ofNat]
  ring

end

open CompletedGauss ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

theorem completedT_finite_smoothed_reflection
    (Ψ:Eis→*ℂ) (hΨ:∀x,‖Ψ x‖≤1)
    (Q:Ideal Eis) (hperiod:CanonicalCoefficientClass.FactorsModulo Q Ψ)
    (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ:Ideal.span {c}≤Ideal.span {(9:Eis)}*Q)
    (d:(Eis⧸Ideal.span {c})→SourceCuspDatum)
    (hd:∀h,(d h).point=thetaFourierTranslation c h)
    (W:ℝ→ℂ) (v0 v1:ℝ) (hv0:0<v0)
    (hWs:Function.support W⊆Set.Icc v0 v1) (hW:ContDiff ℝ ∞ W)
    (X:ℝ) (hX:0<X) :
    completedT Ψ W X=thetaDerivativeScalar⁻¹*
      ∑h:Eis⧸Ideal.span {c},
        finiteAdditiveFourierCoeff (quotientTrace c hc) (fixedThetaQuotient Ψ c) h*
          (d h).smoothedKernel W X := by
  let : Countable Eis := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
  let G:(Eis⧸Ideal.span {c})→ℝ→ℂ:=fun h=>
    cuspBarProfile cubicSourceConjugateFunction (d h).point
  let w:(Eis⧸Ideal.span {c})→ℂ:=fun h=>thetaDerivativeScalar⁻¹*
    finiteAdditiveFourierCoeff (quotientTrace c hc) (fixedThetaQuotient Ψ c) h
  have hFG:∀v:ℝ,0<v→ completedBesselProfile Ψ thetaBesselScale v=∑h,w h*G h v:=
    completedBesselProfile_eq_finite_cuspProfiles Ψ Q hperiod c hc hcQ d hd
  have hG (h:Eis⧸Ideal.span {c}) : ∀s:ℂ,MellinConvergent (G h) s:=
    (d h).cuspBarProfile_mellin_entire.1
  have hF:=completedBesselProfile_mellin_entire_of_periodic Ψ Q hperiod c hc hcQ
  have hVs:=Vstar_support W v0 v1 hWs
  have hV:=Vstar_contDiff W v0 v1 hv0 hWs hW
  let J:(Eis⧸Ideal.span {c})→ℝ→ℂ:=fun h t=>
    besselSmoothingIntegrand (G h) thetaBesselScale (Vstar W) X ((-1:ℂ)+t*Complex.I)
  have hi (h:Eis⧸Ideal.span {c}) : Integrable (J h):=
    besselSmoothingIntegrand_reflected_integrable (G h) sourceCuspRadialLength
      sourceCuspRadialLength_pos (sourceCuspRadialCoefficient (d h).index (d h).dualPoint)
      thetaBesselScale (sourceCuspRadialScale (d h).index) (d h).heightScale
      thetaBesselScale_pos (sourceCuspRadialScale_pos _) (d h).heightScale_pos
      (d h).multiplier (d h).reflection_radial
      (sourceCuspRadialCoefficient_weighted_summable _ _) (Vstar W) v0 v1 hv0 hVs hV X hX
  have hireal (h:Eis⧸Ideal.span {c}) : Integrable (fun t:ℝ=>
      besselSmoothingIntegrand (G h) thetaBesselScale (Vstar W) X (((-1:ℝ):ℂ)+t*Complex.I)):=by
    simpa only [Complex.ofReal_neg,Complex.ofReal_one,J] using hi h
  have hleft:=besselSmoothingIntegrand_finite_integrable
    (completedBesselProfile Ψ thetaBesselScale) G w hFG thetaBesselScale (Vstar W) X (-1)
    (fun h t=>hG h _) hireal
  have hshift:=completedT_mellin_shift Ψ hΨ thetaBesselScale thetaBesselScale_pos hF.1 hF.2
    W v0 v1 hv0 hWs hW X hX (-1) (by norm_num) hleft
  have hline (h:Eis⧸Ideal.span {c}) : (1/(2*Real.pi):ℂ)*(∫t:ℝ,J h t)=(d h).smoothedKernel W X:=by
    exact besselSmoothingIntegral_reflected_kernel (G h) sourceCuspRadialLength
      sourceCuspRadialLength_pos (sourceCuspRadialCoefficient (d h).index (d h).dualPoint)
      thetaBesselScale (sourceCuspRadialScale (d h).index) (d h).heightScale
      thetaBesselScale_pos (sourceCuspRadialScale_pos _) (d h).heightScale_pos
      (d h).multiplier (d h).reflection_radial
      (sourceCuspRadialCoefficient_weighted_summable _ _) (Vstar W) v0 v1 hv0 hVs hV X hX
  calc
    _=(1/(2*Real.pi):ℂ)*∫t:ℝ,
        besselSmoothingIntegrand (completedBesselProfile Ψ thetaBesselScale)
          thetaBesselScale (Vstar W) X ((-1:ℂ)+t*Complex.I):=by
      simpa only [Complex.ofReal_neg,Complex.ofReal_one] using hshift
    _=(1/(2*Real.pi):ℂ)*∫t:ℝ,∑h,w h*J h t:=by
      congr 1
      apply integral_congr_ae
      filter_upwards with t
      exact besselSmoothingIntegrand_finite_sum
        (completedBesselProfile Ψ thetaBesselScale) G w hFG thetaBesselScale (Vstar W) X _
        (fun h=>hG h _)
    _=∑h,w h*((1/(2*Real.pi):ℂ)*∫t:ℝ,J h t):=by
      rw [integral_finsetSum Finset.univ (fun h _=>(hi h).const_mul (w h)),Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h hh
      rw [integral_const_mul]
      ring
    _=∑h,w h*(d h).smoothedKernel W X:=by simp_rw [hline]
    _=_:=by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h hh
      dsimp only [w]
      ring

theorem completedT_canonical_smoothed_reflection_oai
    (Ψ:Eis→*ℂ) (hΨ:∀x,‖Ψ x‖≤1)
    (Q:Ideal Eis) (hperiod:CanonicalCoefficientClass.FactorsModulo Q Ψ)
    (c:Eis) (hc:c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ:Ideal.span {c}≤Ideal.span {(9:Eis)}*Q)
    (W:ℝ→ℂ) (v0 v1:ℝ) (hv0:0<v0)
    (hWs:Function.support W⊆Set.Icc v0 v1) (hW:ContDiff ℝ ∞ W)
    (X:ℝ) (hX:0<X) :
    completedT Ψ W X=thetaDerivativeScalar⁻¹*
      ∑h:Eis⧸Ideal.span {c},
        finiteAdditiveFourierCoeff (quotientTrace c hc) (fixedThetaQuotient Ψ c) h*
          (finiteTwistCusp c hc h).smoothedKernel W X :=
  completedT_finite_smoothed_reflection Ψ hΨ Q hperiod c hc hcQ
    (finiteTwistCusp c hc) (finiteTwistCusp_point c hc) W v0 v1 hv0 hWs hW X hX

end

open scoped Classical MatrixGroups Matrix

open CubicKubota EisensteinCuspModThree ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

end CubicEisenstein

end

end OAI
end

theorem solution : type_of% @OAI.CubicEisenstein.completedT_canonical_smoothed_reflection_oai := @OAI.CubicEisenstein.completedT_canonical_smoothed_reflection_oai
