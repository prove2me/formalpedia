-- Prove2me | solution 1 for OAI.SevenEighths.ProbePhysical.gaussianPhysicalFamily_remote_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T04:24:07.709242+00:00
-- url     : https://prove2.me/submissions/6a7b0fc9-2414-4c59-8808-e0ed783c7dd4

import Mathlib
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B022
import Definitions.Def_OAIHecke78B023

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

open ActualEisensteinCubic ConcreteTraceCRT

end CompletedGauss

open scoped BigOperators Classical

namespace RayFourExpansion
open ActualEisensteinCubic ConcreteTraceCRT ActualEisensteinCoordinates QuadraticGaussRay
open FiniteRayExpansion

theorem fixedGQuotientValue_norm_le_two (r : RayRing) : ‖fixedGQuotientValue r‖ ≤ 2 := by
  let : Fintype (O ⧸ cubicTwoIdeal) := Fintype.ofFinite _
  let χ : MulChar (O ⧸ cubicTwoIdeal) ℂ :=
    (cubicChar cubicTwoIdeal cubicTwoIdeal_good).ringHomComp eisEmbedding
  let x := Ideal.Quotient.mk cubicTwoIdeal (lift (residueQuotientFour r))
  have hc : ‖(χ x)⁻¹‖ ≤ 1 := by
    simpa only [MulChar.inv_apply_eq_inv'] using norm_char_le_one (χ⁻¹) x
  change ‖(χ x)⁻¹ * quadraticRayValue (residueQuotientFour r)‖ ≤ 2
  rw [norm_mul]
  calc
    _ ≤ 1 * 2 := mul_le_mul hc (quadraticRayValue_bounds _).1 (norm_nonneg _) (by norm_num)
    _ = 2 := by norm_num

end RayFourExpansion

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.QuantitativePassage
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

open scoped BigOperators
namespace CompletedDyadic

theorem pow_rpow_comm (s : ℝ) (n : ℕ) : ((2:ℝ)^n)^s=((2:ℝ)^s)^n := by
  rw [←Real.rpow_natCast_mul (by norm_num),←Real.rpow_mul_natCast (by norm_num)]
  congr 1
  ring

theorem kernelTerm_nonneg (t s A : ℝ) (ht : 0<t) (n : ℕ) : 0≤kernelTerm t s A n := by
  unfold kernelTerm
  positivity

theorem kernelTerm_le_head (t s A : ℝ) (ht : 0<t) (hA : 0≤A) (n : ℕ) :
    kernelTerm t s A n≤((2:ℝ)^s)^n := by
  rw [kernelTerm,←pow_rpow_comm]
  exact div_le_self (Real.rpow_nonneg (by positivity) _)
    (Real.one_le_rpow (by nlinarith [pow_pos (by norm_num : (0:ℝ)<2) n]) hA)

theorem kernelTerm_le_tail (t s A : ℝ) (ht : 0<t) (hA : 0≤A) (n : ℕ) :
    kernelTerm t s A n≤t^(-A)*((2:ℝ)^(s-A))^n := by
  have hn : 0<(2:ℝ)^n := by positivity
  have htA : 0<t^A := Real.rpow_pos_of_pos ht _
  calc
    _ ≤ ((2:ℝ)^n)^s/(t*(2:ℝ)^n)^A := by
      unfold kernelTerm
      exact div_le_div_of_nonneg_left (by positivity) (by positivity)
        (Real.rpow_le_rpow (by positivity) (by linarith) hA)
    _ = t^(-A)*(((2:ℝ)^n)^s/((2:ℝ)^n)^A) := by
      rw [Real.mul_rpow ht.le hn.le,Real.rpow_neg ht.le]
      ring
    _ = _ := by rw [←Real.rpow_sub hn,pow_rpow_comm]

theorem ratio_lt_one (s A : ℝ) (hsA : s<A) : (2:ℝ)^(s-A)<1 := by
  exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (sub_neg.mpr hsA)

theorem kernel_summable (t s A : ℝ) (ht : 0<t) (hA : 0≤A) (hsA : s<A) :
    Summable (kernelTerm t s A) := by
  have hq := summable_geometric_of_lt_one (Real.rpow_nonneg (by norm_num : (0:ℝ)≤2) (s-A)) (ratio_lt_one s A hsA)
  exact (hq.mul_left (t^(-A))).of_nonneg_of_le (kernelTerm_nonneg t s A ht) (kernelTerm_le_tail t s A ht hA)

theorem kernel_sum_cutoff (t s A : ℝ) (ht : 0<t) (hs : 0<s) (hsA : s<A) (N : ℕ) :
    (∑'n : ℕ,kernelTerm t s A n)≤
      ((2:ℝ)^s)^N/((2:ℝ)^s-1)+t^(-A)*((2:ℝ)^(s-A))^N/(1-(2:ℝ)^(s-A)) := by
  have hA : 0≤A := by linarith
  have hp : 1<(2:ℝ)^s := Real.one_lt_rpow (by norm_num) hs
  have hq : (2:ℝ)^(s-A)<1 := ratio_lt_one s A hsA
  have hq0 : 0≤(2:ℝ)^(s-A) := by positivity
  have hsum := kernel_summable t s A ht hA hsA
  have hhead : (∑n∈Finset.range N,kernelTerm t s A n)≤((2:ℝ)^s)^N/((2:ℝ)^s-1) := by
    apply (Finset.sum_le_sum (fun n _ => kernelTerm_le_head t s A ht hA n)).trans
    rw [geom_sum_eq hp.ne']
    exact div_le_div_of_nonneg_right (by linarith) (sub_nonneg.mpr hp.le)
  have htail : (∑'n : ℕ,kernelTerm t s A (n+N))≤
      t^(-A)*((2:ℝ)^(s-A))^N/(1-(2:ℝ)^(s-A)) := by
    have hgeo := (summable_geometric_of_lt_one hq0 hq).mul_left (t^(-A)*((2:ℝ)^(s-A))^N)
    have hb := Summable.tsum_le_tsum (fun n => show kernelTerm t s A (n+N)≤
      (t^(-A)*((2:ℝ)^(s-A))^N)*((2:ℝ)^(s-A))^n by
        simpa only [pow_add,mul_assoc,mul_left_comm,mul_comm] using kernelTerm_le_tail t s A ht hA (n+N))
      ((summable_nat_add_iff N).mpr hsum) hgeo
    rw [tsum_mul_left,tsum_geometric_of_lt_one hq0 hq] at hb
    simpa only [div_eq_mul_inv] using hb
  rw [←hsum.sum_add_tsum_nat_add N]
  exact add_le_add hhead htail

theorem kernel_sum_bound (s A : ℝ) (hs : 0<s) (hsA : s<A) :
    ∃C : ℝ,0<C ∧ ∀t : ℝ,0<t →
      Summable (kernelTerm t s A) ∧ (∑'n : ℕ,kernelTerm t s A n)≤C*t^(-s) := by
  let r : ℝ := (2:ℝ)^s
  let q : ℝ := (2:ℝ)^(s-A)
  have hr : 1< r := Real.one_lt_rpow (by norm_num) hs
  have hq : q<1 := ratio_lt_one s A hsA
  have hq0 : 0≤q := by dsimp [q]; positivity
  let C := r/(r-1)+1/(1-q)
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro t ht
  have hA : 0≤A := by linarith
  have hsum := kernel_summable t s A ht hA hsA
  refine ⟨hsum,?_⟩
  by_cases ht1 : 1≤t
  · have hg := (summable_geometric_of_lt_one hq0 hq).mul_left (t^(-A))
    have hb := hsum.tsum_le_tsum (fun n => kernelTerm_le_tail t s A ht hA n) hg
    change (∑'n : ℕ,kernelTerm t s A n)≤∑'n : ℕ,t^(-A)*q^n at hb
    rw [tsum_mul_left,tsum_geometric_of_lt_one hq0 hq] at hb
    calc
      _ ≤ t^(-A)/(1-q) := by simpa only [div_eq_mul_inv] using hb
      _ ≤ t^(-s)/(1-q) := div_le_div_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)) (by linarith)
      _ ≤ C*t^(-s) := by
        have hp : 0≤ r/(r-1)*t^(-s) := by positivity
        calc
          _ ≤ r/(r-1)*t^(-s)+t^(-s)/(1-q) := le_add_of_nonneg_left hp
          _ = C*t^(-s) := by dsimp [C]; ring
  · have ht_le : t≤1 := le_of_not_ge ht1
    have hit : 1≤1/t := (one_le_div ht).mpr ht_le
    obtain ⟨N,hN,hN'⟩ := exists_nat_pow_near hit (by norm_num : (1:ℝ)<2)
    have hheadpow : r^(N+1)≤ r*t^(-s) := by
      change ((2:ℝ)^s)^(N+1)≤(2:ℝ)^s*t^(-s)
      rw [←pow_rpow_comm]
      calc
        _ ≤ ((2:ℝ)/t)^s := by
          apply Real.rpow_le_rpow (by positivity) _ hs.le
          rw [pow_succ]
          calc
            _ ≤ (1/t)*2 := mul_le_mul_of_nonneg_right hN (by norm_num)
            _ = 2/t := by ring
        _ = _ := by rw [Real.div_rpow (by norm_num) ht.le,Real.rpow_neg ht.le]; ring
    have htailpow : t^(-A)*q^(N+1)≤t^(-s) := by
      change t^(-A)*((2:ℝ)^(s-A))^(N+1)≤t^(-s)
      rw [←pow_rpow_comm]
      calc
        _ ≤ t^(-A)*(1/t)^(s-A) := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos (by positivity) hN'.le (by linarith)) (by positivity)
        _ = t^(-A)*t^(-(s-A)) := by rw [one_div,Real.inv_rpow ht.le,←Real.rpow_neg ht.le]
        _ = t^(-s) := by rw [←Real.rpow_add ht]; congr 1; ring
    have hb := kernel_sum_cutoff t s A ht hs hsA (N+1)
    change (∑'n : ℕ,kernelTerm t s A n)≤ r^(N+1)/(r-1)+t^(-A)*q^(N+1)/(1-q) at hb
    calc
      _ ≤ r^(N+1)/(r-1)+t^(-A)*q^(N+1)/(1-q) := hb
      _ ≤ (r*t^(-s))/(r-1)+t^(-s)/(1-q) := add_le_add
        (div_le_div_of_nonneg_right hheadpow (by linarith))
        (div_le_div_of_nonneg_right htailpow (by linarith))
      _ = C*t^(-s) := by dsimp [C]; ring

end CompletedDyadic

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

open ActualEisensteinCubic
local notation "O" => ActualEisensteinCubic.O

end CompletedGauss

open scoped BigOperators Classical
open Finset AddChar MulChar EisensteinEmbedding

end

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

theorem completedMask_norm_le_one (S : Finset (Ideal O)) (D I J : Ideal O) :
    ‖completedMask S D I J‖ ≤ 1 := by
  unfold completedMask
  split_ifs <;> norm_num

theorem completedCorrection_norm_le_two (I J : Ideal O) :
    ‖completedCorrection I J‖ ≤ 2 := by
  have hm : ‖rayMask (completedIndex I J)‖ ≤ 1 := by
    unfold rayMask
    split_ifs <;> norm_num
  unfold completedCorrection
  rw [norm_mul, norm_star]
  exact (mul_le_mul hm (fixedGQuotientValue_norm_le_two _) (norm_nonneg _) (by norm_num)).trans_eq
    (by norm_num)

theorem correctedSummand_summable (S : Finset (Ideal O)) (D : Ideal O)
    (Ψ : O →* ℂ) (W : ℝ → ℂ) (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) :
    Summable (fun p : Ideal O × Ideal O => correctedSummand S D Ψ W X p.1 p.2) := by
  apply summable_of_hasFiniteSupport
  apply (completedT_finite_support Ψ W hW X hX).subset
  intro p hp
  exact fun hz => hp (by simp only [correctedSummand, markedSummand, hz, mul_zero])

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

theorem targetMonoid_norm_le_one (η : HeckeFamily.Character) (a : O) :
    ‖targetMonoid η a‖ ≤ 1 := by
  let : Finite (O ⧸ η.modulus) := Ring.HasFiniteQuotients.finiteQuotient η.modulus_ne_bot
  let : Fintype (O ⧸ η.modulus) := Fintype.ofFinite _
  exact FiniteRayExpansion.norm_char_le_one η.residue (Ideal.Quotient.mk η.modulus a)

theorem rowCoefficient_apply (η : HeckeFamily.Character) (Xi : O →* ℂ)
    (s : O) (hs : Supported (Ideal.span {s})) (m a : O) :
    rowCoefficient η Xi s hs m a = HeckeFamily.elementCoeff η a * star (Xi a) *
      sexticReciprocityPhase s a * idealRowHom m (Ideal.span {a}) := rfl

theorem rowCoefficient_norm_le_one (η : HeckeFamily.Character) (Xi : O →* ℂ)
    (hXi : ∀ a, ‖Xi a‖ ≤ 1) (s : O) (hs : Supported (Ideal.span {s})) (m a : O) :
    ‖rowCoefficient η Xi s hs m a‖ ≤ 1 := by
  rw [rowCoefficient_apply]
  simp only [norm_mul, norm_star]
  refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans (idealRowHom_norm _ _)
  refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans (sexticReciprocityPhase_norm _ _)
  exact (mul_le_of_le_one_left (norm_nonneg _) (targetMonoid_norm_le_one η a)).trans (hXi a)

theorem spectralSummand_norm_le (S : Finset (Ideal O)) (D : Ideal O)
    (Ψ : O →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1) (t : ℂ) (I J : Ideal O) :
    ‖spectralSummand S D Ψ t I J‖ ≤
      2 * (‖CubicEisenstein.fullIdealWeight t I‖ *
        ‖CubicEisenstein.fullIdealWeight (3 * t) J‖) := by
  have hmc : ‖completedMask S D I J * completedCorrection I J‖ ≤ 2 := by
    rw [norm_mul]
    exact (mul_le_mul (completedMask_norm_le_one S D I J)
      (completedCorrection_norm_le_two I J) (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
  have hcol := columnWeight_div_sqrt_norm_le_one Ψ hΨ I
  have hcube := cubeWeight_norm_le_one Ψ hΨ J
  have hc : ‖completedMask S D I J * completedCorrection I J *
      (columnWeight Ψ I / (Real.sqrt (Ideal.absNorm I) : ℂ)) * cubeWeight Ψ J‖ ≤ 2 := by
    rw [norm_mul, norm_mul]
    exact (mul_le_of_le_one_right (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hcube).trans
      ((mul_le_of_le_one_right (norm_nonneg _) hcol).trans hmc)
  unfold spectralSummand
  simpa only [norm_mul] using mul_le_mul_of_nonneg_right hc (mul_nonneg
    (norm_nonneg (CubicEisenstein.fullIdealWeight t I))
    (norm_nonneg (CubicEisenstein.fullIdealWeight (3 * t) J)))

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

theorem localCalibration_nonprincipal (P : Ideal O) [P.IsMaximal] :
    localCalibration P ≠ 1 := (Classical.choose_spec (exists_local_calibration P)).1

theorem calibrationFromPrimes_tau_norm {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P)) :
    ‖(calibrationFromPrimes P hcop).tau‖ = 1 := by
  let b := finitePrimeModulus P
  have hb : b ≠ 0 := finitePrimeModulus_ne_zero P
  let : Finite (O ⧸ Ideal.span {b}) := ConcreteTraceCRT.finite_quotient_span hb
  let : Fintype (O ⧸ Ideal.span {b}) := Fintype.ofFinite _
  let (i : ι) : Field (O ⧸ P i) := Ideal.Quotient.field _
  let (i : ι) : Fintype (O ⧸ P i) := Fintype.ofFinite _
  let e : (O ⧸ Ideal.span {b}) ≃+* ∀ i, O ⧸ P i :=
    (Ideal.quotEquivOfEq (span_finitePrimeModulus P)).trans
      (IdealGaussCRT.quotientProdEquivPi P hcop)
  let ψ := quotientTrace b hb
  have hψ : ψ.IsPrimitive := GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive b hb
  have hg := IdealGaussCRT.norm_gauss_finite_crt_sq (fun i => O ⧸ P i) e
    (fun i => localCalibration (P i)) ψ (fun i => localCalibration_nonprincipal (P i))
    (fun i => IdealGaussCRT.coordinateAddChar_isPrimitive _ e ψ hψ i)
  have hcard : (Fintype.card (O ⧸ Ideal.span {b}) : ℝ) = elementNorm b := by
    rw [← Nat.card_eq_fintype_card]
    rfl
  rw [hcard] at hg
  have hQ : 0 < elementNorm b := by
    unfold elementNorm
    exact_mod_cast Nat.pos_of_ne_zero
      (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hb))
  have hn : ‖∑ x : O ⧸ Ideal.span {b}, (∏ i, localCalibration (P i) (e x i)) * ψ x‖ =
      Real.sqrt (elementNorm b) := by
    have hs := Real.sq_sqrt hQ.le
    have hs0 := Real.sqrt_nonneg (elementNorm b)
    have hn0 := norm_nonneg (∑ x : O ⧸ Ideal.span {b}, (∏ i, localCalibration (P i) (e x i)) * ψ x)
    nlinarith
  change ‖(∑' d : O ⧸ Ideal.span {b}, (∏ i, localCalibration (P i) (e d i)) * ψ d) /
    (Real.sqrt (elementNorm b) : ℂ)‖ = 1
  rw [tsum_fintype, norm_div, hn, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), div_self (Real.sqrt_pos.mpr hQ).ne']

theorem calibrationForSet_tau_norm (S : Finset (Ideal O)) (hS : ∀ P ∈ S, P.IsMaximal) :
    ‖(calibrationForSet S hS).tau‖ = 1 := by
  let (P : S) : P.val.IsMaximal := hS P.val P.property
  unfold calibrationForSet
  apply calibrationFromPrimes_tau_norm

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.RowAnalytic
namespace OAI

noncomputable section
open scoped BigOperators Classical
open MeasureTheory
namespace SevenEighths.ProbeRow
open ActualEisensteinCubic CompletedGauss CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

theorem fullIdealWeight_norm_eq_of_re (s t : ℂ) (h : s.re = t.re) (I : Ideal O) :
    ‖fullIdealWeight s I‖ = ‖fullIdealWeight t I‖ := by
  by_cases hI : I = 0
  · simp [hI, fullIdealWeight]
  · exact (norm_fullIdealWeight s ⟨I, hI⟩).trans
      ((by rw [h] : _ = _).trans (norm_fullIdealWeight t ⟨I, hI⟩).symm)

theorem rowMajorant_summable (σ : ℝ) (hσ : 1 < σ) : Summable (rowMajorant σ) := by
  have h3 : 1 < (3 * (σ : ℂ)).re := by norm_num; linarith
  exact ((fullIdealWeight_summable_norm (σ : ℂ) hσ).mul_of_nonneg
    (fullIdealWeight_summable_norm (3 * (σ : ℂ)) h3)
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)).mul_left 2

theorem spectralSummand_vertical_bound (S : Finset (Ideal O)) (D : Ideal O)
    (Ψ : O →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1) (σ y : ℝ) (p : Ideal O × Ideal O) :
    ‖spectralSummand S D Ψ ((σ : ℂ) + y * Complex.I) p.1 p.2‖ ≤ rowMajorant σ p := by
  have h1 : ((σ : ℂ) + y * Complex.I).re = (σ : ℂ).re := by simp
  have h3 : (3 * ((σ : ℂ) + y * Complex.I)).re = (3 * (σ : ℂ)).re := by simp
  simpa only [rowMajorant, fullIdealWeight_norm_eq_of_re _ _ h1,
    fullIdealWeight_norm_eq_of_re _ _ h3] using
    spectralSummand_norm_le S D Ψ hΨ ((σ : ℂ) + y * Complex.I) p.1 p.2

end SevenEighths.ProbeRow
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.PhysicalAnalytic
namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical
open MeasureTheory ActualEisensteinCubic CompletedGauss CanonicalRowCompletion
open ProbeRow CubicEisenstein CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O

theorem CalibrationData.residueMonoid_norm_le_one (C : CalibrationData) (a : O) :
    ‖C.residueMonoid a‖ ≤ 1 := by
  let : Finite (O ⧸ Ideal.span {C.generator}) :=
    ConcreteTraceCRT.finite_quotient_span C.generator_ne_zero
  let : Fintype (O ⧸ Ideal.span {C.generator}) := Fintype.ofFinite _
  exact FiniteRayExpansion.norm_char_le_one C.residue (Ideal.Quotient.mk _ a)

theorem CalibrationData.Xi_norm_le_one (C : CalibrationData) (a : O) :
    ‖C.Xi a‖ ≤ 1 := by
  change ‖C.residueMonoid a * idealRowHom C.generator (Ideal.span {a})‖ ≤ 1
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (C.residueMonoid_norm_le_one a)).trans
    (idealRowHom_norm _ _)

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

lemma gaussianAnnulus_nonneg (y : ℝ) : 0≤(gaussianAnnulus y).re := by
  by_cases hy : y≤1/2
  · rw [gaussianAnnulus_small y hy]; simp
  · change 0≤Real.smoothTransition (2-y)-Real.smoothTransition (2-2*y)
    exact sub_nonneg.mpr (Real.smoothTransition.monotone (by linarith))
lemma gaussianAnnulus_norm (y : ℝ) : ‖gaussianAnnulus y‖=(gaussianAnnulus y).re := by
  have h : gaussianAnnulus y=((gaussianAnnulus y).re:ℂ) := by
    simp [gaussianAnnulus,annularCutoff,gaussianCutoff]
  rw [h,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (gaussianAnnulus_nonneg y)]
  rfl

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.GaussianFlow
namespace OAI

noncomputable section
open scoped Classical ContDiff Topology
open Filter Set Metric
namespace SevenEighths.ProbePhysical

lemma iteratedDeriv_restrict_real (f : ℂ→ℂ)
    (hf : ∀x : ℝ,AnalyticAt ℂ f (x:ℂ)) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (fun y : ℝ=>f (y:ℂ)) x=iteratedDeriv n f (x:ℂ) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ',iteratedDeriv_succ']
    have he : deriv (fun y : ℝ=>f (y:ℂ))=(fun y : ℝ=>deriv f (y:ℂ)) := by
      funext y
      exact (hf y).differentiableAt.hasDerivAt.comp_ofReal.deriv
    rw [he]
    exact ih (deriv f) (fun y=>(hf y).deriv)

lemma gaussianFlow_disk_bound (a L : ℝ) (_hL : 0≤L) :
    ∃C : ℝ,0<C ∧ ∀R : ℝ,0<R→∀y : ℝ,|y|≤L→
      ∀z∈Metric.closedBall (y:ℂ) 1,‖gaussianFlow R z‖≤C*R^(-a) := by
  let c := ‖((1/(2*Real.pi):ℝ):ℂ)*(Real.pi:ℂ)^(1/2:ℂ)‖
  let B := Real.exp (a^2+1/4+|a| *(L+1))
  have hc : 0≤ c := norm_nonneg _
  have hB : 0<B := Real.exp_pos _
  refine ⟨(c+1)*B,by positivity,?_⟩
  intro R hR y hy z hz
  have hd : ‖z-(y:ℂ)‖≤1 := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hz
  have hzr := (Complex.abs_re_le_norm (z-(y:ℂ))).trans hd
  have hzi := (Complex.abs_im_le_norm (z-(y:ℂ))).trans hd
  simp only [Complex.sub_re,Complex.sub_im,Complex.ofReal_re,Complex.ofReal_im,sub_zero] at hzr hzi
  have hre : |z.re|≤L+1 := by
    have h := abs_add_le (z.re-y) y
    have he : z.re-y+y=z.re := by ring
    rw [he] at h
    linarith
  have hsq : z.im^2≤1 := by nlinarith [(abs_le.mp hzi).1,(abs_le.mp hzi).2]
  have hmul : -(a*z.re)≤|a| *(L+1) := by
    calc
      _ ≤ |a*z.re| := neg_le_abs _
      _ = |a| *|z.re| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hre (abs_nonneg _)
  have he : (-((Real.log R:ℂ)+z)^2/4).re=(z.im^2-(Real.log R+z.re)^2)/4 := by
    simp [pow_two,Complex.mul_re]
  unfold gaussianFlow
  rw [norm_mul,Complex.norm_exp,he]
  have hb : Real.exp ((z.im^2-(Real.log R+z.re)^2)/4)≤B*R^(-a) := by
    rw [Real.rpow_def_of_pos hR,←Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg ((Real.log R+z.re)/2-a)]
  calc
    _ ≤ c*(B*R^(-a)) := mul_le_mul_of_nonneg_left hb hc
    _ ≤ (c+1)*B*R^(-a) := by nlinarith [mul_pos hB (Real.rpow_pos_of_pos hR (-a))]

lemma gaussianFlow_derivative_bound (a L : ℝ) (hL : 0≤L) (n : ℕ) :
    ∃C : ℝ,0<C ∧ ∀R : ℝ,0<R→∀y : ℝ,|y|≤L→
      ‖iteratedDeriv n (fun s : ℝ=>gaussianFlow R (s:ℂ)) y‖≤C*R^(-a) := by
  obtain ⟨B,hB,hbound⟩ := gaussianFlow_disk_bound a L hL
  refine ⟨(n.factorial:ℝ)*B,by positivity,?_⟩
  intro R hR y hy
  rw [iteratedDeriv_restrict_real _ (fun x=>gaussianFlow_analytic R (x:ℂ)) n y]
  have hf : Differentiable ℂ (gaussianFlow R) := fun z=>(gaussianFlow_analytic R z).differentiableAt
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n
    (by norm_num : (0:ℝ)<1) hf.diffContOnCl
    (fun z hz=>hbound R hR y hy z (Metric.sphere_subset_closedBall hz))
  simpa only [one_pow,div_one,mul_assoc] using h

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.GaussianLogWindow
namespace OAI

noncomputable section
open scoped Classical ContDiff Topology SchwartzMap FourierTransform
open Filter Set MeasureTheory
namespace SevenEighths.ProbePhysical

lemma gaussianLogWindow_derivative_outside (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (L : ℝ) (hbox : ∀s,V s≠0→|s|≤L) (R y : ℝ) (hy : L < |y|) (n : ℕ) :
    iteratedDeriv n (gaussianLogWindow V hV R) y=0 := by
  have he : (gaussianLogWindow V hV R:ℝ→ℂ)=ᶠ[𝓝 y](fun _=>0) := by
    have hu : {x : ℝ | L < |x|}∈𝓝 y := (isOpen_lt continuous_const continuous_abs).mem_nhds hy
    filter_upwards [hu] with x hx
    have hv : V x=0 := by by_contra h; exact (not_lt_of_ge (hbox x h)) hx
    simp only [gaussianLogWindow_apply,hv,zero_mul]
  rw [he.iteratedDeriv_eq n]
  simp

lemma gaussianLogWindow_derivative_bound (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (L : ℝ) (hL : 0≤L) (a : ℝ) (n : ℕ) :
    ∃C : ℝ,0<C ∧ ∀R : ℝ,0<R→∀y : ℝ,|y|≤L→
      ‖iteratedDeriv n (gaussianLogWindow V hV R) y‖≤C*R^(-a) := by
  choose B hB hbound using fun i : ℕ=>gaussianFlow_derivative_bound a L hL i
  let A (i : ℕ) := SchwartzMap.seminorm ℝ 0 i V
  let C := ∑i∈Finset.range (n+1),(n.choose i:ℝ)*A i*B (n-i)
  have hA (i : ℕ) : 0≤A i := apply_nonneg _ _
  have hC : 0≤C := Finset.sum_nonneg (fun i _=>mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hA i)) (hB _).le)
  refine ⟨C+1,by positivity,?_⟩
  intro R hR y hy
  change ‖iteratedDeriv n (fun s : ℝ=>V s*gaussianFlow R (s:ℂ)) y‖≤_
  rw [iteratedDeriv_fun_mul (f:=(V:ℝ→ℂ)) (g:=fun s : ℝ=>gaussianFlow R (s:ℂ))
    (V.smooth'.contDiffAt.of_le (by simp))
    ((gaussianFlow_real_smooth R).contDiffAt.of_le (by simp))]
  calc
    _ ≤ ∑i∈Finset.range (n+1),‖(n.choose i:ℂ)*iteratedDeriv i V y*
        iteratedDeriv (n-i) (fun s : ℝ=>gaussianFlow R (s:ℂ)) y‖ := norm_sum_le _ _
    _ ≤ ∑i∈Finset.range (n+1),((n.choose i:ℝ)*A i)*(B (n-i)*R^(-a)) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul,norm_mul,Complex.norm_natCast]
      have hv : ‖iteratedDeriv i V y‖≤A i := by
        simpa only [pow_zero,one_mul] using SchwartzMap.le_seminorm' ℝ 0 i V y
      exact mul_le_mul (mul_le_mul_of_nonneg_left hv (Nat.cast_nonneg _))
        (hbound _ R hR y hy) (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hA i))
    _ = C*R^(-a) := by simp only [C,Finset.sum_mul]; apply Finset.sum_congr rfl; intros; ring
    _ ≤ (C+1)*R^(-a) := by nlinarith [Real.rpow_pos_of_pos hR (-a)]

theorem gaussianLogWindow_seminorm (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (L : ℝ) (hL : 0≤L) (hbox : ∀s,V s≠0→|s|≤L) (a : ℝ) (k n : ℕ) :
    ∃C : ℝ,0<C ∧ ∀R : ℝ,0<R→
      SchwartzMap.seminorm ℝ k n (gaussianLogWindow V hV R)≤C*R^(-a) := by
  obtain ⟨B,hB,hbound⟩ := gaussianLogWindow_derivative_bound V hV L hL a n
  refine ⟨(1+L^k)*B,by positivity,?_⟩
  intro R hR
  apply SchwartzMap.seminorm_le_bound' ℝ k n _ (by positivity)
  intro y
  by_cases hy : |y|≤L
  · calc
      _ ≤ L^k*(B*R^(-a)) := mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hy k)
        (hbound R hR y hy) (norm_nonneg _) (pow_nonneg hL _)
      _ ≤ _ := by nlinarith [mul_pos hB (Real.rpow_pos_of_pos hR (-a))]
  · rw [gaussianLogWindow_derivative_outside V hV L hbox R y (lt_of_not_ge hy) n,norm_zero,mul_zero]
    positivity

theorem gaussianLogWindow_fourier_moment (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (L : ℝ) (hL : 0≤L) (hbox : ∀s,V s≠0→|s|≤L) (a : ℝ) (J : ℕ) :
    ∃C : ℝ,0<C ∧ ∀R : ℝ,0<R→
      (∫t : ℝ,(1+‖t‖)^J*‖(𝓕 (gaussianLogWindow V hV R)) t‖)≤C*R^(-a) := by
  let p := (MeasureTheory.volume : MeasureTheory.Measure ℝ).integrablePower
  let K := J+p
  choose B hB hb using fun q : ℕ×ℕ=>gaussianLogWindow_seminorm V hV L hL hbox a q.1 q.2
  let C := (∑i∈Finset.range (K+1),(B (0,i)+B (p,i)))+1
  have hC : 0<C := by
    have hh : 0≤∑i∈Finset.range (K+1),(B (0,i)+B (p,i)) :=
      Finset.sum_nonneg (fun i _=>add_nonneg (hB _).le (hB _).le)
    dsimp only [C]; linarith
  let D := (2:ℝ)^J*(FourierBridge.coefficientMomentBound 0 C+FourierBridge.coefficientMomentBound J C)
  have hD : 0≤D := mul_nonneg (by positivity)
    (add_nonneg (FourierBridge.coefficientMomentBound_nonneg _ _ hC.le)
      (FourierBridge.coefficientMomentBound_nonneg _ _ hC.le))
  refine ⟨D+1,by positivity,?_⟩
  intro R hR
  have hcancel : R^a*R^(-a)=1 := by rw [←Real.rpow_add hR]; simp
  have hsource (i : ℕ) (hi : i≤J+(MeasureTheory.volume : MeasureTheory.Measure ℝ).integrablePower) :
      R^a*(SchwartzMap.seminorm ℝ 0 i (gaussianLogWindow V hV R)+
        SchwartzMap.seminorm ℝ p i (gaussianLogWindow V hV R))≤C := by
    have hbi : B (0,i)+B (p,i)≤C := by
      have hh := Finset.single_le_sum (s:=Finset.range (K+1)) (a:=i)
        (f:=fun i=>B (0,i)+B (p,i))
        (fun i _=>add_nonneg (hB _).le (hB _).le) (Finset.mem_range.mpr (by dsimp only [K,p]; omega))
      dsimp only [C]; linarith
    calc
      _ ≤ R^a*(B (0,i)*R^(-a)+B (p,i)*R^(-a)) :=
        mul_le_mul_of_nonneg_left (add_le_add (hb (0,i) R hR) (hb (p,i) R hR)) (by positivity)
      _ = B (0,i)+B (p,i) := by rw [←add_mul]; calc
        _=(B (0,i)+B (p,i))*(R^a*R^(-a)) := by ring
        _=_ := by rw [hcancel,mul_one]
      _ ≤ C := hbi
  have hh := FourierBridge.uniform_fourier_one_plus_moment (gaussianLogWindow V hV R) J
    (R^a) C (by positivity) hC.le hsource
  change R^a*(∫t : ℝ,(1+‖t‖)^J*‖(𝓕 (gaussianLogWindow V hV R)) t‖)≤D at hh
  have hp := mul_le_mul_of_nonneg_left hh (Real.rpow_pos_of_pos hR (-a)).le
  have hc' : R^(-a)*R^a=1 := by rw [mul_comm,hcancel]
  rw [←mul_assoc,hc',one_mul] at hp
  exact hp.trans (by nlinarith [Real.rpow_pos_of_pos hR (-a)])

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.GaussianSlots
namespace OAI

noncomputable section
open scoped Classical ContDiff Topology SchwartzMap FourierTransform
open MeasureTheory Filter Set FourierBridge CompletedGauss
namespace SevenEighths.ProbePhysical

lemma gaussianFixedWindow_Vstar_twist (t x : ℝ) (hx : 0<x) :
    Vstar (CompletedHeight.normTwistedSource gaussianFixedWindow t) x=
      gaussianAnnulus x*logPhase t (Real.log x) := by
  have hs : (Real.sqrt x:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hx).ne'
  unfold Vstar CompletedHeight.normTwistedSource gaussianFixedWindow
  field_simp

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.GaussianCompletedSlots
namespace OAI

noncomputable section
open scoped Classical ContDiff Topology SchwartzMap
open MeasureTheory FourierBridge CompletedGauss
namespace SevenEighths.ProbePhysical
open ProbeCompleted
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma correctedSummand_normTwisted (S : Finset Id) (D : Id) (Ψ : O→*ℂ)
    (W : ℝ→ℂ) (T t : ℝ) (I J : Id) :
    correctedSummand S D Ψ (CompletedHeight.normTwistedSource W t) T I J=
      logPhase t (Real.log ((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3/T))*
        correctedSummand S D Ψ W T I J := by
  unfold correctedSummand markedSummand CompletedGauss.summand Vstar
    CompletedHeight.normTwistedSource
  ring

lemma correctedSummand_fixed_finite (S : Finset Id) (D : Id) (Ψ : O→*ℂ)
    (T : ℝ) (hT : 0<T) :
    (Function.support (fun p : Id×Id=>correctedSummand S D Ψ gaussianFixedWindow T p.1 p.2)).Finite := by
  apply (completedT_finite_support Ψ gaussianFixedWindow gaussianFixedWindow_compact T hT).subset
  intro p hp hz
  exact hp (by simp only [correctedSummand,markedSummand,hz,mul_zero])

lemma gaussian_slot_integrable {ι : Type*} [Fintype ι]
    (W : ι→ℝ→ℂ) (q : ι→ℝ) (b : SchwartzMap ℝ ℂ) (x : ℝ) (c : ℂ) :
    Integrable (fun t : ℝ=>logPhase t x*c*
      (∏i,W i (q i)*logPhase (-t) (Real.log (q i)))*b t) := by
  have hh : Integrable (fun t : ℝ=>b t*(logPhase t x*c*
      ∏i,W i (q i)*logPhase (-t) (Real.log (q i)))) := by
    apply b.integrable.mul_bdd (c:=‖c‖*∏i,‖W i (q i)‖)
    · apply Continuous.aestronglyMeasurable
      apply Continuous.mul ((logPhase_continuous_left x).mul_const c)
      apply continuous_finsetProd
      intro i hi
      exact ((logPhase_continuous_left (Real.log (q i))).comp continuous_neg).const_mul _
    · apply Filter.Eventually.of_forall
      intro t
      simp only [norm_mul,norm_prod,logPhase_norm,mul_one,one_mul,le_refl]
  simpa only [mul_comm (b _) _] using hh

lemma gaussian_selected_completed_integrable {ι : Type*} [Fintype ι]
    (W : ι→ℝ→ℂ) (q : ι→ℝ) (b : SchwartzMap ℝ ℂ)
    (S : Finset Id) (D : Id) (Ψ : O→*ℂ) (T : ℝ) (hT : 0<T) :
    Integrable (fun t : ℝ=>correctedCompletedT S D Ψ
      (CompletedHeight.normTwistedSource gaussianFixedWindow t) T*
      (∏i,W i (q i)*logPhase (-t) (Real.log (q i)))*b t) := by
  let hf := correctedSummand_fixed_finite S D Ψ T hT
  have hz (p : Id×Id) (hp : p∉hf.toFinset) :
      correctedSummand S D Ψ gaussianFixedWindow T p.1 p.2=0 := by
    simpa only [Set.Finite.mem_toFinset,Function.mem_support,not_not] using hp
  have hr (t : ℝ) : correctedCompletedT S D Ψ
      (CompletedHeight.normTwistedSource gaussianFixedWindow t) T=
      ∑p∈hf.toFinset,correctedSummand S D Ψ
        (CompletedHeight.normTwistedSource gaussianFixedWindow t) T p.1 p.2 := by
    exact tsum_eq_sum (fun p hp=>by rw [correctedSummand_normTwisted,hz p hp,mul_zero])
  simp_rw [hr,Finset.sum_mul]
  apply integrable_finsetSum
  intro p hp
  simp_rw [correctedSummand_normTwisted]
  exact gaussian_slot_integrable W q b _ _

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.GaussianCrude
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ProbeCompleted ProbeRow CompletedGauss CubicEisenstein FourierBridge
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma gaussianAnnulus_norm_le_one (y : ℝ) : ‖gaussianAnnulus y‖≤1 := by
  rw [gaussianAnnulus_norm]
  change Real.smoothTransition (2-y)-Real.smoothTransition (2-2*y)≤1
  linarith [Real.smoothTransition.le_one (2-y),Real.smoothTransition.nonneg (2-2*y)]

lemma gaussianAnnulus_scaled_square (N T : ℝ) (hN : 0<N) (hT : 0<T) :
    N^2*‖gaussianAnnulus (N/T)‖≤4*T^2 := by
  by_cases hz : gaussianAnnulus (N/T)=0
  · rw [hz,norm_zero,mul_zero]
    positivity
  have hn : N/T<2 := by
    by_contra hh
    exact hz (gaussianAnnulus_large _ (le_of_not_gt hh))
  have hn' : N<2*T := (div_lt_iff₀ hT).mp hn
  calc
    _ ≤ N^2 := mul_le_of_le_one_right (sq_nonneg _) (gaussianAnnulus_norm_le_one _)
    _ ≤ _ := by nlinarith

lemma gaussianFixedWindow_spectral_identity (S : Finset Id) (D : Id) (Ψ : O→*ℂ)
    (T t : ℝ) (hT : 0<T) (I J : Id) (hI : I≠0) (hJ : J≠0) :
    correctedSummand S D Ψ (CompletedHeight.normTwistedSource gaussianFixedWindow t) T I J=
      spectralSummand S D Ψ 2 I J*
        ((((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3:ℝ):ℂ)^2*
          (gaussianAnnulus ((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3/T)*
            logPhase t (Real.log ((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3/T)))) := by
  have hi : (0:ℝ)<Ideal.absNorm I := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hj : (0:ℝ)<Ideal.absNorm J := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hJ)
  have hic : (Ideal.absNorm I:ℂ)≠0 := by exact_mod_cast hi.ne'
  have hjc : (Ideal.absNorm J:ℂ)≠0 := by exact_mod_cast hj.ne'
  unfold correctedSummand markedSummand CompletedGauss.summand spectralSummand fullIdealWeight
  rw [gaussianFixedWindow_Vstar_twist t _ (div_pos (mul_pos hi (pow_pos hj 3)) hT)]
  simp only [if_neg hI,if_neg hJ]
  norm_num only [show (3:ℂ)*2=6 by norm_num,Complex.cpow_neg,Complex.cpow_ofNat]
  push_cast
  field_simp

lemma gaussianFixedWindow_summand_crude (S : Finset Id) (D : Id) (Ψ : O→*ℂ)
    (hΨ : ∀n,‖Ψ n‖≤1) (T t : ℝ) (hT : 0<T) (I J : Id) :
    ‖correctedSummand S D Ψ (CompletedHeight.normTwistedSource gaussianFixedWindow t) T I J‖≤
      4*T^2*rowMajorant 2 (I,J) := by
  by_cases hI : I=0
  · subst I
    simp only [correctedSummand,markedSummand,summand_zero_left,mul_zero,norm_zero]
    unfold rowMajorant
    positivity
  by_cases hJ : J=0
  · subst J
    simp only [correctedSummand,markedSummand,summand_zero_right,mul_zero,norm_zero]
    unfold rowMajorant
    positivity
  have hi : (0:ℝ)<Ideal.absNorm I := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hj : (0:ℝ)<Ideal.absNorm J := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hJ)
  have hN : 0<(Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3 := mul_pos hi (pow_pos hj 3)
  rw [gaussianFixedWindow_spectral_identity S D Ψ T t hT I J hI hJ,
    norm_mul,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hN,
    norm_mul,logPhase_norm,mul_one]
  have hs : ‖spectralSummand S D Ψ 2 I J‖≤ rowMajorant 2 (I,J) := by
    simpa only [Complex.ofReal_ofNat,Complex.ofReal_zero,zero_mul,add_zero] using
      spectralSummand_vertical_bound S D Ψ hΨ 2 0 (I,J)
  have hn := gaussianAnnulus_scaled_square _ T hN hT
  exact (mul_le_mul hs hn (by positivity) (by unfold rowMajorant;positivity)).trans_eq (by ring)

theorem gaussianFixedWindow_completed_crude :
    ∃C : ℝ,0<C ∧ ∀S : Finset Id,∀D : Id,∀Ψ : O→*ℂ,
      (∀n,‖Ψ n‖≤1)→∀T t : ℝ,0<T→
      ‖correctedCompletedT S D Ψ (CompletedHeight.normTwistedSource gaussianFixedWindow t) T‖≤C*T^2 := by
  let M : ℝ := ∑'p : Id×Id,rowMajorant 2 p
  have hM : 0≤M := tsum_nonneg (fun p=>by unfold rowMajorant;positivity)
  refine ⟨4*M+1,by positivity,?_⟩
  intro S D Ψ hΨ T t hT
  have hs := correctedSummand_summable S D Ψ _ (gaussianFixedWindow_twist_compact t) T hT
  change ‖∑'p : Id×Id,correctedSummand S D Ψ (CompletedHeight.normTwistedSource gaussianFixedWindow t) T p.1 p.2‖≤_
  calc
    _ ≤ ∑'p : Id×Id,‖correctedSummand S D Ψ (CompletedHeight.normTwistedSource gaussianFixedWindow t) T p.1 p.2‖ := norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑'p : Id×Id,4*T^2*rowMajorant 2 p := hs.norm.tsum_le_tsum
      (fun p=>gaussianFixedWindow_summand_crude S D Ψ hΨ T t hT p.1 p.2)
      ((rowMajorant_summable 2 (by norm_num)).mul_left (4*T^2))
    _ = (4*M)*T^2 := by rw [tsum_mul_left];dsimp only [M];ring
    _ ≤ _ := by nlinarith [sq_nonneg T]

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.GaussianDensityBudget
namespace OAI

noncomputable section
open scoped Classical SchwartzMap
open MeasureTheory
namespace SevenEighths.ProbePhysical

lemma gaussianJointMoment_nonneg (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (J : ℕ) (R : ℝ) : 0≤gaussianJointMoment V hV J R := by
  apply integral_nonneg
  intro t
  positivity

lemma gaussianJointMoment_power_bound (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (J : ℕ) (A : ℝ) :
    ∃C : ℝ,0<C ∧ ∀R : ℝ,0<R→ gaussianJointMoment V hV J R≤C*R^(-A) := by
  obtain ⟨L,hL,hbox⟩ := hV.isBounded.exists_pos_norm_le
  have hb : ∀s,V s≠0→|s|≤L := by
    intro s hs
    simpa only [Real.norm_eq_abs] using hbox s (subset_tsupport V hs)
  exact gaussianLogWindow_fourier_moment V hV L hL.le hb A J

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

lemma physicalRowMonoid_norm (η : HeckeFamily.Character) (C : CalibrationData)
    (r : PhysicalRowIndex) (n : O) : ‖physicalRowMonoid η C r n‖≤1 :=
  rowCoefficient_norm_le_one η C.Xi C.Xi_norm_le_one _ _ r.2 n

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

lemma physicalRowScale_pos (C : CalibrationData) (X : ℝ) (hX : 0<X)
    (s : {I : Id // Supported I}) : 0<elementNorm C.generator*(Ideal.absNorm s.val:ℝ)*X := by
  have hc : 0<elementNorm C.generator := by
    unfold elementNorm
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr C.generator_ne_zero))
  have hs : (0:ℝ)<Ideal.absNorm s.val := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr s.property.1)
  positivity

theorem physicalRowWeight_finite_support (C : CalibrationData) (W0 W1 : ℝ→ℂ)
    (hW0 : HasCompactSupport W0) (hW1 : HasCompactSupport W1)
    (X Y : ℝ) (hX : 0<X) (hY : 0<Y) :
    (Function.support (physicalRowWeight C W0 W1 X Y)).Finite := by
  have ho := (idealWindow_finite_support W1 hW1 Y hY).preimage
    (f:=fun s : {I : Id // Supported I}=>s.val) Subtype.val_injective.injOn
  apply Set.Finite.of_finite_fibers Prod.fst
  · apply ho.subset
    rintro s ⟨r,hr,rfl⟩
    exact fun hz=>hr (physicalRowWeight_outer_zero C W0 W1 X Y r hz)
  · intro s hs
    have hm := elementWindow_finite_support W0 hW0 _ (physicalRowScale_pos C X hX s)
    apply ((Set.finite_singleton s).prod hm).subset
    intro r hr
    have he : r.1=s := hr.2
    refine ⟨he,?_⟩
    intro hz
    apply hr.1
    apply physicalRowWeight_inner_zero C W0 W1 X Y r
    simpa only [he] using hz

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.GaussianPhysicalTuple
namespace OAI

noncomputable section
open scoped Classical SchwartzMap
open MeasureTheory FourierBridge CompletedGauss
namespace SevenEighths.ProbePhysical
open ProbeCompleted ProbeRow
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma physicalRows_common_finset {α : Type*} (C : CalibrationData) (W0 W1 : ℝ→ℂ)
    (hW0 : HasCompactSupport W0) (hW1 : HasCompactSupport W1)
    (F : Finset α) (X Y : α→ℝ) (hX : ∀k∈F,0<X k) (hY : ∀k∈F,0<Y k) :
    ∃R : Finset PhysicalRowIndex,∀k∈F,∀r,r∉R→physicalRowWeight C W0 W1 (X k) (Y k) r=0 := by
  have hf (k : {k // k∈F}) := physicalRowWeight_finite_support C W0 W1 hW0 hW1
    (X k.val) (Y k.val) (hX k.val k.property) (hY k.val k.property)
  let R := F.attach.biUnion (fun k=>(hf k).toFinset)
  refine ⟨R,?_⟩
  intro k hk r hr
  by_contra hn
  apply hr
  exact Finset.mem_biUnion.mpr ⟨⟨k,hk⟩,by simp,by simpa only [Set.Finite.mem_toFinset,Function.mem_support] using hn⟩

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.GaussianTailBudget
namespace OAI

noncomputable section
open scoped Classical SchwartzMap
open MeasureTheory
namespace SevenEighths.ProbePhysical

lemma gaussianWeightedMoment_nonneg (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (J : ℕ) (k R : ℝ) (hR : 0≤R) : 0≤gaussianWeightedMoment V hV J k R := by
  unfold gaussianWeightedMoment
  exact mul_nonneg (Real.rpow_nonneg hR _) (gaussianJointMoment_nonneg V hV J R)

lemma gaussianWeightedMoment_power_bound (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (J : ℕ) (k A : ℝ) :
    ∃C : ℝ,0<C ∧ ∀R : ℝ,0<R→ gaussianWeightedMoment V hV J k R≤C*R^(-A) := by
  obtain ⟨C,hC,hb⟩ := gaussianJointMoment_power_bound V hV J (A+k)
  refine ⟨C,hC,?_⟩
  intro R hR
  have hh := mul_le_mul_of_nonneg_left (hb R hR) (Real.rpow_nonneg hR.le k)
  change R^k*gaussianJointMoment V hV J R≤_
  calc
    _ ≤ R^k*(C*R^(-(A+k))) := hh
    _ = C*R^(-A) := by
      rw [←mul_assoc,mul_comm (R^k) C,mul_assoc,←Real.rpow_add hR]
      congr 2
      ring

lemma gaussianWeightedMoment_polynomial_decay (V : SchwartzMap ℝ ℂ)
    (hV : HasCompactSupport (V:ℝ→ℂ)) (J : ℕ) (k : ℝ) (N : ℕ) :
    ∃C : ℝ,0<C ∧ ∀R : ℝ,0<R→ gaussianWeightedMoment V hV J k R≤C/(1+R)^N := by
  obtain ⟨B,hB,hzero⟩ := gaussianWeightedMoment_power_bound V hV J k 0
  obtain ⟨C,hC,hdecay⟩ := gaussianWeightedMoment_power_bound V hV J k (N:ℝ)
  refine ⟨(B+C)*(2:ℝ)^N,by positivity,?_⟩
  intro R hR
  have hden : 0<(1+R)^N := pow_pos (by linarith) _
  by_cases hr1 : R≤1
  · have hh := hzero R hR
    simp only [neg_zero,Real.rpow_zero,mul_one] at hh
    apply hh.trans
    apply (le_div_iff₀ hden).mpr
    have hp : (1+R)^N≤(2:ℝ)^N := pow_le_pow_left₀ (by linarith) (by linarith) _
    have hb := mul_le_mul_of_nonneg_left hp hB.le
    nlinarith [mul_nonneg hC.le (pow_nonneg (by norm_num : (0:ℝ)≤2) N)]
  · have hh := hdecay R hR
    rw [Real.rpow_neg hR.le,Real.rpow_natCast] at hh
    apply hh.trans
    apply (le_div_iff₀ hden).mpr
    have hp : (1+R)^N≤(2*R)^N := pow_le_pow_left₀ (by linarith) (by linarith) _
    have hm := mul_le_mul_of_nonneg_left hp (show 0≤C*(R^N)⁻¹ by positivity)
    rw [mul_pow] at hm
    have hn : R^N≠0 := ne_of_gt (pow_pos hR _)
    have he : (C*(R^N)⁻¹)*((2:ℝ)^N*R^N)=C*(2:ℝ)^N := by field_simp
    rw [he] at hm
    exact hm.trans (by nlinarith [mul_nonneg hB.le (pow_nonneg (by norm_num : (0:ℝ)≤2) N)])

theorem gaussianWeightedMoment_summed (V : SchwartzMap ℝ ℂ)
    (hV : HasCompactSupport (V:ℝ→ℂ)) (J : ℕ) (k s : ℝ) (hs : 0<s) :
    ∃C : ℝ,0<C ∧ ∀Z : ℝ,0<Z→
      Summable (fun j : ℕ=>((2:ℝ)^j)^s*gaussianWeightedMoment V hV J k ((2:ℝ)^j/Z)) ∧
      (∑'j : ℕ,((2:ℝ)^j)^s*gaussianWeightedMoment V hV J k ((2:ℝ)^j/Z))≤C*Z^s := by
  obtain ⟨N,hN⟩ := exists_nat_gt s
  obtain ⟨B,hB,hbound⟩ := gaussianWeightedMoment_polynomial_decay V hV J k N
  obtain ⟨C,hC,hkernel⟩ := CompletedDyadic.kernel_sum_bound s (N:ℝ) hs hN
  refine ⟨B*C,by positivity,?_⟩
  intro Z hZ
  obtain ⟨hks,hkt⟩ := hkernel Z⁻¹ (inv_pos.mpr hZ)
  have hb (j : ℕ) : ((2:ℝ)^j)^s*gaussianWeightedMoment V hV J k ((2:ℝ)^j/Z)≤
      B*CompletedDyadic.kernelTerm Z⁻¹ s (N:ℝ) j := by
    have hh := mul_le_mul_of_nonneg_left (hbound ((2:ℝ)^j/Z) (div_pos (by positivity) hZ))
      (Real.rpow_nonneg (by positivity : (0:ℝ)≤2^j) s)
    simpa only [CompletedDyadic.kernelTerm,Real.rpow_natCast,div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using hh
  have hnon (j : ℕ) : 0≤((2:ℝ)^j)^s*gaussianWeightedMoment V hV J k ((2:ℝ)^j/Z) :=
    mul_nonneg (Real.rpow_nonneg (by positivity : (0:ℝ)≤2^j) s) (gaussianWeightedMoment_nonneg V hV J k _ (by positivity))
  have hsum := Summable.of_nonneg_of_le hnon hb (hks.mul_left B)
  refine ⟨hsum,?_⟩
  calc
    _ ≤ ∑'j : ℕ,B*CompletedDyadic.kernelTerm Z⁻¹ s (N:ℝ) j := hsum.tsum_le_tsum hb (hks.mul_left B)
    _ = B*∑'j : ℕ,CompletedDyadic.kernelTerm Z⁻¹ s (N:ℝ) j := tsum_mul_left
    _ ≤ B*(C*(Z⁻¹)^(-s)) := mul_le_mul_of_nonneg_left hkt hB.le
    _ = (B*C)*Z^s := by rw [Real.inv_rpow hZ.le,Real.rpow_neg hZ.le,inv_inv]; ring

theorem gaussianRemoteMoment_summed (V : SchwartzMap ℝ ℂ)
    (hV : HasCompactSupport (V:ℝ→ℂ)) (J N : ℕ) (s : ℝ) (hs : 0<s) :
    ∃C : ℝ,0<C ∧ ∀Z A : ℝ,0<Z→1≤A→
      Summable (gaussianRemoteMoment V hV J s Z A) ∧
      (∑'j : ℕ,gaussianRemoteMoment V hV J s Z A j)≤C*Z^s/A^N := by
  obtain ⟨Cm,hCm,hm⟩ := gaussianWeightedMoment_summed V hV J (-(N:ℝ)) s hs
  obtain ⟨Cp,hCp,hp⟩ := gaussianWeightedMoment_summed V hV J (N:ℝ) s hs
  refine ⟨Cm+Cp,by positivity,?_⟩
  intro Z A hZ hA
  have hAp : 0<A := lt_of_lt_of_le zero_lt_one hA
  have hAN : 0<A^N := pow_pos hAp N
  obtain ⟨hsm,htm⟩ := hm Z hZ
  obtain ⟨hsp,htp⟩ := hp Z hZ
  let U : ℕ→ℝ := fun j=>
    (((2:ℝ)^j)^s*gaussianWeightedMoment V hV J (-(N:ℝ)) ((2:ℝ)^j/Z)+
      ((2:ℝ)^j)^s*gaussianWeightedMoment V hV J (N:ℝ) ((2:ℝ)^j/Z))/A^N
  have hU : Summable U := (hsm.add hsp).div_const _
  have hnon (j : ℕ) : 0≤gaussianRemoteMoment V hV J s Z A j := by
    unfold gaussianRemoteMoment
    split_ifs
    · exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (gaussianJointMoment_nonneg V hV J _)
    · rfl
  have hb (j : ℕ) : gaussianRemoteMoment V hV J s Z A j≤U j := by
    let R := (2:ℝ)^j/Z
    have hR : 0<R := div_pos (by positivity) hZ
    have hM : 0≤gaussianJointMoment V hV J R := gaussianJointMoment_nonneg V hV J R
    unfold gaussianRemoteMoment
    split_ifs with hj
    · have he : A^N≤R^(-(N:ℝ))+R^(N:ℝ) := by
        rcases hj with hlo|hhi
        · have hra : R*A≤1 := (le_div_iff₀ hAp).mp (by simpa only [one_div,R] using hlo)
          have hh := pow_le_pow_left₀ (by positivity : 0≤R*A) hra N
          rw [mul_pow,one_pow] at hh
          have hi : A^N≤R^(-(N:ℝ)) := by
            rw [Real.rpow_neg hR.le,Real.rpow_natCast]
            rw [←one_div]
            exact (le_div_iff₀ (pow_pos hR N)).mpr (by simpa only [mul_comm] using hh)
          exact hi.trans (le_add_of_nonneg_right (Real.rpow_nonneg hR.le _))
        · have hi : A^N≤R^(N:ℝ) := by
            rw [Real.rpow_natCast]
            exact pow_le_pow_left₀ hAp.le hhi N
          exact hi.trans (le_add_of_nonneg_left (Real.rpow_nonneg hR.le _))
      change ((2:ℝ)^j)^s*gaussianJointMoment V hV J R≤_
      dsimp only [U]
      apply (le_div_iff₀ hAN).mpr
      calc
        _ ≤ (((2:ℝ)^j)^s*gaussianJointMoment V hV J R)*(R^(-(N:ℝ))+R^(N:ℝ)) :=
          mul_le_mul_of_nonneg_left he (mul_nonneg (Real.rpow_nonneg (by positivity) _) hM)
        _ = _ := by unfold gaussianWeightedMoment;dsimp only [R];ring
    · dsimp only [U]
      apply div_nonneg _ hAN.le
      exact add_nonneg
        (mul_nonneg (Real.rpow_nonneg (by positivity) _) (gaussianWeightedMoment_nonneg V hV J _ _ hR.le))
        (mul_nonneg (Real.rpow_nonneg (by positivity) _) (gaussianWeightedMoment_nonneg V hV J _ _ hR.le))
  have hsum := Summable.of_nonneg_of_le hnon hb hU
  refine ⟨hsum,?_⟩
  calc
    _ ≤ ∑'j : ℕ,U j := hsum.tsum_le_tsum hb hU
    _ = ((∑'j : ℕ,((2:ℝ)^j)^s*gaussianWeightedMoment V hV J (-(N:ℝ)) ((2:ℝ)^j/Z))+
        (∑'j : ℕ,((2:ℝ)^j)^s*gaussianWeightedMoment V hV J (N:ℝ) ((2:ℝ)^j/Z)))/A^N := by
      dsimp only [U]
      rw [tsum_div_const,hsm.tsum_add hsp]
    _ ≤ (Cm*Z^s+Cp*Z^s)/A^N := div_le_div_of_nonneg_right (add_le_add htm htp) hAN.le
    _ = _ := by ring

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.GaussianRemoteRows
namespace OAI

noncomputable section
open scoped Classical SchwartzMap
open MeasureTheory CompletedGauss FourierBridge
namespace SevenEighths.ProbePhysical
open ProbeCompleted
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma gaussianCompletedFamilyMass_nonneg {α ι : Type*} [Fintype ι]
    (F : Finset α) (a : α→ℂ) (W : ι→ℝ→ℂ) (q : α→ι→ℝ) :
    0≤gaussianCompletedFamilyMass F a W q := by
  unfold gaussianCompletedFamilyMass
  positivity

lemma gaussianCompletedFamily_integrable {α ι : Type*} [Fintype ι]
    (F : Finset α) (a : α→ℂ) (S : Finset Id) (D : α→Id) (Ψ : α→O→*ℂ)
    (W : ι→ℝ→ℂ) (q : α→ι→ℝ) (V : SchwartzMap ℝ ℂ)
    (hV : HasCompactSupport (V:ℝ→ℂ)) (T Z : ℝ) (hT : 0<T) :
    Integrable (fun t : ℝ=>(∑k∈F,a k*correctedCompletedT S (D k) (Ψ k)
      (CompletedHeight.normTwistedSource gaussianFixedWindow t) T*
      (∏i,W i (q k i)*logPhase (-t) (Real.log (q k i))))*gaussianJointDensity V hV (T/Z) t) := by
  have hh := integrable_finsetSum F (fun k _=>(gaussian_selected_completed_integrable W (q k)
    (gaussianJointDensity V hV (T/Z)) S (D k) (Ψ k) T hT).const_mul (a k))
  simpa only [Finset.sum_mul,mul_assoc] using hh

theorem gaussianCompletedFamily_crude :
    ∃C : ℝ,0<C ∧ ∀{α ι : Type*} [Fintype ι],∀F : Finset α,∀a : α→ℂ,
      ∀S : Finset Id,∀D : α→Id,∀Ψ : α→O→*ℂ,
      (∀k∈F,∀n,‖Ψ k n‖≤1)→∀W : ι→ℝ→ℂ,∀q : α→ι→ℝ,
      ∀V : SchwartzMap ℝ ℂ,∀hV : HasCompactSupport (V:ℝ→ℂ),∀T Z : ℝ,0<T→
      ‖gaussianCompletedFamilyIntegral F a S D Ψ W q V hV T Z‖≤
        C*T^2*gaussianCompletedFamilyMass F a W q*gaussianJointMoment V hV 0 (T/Z) := by
  obtain ⟨C,hC,hb⟩ := gaussianFixedWindow_completed_crude
  refine ⟨C,hC,?_⟩
  intro α ι _ F a S D Ψ hΨ W q V hV T Z hT
  have hf := gaussianCompletedFamily_integrable F a S D Ψ W q V hV T Z hT
  have hp (t : ℝ) :
      ‖(∑k∈F,a k*correctedCompletedT S (D k) (Ψ k)
        (CompletedHeight.normTwistedSource gaussianFixedWindow t) T*
        (∏i,W i (q k i)*logPhase (-t) (Real.log (q k i))))*gaussianJointDensity V hV (T/Z) t‖≤
      (C*T^2*gaussianCompletedFamilyMass F a W q)*‖gaussianJointDensity V hV (T/Z) t‖ := by
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    calc
      _ ≤ ∑k∈F,‖a k*correctedCompletedT S (D k) (Ψ k)
        (CompletedHeight.normTwistedSource gaussianFixedWindow t) T*
        (∏i,W i (q k i)*logPhase (-t) (Real.log (q k i)))‖ := norm_sum_le _ _
      _ ≤ ∑k∈F,‖a k‖*(C*T^2)*(∏i,‖W i (q k i)‖) := by
        apply Finset.sum_le_sum
        intro k hk
        simp only [norm_mul,norm_prod,logPhase_norm,mul_one]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hb S (D k) (Ψ k) (hΨ k hk) T t hT) (norm_nonneg _))
          (Finset.prod_nonneg (fun _ _=>norm_nonneg _))
      _ = _ := by unfold gaussianCompletedFamilyMass;rw [Finset.mul_sum];congr 1;funext k;ring
  calc
    _ ≤ ∫t : ℝ,‖(∑k∈F,a k*correctedCompletedT S (D k) (Ψ k)
        (CompletedHeight.normTwistedSource gaussianFixedWindow t) T*
        (∏i,W i (q k i)*logPhase (-t) (Real.log (q k i))))*gaussianJointDensity V hV (T/Z) t‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫t : ℝ,(C*T^2*gaussianCompletedFamilyMass F a W q)*‖gaussianJointDensity V hV (T/Z) t‖ :=
      integral_mono hf.norm ((gaussianJointDensity V hV (T/Z)).integrable.norm.const_mul _) hp
    _ = _ := by simp only [integral_const_mul,gaussianJointMoment,pow_zero,one_mul]

theorem gaussianCompletedFamily_remote (V : SchwartzMap ℝ ℂ)
    (hV : HasCompactSupport (V:ℝ→ℂ)) (N : ℕ) :
    ∃C : ℝ,0<C ∧ ∀{α ι : Type*} [Fintype ι],∀F : Finset α,∀a : α→ℂ,
      ∀S : Finset Id,∀D : α→Id,∀Ψ : α→O→*ℂ,
      (∀k∈F,∀n,‖Ψ k n‖≤1)→∀W : ι→ℝ→ℂ,∀q : α→ι→ℝ,
      ∀Z A : ℝ,0<Z→1≤A→
      Summable (fun j : ℕ=>if (2:ℝ)^j/Z≤A⁻¹ ∨ A≤(2:ℝ)^j/Z then
        ‖gaussianCompletedFamilyIntegral F a S D Ψ W q V hV ((2:ℝ)^j) Z‖ else 0) ∧
      (∑'j : ℕ,if (2:ℝ)^j/Z≤A⁻¹ ∨ A≤(2:ℝ)^j/Z then
        ‖gaussianCompletedFamilyIntegral F a S D Ψ W q V hV ((2:ℝ)^j) Z‖ else 0)≤
          C*gaussianCompletedFamilyMass F a W q*Z^2/A^N := by
  obtain ⟨Cr,hCr,hr⟩ := gaussianCompletedFamily_crude
  obtain ⟨Cg,hCg,hg⟩ := gaussianRemoteMoment_summed V hV 0 N 2 (by norm_num)
  refine ⟨Cr*Cg,by positivity,?_⟩
  intro α ι _ F a S D Ψ hΨ W q Z A hZ hA
  obtain ⟨hs,ht⟩ := hg Z A hZ hA
  let M := gaussianCompletedFamilyMass F a W q
  have hM : 0≤M := gaussianCompletedFamilyMass_nonneg F a W q
  have hb (j : ℕ) :
      (if (2:ℝ)^j/Z≤A⁻¹ ∨ A≤(2:ℝ)^j/Z then
        ‖gaussianCompletedFamilyIntegral F a S D Ψ W q V hV ((2:ℝ)^j) Z‖ else 0)≤
      (Cr*M)*gaussianRemoteMoment V hV 0 2 Z A j := by
    unfold gaussianRemoteMoment
    split_ifs
    · simpa only [M,Real.rpow_two,mul_assoc,mul_comm,mul_left_comm] using
        hr F a S D Ψ hΨ W q V hV ((2:ℝ)^j) Z (by positivity)
    · simp
  have hnon (j : ℕ) : 0≤(if (2:ℝ)^j/Z≤A⁻¹ ∨ A≤(2:ℝ)^j/Z then
      ‖gaussianCompletedFamilyIntegral F a S D Ψ W q V hV ((2:ℝ)^j) Z‖ else 0) := by split_ifs <;> positivity
  have hsum := Summable.of_nonneg_of_le hnon hb (hs.mul_left (Cr*M))
  refine ⟨hsum,?_⟩
  calc
    _ ≤ ∑'j : ℕ,(Cr*M)*gaussianRemoteMoment V hV 0 2 Z A j := hsum.tsum_le_tsum hb (hs.mul_left (Cr*M))
    _ = (Cr*M)*∑'j : ℕ,gaussianRemoteMoment V hV 0 2 Z A j := tsum_mul_left
    _ ≤ (Cr*M)*(Cg*Z^(2:ℝ)/A^N) := mul_le_mul_of_nonneg_left ht (mul_nonneg hCr.le hM)
    _ = _ := by rw [Real.rpow_two];dsimp only [M];ring

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.GaussianPhysicalTail
namespace OAI

noncomputable section
open scoped Classical SchwartzMap
open MeasureTheory CompletedGauss FourierBridge
namespace SevenEighths.ProbePhysical
open ProbeCompleted
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma gaussianPhysicalFamily_mass_eq {α ι : Type*} [Fintype ι]
    (C : CalibrationData) (W0 W1 : ℝ→ℂ) (F : Finset α) (a : α→ℂ) (X Y : α→ℝ)
    (W : ι→ℝ→ℂ) (q : α→ι→ℝ) (R : Finset PhysicalRowIndex)
    (hR : ∀k∈F,∀r∉R,physicalRowWeight C W0 W1 (X k) (Y k) r=0) :
    gaussianCompletedFamilyMass (F×ˢR)
      (fun p=>a p.1*physicalRowWeight C W0 W1 (X p.1) (Y p.1) p.2) W (fun p=>q p.1)=
      gaussianPhysicalFamilyMass C W0 W1 F a X Y W q := by
  unfold gaussianCompletedFamilyMass gaussianPhysicalFamilyMass
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro k hk
  rw [tsum_eq_sum (s:=R) (fun r hr=>by rw [hR k hk r hr,norm_zero]),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [norm_mul]
  ring

lemma gaussianPhysicalFamily_integral_eq {α ι : Type*} [Fintype ι]
    (η : HeckeFamily.Character) (C : CalibrationData) (W0 W1 : ℝ→ℂ)
    (F : Finset α) (a : α→ℂ) (D : α→Id) (X Y : α→ℝ)
    (W : ι→ℝ→ℂ) (q : α→ι→ℝ) (V : SchwartzMap ℝ ℂ)
    (hV : HasCompactSupport (V:ℝ→ℂ)) (T Z : ℝ) (R : Finset PhysicalRowIndex)
    (hR : ∀k∈F,∀r∉R,physicalRowWeight C W0 W1 (X k) (Y k) r=0) :
    gaussianPhysicalFamilyIntegral η C W0 W1 F a D X Y W q V hV T Z=
      gaussianCompletedFamilyIntegral (F×ˢR)
        (fun p=>a p.1*physicalRowWeight C W0 W1 (X p.1) (Y p.1) p.2)
        C.excluded (fun p=>D p.1) (fun p=>physicalRowMonoid η C p.2) W (fun p=>q p.1) V hV T Z := by
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  dsimp only
  congr 1
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro k hk
  rw [tsum_eq_sum (s:=R) (fun r hr=>by rw [hR k hk r hr,zero_mul]),Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r hr
  ring

theorem gaussianPhysicalFamily_remote (V : SchwartzMap ℝ ℂ)
    (hV : HasCompactSupport (V:ℝ→ℂ)) (N : ℕ) :
    ∃C0 : ℝ,0<C0 ∧ ∀{α ι : Type*} [Fintype ι],
      ∀η : HeckeFamily.Character,∀C : CalibrationData,∀W0 W1 : ℝ→ℂ,
      HasCompactSupport W0→HasCompactSupport W1→
      ∀F : Finset α,∀a : α→ℂ,∀D : α→Id,∀X Y : α→ℝ,
      (∀k∈F,0<X k)→(∀k∈F,0<Y k)→∀W : ι→ℝ→ℂ,∀q : α→ι→ℝ,
      ∀Z A : ℝ,0<Z→1≤A→
      Summable (fun j : ℕ=>if (2:ℝ)^j/Z≤A⁻¹ ∨ A≤(2:ℝ)^j/Z then
        ‖gaussianPhysicalFamilyIntegral η C W0 W1 F a D X Y W q V hV ((2:ℝ)^j) Z‖ else 0) ∧
      (∑'j : ℕ,if (2:ℝ)^j/Z≤A⁻¹ ∨ A≤(2:ℝ)^j/Z then
        ‖gaussianPhysicalFamilyIntegral η C W0 W1 F a D X Y W q V hV ((2:ℝ)^j) Z‖ else 0)≤
          C0*gaussianPhysicalFamilyMass C W0 W1 F a X Y W q*Z^2/A^N := by
  obtain ⟨C0,hC0,hb⟩ := gaussianCompletedFamily_remote V hV N
  refine ⟨C0,hC0,?_⟩
  intro α ι _ η C W0 W1 hW0 hW1 F a D X Y hX hY W q Z A hZ hA
  obtain ⟨R,hR⟩ := physicalRows_common_finset C W0 W1 hW0 hW1 F X Y hX hY
  have hh := hb (F×ˢR) (fun p=>a p.1*physicalRowWeight C W0 W1 (X p.1) (Y p.1) p.2)
    C.excluded (fun p=>D p.1) (fun p=>physicalRowMonoid η C p.2)
    (fun p _=>physicalRowMonoid_norm η C p.2) W (fun p=>q p.1) Z A hZ hA
  rw [gaussianPhysicalFamily_mass_eq C W0 W1 F a X Y W q R hR] at hh
  simpa only [gaussianPhysicalFamily_integral_eq η C W0 W1 F a D X Y W q V hV _ Z R hR] using hh

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.LowRowMellin
namespace OAI

noncomputable section
open scoped Classical ContDiff
open MeasureTheory CompletedGauss
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve CanonicalRowCompletion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma calibration_residue_inverse_norm (C : CalibrationData) (a : O) : ‖(C.residueMonoid a)⁻¹‖≤1 := by
  let : Finite (O ⧸ Ideal.span {C.generator}) := Ring.HasFiniteQuotients.finiteQuotient
    (Ideal.span_singleton_eq_bot.not.mpr C.generator_ne_zero)
  let : Fintype (O ⧸ Ideal.span {C.generator}) := Fintype.ofFinite _
  change ‖(C.residue (Ideal.Quotient.mk (Ideal.span {C.generator}) a))⁻¹‖≤1
  simpa only [MulChar.inv_apply_eq_inv'] using
    FiniteRayExpansion.norm_char_le_one C.residue⁻¹ (Ideal.Quotient.mk (Ideal.span {C.generator}) a)

lemma lowArithmeticCoefficient_norm (C : CalibrationData) (s : {I : Id // Supported I}) :
    ‖lowArithmeticCoefficient C s‖≤‖C.tau‖⁻¹ := by
  unfold lowArithmeticCoefficient
  split_ifs
  · simp only [div_eq_mul_inv,mul_inv_rev,norm_mul,norm_inv]
    have hi := calibration_residue_inverse_norm C (primaryGenerator s.val)
    rw [norm_inv] at hi
    have hh := (mul_le_of_le_one_left (inv_nonneg.mpr (norm_nonneg _)) (idealRowHom_norm C.generator s.val)).trans hi
    simpa only [mul_assoc] using mul_le_of_le_one_left (inv_nonneg.mpr (norm_nonneg C.tau)) hh
  · simp

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.LowColumnBounds
namespace OAI

noncomputable section
open scoped Classical
open CompletedGauss
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma lowGaussColumns_mem (W1 : ℝ→ℂ) (hW1 : HasCompactSupport W1) (Y : ℝ) (hY : 0<Y)
    (s : {I : Id // Supported I}) :
    s∈lowGaussColumns W1 hW1 Y hY ↔ W1 ((Ideal.absNorm s.val:ℝ)/Y)≠0 := by
  simp only [lowGaussColumns,Set.Finite.mem_toFinset,Set.mem_preimage,Function.mem_support]

lemma lowGaussColumns_card (W1 : ℝ→ℂ) (hW1 : HasCompactSupport W1) (Y : ℝ) (hY : 1≤Y)
    (a b : ℝ) (hW : Function.support W1⊆Set.Icc a b) :
    ((lowGaussColumns W1 hW1 Y (lt_of_lt_of_le zero_lt_one hY)).card:ℝ)≤128*max 1 b*Y := by
  let F := lowGaussColumns W1 hW1 Y (lt_of_lt_of_le zero_lt_one hY)
  have hH : 1≤ max 1 b*Y := one_le_mul_of_one_le_of_one_le (le_max_left _ _) hY
  have hh := DescentFiberCost.finite_ideal_count_real (F.image Subtype.val) (max 1 b*Y) hH
    (by intro I hI;obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hI;exact s.property.1)
    (by
      intro I hI
      obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hI
      have hw := (hW ((lowGaussColumns_mem W1 hW1 Y _ s).mp hs)).2
      have hn : (Ideal.absNorm s.val:ℝ)≤b*Y := (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hY)).mp hw
      exact hn.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (le_trans zero_le_one hY)))
  rw [Finset.card_image_of_injective _ Subtype.val_injective] at hh
  simpa only [mul_assoc,F] using hh

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.LowActualEnergies
namespace OAI

noncomputable section
open scoped Classical ContDiff SchwartzMap
open MeasureTheory CompletedGauss
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve RayFourExpansion CenteredMomentGaussEnergy
local notation "O" => ActualEisensteinCubic.O

lemma lowNumeratorRows_mem (a b : ℝ) (ha : 0<a) (hb : 0<b) (Q : ℝ) (hQ : 0<Q) (m : O) :
    m∈lowNumeratorRows a b ha hb Q hQ ↔ lowOuterCutoff a b (elementNorm m/Q)≠0 := by
  simp only [lowNumeratorRows,Set.Finite.mem_toFinset,Function.mem_support]

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.PhysicalCrudeMass
namespace OAI

noncomputable section
open scoped Classical
open CompletedGauss
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve CanonicalRowCompletion ConcreteTraceCRT CubicEisenstein
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma calibration_elementNorm_ge_one (C : CalibrationData) : 1≤elementNorm C.generator := by
  unfold elementNorm
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
    (Ideal.span_singleton_eq_bot.not.mpr C.generator_ne_zero))

lemma sexticGauss_norm_le (s : O) (hs : s≠0) (m : O) : ‖sexticGauss s hs m‖≤elementNorm s := by
  let := finite_quotient_span hs
  let : Fintype (O⧸Ideal.span {s}) := Fintype.ofFinite _
  rw [sexticGauss,tsum_fintype]
  calc
    _ ≤ ∑d : O⧸Ideal.span {s},‖idealRowHom (GaussianShiftedPartition.representative s d) (Ideal.span {s})*
      quotientTrace s hs (Ideal.Quotient.mk _ m*d)‖ := norm_sum_le _ _
    _ ≤ ∑_d : O⧸Ideal.span {s},(1:ℝ) := Finset.sum_le_sum (fun d _=>by
      rw [norm_mul,(quotientTrace s hs).norm_apply,mul_one]
      exact idealRowHom_norm _ _)
    _ = _ := by simp [elementNorm,Ideal.absNorm_apply,Submodule.cardQuot_apply,Nat.card_eq_fintype_card]

lemma physicalRowWeight_arithmetic_form (C : CalibrationData) (W0 W1 : ℝ→ℂ)
    (X Y : ℝ) (r : PhysicalRowIndex) :
    physicalRowWeight C W0 W1 X Y r=
      (Y:ℂ)⁻¹*W1 ((Ideal.absNorm r.1.val:ℝ)/Y)*lowArithmeticCoefficient C r.1*
        (Real.sqrt (elementNorm C.generator*(Ideal.absNorm r.1.val:ℝ)*X):ℂ)⁻¹*
        C.residueMonoid r.2*(Real.sqrt (Ideal.absNorm r.1.val):ℂ)⁻¹*
        sexticGauss (primaryGenerator r.1.val) (supported_primaryGenerator_ne_zero r.1.val r.1.property) (-r.2)*
        W0 (elementNorm r.2/(elementNorm C.generator*(Ideal.absNorm r.1.val:ℝ)*X)) := by
  unfold physicalRowWeight lowArithmeticCoefficient
  split_ifs <;> simp only [mul_zero,zero_mul]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

lemma physicalRowWeight_crude_point (C : CalibrationData) (W0 W1 : ℝ→ℂ)
    (B0 B1 : ℝ) (hB0 : 0≤B0) (hB1 : 0≤B1)
    (hW0 : ∀x,‖W0 x‖≤B0) (hW1 : ∀x,‖W1 x‖≤B1)
    (X Y : ℝ) (hX : 1≤X) (hY : 0<Y) (r : PhysicalRowIndex) :
    ‖physicalRowWeight C W0 W1 X Y r‖≤B0*B1*‖C.tau‖⁻¹/Y := by
  have hq : (0:ℝ)<Ideal.absNorm r.1.val := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr r.1.property.1)
  have hb := calibration_elementNorm_ge_one C
  have hscale : 0<elementNorm C.generator*(Ideal.absNorm r.1.val:ℝ)*X :=
    physicalRowScale_pos C X (lt_of_lt_of_le zero_lt_one hX) r.1
  have hqscale : (Ideal.absNorm r.1.val:ℝ)≤elementNorm C.generator*(Ideal.absNorm r.1.val:ℝ)*X := by
    have hbx : 1≤elementNorm C.generator*X := one_le_mul_of_one_le_of_one_le hb hX
    nlinarith
  have hsqrt := Real.sqrt_le_sqrt hqscale
  have hrad : (Real.sqrt (elementNorm C.generator*(Ideal.absNorm r.1.val:ℝ)*X))⁻¹*
      (Real.sqrt (Ideal.absNorm r.1.val:ℝ))⁻¹*(Ideal.absNorm r.1.val:ℝ)≤1 := by
    have hspos : 0<Real.sqrt (elementNorm C.generator*(Ideal.absNorm r.1.val:ℝ)*X)*
      Real.sqrt (Ideal.absNorm r.1.val:ℝ) := mul_pos (Real.sqrt_pos.mpr hscale) (Real.sqrt_pos.mpr hq)
    calc
      _ = (Ideal.absNorm r.1.val:ℝ)/(Real.sqrt (elementNorm C.generator*(Ideal.absNorm r.1.val:ℝ)*X)*
        Real.sqrt (Ideal.absNorm r.1.val:ℝ)) := by simp only [div_eq_mul_inv,mul_inv_rev];ring
      _ ≤ 1 := (div_le_one hspos).mpr (by nlinarith [mul_le_mul_of_nonneg_right hsqrt (Real.sqrt_nonneg (Ideal.absNorm r.1.val:ℝ)), Real.sq_sqrt hq.le])
  have hg := sexticGauss_norm_le (primaryGenerator r.1.val) (supported_primaryGenerator_ne_zero r.1.val r.1.property) (-r.2)
  have he := (primaryGenerator_spec r.1.val (supported_primaryGenerator_ne_zero r.1.val r.1.property)).1
  unfold elementNorm at hg
  rw [he] at hg
  rw [physicalRowWeight_arithmetic_form]
  simp only [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hY,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  calc
    _ ≤ Y⁻¹*B1*‖C.tau‖⁻¹*(Real.sqrt (elementNorm C.generator*(Ideal.absNorm r.1.val:ℝ)*X))⁻¹*
      1*(Real.sqrt (Ideal.absNorm r.1.val:ℝ))⁻¹*(Ideal.absNorm r.1.val:ℝ)*B0 := by
      gcongr
      · exact hW1 _
      · exact lowArithmeticCoefficient_norm C r.1
      · exact C.residueMonoid_norm_le_one r.2
      · exact hW0 _
    _ = (B0*B1*‖C.tau‖⁻¹/Y)*((Real.sqrt (elementNorm C.generator*(Ideal.absNorm r.1.val:ℝ)*X))⁻¹*
        (Real.sqrt (Ideal.absNorm r.1.val:ℝ))⁻¹*(Ideal.absNorm r.1.val:ℝ)) := by ring
    _ ≤ _ := mul_le_of_le_one_right (by positivity) hrad

lemma lowNumeratorRows_card (a b : ℝ) (ha : 0<a) (hb : 0<b) (Q : ℝ) (hQ : 1≤Q) :
    ((lowNumeratorRows a b ha hb Q (lt_of_lt_of_le zero_lt_one hQ)).card:ℝ)≤256*max 1 b*Q := by
  have hscale : 1≤2*max 1 b*Q := by nlinarith [le_max_left 1 b]
  have hh := DescentFiberCost.finite_element_count_real (lowNumeratorRows a b ha hb Q (lt_of_lt_of_le zero_lt_one hQ)) _ hscale
    (by
      intro m hm
      have h := (lowOuterCutoff_support a b ha hb ((lowNumeratorRows_mem a b ha hb Q (lt_of_lt_of_le zero_lt_one hQ) m).mp hm)).2
      have hn := (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hQ)).mp h
      rw [ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span]
      change elementNorm m≤2*max 1 b*Q
      exact hn.trans (by gcongr;exact le_max_right _ _))
  convert (preTransparency := .instances) hh using 1 ; ring

lemma lowPhysicalScale_ge_one (C : CalibrationData) (X Y : ℝ) (hX : 1≤X) (hY : 1≤Y) :
    1≤lowPhysicalScale C X Y :=
  one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (calibration_elementNorm_ge_one C) hX) hY

lemma physicalRowWeight_source_rectangle (C : CalibrationData) (W0 W1 : ℝ→ℂ)
    (hW1c : HasCompactSupport W1) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y : ℝ) (hX : 0<X) (hY : 0<Y) (r : PhysicalRowIndex)
    (hr : r∉(lowGaussColumns W1 hW1c Y hY) ×ˢ
      (lowNumeratorRows (a0*a1) (max 1 (b0*b1)) (mul_pos ha0 ha1)
        (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) (lowPhysicalScale C X Y)
        (lowPhysicalScale_pos C X Y hX hY))) :
    physicalRowWeight C W0 W1 X Y r=0 := by
  by_cases hs : r.1∈lowGaussColumns W1 hW1c Y hY
  · have hm : r.2∉lowNumeratorRows (a0*a1) (max 1 (b0*b1)) (mul_pos ha0 ha1)
        (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) (lowPhysicalScale C X Y)
        (lowPhysicalScale_pos C X Y hX hY) := fun hm=>hr (Finset.mem_product.mpr ⟨hs,hm⟩)
    have hz : lowOuterCutoff (a0*a1) (max 1 (b0*b1)) (elementNorm r.2/lowPhysicalScale C X Y)=0 := by
      simpa only [lowNumeratorRows_mem,not_not] using hm
    rw [physicalRowWeight_insert_cutoff C W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y hY r]
    change lowOuterCutoff _ _ (elementNorm r.2/lowPhysicalScale C X Y)*_=0
    rw [hz,zero_mul]
  · apply physicalRowWeight_outer_zero
    simpa only [lowGaussColumns_mem,not_not] using hs

theorem physicalRowWeight_source_mass (a0 b0 a1 b1 B0 B1 : ℝ)
    (ha0 : 0<a0) (ha1 : 0<a1) (hB0 : 0≤B0) (hB1 : 0≤B1) :
    ∃K : ℝ,0<K ∧ ∀S : Finset Id,∀hS : ∀P∈S,P.IsMaximal,
      ∀W0 W1 : ℝ→ℂ,∀_hW1c : HasCompactSupport W1,
      Function.support W0⊆Set.Icc a0 b0 → Function.support W1⊆Set.Icc a1 b1 →
      (∀x,‖W0 x‖≤B0) → (∀x,‖W1 x‖≤B1) →
      ∀X Y : ℝ,1≤X → 1≤Y →
      (∑'r : PhysicalRowIndex,‖physicalRowWeight (calibrationForSet S hS) W0 W1 X Y r‖)≤
        K*lowPhysicalScale (calibrationForSet S hS) X Y := by
  let K := 32768*max 1 b1*max 1 (b0*b1)*B0*B1+1
  refine ⟨K,by dsimp only [K];positivity,?_⟩
  intro S hS W0 W1 hW1c hW0 hW1 hWB0 hWB1 X Y hX hY
  let C := calibrationForSet S hS
  have hx : 0<X := lt_of_lt_of_le zero_lt_one hX
  have hy : 0<Y := lt_of_lt_of_le zero_lt_one hY
  let Q := lowPhysicalScale C X Y
  have hQ : 1≤Q := lowPhysicalScale_ge_one C X Y hX hY
  let F := lowGaussColumns W1 hW1c Y hy
  let R := lowNumeratorRows (a0*a1) (max 1 (b0*b1)) (mul_pos ha0 ha1)
    (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) Q (lowPhysicalScale_pos C X Y hx hy)
  have hzero (r : PhysicalRowIndex) (hr : r∉F×ˢR) : ‖physicalRowWeight C W0 W1 X Y r‖=0 := by
    rw [physicalRowWeight_source_rectangle C W0 W1 hW1c a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y hx hy r hr,norm_zero]
  have hpoint (r : PhysicalRowIndex) : ‖physicalRowWeight C W0 W1 X Y r‖≤B0*B1/Y := by
    have h := physicalRowWeight_crude_point C W0 W1 B0 B1 hB0 hB1 hWB0 hWB1 X Y hX hy r
    simpa only [C,calibrationForSet_tau_norm,inv_one,mul_one] using h
  have hF : (F.card:ℝ)≤128*max 1 b1*Y := lowGaussColumns_card W1 hW1c Y hY a1 b1 hW1
  have hR : (R.card:ℝ)≤256*max 1 (b0*b1)*Q := by
    simpa only [R,max_eq_right (le_max_left 1 (b0*b1))] using lowNumeratorRows_card (a0*a1) (max 1 (b0*b1)) (mul_pos ha0 ha1)
      (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) Q hQ
  rw [tsum_eq_sum (s:=F×ˢR) hzero]
  calc
    _ ≤ ∑_r∈F×ˢR,B0*B1/Y := Finset.sum_le_sum (fun r _=>hpoint r)
    _ = (F.card:ℝ)*(R.card:ℝ)*(B0*B1/Y) := by simp [Finset.card_product,mul_assoc]
    _ ≤ (128*max 1 b1*Y)*(256*max 1 (b0*b1)*Q)*(B0*B1/Y) := by gcongr
    _ = (32768*max 1 b1*max 1 (b0*b1)*B0*B1)*Q := by field_simp;ring
    _ ≤ K*Q := mul_le_mul_of_nonneg_right (by dsimp only [K];linarith) (le_trans zero_le_one hQ)

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.GaussianPhysicalMass
namespace OAI

noncomputable section
open scoped Classical SchwartzMap
open MeasureTheory CompletedGauss
namespace SevenEighths.ProbePhysical
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem gaussianPhysicalFamily_mass_bound (a0 b0 a1 b1 B0 B1 : ℝ)
    (ha0 : 0<a0) (ha1 : 0<a1) (hB0 : 0≤B0) (hB1 : 0≤B1) :
    ∃K : ℝ,0<K ∧ ∀{α ι : Type*} [Fintype ι],
      ∀S : Finset Id,∀hS : ∀P∈S,P.IsMaximal,
      ∀W0 W1 : ℝ→ℂ,∀_hW1c : HasCompactSupport W1,
      Function.support W0⊆Set.Icc a0 b0 → Function.support W1⊆Set.Icc a1 b1 →
      (∀x,‖W0 x‖≤B0) → (∀x,‖W1 x‖≤B1) →
      ∀F : Finset α,∀a : α→ℂ,∀X Y : α→ℝ,
      (∀k∈F,1≤X k)→(∀k∈F,1≤Y k)→∀W : ι→ℝ→ℂ,∀q : α→ι→ℝ,
      gaussianPhysicalFamilyMass (calibrationForSet S hS) W0 W1 F a X Y W q≤
        K*gaussianPhysicalScaleMass (calibrationForSet S hS) F a X Y W q := by
  obtain ⟨K,hK,hb⟩ := physicalRowWeight_source_mass a0 b0 a1 b1 B0 B1 ha0 ha1 hB0 hB1
  refine ⟨K,hK,?_⟩
  intro α ι _ S hS W0 W1 hW1c hW0 hW1 hWB0 hWB1 F a X Y hX hY W q
  unfold gaussianPhysicalFamilyMass gaussianPhysicalScaleMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  calc
    _ ≤ (‖a k‖*(∏i,‖W i (q k i)‖))*(K*lowPhysicalScale (calibrationForSet S hS) (X k) (Y k)) :=
      mul_le_mul_of_nonneg_left (hb S hS W0 W1 hW1c hW0 hW1 hWB0 hWB1 (X k) (Y k) (hX k hk) (hY k hk)) (by positivity)
    _ = _ := by ring

theorem gaussianPhysicalFamily_remote_polynomial_oai (V : SchwartzMap ℝ ℂ)
    (hV : HasCompactSupport (V:ℝ→ℂ)) (N : ℕ)
    (a0 b0 a1 b1 B0 B1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1) (hB0 : 0≤B0) (hB1 : 0≤B1) :
    ∃K : ℝ,0<K ∧ ∀{α ι : Type*} [Fintype ι],
      ∀η : HeckeFamily.Character,∀S : Finset Id,∀hS : ∀P∈S,P.IsMaximal,
      ∀W0 W1 : ℝ→ℂ,HasCompactSupport W0→HasCompactSupport W1→
      Function.support W0⊆Set.Icc a0 b0 → Function.support W1⊆Set.Icc a1 b1 →
      (∀x,‖W0 x‖≤B0) → (∀x,‖W1 x‖≤B1) →
      ∀F : Finset α,∀a : α→ℂ,∀D : α→Id,∀X Y : α→ℝ,
      (∀k∈F,1≤X k)→(∀k∈F,1≤Y k)→∀W : ι→ℝ→ℂ,∀q : α→ι→ℝ,
      ∀Z A : ℝ,0<Z→1≤A→
      Summable (fun j : ℕ=>if (2:ℝ)^j/Z≤A⁻¹ ∨ A≤(2:ℝ)^j/Z then
        ‖gaussianPhysicalFamilyIntegral η (calibrationForSet S hS) W0 W1 F a D X Y W q V hV ((2:ℝ)^j) Z‖ else 0) ∧
      (∑'j : ℕ,if (2:ℝ)^j/Z≤A⁻¹ ∨ A≤(2:ℝ)^j/Z then
        ‖gaussianPhysicalFamilyIntegral η (calibrationForSet S hS) W0 W1 F a D X Y W q V hV ((2:ℝ)^j) Z‖ else 0)≤
          K*gaussianPhysicalScaleMass (calibrationForSet S hS) F a X Y W q*Z^2/A^N := by
  obtain ⟨C0,hC0,hremote⟩ := gaussianPhysicalFamily_remote V hV N
  obtain ⟨C1,hC1,hmass⟩ := gaussianPhysicalFamily_mass_bound a0 b0 a1 b1 B0 B1 ha0 ha1 hB0 hB1
  refine ⟨C0*C1,mul_pos hC0 hC1,?_⟩
  intro α ι _ η S hS W0 W1 hW0c hW1c hW0 hW1 hWB0 hWB1 F a D X Y hX hY W q Z A hZ hA
  have hh := hremote η (calibrationForSet S hS) W0 W1 hW0c hW1c F a D X Y
    (fun k hk=>lt_of_lt_of_le zero_lt_one (hX k hk)) (fun k hk=>lt_of_lt_of_le zero_lt_one (hY k hk)) W q Z A hZ hA
  refine ⟨hh.1,hh.2.trans ?_⟩
  have hm := hmass S hS W0 W1 hW1c hW0 hW1 hWB0 hWB1 F a X Y hX hY W q
  calc
    _ ≤ C0*(C1*gaussianPhysicalScaleMass (calibrationForSet S hS) F a X Y W q)*Z^2/A^N := by gcongr
    _ = _ := by ring

end SevenEighths.ProbePhysical
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.SevenEighths.ProbePhysical.gaussianPhysicalFamily_remote_polynomial_oai.{u_1, u_2} := @OAI.SevenEighths.ProbePhysical.gaussianPhysicalFamily_remote_polynomial_oai.{u_1, u_2}
