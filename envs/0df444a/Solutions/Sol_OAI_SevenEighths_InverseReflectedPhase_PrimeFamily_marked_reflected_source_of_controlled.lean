-- Prove2me | solution 1 for OAI.SevenEighths.InverseReflectedPhase.PrimeFamily.marked_reflected_source_of_controlled
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T03:33:58.995455+00:00
-- url     : https://prove2.me/submissions/0b421c80-62e6-419b-8a27-25b608827c54

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIHecke78B024
import Theorems.Thm_OAI_CubicEisenstein_completedT_canonical_smoothed_reflection
import Theorems.Thm_OAI_SevenEighths_InverseMoment_cusp_kernel_sum_congr
import Theorems.Thm_OAI_SevenEighths_InverseMoment_mixed_smoothed_eq_reflected

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

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reciprocity.RamifiedSymbol
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

namespace CubicRamified
open ActualEisensteinCubic CubicJacobiGlobal CompletedGauss

theorem symbol_traceLambda_congr_mod_nine (x y : O)
    (hx : lambda ^ 2 ∣ x-1) (hy : lambda ^ 2 ∣ y-1) (hxy : (9 : O) ∣ x-y) :
    symbol traceLambda x = symbol traceLambda y := by
  rw [symbol_traceLambda_eq_linearRay x hx, symbol_traceLambda_eq_linearRay y hy]
  exact linearRay_congr_mod_nine 0 (-1) x y hx hy hxy

end CubicRamified

open scoped BigOperators Classical SchwartzMap

open scoped BigOperators Classical SchwartzMap

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

namespace CubicEisenstein

section
open scoped BigOperators Classical
open MeasureTheory
open Finset AddChar MulChar EisensteinEmbedding

section
local notation "Eis" => ActualEisensteinCubic.O

lemma finiteAdditiveFourier_inversion {R : Type*} [CommRing R] [Fintype R]
    (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) (φ : R→ℂ) (x : R) :
    (∑h,finiteAdditiveFourierCoeff ψ φ h*ψ (h*x))=φ x := by
  have hN : (Fintype.card R:ℂ)≠0:=by exact_mod_cast Fintype.card_ne_zero
  calc
    _ = (∑h,∑y,φ y*ψ (-h*y)*ψ (h*x))/(Fintype.card R:ℂ) := by
      simp only [finiteAdditiveFourierCoeff,div_mul_eq_mul_div,Finset.sum_mul,Finset.sum_div]
    _ = (∑y,φ y*∑h,ψ (h*(x-y)))/(Fintype.card R:ℂ) := by
      rw [Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro y hy
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h hh
      rw [mul_assoc,←AddChar.map_add_eq_mul]
      congr 2
      ring
    _ = (∑y,φ y*(if x-y=0 then (Fintype.card R:ℂ) else 0))/(Fintype.card R:ℂ) := by
      simp only [AddChar.sum_mulShift _ hψ,apply_ite,Nat.cast_zero]
    _ = φ x := by
      have he : (∑y,φ y*(if x-y=0 then (Fintype.card R:ℂ) else 0))=
          φ x*(Fintype.card R:ℂ) := by
        simp [sub_eq_zero]
      rw [he,mul_div_cancel_right₀ _ hN]

lemma thetaFourierTranslation_phase (c : Eis) (hc : c≠0)
    (h : Eis⧸Ideal.span {c}) (x : Eis) :
    ShortDraftTrace.breveE (-cuspFrequency x*thetaFourierTranslation c h)=
      quotientTrace c hc (h*Ideal.Quotient.mk _ x) := by
  have hm : h*Ideal.Quotient.mk _ x=Ideal.Quotient.mk _ (Quotient.out h*x) := by
    rw [map_mul,Ideal.Quotient.mk_out]
  rw [hm]
  simp only [quotientTrace,ConcreteTraceCRT.eisTraceModChar,IdealGaussCRT.traceModChar_mk]
  congr 1
  unfold cuspFrequency thetaFourierTranslation
  rw [map_mul]
  have hc0:=ConcreteTraceCRT.eisEmbedding_ne_zero hc
  have hl:=ConcreteTraceCRT.eisLam_ne_zero
  field_simp
  linear_combination -(ConcreteTraceCRT.eisEmbedding x*
    ConcreteTraceCRT.eisEmbedding (Quotient.out h))*TraceLambdaPhase.eisLam_sq

lemma thetaFourierTranslation_inversion (c : Eis) (hc : c≠0)
    [Fintype (Eis⧸Ideal.span {c})] (φ : (Eis⧸Ideal.span {c})→ℂ) (x : Eis) :
    (∑h,finiteAdditiveFourierCoeff (quotientTrace c hc) φ h*
      ShortDraftTrace.breveE (-cuspFrequency x*thetaFourierTranslation c h))=
      φ (Ideal.Quotient.mk _ x) := by
  simp only [thetaFourierTranslation_phase c hc]
  exact finiteAdditiveFourier_inversion (quotientTrace c hc)
    (GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive c hc) φ _

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

lemma fixedThetaTwist_primary (Ψ : Eis→*ℂ) (x : Eis) (hx : lambda^2∣x-1) :
    fixedThetaTwist Ψ x=eisEmbedding (symbol ramifiedTraceLambda x)*Ψ x := by
  simp only [fixedThetaTwist,if_pos hx]

lemma fixedThetaTwist_not_primary (Ψ : Eis→*ℂ) (x : Eis) (hx : ¬lambda^2∣x-1) :
    fixedThetaTwist Ψ x=0 := by
  simp only [fixedThetaTwist,if_neg hx]

theorem fixedThetaTwist_periodic (Ψ : Eis→*ℂ) (Q : Ideal Eis)
    (hΨ : CanonicalCoefficientClass.FactorsModulo Q Ψ) (x y : Eis)
    (hxy : x-y∈Ideal.span {(9:Eis)}*Q) : fixedThetaTwist Ψ x=fixedThetaTwist Ψ y := by
  have h9 : (9:Eis)∣x-y := Ideal.mem_span_singleton.mp (Ideal.mul_le_left hxy)
  have hd : lambda^2∣x-y := lambda_sq_dvd_three.trans ((show (3:Eis)∣9 from ⟨3,by norm_num⟩).trans h9)
  have hp : lambda^2∣x-1 ↔ lambda^2∣y-1 := by
    constructor
    · intro hx
      convert (preTransparency := .instances) dvd_sub hx hd using 1 ; ring
    · intro hy
      convert (preTransparency := .instances) dvd_add hd hy using 1 ; ring
  by_cases hx : lambda^2∣x-1
  · have hy := hp.mp hx
    rw [fixedThetaTwist_primary Ψ x hx,fixedThetaTwist_primary Ψ y hy,
      hΨ x y (Ideal.mul_le_right hxy)]
    congr 2
    exact CubicRamified.symbol_traceLambda_congr_mod_nine x y hx hy h9
  · rw [fixedThetaTwist_not_primary Ψ x hx,
      fixedThetaTwist_not_primary Ψ y (fun hy=>hx (hp.mpr hy))]

lemma fixedThetaQuotient_mk (Ψ : Eis→*ℂ) (Q : Ideal Eis)
    (hΨ : CanonicalCoefficientClass.FactorsModulo Q Ψ) (c : Eis)
    (hc : Ideal.span {c}≤Ideal.span {(9:Eis)}*Q) (x : Eis) :
    fixedThetaQuotient Ψ c (Ideal.Quotient.mk _ x)=fixedThetaTwist Ψ x := by
  apply fixedThetaTwist_periodic Ψ Q hΨ
  exact hc (Ideal.Quotient.eq.mp (Ideal.Quotient.mk_out (Ideal.Quotient.mk (Ideal.span {c}) x)))

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

namespace CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

lemma cubeWeight_zero_of_primaryGenerator_zero (Ψ:Eis→*ℂ) (I:Ideal Eis)
    (h:primaryGenerator I=0) : cubeWeight Ψ I=0 := by
  simp [cubeWeight,h,FiniteGaussPhase.angularFactor]

end CompletedGauss

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

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
open scoped BigOperators Classical MatrixGroups
open MeasureTheory
open Finset AddChar MulChar EisensteinEmbedding

open CubicKubota EisensteinCuspModThree ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma rationalSourceCusp_point (a c : Eis) (hc : c≠0) :
    (rationalSourceCusp a c hc).point=eisEmbedding a/eisEmbedding c :=
  (exists_sourceCuspDatum a c hc).choose_spec

lemma finiteTwistCusp_point (c : Eis) (hc : c≠0) (h : Eis⧸Ideal.span {c}) :
    (finiteTwistCusp c hc h).point=thetaFourierTranslation c h := by
  rw [finiteTwistCusp,rationalSourceCusp_point,thetaFourierTranslation,TraceLambdaPhase.eisLam_sq]
  simp only [map_mul,map_neg,map_ofNat]

end

open scoped BigOperators Classical
open MeasureTheory
open Finset AddChar MulChar EisensteinEmbedding

local notation "Eis" => ActualEisensteinCubic.O

end CubicEisenstein

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.FixedCuspArrays
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
open scoped Classical MatrixGroups Matrix

open CubicKubota EisensteinCuspModThree ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma upper_right_removed_top (M T:SL(2,Eis)) (hT:T 1 0=0) :
    (M*T⁻¹) 0 0=M 0 0*T 1 1 := by
  simp [Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two,Matrix.mul_apply,Fin.sum_univ_two,hT]

namespace FixedCuspShape
variable {H:SL(2,Eis)} (s:FixedCuspShape H) (g:levelTwo)

lemma datum_matrix (h:((g:SL(2,Eis))*H) 1 0≠0) :
    (s.datum g h).matrix=integralComplexMatrix ((g:SL(2,Eis))*H*s.upper⁻¹) := by
  rw [s.removed_eq g,map_mul]
  rfl

lemma datum_point (h:((g:SL(2,Eis))*H) 1 0≠0) :
    (s.datum g h).point=
      eisEmbedding (((g:SL(2,Eis))*H) 0 0)/eisEmbedding (((g:SL(2,Eis))*H) 1 0) := by
  rw [SourceCuspDatum.point,s.datum_matrix]
  rw [integralComplexMatrix_apply,integralComplexMatrix_apply,
    upper_right_removed_top _ _ s.lower_zero,upper_right_removed_bottom _ _ s.lower_zero]
  simp only [map_mul]
  exact mul_div_mul_right _ _ (eisEmbedding_ne_zero s.lower_unit.ne_zero)

end FixedCuspShape
end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups ContDiff

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.ChineseRemainder.FrequencyLifts
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

namespace ShortDraftCRT
open ActualEisensteinCubic FiniteGaussPhase ConcreteTraceCRT CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι]

theorem finiteCrossNumerator_fraction (a c l:Eis) (p h:ι→Eis)
    (hc:c≠0) (hp:∀i,p i≠0) :
    eisEmbedding (finiteCrossNumerator a c l p h)/eisEmbedding (c*∏i,p i)=
      eisEmbedding a/eisEmbedding c+eisEmbedding l^2*
        ∑i,eisEmbedding (h i)/eisEmbedding (p i) := by
  have hR:(∏i,p i)≠0:=Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)
  have hcC:=eisEmbedding_ne_zero hc
  have hRC:=eisEmbedding_ne_zero hR
  have hs:eisEmbedding (∑i,h i*cofactor p i)/eisEmbedding (∏i,p i)=
      ∑i,eisEmbedding (h i)/eisEmbedding (p i) := by
    rw [map_sum,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    have hpi:=eisEmbedding_ne_zero (hp i)
    have hr:eisEmbedding (p i)*eisEmbedding (cofactor p i)=eisEmbedding (∏i,p i) := by
      rw [←map_mul,prime_mul_cofactor]
    rw [map_mul]
    apply (div_eq_div_iff hRC hpi).mpr
    linear_combination eisEmbedding (h i)*hr
  simp only [finiteCrossNumerator,map_add,map_mul,map_pow]
  rw [←hs]
  field_simp [hcC,hRC]

end ShortDraftCRT

open scoped BigOperators Classical

namespace FixedRayActiveSet

lemma sum_nonzero_ite {F : Type*} [Field F] [Fintype F] (f:F→ℂ) :
    (∑x:F,if x≠0 then f x else 0)=∑u:Fˣ,f (u:F) := by
  calc
    _ = ∑x∈(Finset.univ:Finset F).filter (fun x=>x≠0),f x := by rw [Finset.sum_filter]
    _ = ∑x:{x:F//x≠0},f x := by
      apply Finset.sum_subtype
      intro x
      simp
    _ = _ := (Equiv.sum_comp unitsEquivNeZero (fun x:{x:F//x≠0}=>f x)).symm

theorem sum_active_stratum {ι : Type*} [Fintype ι]
    (F : ι→Type*) [∀i,Field (F i)] [∀i,Fintype (F i)]
    (A:Finset ι) (f:∀i,F i→ℂ) :
    (∑h∈activeStratum F A,∏i,f i (h i))=
      (∏i∈A,∑u:(F i)ˣ,f i (u:F i))*
        (∏i∈(Finset.univ:Finset ι)\A,f i 0) := by
  classical
  let g:=fun i (x:F i)=>if (x≠0↔i∈A) then f i x else 0
  have hs : (∑h∈activeStratum F A,∏i,f i (h i))=
      ∏i,∑x:F i,g i x := by
    rw [activeStratum,Finset.sum_filter]
    calc
      _ = ∑h:∀i,F i,∏i,g i (h i) := by
        apply Finset.sum_congr rfl
        intro h hh
        exact (Fintype.prod_ite_zero (p:=fun i=>h i≠0↔i∈A) (f:=fun i=>f i (h i))).symm
      _ = _ := (Fintype.prod_sum g).symm
  have hg (i:ι) : (∑x:F i,g i x)=if i∈A then ∑u:(F i)ˣ,f i (u:F i) else f i 0 := by
    by_cases hi:i∈A
    · simpa only [g,hi,iff_true,ite_true] using sum_nonzero_ite (f i)
    · simp [g,hi]
  rw [hs]
  simp only [hg,Finset.prod_ite]
  have ha : (Finset.univ:Finset ι).filter (fun i=>i∈A)=A := by ext i;simp
  have hn : (Finset.univ:Finset ι).filter (fun i=>i∉A)=(Finset.univ:Finset ι)\A := by ext i;simp
  rw [ha,hn]

theorem sum_by_active_strata {ι : Type*} [Fintype ι]
    (F : ι→Type*) [∀i,Field (F i)] [∀i,Fintype (F i)]
    (weight:(∀i,F i)→ℂ) :
    (∑h:∀i,F i,weight h)=
      ∑A∈(Finset.univ:Finset ι).powerset,∑h∈activeStratum F A,weight h := by
  classical
  symm
  simp only [activeStratum,Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h hh
  let A:Finset ι:=Finset.univ.filter (fun i=>h i≠0)
  have he : ∀i,h i≠0↔i∈A := by intro i;simp [A]
  rw [Finset.sum_eq_single A]
  · simp only [he,implies_true,ite_true]
  · intro B hB hBA
    have hbad : ¬(∀i,h i≠0↔i∈B) := by
      intro hgood
      apply hBA
      ext i
      simpa only [A,Finset.mem_filter,Finset.mem_univ,true_and] using (hgood i).symm
    simp only [hbad,ite_false]
  · intro hnot
    exact (hnot (Finset.mem_powerset.mpr (Finset.filter_subset _ _))).elim

end FixedRayActiveSet

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

namespace CubicEisenstein

section
open scoped BigOperators Classical ContDiff MatrixGroups Matrix

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss CompletedDyadic CubicKubota
open CubicJacobiGlobal ShortDraftCusp ShortDraftCRT FiniteGaussPhase LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O
namespace ControlledStratumArithmetic
variable {ι:Type*} [Fintype ι] {p:ι→Eis} {N a0 c0:Eis} {mode:Bool}

lemma datum_point (D:ControlledStratumArithmetic p N a0 c0 mode)
    (hN:(9:Eis)*c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1)
    (s:FixedCuspShape (fixedCusp a0 c0 mode))
    (hp:∀i,p i≠0) (hc0:c0≠0) (v:∀i,(Eis⧸Ideal.span {p i})ˣ) :
    (D.datum hN hr hbase s hp hc0 v).point=eisEmbedding a0/eisEmbedding c0+
      eisLam^2*∑i,eisEmbedding (D.lift v i)/eisEmbedding (p i) := by
  rw [datum,s.datum_point,D.sourceGamma_mul,D.numerator,D.denominator]
  simpa only [ramifiedEmbedding_traceLambda] using
    finiteCrossNumerator_fraction a0 c0 ramifiedTraceLambda p (D.lift v) hc0 hp

end ControlledStratumArithmetic

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff MatrixGroups

open CompletedGauss ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

end CubicEisenstein

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.FixedThetaTwists
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
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion
local notation "Eis" => ActualEisensteinCubic.O

lemma fixedThetaTwist_mul (φ χ:Eis→*ℂ) (n:Eis) :
    fixedThetaTwist (φ*χ) n=fixedThetaTwist φ n*χ n := by
  by_cases hn:lambda^2∣n-1
  · rw [fixedThetaTwist_primary _ n hn,fixedThetaTwist_primary _ n hn,MonoidHom.mul_apply]
    ring
  · rw [fixedThetaTwist_not_primary _ n hn,fixedThetaTwist_not_primary _ n hn,zero_mul]

end CubicEisenstein

open scoped Classical BigOperators ContDiff

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.RowCompletion.ControlledPrimeStrata
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

namespace FixedRayActiveSet

theorem fourier_inversion_by_active_set {ι:Type*} [Fintype ι]
    (F:ι→Type*) [∀i,Field (F i)] [∀i,Fintype (F i)]
    (ψ:∀i,AddChar (F i) ℂ) (hψ:∀i,(ψ i).IsPrimitive)
    (φ:∀i,F i→ℂ) (x:∀i,F i) :
    (∏i,φ i (x i))=
      ∑A∈(Finset.univ:Finset ι).powerset,
        (∏i∈(Finset.univ:Finset ι)\A,CubicEisenstein.finiteAdditiveFourierCoeff (ψ i) (φ i) 0)*
        (∑v:∀i:A,(F i.val)ˣ,
          (∏i:A,CubicEisenstein.finiteAdditiveFourierCoeff (ψ i.val) (φ i.val) (v i)) *
            (∏i:A,ψ i.val ((v i:F i.val)*x i.val))) := by
  let f:=fun i (a:F i)=>CubicEisenstein.finiteAdditiveFourierCoeff (ψ i) (φ i) a*ψ i (a*x i)
  have he: (∑h:∀i,F i,∏i,f i (h i))=∏i,φ i (x i):=by
    rw [←Fintype.prod_sum]
    apply Finset.prod_congr rfl
    intro i hi
    exact CubicEisenstein.finiteAdditiveFourier_inversion (ψ i) (hψ i) (φ i) (x i)
  rw [←he,sum_by_active_strata]
  apply Finset.sum_congr rfl
  intro A hA
  rw [sum_active_stratum]
  have hz:(∏i∈(Finset.univ:Finset ι)\A,f i 0)=
      ∏i∈(Finset.univ:Finset ι)\A,CubicEisenstein.finiteAdditiveFourierCoeff (ψ i) (φ i) 0:=by
    apply Finset.prod_congr rfl
    intro i hi
    simp only [f,zero_mul,AddChar.map_zero_eq_one,mul_one]
  rw [hz,mul_comm]
  congr 1
  rw [show (∑v:∀i:A,(F i.val)ˣ,
      (∏i:A,CubicEisenstein.finiteAdditiveFourierCoeff (ψ i.val) (φ i.val) (v i)) *
        (∏i:A,ψ i.val ((v i:F i.val)*x i.val)))=
      ∑v:∀i:A,(F i.val)ˣ,∏i:A,f i.val (v i) by
    apply Finset.sum_congr rfl
    intro v hv
    exact (Finset.prod_mul_distrib).symm]
  calc
    _=∏i:A,∑u:(F i.val)ˣ,f i.val (u:F i.val):=
      (Finset.prod_coe_sort A (fun i=>∑u:(F i)ˣ,f i (u:F i))).symm
    _=_:=Fintype.prod_sum (fun (i:A) (u:(F i.val)ˣ)=>f i.val (u:F i.val))

end FixedRayActiveSet

open scoped BigOperators Classical ContDiff

namespace CubicEisenstein

open scoped BigOperators Classical MatrixGroups

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss CubicKubota
local notation "Eis" => ActualEisensteinCubic.O

lemma theta_lifted_phase (c:Eis) (hc:c≠0) (lift n:Eis) :
    ShortDraftTrace.breveE (-cuspFrequency n*(eisLam^2*eisEmbedding lift/eisEmbedding c))=
      quotientTrace c hc (Ideal.Quotient.mk _ lift*Ideal.Quotient.mk _ n) := by
  rw [←map_mul]
  simp only [quotientTrace,eisTraceModChar,IdealGaussCRT.traceModChar_mk]
  congr 1
  unfold cuspFrequency
  rw [map_mul]
  have hc0:=eisEmbedding_ne_zero hc
  have hl:=eisLam_ne_zero
  field_simp
  linear_combination -(eisEmbedding n*eisEmbedding lift)*TraceLambdaPhase.eisLam_sq

lemma breveE_finset_sum {ι:Type*} (s:Finset ι) (z:ι→ℂ) :
    ShortDraftTrace.breveE (∑i∈s,z i)=∏i∈s,ShortDraftTrace.breveE (z i) := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty,Finset.prod_empty,AddChar.map_zero_eq_one]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi,Finset.prod_insert hi,AddChar.map_add_eq_mul,ih]

lemma ControlledStratumArithmetic.datum_fourier_phase {ι:Type*} [Fintype ι]
    {p:ι→Eis} {N a0 c0:Eis} {mode:Bool}
    (D:ControlledStratumArithmetic p N a0 c0 mode)
    (hN:(9:Eis)*c0∣N) (hr:lambda^2∣(∏i,p i)-1)
    (hbase:if mode then lambda^2∣a0-1 else lambda^2∣c0-1)
    (s:FixedCuspShape (ControlledStratumArithmetic.fixedCusp a0 c0 mode))
    (hp:∀i,p i≠0) (hc0:c0≠0) (v:∀i,(Eis⧸Ideal.span {p i})ˣ) (n:Eis) :
    ShortDraftTrace.breveE (-cuspFrequency n*(D.datum hN hr hbase s hp hc0 v).point)=
      ShortDraftTrace.breveE (-cuspFrequency n*(eisEmbedding a0/eisEmbedding c0))*
        ∏i,quotientTrace (p i) (hp i) ((v i:Eis⧸Ideal.span {p i})*Ideal.Quotient.mk _ n) := by
  rw [D.datum_point]
  have he:-cuspFrequency n*(eisEmbedding a0/eisEmbedding c0+
      eisLam^2*∑i,eisEmbedding (D.lift v i)/eisEmbedding (p i))=
      -cuspFrequency n*(eisEmbedding a0/eisEmbedding c0)+
        ∑i,-cuspFrequency n*(eisLam^2*eisEmbedding (D.lift v i)/eisEmbedding (p i)):=by
    simp only [Finset.mul_sum,neg_mul,mul_add]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [he,AddChar.map_add_eq_mul,breveE_finset_sum]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  rw [theta_lifted_phase,D.lift_residue]

end CubicEisenstein

open scoped BigOperators Classical ContDiff

open scoped BigOperators Classical

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

theorem markedCompletedT_const_mul (Ψ : Eis →* ℂ) (W : ℝ → ℂ) (X : ℝ)
    (c : ℂ) (d : Ideal Eis → ℂ) :
    markedCompletedT Ψ W X (fun A => c * d A) = c * markedCompletedT Ψ W X d := by
  simp only [markedCompletedT, mul_left_comm _ c, tsum_mul_left]

theorem markedCompletedT_finset_sum {ι : Type*} (s : Finset ι)
    (Ψ : Eis →* ℂ) (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (X : ℝ) (hX : 0 < X) (d : ι → Ideal Eis → ℂ) :
    markedCompletedT Ψ W X (fun A => ∑ i ∈ s, d i A) =
      ∑ i ∈ s, markedCompletedT Ψ W X (d i) := by
  simp only [markedCompletedT_eq_tsum Ψ W hW X hX, Finset.mul_sum]
  exact Summable.tsum_finsetSum (fun i _ => markedCompletedT_summable Ψ W hW X hX (d i))

end

end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.MarkedFourier
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CompletedGauss CanonicalRowCompletion
open CubicEisenstein hiding summand
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem completed_summand_primary_support (Ψ : Eis →* ℂ) (W : ℝ → ℂ)
    (X : ℝ) (I J : Ideal Eis) (h : summand Ψ W X I J ≠ 0) :
    primaryGenerator (I * J ^ 3) ≠ 0 := by
  have hI : primaryGenerator I ≠ 0 := by
    intro hz
    apply h
    simp [summand, columnWeight, squarefreeGaussCoefficient, hz]
  have hJ : primaryGenerator J ≠ 0 := by
    intro hz
    apply h
    rw [summand, cubeWeight_zero_of_primaryGenerator_zero Ψ J hz]
    ring
  rw [primaryGenerator_mul, show primaryGenerator (J ^ 3) = primaryGenerator J ^ 3 from
    map_pow primaryGeneratorHom J 3]
  exact mul_ne_zero hI (pow_ne_zero _ hJ)

theorem markedCompletedT_congr_primary (Ψ : Eis →* ℂ) (W : ℝ → ℂ) (X : ℝ)
    (d e : Ideal Eis → ℂ) (h : ∀ A, primaryGenerator A ≠ 0 → d A = e A) :
    markedCompletedT Ψ W X d = markedCompletedT Ψ W X e := by
  apply tsum_congr
  intro I
  apply tsum_congr
  intro J
  by_cases hz : summand Ψ W X I J = 0
  · simp only [hz, zero_mul]
  · rw [h (I * J ^ 3) (completed_summand_primary_support Ψ W X I J hz)]

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.MarkedTwists
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CompletedGauss CanonicalRowCompletion
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem markedCompletedT_monoid (Ψ φ : Eis →* ℂ) (W : ℝ → ℂ) (X : ℝ) :
    markedCompletedT Ψ W X (fun A => φ (primaryGenerator A)) = completedT (φ * Ψ) W X := by
  unfold markedCompletedT completedT
  apply tsum_congr
  intro I
  apply tsum_congr
  intro J
  change summand Ψ W X I J * φ (primaryGenerator (I * J ^ 3)) = _
  rw [summand_mul_fixed_twist, primaryGenerator_mul,
    show primaryGenerator (J ^ 3) = primaryGenerator J ^ 3 from map_pow primaryGeneratorHom J 3]
  exact mul_comm _ _

theorem whole_prime_mark_eq_mask_complement (p : Eis) (hp : Prime p)
    (A : Ideal Eis) (hA : primaryGenerator A ≠ 0) :
    (if Ideal.span {p} ∣ A then (1 : ℂ) else 0) =
      1 - coprimalityMask p (primaryGenerator A) := by
  have hd : Ideal.span {p} ∣ A ↔ p ∣ primaryGenerator A := by
    calc
      _ ↔ A ≤ Ideal.span {p} := Ideal.dvd_iff_le
      _ ↔ Ideal.span {primaryGenerator A} ≤ Ideal.span {p} := by
        rw [(primaryGenerator_spec A hA).1]
      _ ↔ _ := by rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_span_singleton]
  change (if Ideal.span {p} ∣ A then (1 : ℂ) else 0) =
    1 - (if IsCoprime p (primaryGenerator A) then 1 else 0)
  rw [hp.coprime_iff_not_dvd]
  by_cases h : p ∣ primaryGenerator A <;> simp [hd, h]

theorem markedCompletedT_prime_product_twists {ι : Type*}
    (S : Finset ι) (p : ι → Eis) (hp : ∀ i ∈ S, Prime (p i))
    (Ψ : Eis →* ℂ) (W : ℝ → ℂ) (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) :
    markedCompletedT Ψ W X
      (fun A => ∏ i ∈ S, if Ideal.span {p i} ∣ A then 1 else 0) =
      ∑ T ∈ S.powerset, (-1 : ℂ) ^ T.card *
        completedT ((∏ i ∈ T, coprimalityMask (p i)) * Ψ) W X := by
  have he : markedCompletedT Ψ W X
      (fun A => ∏ i ∈ S, if Ideal.span {p i} ∣ A then 1 else 0) =
      markedCompletedT Ψ W X (fun A =>
        ∑ T ∈ S.powerset, (-1 : ℂ) ^ T.card *
          (∏ i ∈ T, coprimalityMask (p i)) (primaryGenerator A)) := by
    apply markedCompletedT_congr_primary
    intro A hA
    calc
      _ = ∏ i ∈ S, (1 - coprimalityMask (p i) (primaryGenerator A)) := by
        apply Finset.prod_congr rfl
        intro i hi
        exact whole_prime_mark_eq_mask_complement (p i) (hp i hi) A hA
      _ = _ := by
        rw [Finset.prod_sub]
        simp
  rw [he, markedCompletedT_finset_sum S.powerset Ψ W hW X hX]
  apply Finset.sum_congr rfl
  intro T hT
  rw [markedCompletedT_const_mul, markedCompletedT_monoid]

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.MarkedReflection
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical ContDiff
open CompletedGauss CanonicalRowCompletion CubicEisenstein
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

variable {ι : Type*}

theorem markTwist_norm (p : ι → Eis) (T : Finset ι) (x : Eis) : ‖markTwist p T x‖ ≤ 1 := by
  simp only [markTwist, MonoidHom.finsetProd_apply, norm_prod]
  exact Finset.prod_le_one (fun i hi => norm_nonneg _) (fun i hi => coprimalityMask_norm _ _)

theorem markTwist_periodic (p : ι → Eis) (S T : Finset ι) (hTS : T ⊆ S) :
    CanonicalCoefficientClass.FactorsModulo (Ideal.span {∏ i ∈ S, p i}) (markTwist p T) := by
  intro x y hxy
  simp only [markTwist, MonoidHom.finsetProd_apply]
  apply Finset.prod_congr rfl
  intro i hi
  apply coprimalityMask_periodic (p i) x y
  apply Ideal.mem_span_singleton.mpr
  exact (Finset.dvd_prod_of_mem p (hTS hi)).trans (Ideal.mem_span_singleton.mp hxy)

theorem markedThetaQuotient_twists (p : ι → Eis) (S : Finset ι)
    (hp : ∀ i ∈ S, Prime (p i)) (Ψ : Eis →* ℂ) (c : Eis)
    (x : Eis ⧸ Ideal.span {c}) :
    markedThetaQuotient p S Ψ c x =
      ∑ T ∈ S.powerset, (-1 : ℂ) ^ T.card * fixedThetaQuotient (markTwist p T * Ψ) c x := by
  have hmark (i : ι) (hi : i ∈ S) :
      (if p i ∣ Quotient.out x then (1 : ℂ) else 0) =
        1 - coprimalityMask (p i) (Quotient.out x) := by
    change (if p i ∣ Quotient.out x then (1 : ℂ) else 0) =
      1 - (if IsCoprime (p i) (Quotient.out x) then 1 else 0)
    rw [(hp i hi).coprime_iff_not_dvd]
    by_cases h : p i ∣ Quotient.out x <;> simp [h]
  unfold markedThetaQuotient
  rw [Finset.prod_congr rfl hmark, Finset.prod_sub]
  simp only [Finset.prod_const_one, mul_one, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T hT
  rw [show markTwist p T * Ψ = Ψ * markTwist p T from mul_comm _ _]
  simp only [fixedThetaQuotient, fixedThetaTwist_mul, markTwist, MonoidHom.finsetProd_apply]
  ring

theorem markedCompletedT_canonical_reflection (p : ι → Eis) (S : Finset ι)
    (hp : ∀ i ∈ S, Prime (p i))
    (Ψ : Eis →* ℂ) (hΨ : ∀ x, ‖Ψ x‖ ≤ 1)
    (Q : Ideal Eis) (hperiod : CanonicalCoefficientClass.FactorsModulo Q Ψ)
    (c : Eis) (hc : c ≠ 0) [Fintype (Eis ⧸ Ideal.span {c})]
    (hcQ : Ideal.span {c} ≤ Ideal.span {(9 : Eis)} * (Q * Ideal.span {∏ i ∈ S, p i}))
    (W : ℝ → ℂ) (hWcompact : HasCompactSupport W)
    (v0 v1 : ℝ) (hv0 : 0 < v0) (hWs : Function.support W ⊆ Set.Icc v0 v1)
    (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0 < X) :
    markedCompletedT Ψ W X (fun A => ∏ i ∈ S, if Ideal.span {p i} ∣ A then 1 else 0) =
      thetaDerivativeScalar⁻¹ * ∑ h : Eis ⧸ Ideal.span {c},
        finiteAdditiveFourierCoeff (quotientTrace c hc) (markedThetaQuotient p S Ψ c) h *
          (finiteTwistCusp c hc h).smoothedKernel W X := by
  have hnorm (T : Finset ι) : ∀ x, ‖(markTwist p T * Ψ) x‖ ≤ 1 := by
    intro x
    rw [MonoidHom.mul_apply, norm_mul]
    exact (mul_le_mul_of_nonneg_right (markTwist_norm p T x) (norm_nonneg _)).trans
      ((one_mul _).le.trans (hΨ x))
  have hper (T : Finset ι) (hT : T ∈ S.powerset) :
      CanonicalCoefficientClass.FactorsModulo (Q * Ideal.span {∏ i ∈ S, p i})
        (markTwist p T * Ψ) := by
    intro x y hxy
    simp only [MonoidHom.mul_apply]
    rw [markTwist_periodic p S T (Finset.mem_powerset.mp hT) x y (Ideal.mul_le_right hxy),
      hperiod x y (Ideal.mul_le_left hxy)]
  have hcoeff (h : Eis ⧸ Ideal.span {c}) :
      finiteAdditiveFourierCoeff (quotientTrace c hc) (markedThetaQuotient p S Ψ c) h =
        ∑ T ∈ S.powerset, (-1 : ℂ) ^ T.card *
          finiteAdditiveFourierCoeff (quotientTrace c hc)
            (fixedThetaQuotient (markTwist p T * Ψ) c) h := by
    unfold finiteAdditiveFourierCoeff
    simp_rw [markedThetaQuotient_twists p S hp Ψ c]
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    simp only [Finset.sum_div, Finset.mul_sum, mul_div_assoc, mul_assoc]
  rw [markedCompletedT_prime_product_twists S p hp Ψ W hWcompact X hX]
  change (∑ T ∈ S.powerset, (-1 : ℂ) ^ T.card * completedT (markTwist p T * Ψ) W X) = _
  calc
    _ = ∑ T ∈ S.powerset, (-1 : ℂ) ^ T.card * (thetaDerivativeScalar⁻¹ *
        ∑ h : Eis ⧸ Ideal.span {c}, finiteAdditiveFourierCoeff (quotientTrace c hc)
          (fixedThetaQuotient (markTwist p T * Ψ) c) h *
            (finiteTwistCusp c hc h).smoothedKernel W X) := by
      apply Finset.sum_congr rfl
      intro T hT
      rw [completedT_canonical_smoothed_reflection _ (hnorm T) _ (hper T hT)
        c hc hcQ W v0 v1 hv0 hWs hW X hX]
    _ = _ := by
      simp_rw [hcoeff]
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro h hh
      apply Finset.sum_congr rfl
      intro T hT
      ring

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.CuspCongruence
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical ContDiff
open MeasureTheory CompletedGauss CubicEisenstein
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem markedCompletedT_of_cusp_multiplier {ι κ : Type*} [Fintype κ]
    (p : ι → Eis) (S : Finset ι) (hp : ∀ i ∈ S, Prime (p i))
    (Ψ : Eis →* ℂ) (hΨ : ∀ x, ‖Ψ x‖ ≤ 1)
    (Q : Ideal Eis) (hperiod : CanonicalCoefficientClass.FactorsModulo Q Ψ)
    (c : Eis) (hc : c ≠ 0) [Fintype (Eis ⧸ Ideal.span {c})]
    (hcQ : Ideal.span {c} ≤ Ideal.span {(9 : Eis)} * (Q * Ideal.span {∏ i ∈ S, p i}))
    (d : κ → SourceCuspDatum) (w : κ → ℂ)
    (hmult : ∀ n : Eis, (∑ k, w k * ShortDraftTrace.breveE (-cuspFrequency n * (d k).point)) =
      markedThetaQuotient p S Ψ c (Ideal.Quotient.mk _ n))
    (W : ℝ → ℂ) (hWcompact : HasCompactSupport W)
    (lo hi : ℝ) (hlo : 0 < lo) (hsupp : Function.support W ⊆ Set.Icc lo hi)
    (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0 < X) :
    markedCompletedT Ψ W X (fun A => ∏ i ∈ S, if Ideal.span {p i} ∣ A then 1 else 0) =
      thetaDerivativeScalar⁻¹ * ∑ k, w k * (d k).smoothedKernel W X := by
  rw [markedCompletedT_canonical_reflection p S hp Ψ hΨ Q hperiod c hc hcQ
    W hWcompact lo hi hlo hsupp hW X hX]
  congr 1
  apply cusp_kernel_sum_congr (finiteTwistCusp c hc)
    (finiteAdditiveFourierCoeff (quotientTrace c hc)
      (markedThetaQuotient p S Ψ c)) d w ?_ W lo hi hlo hsupp hW X hX
  intro n
  simp_rw [finiteTwistCusp_point]
  rw [thetaFourierTranslation_inversion c hc, hmult]

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.ActiveCusp
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CompletedGauss CubicEisenstein ConcreteTraceCRT
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

variable {ι : Type*} [Fintype ι]

attribute [local instance] OAI.SevenEighths.InverseMoment.activeQuotientFintype
theorem primeFunction_fourier_by_active
    (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (F : ∀ i, (Eis ⧸ Ideal.span {p i}) → ℂ) (n : Eis) :
    (∏ i, F i (Ideal.Quotient.mk _ n)) =
      ∑ A : Finset ι, localInactiveWeight p hp F A *
        ∑ v : ∀ i : A, (Eis ⧸ Ideal.span {p i.val})ˣ,
          localActiveWeight p hp F A v *
            ∏ i : A, quotientTrace (p i.val) (hp i.val)
              ((v i : Eis ⧸ Ideal.span {p i.val}) * Ideal.Quotient.mk _ n) := by
  let (i : ι) : Field (Eis ⧸ Ideal.span {p i}) := Ideal.Quotient.field _
  have hpow : (Finset.univ : Finset ι).powerset = (Finset.univ : Finset (Finset ι)) := by
    ext A
    simp
  simpa only [hpow, localInactiveWeight, localActiveWeight] using
    FixedRayActiveSet.fourier_inversion_by_active_set (fun i => Eis ⧸ Ideal.span {p i})
      (fun i => quotientTrace (p i) (hp i))
      (fun i => GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive (p i) (hp i)) F
      (fun i => Ideal.Quotient.mk _ n)

theorem activeStratum_function_multiplier
    (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (hprimary : ∀ i, λ₀ ^ 2 ∣ p i - 1)
    (F : ∀ i, (Eis ⧸ Ideal.span {p i}) → ℂ)
    {N a0 c0 : Eis} {mode : Bool}
    (D : ∀ A : Finset ι, ControlledStratumArithmetic (fun i : A => p i.val) N a0 c0 mode)
    (hN : (9 : Eis) * c0 ∣ N) (hc0 : c0 ≠ 0)
    (hbase : if mode then λ₀ ^ 2 ∣ a0 - 1 else λ₀ ^ 2 ∣ c0 - 1)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a0 c0 mode)) (n : Eis) :
    (∑ A : Finset ι, localInactiveWeight p hp F A *
      ∑ v : ∀ i : A, (Eis ⧸ Ideal.span {p i.val})ˣ,
        localActiveWeight p hp F A v * ShortDraftTrace.breveE (-cuspFrequency n *
          (activeStratumDatum p hp hprimary D hN hc0 hbase s A v).point)) =
      ShortDraftTrace.breveE (-cuspFrequency n * (eisEmbedding a0 / eisEmbedding c0)) *
        ∏ i, F i (Ideal.Quotient.mk _ n) := by
  have hlocal (A : Finset ι) (v : ∀ i : A, (Eis ⧸ Ideal.span {p i.val})ˣ) :
      ShortDraftTrace.breveE (-cuspFrequency n *
        (activeStratumDatum p hp hprimary D hN hc0 hbase s A v).point) =
      ShortDraftTrace.breveE (-cuspFrequency n * (eisEmbedding a0 / eisEmbedding c0)) *
        ∏ i : A, quotientTrace (p i.val) (hp i.val)
          ((v i : Eis ⧸ Ideal.span {p i.val}) * Ideal.Quotient.mk _ n) :=
    (D A).datum_fourier_phase hN
      (primary_finset_product Finset.univ (fun i : A => p i.val) (fun i _ => hprimary i.val))
      hbase s (fun i => hp i.val) hc0 v n
  simp_rw [hlocal]
  rw [primeFunction_fourier_by_active p hp F n]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A hA
  apply Finset.sum_congr rfl
  intro v hv
  ring

theorem fixedActiveFunction_multiplier
    (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (hprimary : ∀ i, λ₀ ^ 2 ∣ p i - 1)
    (F : ∀ i, (Eis ⧸ Ideal.span {p i}) → ℂ)
    (c : Eis) (hc : c ≠ 0) [Fintype (Eis ⧸ Ideal.span {c})]
    (G : ∀ h : Eis ⧸ Ideal.span {c}, FixedFourierGeometry c h) (N : Eis)
    (hN : ∀ h, (9 : Eis) * (G h).c0 ∣ N)
    (D : ∀ h : Eis ⧸ Ideal.span {c}, ∀ A : Finset ι,
      ControlledStratumArithmetic (fun i : A => p i.val) N (G h).a0 (G h).c0 (G h).mode)
    (Q : Ideal Eis) (hcQ : Ideal.span {c} ≤ Ideal.span {(9 : Eis)} * Q)
    (φ : Eis →* ℂ) (hφ : CanonicalCoefficientClass.FactorsModulo Q φ) (n : Eis) :
    (∑ t : FixedActiveCuspIndex c p, fixedActiveFunctionWeight p hp F c hc φ t *
      ShortDraftTrace.breveE (-cuspFrequency n *
        (fixedActiveCuspDatum p hp hprimary c G N hN D t).point)) =
      fixedThetaTwist φ n * ∏ i, F i (Ideal.Quotient.mk _ n) := by
  simp only [FixedActiveCuspIndex, Fintype.sum_sigma, fixedActiveFunctionWeight, fixedActiveCuspDatum]
  have hf : (∑ h : Eis ⧸ Ideal.span {c}, fixedThetaRowCoeff c hc φ h *
      ShortDraftTrace.breveE (-cuspFrequency n * thetaFourierTranslation c h)) = fixedThetaTwist φ n := by
    simp only [fixedThetaRowCoeff]
    rw [thetaFourierTranslation_inversion c hc,
      fixedThetaQuotient_mk φ Q hφ c hcQ]
  rw [← hf, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro h hh
  calc
    _ = fixedThetaRowCoeff c hc φ h *
        (∑ A : Finset ι, localInactiveWeight p hp F A *
          ∑ v : ∀ i : A, (Eis ⧸ Ideal.span {p i.val})ˣ,
            localActiveWeight p hp F A v * ShortDraftTrace.breveE (-cuspFrequency n *
              (activeStratumDatum p hp hprimary (D h) (hN h) (G h).denominator_ne_zero
                (G h).primary (G h).shape A v).point)) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro A hA
      apply Finset.sum_congr rfl
      intro v hv
      ring
    _ = _ := by
      rw [activeStratum_function_multiplier p hp hprimary F (D h) (hN h)
        (G h).denominator_ne_zero (G h).primary (G h).shape n, (G h).point]
      ring

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.MixedRow
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CompletedGauss CanonicalRowCompletion CubicEisenstein
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι : Type*} [Fintype ι]

attribute [local instance] OAI.SevenEighths.InverseMoment.mixedQuotientFintype
theorem unmarkedSexticTwist_norm (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (j : ι → ℕ) (S : Finset ι) (n : Eis) :
    ‖unmarkedSexticTwist p hg j S n‖ ≤ 1 := by
  change ‖∏ i ∈ (Finset.univ : Finset ι) \ S,
    (actualSextic (Ideal.span {p i}) (hg i) ^ j i) (Ideal.Quotient.mk _ n)‖ ≤ 1
  rw [norm_prod]
  exact Finset.prod_le_one (fun i hi => norm_nonneg _)
    (fun i hi => FiniteRayExpansion.norm_char_le_one _ _)

theorem unmarkedSexticTwist_periodic (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (j : ι → ℕ) (S : Finset ι) :
    CanonicalCoefficientClass.FactorsModulo (Ideal.span {∏ i, p i}) (unmarkedSexticTwist p hg j S) := by
  intro x y hxy
  change (∏ i ∈ (Finset.univ : Finset ι) \ S, _) = ∏ i ∈ (Finset.univ : Finset ι) \ S, _
  apply Finset.prod_congr rfl
  intro i hi
  have he : Ideal.Quotient.mk (Ideal.span {p i}) x = Ideal.Quotient.mk _ y := by
    apply Ideal.Quotient.eq.mpr
    apply Ideal.mem_span_singleton.mpr
    exact (Finset.dvd_prod_of_mem p (Finset.mem_univ i)).trans (Ideal.mem_span_singleton.mp hxy)
  rw [he]

theorem mixedPrimeFunction_product (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (j : ι → ℕ) (S : Finset ι) (n : Eis) :
    (∏ i, mixedPrimeFunction p hg j S i (Ideal.Quotient.mk _ n)) =
      unmarkedSexticTwist p hg j S n * ∏ i ∈ S, if p i ∣ n then 1 else 0 := by
  rw [← Finset.prod_sdiff (Finset.subset_univ S)]
  have hS : (∏ i ∈ S, mixedPrimeFunction p hg j S i (Ideal.Quotient.mk _ n)) =
      ∏ i ∈ S, if p i ∣ n then (1 : ℂ) else 0 := by
    apply Finset.prod_congr rfl
    intro i hi
    simp only [mixedPrimeFunction, hi, ite_true, zeroMark,
      Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  rw [hS]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  simp only [mixedPrimeFunction, (Finset.mem_sdiff.mp hi).2, ite_false]

omit [Fintype ι] in
theorem markedThetaQuotient_mk (p : ι → Eis) (S : Finset ι)
    (Ψ : Eis →* ℂ) (Q : Ideal Eis) (hΨ : CanonicalCoefficientClass.FactorsModulo Q Ψ)
    (c : Eis) (hcQ : Ideal.span {c} ≤ Ideal.span {(9 : Eis)} * (Q * Ideal.span {∏ i ∈ S, p i}))
    (n : Eis) :
    markedThetaQuotient p S Ψ c (Ideal.Quotient.mk _ n) =
      fixedThetaTwist Ψ n * ∏ i ∈ S, if p i ∣ n then 1 else 0 := by
  unfold markedThetaQuotient
  have hcbase : Ideal.span {c} ≤ Ideal.span {(9 : Eis)} * Q :=
    hcQ.trans (Ideal.mul_mono_right Ideal.mul_le_left)
  rw [fixedThetaQuotient_mk Ψ Q hΨ c hcbase]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  have hxy : Quotient.out (Ideal.Quotient.mk (Ideal.span {c}) n) - n ∈ Ideal.span {c} :=
    Ideal.Quotient.eq.mp (Ideal.Quotient.mk_out (Ideal.Quotient.mk (Ideal.span {c}) n))
  have hp : p i ∣ Quotient.out (Ideal.Quotient.mk (Ideal.span {c}) n) - n :=
    (Finset.dvd_prod_of_mem p hi).trans (Ideal.mem_span_singleton.mp
      (Ideal.mul_le_right (Ideal.mul_le_right (hcQ hxy))))
  simp only [dvd_iff_dvd_of_dvd_sub hp]

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.ActiveReflection
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical ContDiff
open CompletedGauss CubicEisenstein CanonicalRowCompletion
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

attribute [local instance] OAI.SevenEighths.InverseMoment.activeReflectionQuotientFintype
theorem markedCompletedT_fixed_active_strata {ι : Type*} [Fintype ι]
    (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (hprime : ∀ i, Prime (p i))
    (hprimary : ∀ i, λ₀ ^ 2 ∣ p i - 1)
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (j : ι → ℕ) (S : Finset ι)
    (φ : Eis →* ℂ) (hφnorm : ∀ n, ‖φ n‖ ≤ 1)
    (Q : Ideal Eis) (hφperiod : CanonicalCoefficientClass.FactorsModulo Q φ)
    (c : Eis) (hc : c ≠ 0) [Fintype (Eis ⧸ Ideal.span {c})]
    (hcQ : Ideal.span {c} ≤ Ideal.span {(9 : Eis)} * Q)
    (G : ∀ h : Eis ⧸ Ideal.span {c}, FixedFourierGeometry c h) (N : Eis)
    (hN : ∀ h, (9 : Eis) * (G h).c0 ∣ N)
    (D : ∀ h : Eis ⧸ Ideal.span {c}, ∀ A : Finset ι,
      ControlledStratumArithmetic (fun i : A => p i.val) N (G h).a0 (G h).c0 (G h).mode)
    (call : Eis) (hcall : call ≠ 0) [Fintype (Eis ⧸ Ideal.span {call})]
    (hcallQ : Ideal.span {call} ≤ Ideal.span {(9 : Eis)} *
      ((Q * Ideal.span {∏ i, p i}) * Ideal.span {∏ i ∈ S, p i}))
    (W : ℝ → ℂ) (hWcompact : HasCompactSupport W)
    (lo hi : ℝ) (hlo : 0 < lo) (hsupp : Function.support W ⊆ Set.Icc lo hi)
    (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0 < X) :
    markedCompletedT (φ * unmarkedSexticTwist p hg j S) W X
      (fun A => ∏ i ∈ S, if Ideal.span {p i} ∣ A then 1 else 0) =
      thetaDerivativeScalar⁻¹ * ∑ t : FixedActiveCuspIndex c p,
        fixedActiveFunctionWeight p hp (mixedPrimeFunction p hg j S) c hc φ t *
          (fixedActiveCuspDatum p hp hprimary c G N hN D t).smoothedKernel W X := by
  have hnorm (n : Eis) : ‖(φ * unmarkedSexticTwist p hg j S) n‖ ≤ 1 := by
    rw [MonoidHom.mul_apply, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hφnorm n)).trans
      (unmarkedSexticTwist_norm p hg j S n)
  have hperiod : CanonicalCoefficientClass.FactorsModulo (Q * Ideal.span {∏ i, p i})
      (φ * unmarkedSexticTwist p hg j S) := by
    intro x y hxy
    simp only [MonoidHom.mul_apply]
    rw [hφperiod x y (Ideal.mul_le_left hxy),
      unmarkedSexticTwist_periodic p hg j S x y (Ideal.mul_le_right hxy)]
  apply markedCompletedT_of_cusp_multiplier p S (fun i _ => hprime i) _ hnorm _ hperiod
    call hcall hcallQ (fixedActiveCuspDatum p hp hprimary c G N hN D)
    (fixedActiveFunctionWeight p hp (mixedPrimeFunction p hg j S) c hc φ) ?_
    W hWcompact lo hi hlo hsupp hW X hX
  intro n
  rw [fixedActiveFunction_multiplier p hp hprimary (mixedPrimeFunction p hg j S)
    c hc G N hN D Q hcQ φ hφperiod,
    markedThetaQuotient_mk p S _ _ hperiod call hcallQ,
    fixedThetaTwist_mul, mixedPrimeFunction_product]
  ring

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.MarkedSource
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

namespace PrimeFamily
variable {ι : Type*} (P : PrimeFamily ι)
lemma generator_prime (i : ι) : Prime (P.generator i) :=
  (Ideal.span_singleton_prime (P.generator_ne_zero i)).mp inferInstance

end PrimeFamily
end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.MarkedRestriction
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
lemma mem_activeMarks (A S : Finset ι) (i : A) : i∈activeMarks A S ↔ i.val∈S := by
  simp [activeMarks]

omit [Fintype ι] in
lemma mixedPrimeFunction_restrict (P : PrimeFamily ι) (j : ι→ℕ) (A S : Finset ι)
    (i : A) (x : Eis⧸Ideal.span {P.generator i.val}) :
    mixedPrimeFunction (P.restrict A).generator (P.restrict A).generator_good
      (fun i => j i.val) (activeMarks A S) i x =
    mixedPrimeFunction P.generator P.generator_good j S i.val x := by
  simp only [mixedPrimeFunction,mem_activeMarks]
  rfl

omit [Fintype ι] in
lemma localActiveWeight_restrict (P : PrimeFamily ι) (j : ι→ℕ) (A S : Finset ι)
    (v : ∀ i : A, (Eis⧸Ideal.span {P.generator i.val})ˣ) :
    localActiveWeight P.generator P.generator_ne_zero
      (mixedPrimeFunction P.generator P.generator_good j S) A v =
    fullLocalFourierWeight (P.restrict A).generator_ne_zero
      (mixedPrimeFunction (P.restrict A).generator (P.restrict A).generator_good
        (fun i => j i.val) (activeMarks A S)) v := by
  unfold localActiveWeight fullLocalFourierWeight
  apply Finset.prod_congr rfl
  intro i hi
  congr 1
  funext x
  exact (mixedPrimeFunction_restrict P j A S i x).symm

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.MarkedChosenSource
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
namespace PrimeFamily
variable {ι : Type*} (P : PrimeFamily ι)

theorem marked_source_of_controlled [Fintype ι]
    (_hP : Pairwise (Function.onFun IsCoprime P.ideal)) (j : ι→ℕ) (S : Finset ι)
    (φ : Eis→*ℂ) (hφnorm : ∀ n, ‖φ n‖≤1)
    (Q : Ideal Eis) (hQ : Q≠0) (hφperiod : CanonicalCoefficientClass.FactorsModulo Q φ)
    (c : Eis) (hc : c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ : Ideal.span {c}≤Ideal.span {(9:Eis)}*Q)
    (G : ∀ h : Eis⧸Ideal.span {c}, FixedFourierGeometry c h)
    (N : Eis) (hN : ∀ h, (9:Eis)*(G h).c0∣N)
    (C : ∀ h : Eis⧸Ideal.span {c}, ∀ A : Finset ι,
      ControlledStratumArithmetic (fun i : A => P.generator i.val) N (G h).a0 (G h).c0 (G h).mode)
    (W : ℝ→ℂ) (hWcompact : HasCompactSupport W)
    (lo hi : ℝ) (hlo : 0<lo) (hsupp : Function.support W⊆Set.Icc lo hi)
    (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0<X) :
    markedCompletedT (φ*unmarkedSexticTwist P.generator P.generator_good j S) W X
      (fun A => ∏ i∈S, if Ideal.span {P.generator i}∣A then 1 else 0)=
    thetaDerivativeScalar⁻¹*∑ t : FixedActiveCuspIndex c P.generator,
      fixedActiveFunctionWeight P.generator P.generator_ne_zero
        (mixedPrimeFunction P.generator P.generator_good j S) c hc φ t *
      (fixedActiveCuspDatum P.generator P.generator_ne_zero P.generator_primary c G N hN
        C t).smoothedKernel W X := by
  let Qall := (Q*Ideal.span {∏ i, P.generator i})*Ideal.span {∏ i∈S, P.generator i}
  have hprod : (∏ i, P.generator i)≠0 := Finset.prod_ne_zero_iff.mpr (fun i _ => P.generator_ne_zero i)
  have hmark : (∏ i∈S, P.generator i)≠0 := Finset.prod_ne_zero_iff.mpr (fun i _ => P.generator_ne_zero i)
  have hQall : Qall≠0 := mul_ne_zero (mul_ne_zero hQ
    (by simpa only [ne_eq,Ideal.zero_eq_bot,Ideal.span_singleton_eq_bot] using hprod))
    (by simpa only [ne_eq,Ideal.zero_eq_bot,Ideal.span_singleton_eq_bot] using hmark)
  let call := ConcretePrimeRowBridge.idealGenerator (Ideal.span {(9:Eis)}*Qall)
  have hcall : call≠0 := by
    apply ConcretePrimeRowBridge.idealGenerator_ne_zero
    apply mul_ne_zero _ hQall
    simp only [ne_eq,Ideal.zero_eq_bot,Ideal.span_singleton_eq_bot]
    norm_num
  let : Finite (Eis⧸Ideal.span {call}) := ConcreteTraceCRT.finite_quotient_span hcall
  let : Fintype (Eis⧸Ideal.span {call}) := Fintype.ofFinite _
  have hcallQ : Ideal.span {call}≤Ideal.span {(9:Eis)}*Qall := by
    rw [ConcretePrimeRowBridge.span_idealGenerator]
  exact markedCompletedT_fixed_active_strata P.generator P.generator_ne_zero P.generator_prime
    P.generator_primary P.generator_good j S φ hφnorm Q hφperiod c hc hcQ G N hN
    C call hcall hcallQ W hWcompact lo hi hlo hsupp hW X hX
end PrimeFamily
end
end SevenEighths.InverseReflectedPhase

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Reflection.MarkedChosenDual
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
namespace PrimeFamily
variable {ι : Type*} [Fintype ι] (P : PrimeFamily ι)

lemma fixed_active_sum_eq_mixed_of_controlled
    (_hP : Pairwise (Function.onFun IsCoprime P.ideal)) (j : ι→ℕ) (S : Finset ι)
    (φ : Eis→*ℂ) (c : Eis) (hc : c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (G : ∀ h : Eis⧸Ideal.span {c}, FixedFourierGeometry c h)
    (N : Eis) (hN : ∀ h, (9:Eis)*(G h).c0∣N)
    (C : ∀ h : Eis⧸Ideal.span {c}, ∀ A : Finset ι,
      ControlledStratumArithmetic (fun i : A => P.generator i.val) N (G h).a0 (G h).c0 (G h).mode) (W : ℝ→ℂ) (X : ℝ) :
    (∑ t : FixedActiveCuspIndex c P.generator,
      fixedActiveFunctionWeight P.generator P.generator_ne_zero
        (mixedPrimeFunction P.generator P.generator_good j S) c hc φ t *
      (fixedActiveCuspDatum P.generator P.generator_ne_zero P.generator_primary c G N hN
        C t).smoothedKernel W X)=
    ∑ h : Eis⧸Ideal.span {c}, fixedThetaRowCoeff c hc φ h *
      ∑ A : Finset ι,
        localInactiveWeight P.generator P.generator_ne_zero (mixedPrimeFunction P.generator P.generator_good j S) A *
        mixedSmoothedValue (C h A) (hN h)
          (P.restrict A).generator_product_primary (G h).primary (G h).shape
          (P.restrict A).generator_ne_zero (G h).denominator_ne_zero (P.restrict A).generator_good
          (fun i => j i.val) (activeMarks A S) W X := by
  simp only [FixedActiveCuspIndex,Fintype.sum_sigma,fixedActiveFunctionWeight,fixedActiveCuspDatum,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  apply Finset.sum_congr rfl
  intro A hA
  simp only [mixedSmoothedValue,Finset.mul_sum]
  apply Finset.sum_congr (by ext v; simp only [Finset.mem_univ])
  intro v hv
  rw [localActiveWeight_restrict]
  have hw : fullLocalFourierWeight (P.restrict A).generator_ne_zero
      (mixedPrimeFunction (P.restrict A).generator (P.restrict A).generator_good
        (fun i => j i.val) (activeMarks A S)) v =
      fullLocalFourierWeight (fun i : A => P.generator_ne_zero i.val)
        (mixedPrimeFunction (fun i : A => P.generator i.val) (fun i => P.generator_good i.val)
          (fun i => j i.val) (activeMarks A S)) v := rfl
  rw [hw]
  dsimp only [activeStratumDatum]
  ring

theorem marked_reflected_source_of_controlled_oai
    (hP : Pairwise (Function.onFun IsCoprime P.ideal))
    (hodd : ∀ i, ringChar (Eis⧸P.ideal i)≠2) (j : ι→ℕ) (hj : ∀ i, j i<6) (S : Finset ι)
    (φ : Eis→*ℂ) (hφnorm : ∀ n, ‖φ n‖≤1)
    (Q : Ideal Eis) (hQ : Q≠0) (hφperiod : CanonicalCoefficientClass.FactorsModulo Q φ)
    (c : Eis) (hc : c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ : Ideal.span {c}≤Ideal.span {(9:Eis)}*Q)
    (G : ∀ h : Eis⧸Ideal.span {c}, FixedFourierGeometry c h)
    (N : Eis) (hN : ∀ h, (9:Eis)*(G h).c0∣N)
    (C : ∀ h : Eis⧸Ideal.span {c}, ∀ A : Finset ι,
      ControlledStratumArithmetic (fun i : A => P.generator i.val) N (G h).a0 (G h).c0 (G h).mode)
    (W : ℝ→ℂ) (hWcompact : HasCompactSupport W)
    (lo hi : ℝ) (hlo : 0<lo) (hsupp : Function.support W⊆Set.Icc lo hi)
    (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0<X) :
    markedCompletedT (φ*unmarkedSexticTwist P.generator P.generator_good j S) W X
      (fun A => ∏ i∈S, if Ideal.span {P.generator i}∣A then 1 else 0)=
    thetaDerivativeScalar⁻¹*∑ h : Eis⧸Ideal.span {c}, fixedThetaRowCoeff c hc φ h *
      ∑ A : Finset ι,
        localInactiveWeight P.generator P.generator_ne_zero (mixedPrimeFunction P.generator P.generator_good j S) A *
        mixedReflectedValue (C h A) (G h).shape
          (P.restrict A).generator_ne_zero (G h).denominator_ne_zero (P.restrict A).generator_good
          (fun i => j i.val) (activeMarks A S) W X := by
  rw [P.marked_source_of_controlled hP j S φ hφnorm Q hQ hφperiod c hc hcQ G N hN C
    W hWcompact lo hi hlo hsupp hW X hX,
    P.fixed_active_sum_eq_mixed_of_controlled hP j S φ c hc G N hN C W X]
  congr 1
  apply Finset.sum_congr rfl
  intro h hh
  congr 1
  apply Finset.sum_congr rfl
  intro A hA
  congr 1
  apply mixed_smoothed_eq_reflected
  · intro i k hik
    change IsCoprime (Ideal.span {P.generator i.val}) (Ideal.span {P.generator k.val})
    rw [P.generator_span,P.generator_span]
    exact hP (fun he => hik (Subtype.ext he))
  · intro i
    rw [P.generator_span]
    exact hodd i.val
  · exact fun i => hj i.val
  · exact hlo
  · exact hsupp
  · exact hW
  · exact hX
end PrimeFamily
end
end SevenEighths.InverseReflectedPhase

end OAI
end

theorem solution.{u_1} : type_of% @OAI.SevenEighths.InverseReflectedPhase.PrimeFamily.marked_reflected_source_of_controlled_oai.{u_1} := @OAI.SevenEighths.InverseReflectedPhase.PrimeFamily.marked_reflected_source_of_controlled_oai.{u_1}
