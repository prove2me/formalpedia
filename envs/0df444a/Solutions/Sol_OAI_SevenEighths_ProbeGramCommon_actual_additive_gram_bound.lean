-- Prove2me | solution 1 for OAI.SevenEighths.ProbeGramCommon.actual_additive_gram_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T04:09:56.796487+00:00
-- url     : https://prove2.me/submissions/f7485784-a08a-42dd-b2d4-44913e102f01

import Mathlib
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B026
import Theorems.Thm_OAI_SevenEighths_ProbeGramCommon_canonical_exceptional_ideal_sum
import Theorems.Thm_OAI_SevenEighths_ProbeGramCommon_canonical_nonexceptional_weighted
import Theorems.Thm_OAI_SevenEighths_ProbeGramCommon_original_energy_common_blocks
import Theorems.Thm_OAI_SevenEighths_ProbeGramCommon_sourceTruncation_eq_canonical

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

end EisensteinSchwartzPoisson

open scoped BigOperators Classical SchwartzMap ContDiff

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

theorem norm_finite_character_le_one {R : Type*} [CommRing R] [Fintype R]
    (χ : MulChar R ℂ) (r : R) : ‖χ r‖ ≤ 1 := by
  by_cases hr : IsUnit r
  · obtain ⟨u, rfl⟩ := hr
    simpa only [MulChar.coe_equivToUnitHom] using
      (Complex.norm_eq_one_of_mem_rootsOfUnity (χ.apply_mem_rootsOfUnity u)).le
  · rw [MulChar.map_nonunit χ hr, norm_zero]
    exact zero_le_one

end QuadraticInitialBound

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

lemma calibrationRowModulus_ne_zero (C : CalibrationData) (B : O) (hB : B≠0)
    (D : GoodMaskRowData B 1 C.generator) : calibrationRowModulus C B D≠0 := by
  unfold calibrationRowModulus
  apply mul_ne_zero
  · apply mul_ne_zero
    · exact mul_ne_zero one_ne_zero (Ideal.span_singleton_eq_bot.not.mpr hB)
    · apply Ideal.span_singleton_eq_bot.not.mpr
      norm_num
  · exact D.numeratorSupported.1

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

lemma lowArithmeticCoefficient_source_norm (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (s : {I : Id // Supported I}) : ‖lowArithmeticCoefficient (calibrationForSet S hS) s‖≤1 := by
  simpa only [calibrationForSet_tau_norm,inv_one] using lowArithmeticCoefficient_norm (calibrationForSet S hS) s

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

lemma lowGaussColumn_norm_bound (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (W1 : ℝ→ℂ) (a b B : ℝ) (ha : 0<a) (hB : 0≤B)
    (hW : Function.support W1⊆Set.Icc a b) (hWB : ∀x,‖W1 x‖≤B)
    (Y : ℝ) (hY : 0<Y) (σ : RayRing) (v : ℝ) (s : {I : Id // Supported I}) :
    ‖lowGaussColumn (calibrationForSet S hS) W1 Y σ v s‖≤
      B*a^(-(1/2:ℝ))/Y := by
  have hq : (0:ℝ)<Ideal.absNorm s.val := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr s.property.1)
  by_cases hzero : W1 ((Ideal.absNorm s.val:ℝ)/Y)=0
  · simp only [lowGaussColumn,hzero,mul_zero,zero_mul,ite_self,norm_zero]
    positivity
  have hqa := (hW hzero).1
  have hp : ‖(((Ideal.absNorm s.val:ℝ)/Y:ℝ):ℂ)^(-(1/2:ℂ)+(v:ℂ)*Complex.I)‖=
      ((Ideal.absNorm s.val:ℝ)/Y)^(-(1/2:ℝ)) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (div_pos hq hY)]
    congr 1
    simp
  have hr : ((Ideal.absNorm s.val:ℝ)/Y)^(-(1/2:ℝ))≤a^(-(1/2:ℝ)) :=
    Real.rpow_le_rpow_of_nonpos ha hqa (by norm_num)
  unfold lowGaussColumn
  split_ifs
  · rw [norm_mul,norm_mul,norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hY,hp]
    calc
      _ ≤ Y⁻¹*B*1*a^(-(1/2:ℝ)) := by
        gcongr
        · exact hWB _
        · exact lowArithmeticCoefficient_source_norm S hS s
      _ = _ := by ring
  · simp only [norm_zero]
    positivity

theorem lowGaussColumn_l2_bound (a b B : ℝ) (ha : 0<a) (hB : 0≤B) :
    ∃C : ℝ,0<C ∧ ∀S : Finset Id,∀hS : ∀P∈S,P.IsMaximal,
      ∀W1 : ℝ→ℂ,∀hW1 : HasCompactSupport W1,
      Function.support W1⊆Set.Icc a b → (∀x,‖W1 x‖≤B) →
      ∀Y : ℝ,∀hY : 1≤Y,∀σ : RayRing,∀v : ℝ,
      (∑s∈lowGaussColumns W1 hW1 Y (lt_of_lt_of_le zero_lt_one hY),
        ‖lowGaussColumn (calibrationForSet S hS) W1 Y σ v s‖^2)≤C/Y := by
  let C := 128*max 1 b*(B*a^(-(1/2:ℝ)))^2+1
  have hC : 0<C := by dsimp only [C];positivity
  refine ⟨C,hC,?_⟩
  intro S hS W1 hW1 hW hWB Y hY σ v
  have hy : 0<Y := lt_of_lt_of_le zero_lt_one hY
  have hcoef (s : {I : Id // Supported I}) := lowGaussColumn_norm_bound S hS W1 a b B ha hB hW hWB Y hy σ v s
  calc
    _ ≤ ∑_s∈lowGaussColumns W1 hW1 Y hy,(B*a^(-(1/2:ℝ))/Y)^2 := by
      apply Finset.sum_le_sum
      intro s hs
      exact pow_le_pow_left₀ (norm_nonneg _) (hcoef s) 2
    _ = ((lowGaussColumns W1 hW1 Y hy).card:ℝ)*(B*a^(-(1/2:ℝ))/Y)^2 := by simp
    _ ≤ (128*max 1 b*Y)*(B*a^(-(1/2:ℝ))/Y)^2 :=
      mul_le_mul_of_nonneg_right (lowGaussColumns_card W1 hW1 Y hY a b hW) (sq_nonneg _)
    _ = (128*max 1 b*(B*a^(-(1/2:ℝ)))^2)/Y := by field_simp
    _ ≤ C/Y := div_le_div_of_nonneg_right (by dsimp only [C];linarith) hy.le

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.LowGramFixedCoefficient
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma gramFixedModulus_nonzero (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) : gramFixedModulus S hS≠0 := by
  unfold gramFixedModulus
  apply mul_ne_zero
  · exact mul_ne_zero (Ideal.span_singleton_eq_bot.not.mpr (calibrationForSet S hS).generator_ne_zero)
      (calibrationRowModulus_ne_zero _ _ (calibrationForSet S hS).generator_ne_zero _)
  · exact Ideal.span_singleton_eq_bot.not.mpr (by norm_num)

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.GramJointFixed
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

lemma jointFixedModulus_nonzero (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) : jointFixedModulus S hS≠0 := by
  apply mul_ne_zero
  · apply mul_ne_zero (gramFixedModulus_nonzero S hS)
    exact Ideal.span_singleton_eq_bot.not.mpr (pow_ne_zero _ ConcretePrimeRowBridge.goodLambda_prime.ne_zero)
  · exact Ideal.span_singleton_eq_bot.not.mpr (by norm_num)

end SevenEighths.ProbeGramCommon
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.Tail
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentTail
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein EisensteinSchwartzPoisson
open CenteredMomentCommonSupport CenteredMomentCorrelation CenteredMomentFourier
open CenteredMomentSupportedCorrelation

theorem fullModulusCorrelation_norm_le (u v : O) (_hu : u ≠ 0) (_hv : v ≠ 0)
    [Fintype (Residue u)] [Fintype (Residue v)]
    (χu : MulChar (Residue u) ℂ) (χv : MulChar (Residue v) ℂ) (j : O) :
    ‖fullModulusCorrelation u v χu χv j‖ ≤
      (Ideal.absNorm (Ideal.span {u}) : ℝ) * (Ideal.absNorm (Ideal.span {v}) : ℝ) := by
  unfold fullModulusCorrelation fullCorrelation
  calc
    _ ≤ ∑ x : Residue u, ‖∑ y : Residue v,
      if scaledResidue u v (u * v) rfl x - scaledResidue v u (u * v) (mul_comm u v) y =
        Ideal.Quotient.mk _ j then χu x * star (χv y) else 0‖ := norm_sum_le _ _
    _ ≤ ∑ _x : Residue u, ∑ _y : Residue v, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro x hx
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro y hy
      split_ifs
      · rw [norm_mul, norm_star]
        exact (mul_le_of_le_one_left (norm_nonneg _)
          (QuadraticInitialBound.norm_finite_character_le_one χu x)).trans
          (QuadraticInitialBound.norm_finite_character_le_one χv y)
      · simp
    _ = _ := by
      simp [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]

theorem actualCorrelation_norm_le (u v : O)
    (hu : CanonicalQuadraticSieve.Supported (Ideal.span {u}))
    (hv : CanonicalQuadraticSieve.Supported (Ideal.span {v})) (j : O) :
    ‖actualCorrelation u v hu hv j‖ ≤
      (Ideal.absNorm (Ideal.span {u}) : ℝ) * (Ideal.absNorm (Ideal.span {v}) : ℝ) := by
  let := finite_quotient_span (supported_element_ne_zero u hu)
  let := finite_quotient_span (supported_element_ne_zero v hv)
  let : Fintype (Residue u) := Fintype.ofFinite _
  let : Fintype (Residue v) := Fintype.ofFinite _
  unfold actualCorrelation
  exact fullModulusCorrelation_norm_le u v (supported_element_ne_zero u hu)
    (supported_element_ne_zero v hv) _ _ j

end SevenEighths.CenteredMomentTail
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.GramFrequencyConvergence
namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CompletedGauss ConcreteTraceCRT
open CenteredMomentSupportedCorrelation EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O

lemma actual_correlation_radial_summable (I J : SupportedIdeal) (C : O) (hC : C≠0)
    (U : SchwartzMap ℝ ℂ) (Q : ℝ) (hQ : 0<Q) :
    Summable (fun k : O=>actualCorrelation (primaryGenerator I.val) (primaryGenerator J.val)
      ((supported_span_primaryGenerator_iff _).mpr I.property)
      ((supported_span_primaryGenerator_iff _).mpr J.property) (C*k)*
      paperRadialFourier U (Q*‖eisEmbedding (C*k)‖^2/
        ‖eisEmbedding (primaryGenerator I.val*primaryGenerator J.val)‖^2)) := by
  let t:=Q*‖eisEmbedding C‖^2/‖eisEmbedding (primaryGenerator I.val*primaryGenerator J.val)‖^2
  have hc : 0<‖eisEmbedding C‖^2 := sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hC))
  have hd : 0<‖eisEmbedding (primaryGenerator I.val*primaryGenerator J.val)‖^2 :=
    sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero (mul_ne_zero
      (supported_primaryGenerator_ne_zero _ I.property) (supported_primaryGenerator_ne_zero _ J.property))))
  have ht : 0<t := div_pos (mul_pos hQ hc) hd
  have hs := paperRadialFourier_lattice_summable_norm U t ht
  let B : ℝ := (Ideal.absNorm I.val:ℝ)*Ideal.absNorm J.val
  have hb (k : O) : ‖actualCorrelation (primaryGenerator I.val) (primaryGenerator J.val)
      ((supported_span_primaryGenerator_iff _).mpr I.property)
      ((supported_span_primaryGenerator_iff _).mpr J.property) (C*k)‖≤B := by
    have hh := CenteredMomentTail.actualCorrelation_norm_le (primaryGenerator I.val) (primaryGenerator J.val)
      ((supported_span_primaryGenerator_iff _).mpr I.property)
      ((supported_span_primaryGenerator_iff _).mpr J.property) (C*k)
    simpa only [(primaryGenerator_spec _ (supported_primaryGenerator_ne_zero _ I.property)).1,
      (primaryGenerator_spec _ (supported_primaryGenerator_ne_zero _ J.property)).1] using hh
  have harg (k : O) : Q*‖eisEmbedding (C*k)‖^2/‖eisEmbedding (primaryGenerator I.val*primaryGenerator J.val)‖^2=t*‖eisEmbedding k‖^2 := by
    simp only [map_mul,norm_mul,mul_pow,t]
    ring
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun k=>norm_nonneg _) _ (hs.mul_left B)
  intro k
  rw [norm_mul,harg]
  exact mul_le_mul_of_nonneg_right (hb k) (norm_nonneg _)

lemma originalCommonBlock_summable (S : Finset (Ideal O)) (hS : ∀p∈S,p.IsMaximal)
    (σ : RayFourExpansion.RayRing) (C : SupportedIdeal) (W : ℝ→ℂ) (hW : HasCompactSupport W)
    (Y Q : ℝ) (hY : 0<Y) (hQ : 0<Q) (U : SchwartzMap ℝ ℂ) (v : ℝ) :
    Summable (fun k : GramFrequency=>originalCommonBlock S hS σ C k W hW Y Q hY U v) := by
  unfold originalCommonBlock
  apply summable_sum
  intro I hI
  apply summable_sum
  intro J hJ
  by_cases hij : IsCoprime I.val J.val
  · simp only [hij,ite_true]
    have hs := (actual_correlation_radial_summable (supportedIdealProduct C I) (supportedIdealProduct C J)
      (primaryGenerator C.val) (supported_primaryGenerator_ne_zero _ C.property) U Q hQ).subtype (fun k : O=>k≠0)
    simpa only [Function.comp_def,mul_assoc] using hs.mul_left
      ((lowGramCoefficient (calibrationForSet S hS) σ (supportedIdealProduct C I)*
        lowGramProfile W v ((Ideal.absNorm (supportedIdealProduct C I).val:ℝ)/Y))*
       star (lowGramCoefficient (calibrationForSet S hS) σ (supportedIdealProduct C J)*
        lowGramProfile W v ((Ideal.absNorm (supportedIdealProduct C J).val:ℝ)/Y)))
  · simpa only [hij,ite_false] using (summable_zero : Summable (fun _ : GramFrequency=>(0:ℂ)))

end SevenEighths.ProbeGramCommon
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondDiagonal
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondDiagonal
open CenteredMomentCorrelation CenteredMomentCommonSupport CenteredMomentSupportedCorrelation
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
local notation "O" => ActualEisensteinCubic.O

theorem full_zero_off_diagonal (u v : O)
    [Fintype (Residue u)] [Fintype (Residue v)]
    (χ : MulChar (Residue u) ℂ) (ψ : MulChar (Residue v) ℂ)
    (hne : (Ideal.span {u} : Ideal O) ≠ Ideal.span {v}) :
    fullModulusCorrelation u v χ ψ 0 = 0 := by
  unfold fullModulusCorrelation fullCorrelation
  apply Finset.sum_eq_zero
  intro x hx
  apply Finset.sum_eq_zero
  intro y hy
  obtain ⟨x,rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨y,rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [scaledResidue_congruence]
  split_ifs with hc
  · by_cases hx0 : χ (Ideal.Quotient.mk _ x) = 0
    · rw [hx0,zero_mul]
    by_cases hy0 : ψ (Ideal.Quotient.mk _ y) = 0
    · rw [hy0,star_zero,mul_zero]
    have hux : IsCoprime u x := ((Ideal.isCoprime_span_singleton_iff x u).mp
      ((IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp (MulChar.apply_ne_zero_iff.mp hx0))).symm
    have hvy : IsCoprime v y := ((Ideal.isCoprime_span_singleton_iff y v).mp
      ((IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp (MulChar.apply_ne_zero_iff.mp hy0))).symm
    simp only [sub_zero] at hc
    have hu : u ∣ v*x := by
      have he := dvd_add ((dvd_mul_right u v).trans hc) (dvd_mul_right u y)
      convert (preTransparency := .instances) he using 1 ; ring
    have hv : v ∣ u*y := by
      have he := dvd_sub (dvd_mul_right v x) ((dvd_mul_left v u).trans hc)
      convert (preTransparency := .instances) he using 1 ; ring
    have huv := hux.dvd_of_dvd_mul_right hu
    have hvu := hvy.dvd_of_dvd_mul_right hv
    exact False.elim (hne (le_antisymm (Ideal.span_singleton_le_span_singleton.mpr hvu)
      (Ideal.span_singleton_le_span_singleton.mpr huv)))
  · rfl

theorem full_same_zero (u : O) (hu : u ≠ 0) [Fintype (Residue u)]
    (χ : MulChar (Residue u) ℂ) :
    fullModulusCorrelation u u χ χ 0 = ∑ x : Residue u, χ x*star (χ x) := by
  have hcong (x y : Residue u) :
      scaledResidue u u (u*u) rfl x - scaledResidue u u (u*u) (mul_comm u u) y =
        Ideal.Quotient.mk (Ideal.span {u*u}) 0 ↔ x=y := by
    obtain ⟨x,rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y,rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [scaledResidue_congruence,sub_zero,← mul_sub,mul_dvd_mul_iff_left hu]
    exact Ideal.mem_span_singleton.symm.trans Ideal.Quotient.eq.symm
  simp only [fullModulusCorrelation,fullCorrelation,hcong,Finset.sum_ite_eq,Finset.mem_univ,ite_true]

theorem full_same_zero_norm_le (u : O) (hu : u ≠ 0) [Fintype (Residue u)]
    (χ : MulChar (Residue u) ℂ) :
    ‖fullModulusCorrelation u u χ χ 0‖ ≤ (Fintype.card (Residue u) : ℝ) := by
  rw [full_same_zero u hu χ]
  calc
    _ ≤ ∑ x : Residue u, ‖χ x*star (χ x)‖ := norm_sum_le _ _
    _ ≤ ∑ _x : Residue u, (1:ℝ) := by
      apply Finset.sum_le_sum
      intro x hx
      by_cases hn : χ x = 0
      · simp only [hn,zero_mul,norm_zero,zero_le_one]
      · rw [MulChar.star_apply',MulChar.inv_apply_eq_inv',mul_inv_cancel₀ hn,norm_one]
    _ = _ := by simp

theorem actual_zero_off_diagonal (u v : O) (hu : Supported (Ideal.span {u}))
    (hv : Supported (Ideal.span {v}))
    (hpu : ConcretePrimeRowBridge.goodLambda^2 ∣ u-1)
    (hpv : ConcretePrimeRowBridge.goodLambda^2 ∣ v-1) (hne : u ≠ v) :
    actualCorrelation u v hu hv 0 = 0 := by
  let := ConcreteTraceCRT.finite_quotient_span (supported_element_ne_zero u hu)
  let := ConcreteTraceCRT.finite_quotient_span (supported_element_ne_zero v hv)
  let : Fintype (Residue u) := Fintype.ofFinite _
  let : Fintype (Residue v) := Fintype.ofFinite _
  apply full_zero_off_diagonal u v
  intro he
  apply hne
  rw [← primaryGenerator_span u (supported_element_ne_zero u hu) hpu,
    ← primaryGenerator_span v (supported_element_ne_zero v hv) hpv,he]

theorem actual_same_zero_norm_le (u : O) (hu : Supported (Ideal.span {u})) :
    ‖actualCorrelation u u hu hu 0‖ ≤ (Ideal.absNorm (Ideal.span {u}) : ℝ) := by
  let := ConcreteTraceCRT.finite_quotient_span (supported_element_ne_zero u hu)
  let : Fintype (Residue u) := Fintype.ofFinite _
  have hb := full_same_zero_norm_le u (supported_element_ne_zero u hu) (supportedModulusCharacter u hu)
  simpa only [actualCorrelation,supportedCorrelation,Ideal.absNorm_apply,Submodule.cardQuot_apply,Nat.card_eq_fintype_card] using hb

theorem secondZeroEnergy_bound {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i}))
    (hp : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ a i-1)
    (hinj : Set.InjOn a S) (c : α → ℂ) :
    ‖secondZeroEnergy S a ha c‖ ≤ ∑ i ∈ S, ‖c i‖^2 := by
  have hroot (i : α) :
      ((Real.sqrt (Ideal.absNorm (Ideal.span {a i}) : ℝ) : ℂ)*
       (Real.sqrt (Ideal.absNorm (Ideal.span {a i}) : ℝ) : ℂ)) =
        (Ideal.absNorm (Ideal.span {a i}) : ℂ) := by
    rw [← Complex.ofReal_mul,Real.mul_self_sqrt (Nat.cast_nonneg _),Complex.ofReal_natCast]
  have he : secondZeroEnergy S a ha c =
      ∑ i ∈ S, (c i*star (c i)) *
        (actualCorrelation (a i) (a i) (ha i) (ha i) 0 /(Ideal.absNorm (Ideal.span {a i}) : ℂ)) := by
    unfold secondZeroEnergy
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_eq_single i]
    · rw [hroot]
    · intro j hj hji
      have hne : a i ≠ a j := fun he => hji (hinj hi hj he).symm
      rw [actual_zero_off_diagonal _ _ (ha i) (ha j) (hp i) (hp j) hne,zero_div,mul_zero]
    · exact fun hnot => False.elim (hnot hi)
  rw [he]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  rw [norm_mul,norm_mul,norm_star,norm_div,Complex.norm_natCast,← pow_two]
  have hN : 0 < (Ideal.absNorm (Ideal.span {a i}) : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (ha i).1)
  exact mul_le_of_le_one_right (sq_nonneg _) ((div_le_one hN).mpr (actual_same_zero_norm_le _ (ha i)))

end SevenEighths.CenteredMomentSecondDiagonal

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.LowGramDiagonal
namespace OAI

noncomputable section
open scoped Classical SchwartzMap
open CompletedGauss
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve RayFourExpansion CenteredMomentGaussEnergy
open CenteredMomentSupportedCorrelation CenteredMomentSecondDiagonal EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma lowGramZeroMode_bound (C : CalibrationData) (W1 : ℝ→ℂ) (hW1 : HasCompactSupport W1)
    (Y : ℝ) (hY : 0<Y) (σ : RayRing) (v : ℝ) (U : SchwartzMap ℝ ℂ) (Q : ℝ) (hQ : 0≤Q) :
    ‖lowGramZeroMode C W1 hW1 Y hY σ v U Q‖≤
      Q*‖paperRadialFourier U 0‖*∑s∈lowGaussColumns W1 hW1 Y hY,‖lowGaussColumn C W1 Y σ v s‖^2 := by
  rw [lowGramZeroMode,norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hQ]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply secondZeroEnergy_bound
  · intro s
    exact (primaryGenerator_spec s.val (supported_primaryGenerator_ne_zero s.val s.property)).2
  · intro s hs t ht h
    apply Subtype.ext
    have hes := (primaryGenerator_spec s.val (supported_primaryGenerator_ne_zero s.val s.property)).1
    have het := (primaryGenerator_spec t.val (supported_primaryGenerator_ne_zero t.val t.property)).1
    rw [←hes,←het]
    exact congrArg (fun z : O=>Ideal.span {z}) h

theorem lowGramZeroMode_source_bound (a b B : ℝ) (ha : 0<a) (hB : 0≤B) :
    ∃C : ℝ,0<C ∧ ∀S : Finset Id,∀hS : ∀P∈S,P.IsMaximal,
      ∀W1 : ℝ→ℂ,∀hW1 : HasCompactSupport W1,
      Function.support W1⊆Set.Icc a b→(∀x,‖W1 x‖≤B)→
      ∀Y : ℝ,∀hY : 1≤Y,∀σ : RayRing,∀v : ℝ,∀U : SchwartzMap ℝ ℂ,∀Q : ℝ,0≤Q→
      ‖lowGramZeroMode (calibrationForSet S hS) W1 hW1 Y (lt_of_lt_of_le zero_lt_one hY) σ v U Q‖≤
        C*‖paperRadialFourier U 0‖*Q/Y := by
  obtain ⟨C,hC,hb⟩ := lowGaussColumn_l2_bound a b B ha hB
  refine ⟨C,hC,?_⟩
  intro S hS W1 hW1 hWS hWB Y hY σ v U Q hQ
  apply (lowGramZeroMode_bound (calibrationForSet S hS) W1 hW1 Y (lt_of_lt_of_le zero_lt_one hY) σ v U Q hQ).trans
  calc
    _ ≤ Q*‖paperRadialFourier U 0‖*(C/Y) := by
      exact mul_le_mul_of_nonneg_left (hb S hS W1 hW1 hWS hWB Y hY σ v) (by positivity)
    _ = _ := by ring

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.GramFrequencySummation
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.ProbeGramFrequencySummation
local notation "O" => ActualEisensteinCubic.O

lemma frequencyNorm_nonneg (k : O) : 0 ≤ frequencyNorm k := Nat.cast_nonneg _

lemma frequencyNorm_one_le (k : O) (hk : k ≠ 0) : 1 ≤ frequencyNorm k := by
  unfold frequencyNorm
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
    (Ideal.span_singleton_eq_bot.not.mpr hk))

theorem finite_weighted_of_count {α : Type*} (E : Finset α) (q : α → ℝ)
    (hq : ∀ x, 0 ≤ q x) (C d H : ℝ) (hC : 0 ≤ C) (hd : d ≤ 1) (hH : 0 < H)
    (hcount : ∀ F : Finset α, F ⊆ E → ∀ R : ℝ, 0 < R →
      (∀ x ∈ F, q x ≤ R) → (F.card : ℝ) ≤ C * R ^ d) :
    ∑ x ∈ E, (1 + q x / H) ^ (-2 : ℝ) ≤ 4 * C * H ^ d := by
  have hex (x : α) : ∃ n : ℕ, (2:ℝ)^n ≤ 1 + q x / H ∧
      1 + q x / H < (2:ℝ)^(n+1) :=
    exists_nat_pow_near (by linarith [div_nonneg (hq x) hH.le]) (by norm_num)
  let bin (x : α) : ℕ := Classical.choose (hex x)
  have hlo (x : α) : (2:ℝ)^(bin x) ≤ 1 + q x / H := (Classical.choose_spec (hex x)).1
  have hhi (x : α) : 1 + q x / H < (2:ℝ)^(bin x+1) := (Classical.choose_spec (hex x)).2
  have hbin (n : ℕ) :
      ∑ x ∈ E.filter (fun x => bin x = n), (1 + q x / H) ^ (-2 : ℝ) ≤
        (2*C*H^d) * (1/2:ℝ)^n := by
    let F := E.filter (fun x => bin x = n)
    have hcard : (F.card:ℝ) ≤ C * ((2:ℝ)^(n+1)*H)^d := by
      apply hcount F (Finset.filter_subset _ _) _ (by positivity)
      intro x hx
      have he := (Finset.mem_filter.mp hx).2
      have hh := hhi x
      rw [he] at hh
      have hqdiv : q x/H ≤ (2:ℝ)^(n+1) := by linarith
      exact (div_le_iff₀ hH).mp hqdiv
    have hweight (x : α) (hx : x∈F) : (1+q x/H)^(-2:ℝ) ≤ (1/4:ℝ)^n := by
      have hl := hlo x
      rw [(Finset.mem_filter.mp hx).2] at hl
      apply (Real.rpow_le_rpow_of_nonpos (by positivity) hl (by norm_num)).trans_eq
      rw [Real.rpow_neg (by positivity), Real.rpow_two, ← pow_mul, Nat.mul_comm, pow_mul, ← inv_pow]
      norm_num
    have hp : ((2:ℝ)^(n+1))^d ≤ (2:ℝ)^(n+1) :=
      Real.rpow_le_self_of_one_le (one_le_pow₀ (by norm_num)) hd
    calc
      _ ≤ (F.card:ℝ)*(1/4:ℝ)^n := by
        apply (Finset.sum_le_sum hweight).trans_eq
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (C*((2:ℝ)^(n+1)*H)^d)*(1/4:ℝ)^n :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
      _ ≤ (C*((2:ℝ)^(n+1)*H^d))*(1/4:ℝ)^n := by
        rw [Real.mul_rpow (by positivity) hH.le]
        gcongr
      _ = (2*C*H^d)*((2:ℝ)^n*(1/4:ℝ)^n) := by rw [pow_succ]; ring
      _ = _ := by rw [←mul_pow]; norm_num
  have hsum : (∑ x∈E,(1+q x/H)^(-2:ℝ)) =
      ∑ n∈E.image bin, ∑ x∈E.filter (fun x=>bin x=n), (1+q x/H)^(-2:ℝ) := by
    symm
    exact Finset.sum_fiberwise_of_maps_to (fun x hx => Finset.mem_image.mpr ⟨x,hx,rfl⟩) _
  rw [hsum]
  apply (Finset.sum_le_sum (fun n _=>hbin n)).trans
  have hs := (summable_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/2)
    (by norm_num : (1/2:ℝ)<1)).mul_left (2*C*H^d)
  apply (Summable.sum_le_tsum _ (by intro n _; positivity) hs).trans_eq
  rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/2)
    (by norm_num : (1/2:ℝ)<1)]
  ring

theorem nonzero_frequency_count (E : Finset O) (R : ℝ) (hR : 0 < R)
    (hE : ∀ k∈E, k≠0) (hN : ∀ k∈E, frequencyNorm k≤R) :
    (E.card:ℝ) ≤ 128*R := by
  by_cases hr : 1≤R
  · apply DescentFiberCost.finite_element_count_real E R hr
    intro k hk
    simpa only [ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span,frequencyNorm]
      using hN k hk
  · have he : E=∅ := Finset.eq_empty_iff_forall_notMem.mpr (by
      intro k hk
      have hh := frequencyNorm_one_le k (hE k hk)
      have hb := hN k hk
      linarith)
    rw [he,Finset.card_empty,Nat.cast_zero]
    positivity

theorem frequency_weighted_sum :
    ∃ K : ℝ, 0<K ∧ ∀ (E : Finset O) (H : ℝ), 0<H →
      (∀ k∈E,k≠0) →
      ∑ k∈E,(1+frequencyNorm k/H)^(-2:ℝ) ≤ K*H := by
  refine ⟨512,by norm_num,?_⟩
  intro E H hH hE
  have hh := finite_weighted_of_count E frequencyNorm frequencyNorm_nonneg
    128 1 H (by norm_num) (by norm_num) hH (by
      intro F hFE R hR hN
      simpa only [Real.rpow_one] using
        nonzero_frequency_count F R hR (fun k hk=>hE k (hFE hk)) hN)
  norm_num only [Real.rpow_one,show (4:ℝ)*128=512 by norm_num] at hh
  exact hh

end SevenEighths.ProbeGramFrequencySummation

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.GramFrequencyMass
namespace OAI

noncomputable section
open scoped Classical SchwartzMap ContDiff
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CompletedGauss RayFourExpansion ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma gramFrequency_image_sum (E : Finset GramFrequency) (f : O→ℝ) :
    (∑k∈E.image Subtype.val,f k)=∑k∈E,f k.val :=
  Finset.sum_image (fun _ _ _ _ h=>Subtype.val_injective h)

theorem canonical_nonexceptional_frequency_sum (A : ℕ) (hA : 2<A) (a₀ b₀ : ℝ)
    (ha₀ : 0<a₀) (hab : a₀<b₀) :
    ∃(J : ℕ)(H₀ : Finset (ℕ×ℕ)),
      ∀(W : ℝ→ℂ)(_hs : Function.support W⊆Set.Icc a₀ b₀)(_hW : ContDiff ℝ ∞ W),
      ∃K : ℝ,0<K ∧ ∀(S : Finset Id)(hS : ∀p∈S,p.IsMaximal)(σ : RayRing)
      (C : SupportedIdeal)(E : Finset GramFrequency),
      (∀k∈E,¬ExceptionalFrequency S hS C k)→
      ∀(d : O)(U : SchwartzMap ℝ ℂ)(v H N : ℝ),0<H→0<N→
        ‖∑k∈E,canonicalLatticeBlock S hS σ C k d W U v ((Ideal.absNorm (Ideal.span {k.val}):ℝ)/H) N‖≤
        K*H₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(1+|v|)^J*
          (Ideal.absNorm C.val:ℝ)*N^2*H*
          min 1 (((Ideal.absNorm (jointFixedModulus S hS):ℝ)*Ideal.absNorm C.val*H/N)^A) := by
  obtain ⟨J,H₀,hblock⟩ := canonical_nonexceptional_weighted A hA a₀ b₀ ha₀ hab
  obtain ⟨L,hL,hcount⟩ := ProbeGramFrequencySummation.frequency_weighted_sum
  refine ⟨J,H₀,?_⟩
  intro W hs hW
  obtain ⟨K,hK,hblock⟩ := hblock W hs hW
  refine ⟨K*L,mul_pos hK hL,?_⟩
  intro S hS σ C E hE d U v H N hH hN
  have hc := hcount (E.image Subtype.val) H hH (by
    intro k hk;obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hk;exact j.property)
  rw [gramFrequency_image_sum] at hc
  let V := K*H₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(1+|v|)^J*(Ideal.absNorm C.val:ℝ)*N^2*
    min 1 (((Ideal.absNorm (jointFixedModulus S hS):ℝ)*Ideal.absNorm C.val*H/N)^A)
  have hV : 0≤V := by dsimp [V];positivity
  calc
    _≤∑k∈E,‖canonicalLatticeBlock S hS σ C k d W U v ((Ideal.absNorm (Ideal.span {k.val}):ℝ)/H) N‖ := norm_sum_le _ _
    _≤∑k∈E,V*(1+(Ideal.absNorm (Ideal.span {k.val}):ℝ)/H)^(-2:ℝ) :=
      Finset.sum_le_sum (fun k hk=>hblock S hS σ C k (hE k hk) d U v H N hH hN)
    _=V*(∑k∈E,(1+(Ideal.absNorm (Ideal.span {k.val}):ℝ)/H)^(-2:ℝ)) := (Finset.mul_sum ..).symm
    _≤V*(L*H) := mul_le_mul_of_nonneg_left hc hV
    _=_ := by dsimp [V];ring

end SevenEighths.ProbeGramCommon
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.GramIdealSummation
namespace OAI

noncomputable section

open scoped BigOperators Classical
namespace SevenEighths.ProbeGramCommon
open ActualEisensteinCubic CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "SupportedIdeal" => {I : Ideal O // Supported I}

lemma gramIdealNorm_pos (I : SupportedIdeal) : 0 < gramIdealNorm I := by
  unfold gramIdealNorm
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr I.property.1)

theorem supportedIdeal_rpow_summable (r : ℝ) (hr : r < -1) :
    Summable (fun I : SupportedIdeal => gramIdealNorm I ^ r) := by
  have hs := CubicEisenstein.fullIdealWeight_summable_norm ((-r:ℝ):ℂ)
    (by simp only [Complex.ofReal_re]; linarith)
  have hinj : Function.Injective (fun I : SupportedIdeal => I.val) := Subtype.val_injective
  have ht := hs.comp_injective hinj
  apply ht.congr
  intro I
  rw [Function.comp_apply,CubicEisenstein.fullIdealWeight,if_neg I.property.1]
  have he : (Ideal.absNorm I.val:ℂ) = ((gramIdealNorm I:ℝ):ℂ) := by simp [gramIdealNorm]
  rw [he,Complex.norm_cpow_eq_rpow_re_of_pos (gramIdealNorm_pos I)]
  simp only [Complex.neg_re,Complex.ofReal_re,neg_neg]

theorem supportedIdeal_rpow_finite_bound (r : ℝ) (hr : r < -1) :
    ∃ K : ℝ, 0 < K ∧ ∀ F : Finset SupportedIdeal,
      (∑ I ∈ F, gramIdealNorm I ^ r) ≤ K := by
  have hs := supportedIdeal_rpow_summable r hr
  let K := 1 + ∑' I : SupportedIdeal, gramIdealNorm I ^ r
  have hn : 0 ≤ ∑' I : SupportedIdeal, gramIdealNorm I ^ r :=
    tsum_nonneg (fun I => Real.rpow_nonneg (gramIdealNorm_pos I).le _)
  refine ⟨K, by dsimp [K]; linarith, ?_⟩
  intro F
  exact (hs.sum_le_tsum F (fun I _ => Real.rpow_nonneg (gramIdealNorm_pos I).le _)).trans
    (by dsimp [K]; linarith)

lemma ideal_sum_min_power_bound (t : ℝ) (ht : 0 < t) (A : ℕ) (θ : ℝ)
    (hθ : 0 ≤ θ) (hA : θ ≤ A) : min 1 (t^A) ≤ t^θ := by
  by_cases h : t ≤ 1
  · apply (min_le_right _ _).trans
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_ge ht h hA
  · exact (min_le_left _ _).trans (Real.one_le_rpow (le_of_not_ge h) hθ)

lemma gram_ideal_term_bound (δ Λ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hΛ : 0 < Λ) (A : ℕ) (hA : 1 ≤ A) (I J : SupportedIdeal) :
    gramIdealNorm I ^ (-2:ℝ) * gramIdealNorm J ^ (-2:ℝ) *
      min 1 ((gramIdealNorm I*gramIdealNorm J/Λ)^A) ≤
      Λ^(-1+δ) * (gramIdealNorm I ^(-1-δ) * gramIdealNorm J^(-1-δ)) := by
  have hi := gramIdealNorm_pos I
  have hj := gramIdealNorm_pos J
  have ha : (1-δ:ℝ) ≤ A := by
    have hh : (1:ℝ) ≤ A := by exact_mod_cast hA
    linarith
  have hm := ideal_sum_min_power_bound (gramIdealNorm I*gramIdealNorm J/Λ)
    (by positivity) A (1-δ) (by linarith) ha
  apply (mul_le_mul_of_nonneg_left hm (by positivity)).trans_eq
  rw [Real.div_rpow (by positivity) hΛ.le,Real.mul_rpow hi.le hj.le,
    div_eq_mul_inv,← Real.rpow_neg hΛ.le]
  have hi' : gramIdealNorm I ^(-2:ℝ)*gramIdealNorm I ^(1-δ)=gramIdealNorm I ^(-1-δ) := by
    rw [←Real.rpow_add hi]
    congr 1
    ring
  have hj' : gramIdealNorm J^(-2:ℝ)*gramIdealNorm J^(1-δ)=gramIdealNorm J^(-1-δ) := by
    rw [←Real.rpow_add hj]
    congr 1
    ring
  rw [show -(1-δ) = -1+δ by ring]
  calc
    _ = Λ^(-1+δ)*((gramIdealNorm I ^(-2:ℝ)*gramIdealNorm I ^(1-δ))*
        (gramIdealNorm J^(-2:ℝ)*gramIdealNorm J^(1-δ))) := by ring
    _ = _ := by rw [hi',hj']

theorem gram_supported_double_sum (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ (A : ℕ), 1 ≤ A → ∀ (Λ : ℝ), 0 < Λ →
      ∀ (F G : Finset SupportedIdeal),
      (∑ I ∈ F, ∑ J ∈ G, gramIdealNorm I ^(-2:ℝ) * gramIdealNorm J^(-2:ℝ) *
        min 1 ((gramIdealNorm I*gramIdealNorm J/Λ)^A)) ≤ K*Λ^(-1+δ) := by
  obtain ⟨C,hC,hb⟩ := supportedIdeal_rpow_finite_bound (-1-δ) (by linarith)
  refine ⟨C ^2, by positivity, ?_⟩
  intro A hA Λ hΛ F G
  have hF := hb F
  have hG := hb G
  have hGn : 0 ≤ ∑ J ∈ G, gramIdealNorm J^(-1-δ) :=
    Finset.sum_nonneg (fun J _ => Real.rpow_nonneg (gramIdealNorm_pos J).le _)
  calc
    _ ≤ ∑ I ∈ F, ∑ J ∈ G, Λ^(-1+δ)*
        (gramIdealNorm I ^(-1-δ)*gramIdealNorm J^(-1-δ)) :=
      Finset.sum_le_sum (fun I _ => Finset.sum_le_sum
        (fun J _ => gram_ideal_term_bound δ Λ hδ hδ1 hΛ A hA I J))
    _ = Λ^(-1+δ)*((∑ I ∈ F, gramIdealNorm I ^(-1-δ))*
        (∑ J ∈ G, gramIdealNorm J^(-1-δ))) := by
      simp only [Finset.mul_sum,Finset.sum_mul]
      rw [Finset.sum_comm]
    _ ≤ Λ^(-1+δ)*C ^2 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [pow_two] using mul_le_mul hF hG hGn hC.le
    _ = _ := by ring

end SevenEighths.ProbeGramCommon

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.GramPrefactor
namespace OAI

noncomputable section
namespace SevenEighths.ProbeGramCommon

lemma nonexceptional_prefactor (c d F P Y Q : ℝ)
    (hc : 0<c) (hd : 0<d) (hF : 0<F) (hP : 0<P) (hY : 0<Y) (A : ℕ) :
    (Q/Y^3)*c*(Y/(c*d))^2*(P/c)*min 1 ((F*c*(P/c)/(Y/(c*d)))^A)=
      (Q/Y)*P*(c^(-2:ℝ)*d^(-2:ℝ)*min 1 ((c*d/(Y/(F*P)))^A)) := by
  have he : F*c*(P/c)/(Y/(c*d))=c*d/(Y/(F*P)) := by field_simp
  rw [he,Real.rpow_neg hc.le,Real.rpow_neg hd.le,Real.rpow_two,Real.rpow_two]
  field_simp

lemma supported_nonexceptional_prefactor (C D : SupportedIdeal) (F P Y Q : ℝ)
    (hF : 0<F) (hP : 0<P) (hY : 0<Y) (A : ℕ) :
    (Q/Y^3)*gramIdealNorm C*(Y/(gramIdealNorm C*gramIdealNorm D))^2*(P/gramIdealNorm C)*
      min 1 ((F*gramIdealNorm C*(P/gramIdealNorm C)/(Y/(gramIdealNorm C*gramIdealNorm D)))^A)=
      (Q/Y)*P*(gramIdealNorm C ^(-2:ℝ)*gramIdealNorm D^(-2:ℝ)*
        min 1 ((gramIdealNorm C*gramIdealNorm D/(Y/(F*P)))^A)) :=
  nonexceptional_prefactor _ _ _ _ _ _ (gramIdealNorm_pos C) (gramIdealNorm_pos D) hF hP hY A

end SevenEighths.ProbeGramCommon
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.GramIdealMass
namespace OAI

noncomputable section
open scoped Classical SchwartzMap ContDiff
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CompletedGauss RayFourExpansion ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma normalized_double_sum_bound (F G : Finset SupportedIdeal) (α V : SupportedIdeal→SupportedIdeal→ℂ)
    (hα : ∀C∈F,∀D∈G,‖α C D‖≤1) (p : ℝ) (hp : 0≤p) :
    ‖(p:ℂ)*(∑C∈F,∑D∈G,α C D*V C D)‖≤∑C∈F,∑D∈G,p*‖V C D‖ := by
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hp]
  calc
    _≤p*(∑C∈F,∑D∈G,‖α C D*V C D‖) := mul_le_mul_of_nonneg_left
      ((norm_sum_le _ _).trans (Finset.sum_le_sum (fun _ _=>norm_sum_le _ _))) hp
    _≤p*(∑C∈F,∑D∈G,‖V C D‖) := by
      apply mul_le_mul_of_nonneg_left _ hp
      apply Finset.sum_le_sum
      intro C hC
      apply Finset.sum_le_sum
      intro D hD
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right (hα C hC D hD) (norm_nonneg _)).trans_eq (one_mul _)
    _=_ := by simp only [Finset.mul_sum]

theorem canonical_nonexceptional_ideal_sum (δ : ℝ) (hδ : 0<δ) (hδ1 : δ<1)
    (A : ℕ) (hA : 2<A) (a b : ℝ) (ha : 0<a) (hab : a<b) :
    ∃(J : ℕ)(H₀ : Finset (ℕ×ℕ)),
      ∀(W : ℝ→ℂ)(_hs : Function.support W⊆Set.Icc a b)(_hW : ContDiff ℝ ∞ W),
      ∃K : ℝ,0<K ∧ ∀(S : Finset Id)(hS : ∀p∈S,p.IsMaximal)(σ : RayRing)
      (F G : Finset SupportedIdeal)(E : SupportedIdeal→SupportedIdeal→Finset GramFrequency)
      (α : SupportedIdeal→SupportedIdeal→ℂ),
      (∀C∈F,∀D∈G,‖α C D‖≤1)→(∀C∈F,∀D∈G,∀k∈E C D,¬ExceptionalFrequency S hS C k)→
      ∀(U : SchwartzMap ℝ ℂ)(v P Y Q : ℝ),0<P→0<Y→0≤Q→
        ‖((Q/Y^3:ℝ):ℂ)*(∑C∈F,∑D∈G,α C D*∑k∈E C D,
          canonicalLatticeBlock S hS σ C k (primaryGenerator D.val) W U v
            ((Ideal.absNorm (Ideal.span {k.val}):ℝ)/(P/gramIdealNorm C))
            (Y/(gramIdealNorm C*gramIdealNorm D)))‖≤
        K*H₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(1+|v|)^J*(Q/Y)*P*
          (Y/((Ideal.absNorm (jointFixedModulus S hS):ℝ)*P))^(-1+δ) := by
  obtain ⟨J,H₀,hfreq⟩ := canonical_nonexceptional_frequency_sum A hA a b ha hab
  obtain ⟨L,hL,hideal⟩ := gram_supported_double_sum δ hδ hδ1
  refine ⟨J,H₀,?_⟩
  intro W hs hW
  obtain ⟨K,hK,hfreq⟩ := hfreq W hs hW
  refine ⟨K*L,mul_pos hK hL,?_⟩
  intro S hS σ F G E α hα hE U v P Y Q hP hY hQ
  let M : ℝ := Ideal.absNorm (jointFixedModulus S hS)
  have hM : 0<M := by dsimp [M];exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (jointFixedModulus_nonzero S hS))
  let V := fun C D : SupportedIdeal=>∑k∈E C D,
    canonicalLatticeBlock S hS σ C k (primaryGenerator D.val) W U v
      ((Ideal.absNorm (Ideal.span {k.val}):ℝ)/(P/gramIdealNorm C)) (Y/(gramIdealNorm C*gramIdealNorm D))
  let B := K*H₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(1+|v|)^J*(Q/Y)*P
  have hB : 0≤B := by dsimp [B];positivity
  have ht (C D : SupportedIdeal) (hC : C∈F) (hD : D∈G) :
      (Q/Y^3)*‖V C D‖≤B*(gramIdealNorm C ^(-2:ℝ)*gramIdealNorm D^(-2:ℝ)*
        min 1 ((gramIdealNorm C*gramIdealNorm D/(Y/(M*P)))^A)) := by
    have hc := gramIdealNorm_pos C
    have hd := gramIdealNorm_pos D
    have hh := hfreq S hS σ C (E C D) (hE C hC D hD) (primaryGenerator D.val) U v
      (P/gramIdealNorm C) (Y/(gramIdealNorm C*gramIdealNorm D)) (by positivity) (by positivity)
    have hh' := mul_le_mul_of_nonneg_left hh (show 0≤Q/Y^3 by positivity)
    apply hh'.trans_eq
    change (Q/Y^3)*(K*H₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(1+|v|)^J*
      gramIdealNorm C*(Y/(gramIdealNorm C*gramIdealNorm D))^2*(P/gramIdealNorm C)*
      min 1 ((M*gramIdealNorm C*(P/gramIdealNorm C)/(Y/(gramIdealNorm C*gramIdealNorm D)))^A))=_
    calc
      _=(K*H₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(1+|v|)^J)*
        ((Q/Y^3)*gramIdealNorm C*(Y/(gramIdealNorm C*gramIdealNorm D))^2*(P/gramIdealNorm C)*
        min 1 ((M*gramIdealNorm C*(P/gramIdealNorm C)/(Y/(gramIdealNorm C*gramIdealNorm D)))^A)) := by ring
      _=_ := by rw [supported_nonexceptional_prefactor C D M P Y Q hM hP hY A];dsimp [B];ring
  calc
    _≤∑C∈F,∑D∈G,(Q/Y^3)*‖V C D‖ := normalized_double_sum_bound F G α V hα _ (by positivity)
    _≤∑C∈F,∑D∈G,B*(gramIdealNorm C ^(-2:ℝ)*gramIdealNorm D^(-2:ℝ)*
        min 1 ((gramIdealNorm C*gramIdealNorm D/(Y/(M*P)))^A)) := Finset.sum_le_sum (fun C hC=>Finset.sum_le_sum (fun D hD=>ht C D hC hD))
    _=B*(∑C∈F,∑D∈G,gramIdealNorm C ^(-2:ℝ)*gramIdealNorm D^(-2:ℝ)*
        min 1 ((gramIdealNorm C*gramIdealNorm D/(Y/(M*P)))^A)) := by simp only [Finset.mul_sum]
    _≤B*(L*(Y/(M*P))^(-1+δ)) := mul_le_mul_of_nonneg_left (hideal A (by omega) _ (by positivity) F G) hB
    _=_ := by dsimp [B,M];ring

end SevenEighths.ProbeGramCommon
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.GramSourceDivisors
namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CompletedGauss RayFourExpansion ConcreteTraceCRT
open CenteredMomentMobiusRegroup UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma sourceMobiusWeight_norm (W : ℝ→ℂ) (hW : HasCompactSupport W) (Y : ℝ) (hY : 0<Y) (C D : SupportedIdeal) :
    ‖sourceMobiusWeight W hW Y hY C D‖≤1 := by
  unfold sourceMobiusWeight
  split_ifs
  · exact CubicEisenstein.norm_ideal_moebius_le_one _
  · simp

end SevenEighths.ProbeGramCommon
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.GramTruncation
namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CompletedGauss RayFourExpansion ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma sourceCanonicalSum_split (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (σ : RayRing)
    (F : Finset SupportedIdeal) (E : Finset GramFrequency) (W : ℝ→ℂ) (hW : HasCompactSupport W)
    (Y Q : ℝ) (hY : 0<Y) (U : SchwartzMap ℝ ℂ) (v : ℝ) :
    sourceCanonicalSum S hS σ F (fun _=>E) W hW Y Q hY U v=
      sourceCanonicalSum S hS σ F (exceptionalFrequencies S hS E) W hW Y Q hY U v+
      sourceCanonicalSum S hS σ F (nonexceptionalFrequencies S hS E) W hW Y Q hY U v := by
  unfold sourceCanonicalSum exceptionalFrequencies nonexceptionalFrequencies
  rw [←mul_add,←Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro C hC
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro D hD
  rw [←mul_add,Finset.sum_filter_add_sum_filter_not]

end SevenEighths.ProbeGramCommon
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.GramSourceEstimate
namespace OAI

noncomputable section
open scoped Classical SchwartzMap ContDiff
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CompletedGauss RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem original_source_truncation_bound (δ ε : ℝ) (hδ : 0<δ) (hδ1 : δ<1)
    (hε : 0<ε) (hε1 : ε<1/6) (a b M₀ : ℝ) (ha : 0<a) (hab : a<b) (hM₀ : 0≤M₀)
    (W : ℝ→ℂ) (hcompact : HasCompactSupport W) (hs : Function.support W⊆Set.Icc a b)
    (hW : ContDiff ℝ ∞ W) (hWM : ∀x,‖W x‖≤M₀) :
    ∃(J : ℕ)(H₁ H₂ : Finset (ℕ×ℕ))(K₁ K₂ : ℝ),0<K₁ ∧ 0<K₂ ∧
      ∀(S : Finset Id)(hS : ∀p∈S,p.IsMaximal),fixedBadPrimes⊆S→∀(σ : RayRing)
      (F : Finset SupportedIdeal)(E : Finset GramFrequency)(U : SchwartzMap ℝ ℂ)
      (v Y Q : ℝ)(hY : 0<Y),0<Q→
      ‖sourceTruncation S hS σ F E W hcompact Y Q hY U v‖≤
        K₁*H₁.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(1+|v|)^J*(Q/Y)*(Y^2/Q)*
          (Y/((Ideal.absNorm (jointFixedModulus S hS):ℝ)*(Y^2/Q)))^(-1+δ)+
        K₂*H₂.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(Q/Y)*
          (Ideal.absNorm (jointFixedModulus S hS):ℝ)^ε*(Y^2/Q)^(1/6:ℝ) := by
  obtain ⟨J,H₁,hgood⟩ := canonical_nonexceptional_ideal_sum δ hδ hδ1 3 (by norm_num) a b ha hab
  obtain ⟨K₁,hK₁,hgood⟩ := hgood W hs hW
  obtain ⟨H₂,K₂,hK₂,hbadbound⟩ := canonical_exceptional_ideal_sum ε hε hε1 a b M₀ ha (by linarith) hM₀
  refine ⟨J,H₁,H₂,K₁,K₂,hK₁,hK₂,?_⟩
  intro S hS hbad σ F E U v Y Q hY hQ
  let G:=sourceDivisorUnion F W hcompact Y hY
  have hα := fun (C : SupportedIdeal) (_ : C∈F) (D : SupportedIdeal) (_ : D∈G)=>sourceMobiusWeight_norm W hcompact Y hY C D
  have hg := hgood S hS σ F G (fun C _=>nonexceptionalFrequencies S hS E C)
    (sourceMobiusWeight W hcompact Y hY) hα
    (by intro C hC D hD k hk;exact (Finset.mem_filter.mp hk).2)
    U v (Y^2/Q) Y Q (by positivity) hY hQ.le
  have hb := hbadbound W hcompact hs hWM S hS σ F G (fun C _=>exceptionalFrequencies S hS E C)
    (sourceMobiusWeight W hcompact Y hY) hα
    (by intro C hC D hD k hk;exact (Finset.mem_filter.mp hk).2)
    U v (Y^2/Q) Y Q (by positivity) hY hQ.le
  rw [sourceTruncation_eq_canonical S hS hbad σ F E W hcompact Y Q hY hQ U v,sourceCanonicalSum_split]
  exact (norm_add_le _ _).trans ((add_le_add hb hg).trans_eq (add_comm _ _))

end SevenEighths.ProbeGramCommon
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.GramInfiniteEstimate
namespace OAI

noncomputable section
open scoped Classical SchwartzMap ContDiff Topology
namespace SevenEighths.ProbeGramCommon
open Filter ProbePhysical CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentGaussEnergy
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma sourceTruncation_tendsto (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (σ : RayRing)
    (F : Finset SupportedIdeal) (W : ℝ→ℂ) (hW : HasCompactSupport W)
    (Y Q : ℝ) (hY : 0<Y) (hQ : 0<Q) (U : SchwartzMap ℝ ℂ) (v : ℝ) :
    Tendsto (fun E : Finset GramFrequency=>sourceTruncation S hS σ F E W hW Y Q hY U v) atTop
      (𝓝 (((Q/Y^3:ℝ):ℂ)*∑C∈F,∑'k : GramFrequency,originalCommonBlock S hS σ C k W hW Y Q hY U v)) := by
  have hs (C : SupportedIdeal) : Summable (fun k : GramFrequency=>originalCommonBlock S hS σ C k W hW Y Q hY U v) :=
    originalCommonBlock_summable S hS σ C W hW Y Q hY hQ U v
  have hh := (summable_sum (s:=F) (fun C hC=>hs C)).hasSum.mul_left ((Q/Y^3:ℝ):ℂ)
  rw [Summable.tsum_finsetSum (fun C hC=>hs C)] at hh
  change Tendsto _ atTop (𝓝 _) at hh
  convert (preTransparency := .instances) hh using 1
  funext E
  unfold sourceTruncation
  rw [←Finset.mul_sum,Finset.sum_comm]

theorem original_energy_nonzero_bound (δ ε : ℝ) (hδ : 0<δ) (hδ1 : δ<1)
    (hε : 0<ε) (hε1 : ε<1/6) (a b M₀ : ℝ) (ha : 0<a) (hab : a<b) (hM₀ : 0≤M₀)
    (W : ℝ→ℂ) (hcompact : HasCompactSupport W) (hs : Function.support W⊆Set.Icc a b)
    (hW : ContDiff ℝ ∞ W) (hWM : ∀x,‖W x‖≤M₀) :
    ∃(J : ℕ)(H₁ H₂ : Finset (ℕ×ℕ))(K₁ K₂ : ℝ),0<K₁ ∧ 0<K₂ ∧
      ∀(S : Finset Id)(hS : ∀p∈S,p.IsMaximal),fixedBadPrimes⊆S→∀(σ : RayRing)
      (U : SchwartzMap ℝ ℂ)(v Y Q : ℝ)(hY : 0<Y),0<Q→
      ‖gaussEnergy (lowGaussColumns W hcompact Y hY) (fun I=>primaryGenerator I.val)
        (fun I=>(supported_span_primaryGenerator_iff _).mpr I.property)
        (lowGaussColumn (calibrationForSet S hS) W Y σ v) U Q-
        lowGramZeroMode (calibrationForSet S hS) W hcompact Y hY σ v U Q‖≤
        K₁*H₁.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(1+|v|)^J*(Q/Y)*(Y^2/Q)*
          (Y/((Ideal.absNorm (jointFixedModulus S hS):ℝ)*(Y^2/Q)))^(-1+δ)+
        K₂*H₂.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(Q/Y)*
          (Ideal.absNorm (jointFixedModulus S hS):ℝ)^ε*(Y^2/Q)^(1/6:ℝ) := by
  obtain ⟨J,H₁,H₂,K₁,K₂,hK₁,hK₂,hbound⟩ := original_source_truncation_bound δ ε hδ hδ1 hε hε1 a b M₀ ha hab hM₀ W hcompact hs hW hWM
  refine ⟨J,H₁,H₂,K₁,K₂,hK₁,hK₂,?_⟩
  intro S hS hbad σ U v Y Q hY hQ
  rw [original_energy_common_blocks S hS σ W hcompact Y Q hY hQ U v,add_sub_cancel_left]
  exact le_of_tendsto (sourceTruncation_tendsto S hS σ _ W hcompact Y Q hY hQ U v).norm
    (Eventually.of_forall (fun E=>hbound S hS hbad σ _ E U v Y Q hY hQ))

end SevenEighths.ProbeGramCommon
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.GramScaleLoss
namespace OAI

noncomputable section
namespace SevenEighths.ProbeGramCommon

lemma nonexceptional_scale_identity (M P Y δ : ℝ) (hM : 0<M) (hP : 0<P) (hY : 0<Y) :
    P*(Y/(M*P))^(-1+δ)=M^(1-δ)*P^(2-δ)*Y^(-1+δ) := by
  rw [Real.div_rpow hY.le (mul_pos hM hP).le,Real.mul_rpow hM.le hP.le,div_eq_mul_inv,mul_inv_rev,
    ←Real.rpow_neg hM.le,←Real.rpow_neg hP.le]
  have he : P*P^(-(-1+δ))=P^(2-δ) := by
    conv_lhs => lhs;rw [←Real.rpow_one P]
    rw [←Real.rpow_add hP]
    congr 1
    ring
  calc
    _=M^(1-δ)*(P*P^(-(-1+δ)))*Y^(-1+δ) := by rw [show -(-1+δ)=1-δ by ring];ring
    _=_ := by rw [he]

lemma nonexceptional_scale_loss (M P Y δ : ℝ) (hM : 1≤M) (hP : 1≤P) (hY : 0<Y)
    (hδ : 0≤δ) :
    P*(Y/(M*P))^(-1+δ)≤M*(P^2/Y)*Y^δ := by
  have hm : 0<M := lt_of_lt_of_le zero_lt_one hM
  have hp : 0<P := lt_of_lt_of_le zero_lt_one hP
  rw [nonexceptional_scale_identity M P Y δ hm hp hY]
  have hmp : M^(1-δ)≤M := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hM (show 1-δ≤1 by linarith)
  have hpp : P^(2-δ)≤P^2 := by
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le hP (show 2-δ≤2 by linarith)
  calc
    _≤M*P^2*Y^(-1+δ) := mul_le_mul_of_nonneg_right
      (mul_le_mul hmp hpp (by positivity) hm.le) (by positivity)
    _=_ := by rw [Real.rpow_add hY,Real.rpow_neg_one];ring

end SevenEighths.ProbeGramCommon
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.GramBound
namespace OAI

noncomputable section
open scoped Classical SchwartzMap ContDiff
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentGaussEnergy EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem actual_additive_gram_bound_oai (δ : ℝ) (hδ : 0<δ) (hδ1 : δ<1)
    (a b M₀ : ℝ) (ha : 0<a) (hab : a<b) (hM₀ : 0≤M₀)
    (W : ℝ→ℂ) (hcompact : HasCompactSupport W) (hs : Function.support W⊆Set.Icc a b)
    (hW : ContDiff ℝ ∞ W) (hWM : ∀x,‖W x‖≤M₀) :
    ∃J : ℕ,∀(S : Finset Id)(hS : ∀p∈S,p.IsMaximal),fixedBadPrimes⊆S→∀U : SchwartzMap ℝ ℂ,
    ∃K : ℝ,0<K ∧ ∀(σ : RayRing)(v Y Q : ℝ)(hY : 1≤Y),0<Q→1≤Y^2/Q→
      ‖gaussEnergy (lowGaussColumns W hcompact Y (lt_of_lt_of_le zero_lt_one hY))
        (fun I=>primaryGenerator I.val) (fun I=>(supported_span_primaryGenerator_iff _).mpr I.property)
        (lowGaussColumn (calibrationForSet S hS) W Y σ v) U Q‖≤
      K*(1+|v|)^J*(Q/Y)*(1+(Y^2/Q)^(1/6:ℝ)+(Y^2/Q)^2/Y)*Y^δ := by
  obtain ⟨J,H₁,H₂,K₁,K₂,hK₁,hK₂,hbound⟩ := original_energy_nonzero_bound δ (1/12) hδ hδ1
    (by norm_num) (by norm_num) a b M₀ ha hab hM₀ W hcompact hs hW hWM
  obtain ⟨K₀,hK₀,hzero⟩ := lowGramZeroMode_source_bound a b M₀ ha hM₀
  refine ⟨J,?_⟩
  intro S hS hbad U
  let M : ℝ := Ideal.absNorm (jointFixedModulus S hS)
  have hM : 1≤M := by dsimp [M];exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (jointFixedModulus_nonzero S hS))
  let A₀ := K₀*‖paperRadialFourier U 0‖
  let A₁ := K₁*H₁.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*M
  let A₂ := K₂*H₂.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*M^(1/12:ℝ)
  have hA₀ : 0≤A₀ := by dsimp [A₀];positivity
  have hA₁ : 0≤A₁ := by dsimp [A₁];positivity
  have hA₂ : 0≤A₂ := by dsimp [A₂];positivity
  refine ⟨1+A₀+A₁+A₂,by positivity,?_⟩
  intro σ v Y Q hY hQ hP
  have hy : 0<Y := lt_of_lt_of_le zero_lt_one hY
  let P := Y^2/Q
  have hp : 1≤P := hP
  have hp0 : 0<P := lt_of_lt_of_le zero_lt_one hp
  let Z := lowGramZeroMode (calibrationForSet S hS) W hcompact Y hy σ v U Q
  let E := gaussEnergy (lowGaussColumns W hcompact Y hy) (fun I=>primaryGenerator I.val)
    (fun I=>(supported_span_primaryGenerator_iff _).mpr I.property)
    (lowGaussColumn (calibrationForSet S hS) W Y σ v) U Q
  have hn := hbound S hS hbad σ U v Y Q hy hQ
  have hz : ‖Z‖≤A₀*(Q/Y) := by
    have hh := hzero S hS W hcompact hs hWM Y hY σ v U Q hQ.le
    convert (preTransparency := .instances) hh using 1 ; dsimp [Z,A₀] ; ring
  have hgood : K₁*H₁.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(1+|v|)^J*(Q/Y)*P*
      (Y/(M*P))^(-1+δ)≤A₁*(1+|v|)^J*(Q/Y)*(P^2/Y)*Y^δ := by
    have hh := mul_le_mul_of_nonneg_left (nonexceptional_scale_loss M P Y δ hM hp hy hδ.le)
      (show 0≤K₁*H₁.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(1+|v|)^J*(Q/Y) by positivity)
    convert (preTransparency := .instances) hh using 1 <;> (try dsimp [A₁]) <;> ring
  have henergy : ‖E‖≤A₀*(Q/Y)+A₁*(1+|v|)^J*(Q/Y)*(P^2/Y)*Y^δ+A₂*(Q/Y)*P^(1/6:ℝ) := by
    have hn' : ‖E-Z‖≤A₁*(1+|v|)^J*(Q/Y)*(P^2/Y)*Y^δ+A₂*(Q/Y)*P^(1/6:ℝ) := by
      apply hn.trans
      exact add_le_add hgood (by dsimp [A₂,M,P];ring_nf;exact le_rfl)
    calc
      ‖E‖=‖(E-Z)+Z‖ := by congr 1;ring
      _≤‖E-Z‖+‖Z‖ := norm_add_le _ _
      _≤_ := by linarith
  let B := (1+|v|)^J*(Q/Y)*(1+P^(1/6:ℝ)+P^2/Y)*Y^δ
  have hb : 0≤B := by dsimp [B];positivity
  have hh : 1≤(1+|v|)^J := one_le_pow₀ (by linarith [abs_nonneg v])
  have hyd : 1≤Y^δ := Real.one_le_rpow hY hδ.le
  have hshape : 1≤1+P^(1/6:ℝ)+P^2/Y := by
    have hpow : 0≤P^(1/6:ℝ) := by positivity
    have hratio : 0≤P^2/Y := by positivity
    linarith
  have hb₀ : Q/Y≤B := by
    calc
      Q/Y=(1:ℝ)*(Q/Y)*1*1 := by ring
      _≤B := by dsimp [B];gcongr
  have hb₁ : (1+|v|)^J*(Q/Y)*(P^2/Y)*Y^δ≤B := by
    dsimp [B]
    gcongr
    have hpow : 0≤P^(1/6:ℝ) := by positivity
    linarith
  have hb₂ : (Q/Y)*P^(1/6:ℝ)≤B := by
    calc
      _=(1:ℝ)*(Q/Y)*P^(1/6:ℝ)*1 := by ring
      _≤B := by
        dsimp [B]
        gcongr
        have hratio : 0≤P^2/Y := by positivity
        linarith
  change ‖E‖≤_
  calc
    _≤A₀*(Q/Y)+A₁*((1+|v|)^J*(Q/Y)*(P^2/Y)*Y^δ)+A₂*((Q/Y)*P^(1/6:ℝ)) := by convert (preTransparency := .instances) henergy using 1 ; ring
    _≤A₀*B+A₁*B+A₂*B := add_le_add (add_le_add (mul_le_mul_of_nonneg_left hb₀ hA₀)
      (mul_le_mul_of_nonneg_left hb₁ hA₁)) (mul_le_mul_of_nonneg_left hb₂ hA₂)
    _≤(1+A₀+A₁+A₂)*B := by nlinarith
    _=_ := by dsimp [B,P];ring

end SevenEighths.ProbeGramCommon
end

end OAI
end

theorem solution : type_of% @OAI.SevenEighths.ProbeGramCommon.actual_additive_gram_bound_oai := @OAI.SevenEighths.ProbeGramCommon.actual_additive_gram_bound_oai
