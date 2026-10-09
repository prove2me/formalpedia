-- Prove2me | solution 1 for OAI.SevenEighths.ProbePhysical.calibratedHighCoefficient_eq_bare
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T04:21:25.63075+00:00
-- url     : https://prove2.me/submissions/6d641b4c-caa0-4c88-9a6b-f58b1c523a4a

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B027

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Poisson.EisensteinLattice
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

namespace IdealGaussCRT

theorem gauss_transform_finite_crt_scalar {ι T : Type*} [Fintype ι]
    (R : ι → Type*) [CommRing T] [∀ i, Field (R i)]
    [Fintype T] [∀ i, Fintype (R i)]
    (e : T ≃+* ∀ i, R i)
    (χ : ∀ i, MulChar (R i) ℂ) (ψ : AddChar T ℂ)
    (hχ : ∀ i, χ i ≠ 1) (h : T) :
    (∑ x : T, (∏ i, χ i (e x i)) * ψ (h * x)) =
      (∏ i, χ i (e h i))⁻¹ *
        ∑ x : T, (∏ i, χ i (e x i)) * ψ x := by
  classical
  have hbase := gauss_transform_finite_crt R e χ ψ hχ (1 : T)
  simp only [one_mul, map_one, Pi.one_apply, one_ne_zero, ↓reduceIte,
    inv_one, one_mul] at hbase
  rw [gauss_transform_finite_crt R e χ ψ hχ h, hbase]
  have hlocal (i : ι) :
      (if e h i = 0 then 0 else
        (χ i (e h i))⁻¹ * gaussSum (χ i) (coordinateAddChar R e ψ i)) =
      (χ i (e h i))⁻¹ * gaussSum (χ i) (coordinateAddChar R e ψ i) := by
    split_ifs with hi
    · simp [hi]
    · rfl
  simp_rw [hlocal]
  rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib]

end IdealGaussCRT

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.Physical
namespace OAI

noncomputable section

open scoped BigOperators Classical
open MeasureTheory
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open CubicEisenstein ProbeCompleted ProbeRow

local notation "O" => ActualEisensteinCubic.O

theorem sexticGauss_coefficient_mk (s : O) (a : O) :
    idealRowHom (GaussianShiftedPartition.representative s
      (Ideal.Quotient.mk (Ideal.span {s}) a)) (Ideal.span {s}) =
      idealRowHom a (Ideal.span {s}) := by
  apply idealRowHom_congr_mod
  apply Ideal.Quotient.eq.mp
  exact GaussianShiftedPartition.representative_spec _ _

attribute [local irreducible] markedPhysicalProbe

end SevenEighths.ProbePhysical
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

theorem crtCharacter_pow_six {ι T : Type*} [Fintype ι] [CommRing T]
    (R : ι → Type*) [∀ i, Field (R i)] (e : T ≃+* ∀ i, R i)
    (χ : ∀ i, MulChar (R i) ℂ) (hχ : ∀ i, χ i ^ 6 = 1) :
    crtCharacter R e χ ^ 6 = 1 := by
  apply MulChar.ext
  intro x
  rw [MulChar.pow_apply' _ (by decide : (6 : ℕ) ≠ 0), MulChar.one_apply x.isUnit]
  change (∏ i, χ i (e x i)) ^ 6 = 1
  rw [← Finset.prod_pow]
  apply Finset.prod_eq_one
  intro i _
  have hu : IsUnit (e x i) := (Pi.isUnit_iff.mp (x.isUnit.map e.toMonoidHom)) i
  have he := congrArg (fun f : MulChar (R i) ℂ => f (e x i)) (hχ i)
  simpa only [MulChar.pow_apply' _ (by decide : (6 : ℕ) ≠ 0), MulChar.one_apply hu] using he

theorem localCalibration_nonprincipal (P : Ideal O) [P.IsMaximal] :
    localCalibration P ≠ 1 := (Classical.choose_spec (exists_local_calibration P)).1

theorem localCalibration_pow_six (P : Ideal O) [P.IsMaximal] :
    localCalibration P ^ 6 = 1 := (Classical.choose_spec (exists_local_calibration P)).2

theorem calibrationFromPrimes_pow_six {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P)) :
    (calibrationFromPrimes P hcop).residue ^ 6 = 1 := by
  let (i : ι) : Field (O ⧸ P i) := Ideal.Quotient.field _
  exact crtCharacter_pow_six _ _ _ (fun i => localCalibration_pow_six (P i))

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

theorem calibrationForSet_pow_six (S : Finset (Ideal O)) (hS : ∀ P ∈ S, P.IsMaximal) :
    (calibrationForSet S hS).residue ^ 6 = 1 := by
  let (P : S) : P.val.IsMaximal := hS P.val P.property
  unfold calibrationForSet
  apply calibrationFromPrimes_pow_six

theorem calibrationForSet_tau_norm (S : Finset (Ideal O)) (hS : ∀ P ∈ S, P.IsMaximal) :
    ‖(calibrationForSet S hS).tau‖ = 1 := by
  let (P : S) : P.val.IsMaximal := hS P.val P.property
  unfold calibrationForSet
  apply calibrationFromPrimes_tau_norm

theorem calibrationForSet_tau_ne_zero (S : Finset (Ideal O)) (hS : ∀ P ∈ S, P.IsMaximal) :
    (calibrationForSet S hS).tau ≠ 0 := by
  exact norm_ne_zero_iff.mp (by rw [calibrationForSet_tau_norm]; norm_num)

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.CalibrationFourier
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

theorem calibrationGauss_one (C : CalibrationData) :
    calibrationGauss C 1 = (Real.sqrt (elementNorm C.generator) : ℂ) * C.tau := by
  have hn : 0 < elementNorm C.generator := by
    unfold elementNorm
    exact_mod_cast Nat.pos_of_ne_zero
      (Ideal.absNorm_eq_zero_iff.not.mpr
        (Ideal.span_singleton_eq_bot.not.mpr C.generator_ne_zero))
  have hc : (Real.sqrt (elementNorm C.generator) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hn).ne'
  simp only [calibrationGauss, map_one, one_mul, CalibrationData.tau]
  field_simp

theorem calibrationFromPrimes_gauss {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P)) (h : O) :
    calibrationGauss (calibrationFromPrimes P hcop) h =
      ((calibrationFromPrimes P hcop).residueMonoid h)⁻¹ *
        calibrationGauss (calibrationFromPrimes P hcop) 1 := by
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
  have ht := IdealGaussCRT.gauss_transform_finite_crt_scalar (fun i => O ⧸ P i) e
    (fun i => localCalibration (P i)) ψ (fun i => localCalibration_nonprincipal (P i))
    (Ideal.Quotient.mk (Ideal.span {b}) h)
  change (∑' d : O ⧸ Ideal.span {b}, (∏ i, localCalibration (P i) (e d i)) *
      ψ (Ideal.Quotient.mk (Ideal.span {b}) h * d)) =
    (∏ i, localCalibration (P i) (e (Ideal.Quotient.mk (Ideal.span {b}) h) i))⁻¹ *
      ∑' d : O ⧸ Ideal.span {b}, (∏ i, localCalibration (P i) (e d i)) *
        ψ (Ideal.Quotient.mk (Ideal.span {b}) 1 * d)
  simpa only [tsum_fintype, map_one, one_mul] using ht

theorem calibrationForSet_gauss (S : Finset (Ideal O)) (hS : ∀ P ∈ S, P.IsMaximal)
    (h : O) :
    calibrationGauss (calibrationForSet S hS) h =
      star ((calibrationForSet S hS).residueMonoid h) *
        (Real.sqrt (elementNorm (calibrationForSet S hS).generator) : ℂ) *
        (calibrationForSet S hS).tau := by
  let C := calibrationForSet S hS
  let : Finite (O ⧸ Ideal.span {C.generator}) :=
    ConcreteTraceCRT.finite_quotient_span C.generator_ne_zero
  have hc : star (C.residueMonoid h) = (C.residueMonoid h)⁻¹ := by
    exact (MulChar.star_apply' C.residue (Ideal.Quotient.mk _ h)).trans
      (MulChar.inv_apply_eq_inv' _ _)
  have he : calibrationGauss C h = (C.residueMonoid h)⁻¹ * calibrationGauss C 1 := by
    let (P : S) : P.val.IsMaximal := hS P.val P.property
    unfold C calibrationForSet
    apply calibrationFromPrimes_gauss
  rw [he, calibrationGauss_one, ← hc]
  ring

theorem calibrationForSet_residue_sixth (S : Finset (Ideal O)) (hS : ∀ P ∈ S, P.IsMaximal)
    (a : O) (ha : IsCoprime (calibrationForSet S hS).generator a) :
    (calibrationForSet S hS).residueMonoid a ^ 6 = 1 := by
  let C := calibrationForSet S hS
  have hu := (isUnit_quotient_span_iff C.generator a).mpr ha
  have h6 := congrArg (fun χ : MulChar (O ⧸ Ideal.span {C.generator}) ℂ =>
    χ (Ideal.Quotient.mk _ a)) (calibrationForSet_pow_six S hS)
  change C.residue (Ideal.Quotient.mk _ a) ^ 6 = 1
  simpa only [MulChar.pow_apply' _ (by decide : (6 : ℕ) ≠ 0), MulChar.one_apply hu] using h6

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.CongruenceScalar
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePrimePower
open ActualEisensteinCubic CubicEisenstein GaussianShiftedPartition
local notation "O" => ActualEisensteinCubic.O

lemma exactQuotient_spec (a b : O) (h : b ∣ a) : a = b * exactQuotient a b h :=
  Classical.choose_spec h

end SevenEighths.ProbePrimePower
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.LiftedFourier
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePrimePower
open ActualEisensteinCubic CubicEisenstein GaussianShiftedPartition
local notation "O" => ActualEisensteinCubic.O

lemma quotientTrace_split_frequency (a b : O) (ha : a ≠ 0) (hb : b ≠ 0)
    (H d v : O) :
    quotientTrace (a*b) (mul_ne_zero ha hb) (Ideal.Quotient.mk _ ((H-b*d)*v)) =
      quotientTrace (a*b) (mul_ne_zero ha hb) (Ideal.Quotient.mk _ (H*v)) *
        quotientTrace a ha (Ideal.Quotient.mk _ ((-v)*d)) := by
  have hs := quotientTrace_conductor_scale a b ((-v)*d) ha hb 1
  simp only [mul_one, map_one] at hs
  rw [show (H-b*d)*v = H*v+b*((-v)*d) by ring, map_add, AddChar.map_add_eq_mul, hs]

end SevenEighths.ProbePrimePower
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.PhysicalFourier
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein GaussianShiftedPartition ProbePrimePower
local notation "O" => ActualEisensteinCubic.O

theorem rawFourier_exactQuotient (a s : O) (ha : a≠0) (hs : s≠0)
    (F : (O ⧸ Ideal.span {a}) → ℂ) (H : O) :
    conductorFourier a s ha hs F H =
      (Ideal.absNorm (Ideal.span {s}):ℂ) *
        (if h : s∣H then rawFourier a ha F (exactQuotient H s h) else 0) := by
  by_cases h : s∣H
  · rw [dif_pos h]
    conv_lhs => rw [exactQuotient_spec H s h]
    exact conductorFourier_lift a s ha hs F _
  · rw [dif_neg h, mul_zero]
    by_contra hn
    exact h (conductorFourier_support a s ha hs F H hn)

lemma trace_split_product (a s : O) (ha : a≠0) (hs : s≠0) (H m d : O) :
    quotientTrace (a*s) (mul_ne_zero ha hs) (Ideal.Quotient.mk _ (H*m)) *
      quotientTrace s hs (Ideal.Quotient.mk _ ((-m)*d)) =
    quotientTrace (a*s) (mul_ne_zero ha hs) (Ideal.Quotient.mk _ ((H-a*d)*m)) := by
  have he := quotientTrace_split_frequency s a hs ha H d m
  simp only [quotientTrace_mk] at he ⊢
  simpa only [mul_comm s a] using he.symm

theorem fullFourier_eq_congruence (a s : O) (ha : a≠0) (hs : s≠0)
    (F : (O ⧸ Ideal.span {a}) → ℂ) (χ : (O ⧸ Ideal.span {s}) → ℂ) (H : O) :
    fullFourier a s ha hs F χ H =
      (Ideal.absNorm (Ideal.span {s}):ℂ) * congruenceCoefficient a s ha F χ H := by
  let : Finite (O ⧸ Ideal.span {a*s}) := finite_quotient_span (mul_ne_zero ha hs)
  let : Finite (O ⧸ Ideal.span {s}) := finite_quotient_span hs
  let : Fintype (O ⧸ Ideal.span {a*s}) := Fintype.ofFinite _
  let : Fintype (O ⧸ Ideal.span {s}) := Fintype.ofFinite _
  unfold fullFourier rawFourier
  simp_rw [tsum_fintype, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  unfold congruenceCoefficient
  rw [tsum_fintype, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  calc
    _ = χ d * conductorFourier a s ha hs F (H-a*representative s d) := by
      rw [conductorFourier, tsum_fintype, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      have ht := trace_split_product a s ha hs H (representative (a*s) m) (representative s d)
      simp only [map_mul, representative_spec] at ht
      rw [← ht]
      ring
    _ = _ := by rw [rawFourier_exactQuotient]; ring

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.PhysicalCoefficient
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CubicEisenstein GaussianShiftedPartition CanonicalRowCompletion
local notation "O" => ActualEisensteinCubic.O

lemma calibratedNumerator_congr (C : CalibrationData) (A m n : O)
    (h : m-n ∈ (Ideal.span {C.generator*A} : Ideal O)) :
    calibratedNumerator C A m = calibratedNumerator C A n := by
  have hd : C.generator*A ∣ m-n := Ideal.mem_span_singleton.mp h
  have hb : Ideal.Quotient.mk (Ideal.span {C.generator}) m =
      Ideal.Quotient.mk (Ideal.span {C.generator}) n := by
    apply Ideal.Quotient.eq.mpr
    exact Ideal.mem_span_singleton.mpr ((dvd_mul_right C.generator A).trans hd)
  have hA : m-n ∈ (Ideal.span {A} : Ideal O) :=
    Ideal.mem_span_singleton.mpr ((dvd_mul_left A C.generator).trans hd)
  unfold calibratedNumerator CalibrationData.residueMonoid
  simp only [MonoidHom.comp_apply, RingHom.toMonoidHom_eq_coe,
    MonoidHom.coe_coe, hb, idealRowHom_congr_mod (Ideal.span {A}) m n hA]

lemma calibratedQuotient_mk (C : CalibrationData) (A m : O) :
    calibratedQuotient C A (Ideal.Quotient.mk _ m) = calibratedNumerator C A m := by
  apply calibratedNumerator_congr
  exact Ideal.Quotient.eq.mp (representative_spec _ _)

lemma rawFourier_outer (s : O) (hs : s≠0) (h : O) :
    rawFourier s hs (outerQuotient s) h = sexticGauss s hs h := rfl

theorem actualPhysicalFourier_eq (C : CalibrationData) (A s : O) (hA : A≠0) (hs : s≠0) (H : O) :
    actualPhysicalFourier C A s hA hs H =
      (Ideal.absNorm (Ideal.span {s}):ℂ) * actualCongruenceCoefficient C A s hA H := by
  unfold actualCongruenceCoefficient
  rw [← fullFourier_eq_congruence (C.generator*A) s (mul_ne_zero C.generator_ne_zero hA) hs]
  unfold actualPhysicalFourier fullFourier
  apply tsum_congr
  intro m
  rw [rawFourier_outer]
  have he : conductorReduction (C.generator*A) s m =
      Ideal.Quotient.mk (Ideal.span {C.generator*A}) (representative ((C.generator*A)*s) m) := by
    conv_lhs => rw [← representative_spec ((C.generator*A)*s) m]
    rfl
  rw [he, calibratedQuotient_mk]

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.CommonSupport
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentCommonSupport
open CenteredMomentCorrelation
variable {A : Type*} [CommRing A]

lemma residue_eq_zero_iff_dvd (d n : A) :
    Ideal.Quotient.mk (Ideal.span {d}) n = 0 ↔ d ∣ n := by
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]

end SevenEighths.CenteredMomentCommonSupport
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.Fourier
namespace OAI

noncomputable section
open scoped BigOperators Classical
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentFourier
open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT
open CenteredMomentCorrelation CenteredMomentCommonSupport CenteredMomentSupportedCorrelation

theorem quotientTrace_scaled (d a m : O) (hm : m = d * a)
    (hd : d ≠ 0) (ha : a ≠ 0) (hm0 : m ≠ 0)
    (h : Residue m) (x : Residue d) :
    quotientTrace m hm0 (h * scaledResidue d a m hm x) =
      quotientTrace d hd (frequencyReduction d m (hm ▸ dvd_mul_right d a) h * x) := by
  subst m
  obtain ⟨h, rfl⟩ := Ideal.Quotient.mk_surjective h
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  have ht := quotientTrace_conductor_scale d a h hd ha (Ideal.Quotient.mk _ x)
  simp only [scaledResidue_mk, frequencyReduction_mk, ← map_mul]
  simpa only [← map_mul, conductorReduction, Ideal.Quotient.factor_mk, mul_assoc,
    mul_left_comm, mul_comm] using ht

theorem residueGauss_supported_mk (d : O)
    (hd : CanonicalQuadraticSieve.Supported (Ideal.span {d})) (h : O) :
    residueGauss d (supported_element_ne_zero d hd) (supportedModulusCharacter d hd)
      (Ideal.Quotient.mk _ h) = ProbePhysical.sexticGauss d (supported_element_ne_zero d hd) h := by
  apply tsum_congr
  intro x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [supportedModulusCharacter_mk, ProbePhysical.sexticGauss_coefficient_mk]

end SevenEighths.CenteredMomentFourier
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FirstPoisson
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentFirstPoisson
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein EisensteinSchwartzPoisson
open CenteredMomentCorrelation CenteredMomentCommonSupport CenteredMomentFourier

lemma principalCRT_scaled_left (a b : O) (hcop : IsCoprime a b) (x : Residue a) :
    principalCRT a b hcop (scaledResidue a b (a * b) rfl x) =
      (Ideal.Quotient.mk _ b * x, 0) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [scaledResidue_mk, principalCRT_mk]
  have hb : Ideal.Quotient.mk (Ideal.span {b}) b = 0 :=
    (residue_eq_zero_iff_dvd b b).mpr dvd_rfl
  simp only [map_mul, hb, zero_mul]

lemma principalCRT_scaled_right (a b : O) (hcop : IsCoprime a b) (y : Residue b) :
    principalCRT a b hcop (scaledResidue b a (a * b) (mul_comm a b) y) =
      (0, Ideal.Quotient.mk _ a * y) := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [scaledResidue_mk, principalCRT_mk]
  have ha : Ideal.Quotient.mk (Ideal.span {a}) a = 0 :=
    (residue_eq_zero_iff_dvd a a).mpr dvd_rfl
  simp only [map_mul, ha, zero_mul]

end SevenEighths.CenteredMomentFirstPoisson
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.CalibrationCRT
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein
open CenteredMomentCorrelation CenteredMomentCommonSupport CenteredMomentFourier
open CenteredMomentFirstPoisson
local notation "O" => ActualEisensteinCubic.O

theorem coprime_mixed_fourier (a b : O) (ha : a ≠ 0) (hb : b ≠ 0)
    (hcop : IsCoprime a b)
    [Fintype (Residue a)] [Fintype (Residue b)] [Fintype (Residue (a * b))]
    (χa : MulChar (Residue a) ℂ) (F : Residue b → ℂ)
    (h : Residue (a * b)) :
    (∑ x : Residue (a * b),
      χa (frequencyReduction a (a * b) (dvd_mul_right a b) x) *
        F (frequencyReduction b (a * b) (dvd_mul_left b a) x) *
          quotientTrace (a * b) (mul_ne_zero ha hb) (h * x)) =
      χa (Ideal.Quotient.mk _ b) *
        residueGauss a ha χa (frequencyReduction a (a*b) (dvd_mul_right a b) h) *
        (∑ y : Residue b, F (Ideal.Quotient.mk _ a*y) *
          quotientTrace b hb (frequencyReduction b (a*b) (dvd_mul_left b a) h*y)) := by
  let ua := residueUnit a b hcop
  let ub := residueUnit b a hcop.symm
  let e : Residue a × Residue b ≃ Residue (a * b) :=
    (ua.mulLeft.prodCongr ub.mulLeft).trans (principalCRT a b hcop).toEquiv.symm
  have heproj (x : Residue a × Residue b) : principalCRT a b hcop (e x) =
      ((ua : Residue a) * x.1, (ub : Residue b) * x.2) := by
    change (principalCRT a b hcop).toEquiv
      ((principalCRT a b hcop).toEquiv.symm ((ua : Residue a) * x.1, (ub : Residue b) * x.2)) = _
    exact (principalCRT a b hcop).toEquiv.apply_symm_apply _
  have he (x : Residue a × Residue b) : e x =
      scaledResidue a b (a * b) rfl x.1 + scaledResidue b a (a * b) (mul_comm a b) x.2 := by
    apply (principalCRT a b hcop).injective
    rw [heproj, map_add, principalCRT_scaled_left, principalCRT_scaled_right]
    simp only [Prod.mk_add_mk, add_zero, zero_add, ua, ub, residueUnit_coe]
  have hproj (x : Residue (a * b)) :
      (frequencyReduction a (a * b) (dvd_mul_right a b) x,
        frequencyReduction b (a * b) (dvd_mul_left b a) x) = principalCRT a b hcop x := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp only [frequencyReduction_mk, principalCRT_mk]
  have hprojA (x : Residue a × Residue b) :
      frequencyReduction a (a * b) (dvd_mul_right a b) (e x) = Ideal.Quotient.mk _ b * x.1 := by
    have ht := congrArg Prod.fst (hproj (e x))
    rw [heproj] at ht
    simpa only [ua, residueUnit_coe] using ht
  have hprojB (x : Residue a × Residue b) :
      frequencyReduction b (a * b) (dvd_mul_left b a) (e x) = Ideal.Quotient.mk _ a * x.2 := by
    have ht := congrArg Prod.snd (hproj (e x))
    rw [heproj] at ht
    simpa only [ub, residueUnit_coe] using ht
  rw [← e.sum_comp]
  simp_rw [hprojA, hprojB]
  simp only [map_mul, he, mul_add, AddChar.map_add_eq_mul,
    quotientTrace_scaled a b (a * b) rfl ha hb (mul_ne_zero ha hb),
    quotientTrace_scaled b a (a * b) (mul_comm a b) hb ha (mul_ne_zero ha hb)]
  simp only [Fintype.sum_prod_type, residueGauss, tsum_fintype]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem calibration_mixed_fourier (S : Finset (Ideal O)) (hS : ∀ P∈S, P.IsMaximal)
    (b : O) (hb : b≠0) (hcop : IsCoprime (calibrationForSet S hS).generator b)
    (F : Residue b → ℂ) (H : O) :
    let C := calibrationForSet S hS
    (∑' x : Residue (C.generator*b),
      C.residue (frequencyReduction C.generator (C.generator*b) (dvd_mul_right _ _) x) *
        F (frequencyReduction b (C.generator*b) (dvd_mul_left _ _) x) *
        quotientTrace (C.generator*b) (mul_ne_zero C.generator_ne_zero hb) (Ideal.Quotient.mk _ H*x)) =
      C.residueMonoid b * star (C.residueMonoid H) * (Real.sqrt (elementNorm C.generator):ℂ) * C.tau *
        (∑' y : Residue b, F (Ideal.Quotient.mk _ C.generator*y) *
          quotientTrace b hb (Ideal.Quotient.mk _ H*y)) := by
  dsimp only
  let C := calibrationForSet S hS
  let := finite_quotient_span C.generator_ne_zero
  let := finite_quotient_span hb
  let := finite_quotient_span (mul_ne_zero C.generator_ne_zero hb)
  let : Fintype (Residue C.generator) := Fintype.ofFinite _
  let : Fintype (Residue b) := Fintype.ofFinite _
  let : Fintype (Residue (C.generator*b)) := Fintype.ofFinite _
  rw [tsum_fintype, coprime_mixed_fourier _ _ C.generator_ne_zero hb hcop]
  change C.residueMonoid b * calibrationGauss C H * _ = _
  rw [calibrationForSet_gauss]
  rw [tsum_fintype]
  dsimp only [C]
  simp only [frequencyReduction_mk]
  ring

theorem calibration_mixed_fourier_zero (S : Finset (Ideal O)) (hS : ∀ P∈S, P.IsMaximal)
    (b : O) (hb : b≠0) (hcop : IsCoprime (calibrationForSet S hS).generator b)
    (F : Residue b → ℂ) (H : O) (hH : ¬IsCoprime (calibrationForSet S hS).generator H) :
    let C := calibrationForSet S hS
    (∑' x : Residue (C.generator*b),
      C.residue (frequencyReduction C.generator (C.generator*b) (dvd_mul_right _ _) x) *
        F (frequencyReduction b (C.generator*b) (dvd_mul_left _ _) x) *
        quotientTrace (C.generator*b) (mul_ne_zero C.generator_ne_zero hb) (Ideal.Quotient.mk _ H*x)) = 0 := by
  dsimp only
  rw [calibration_mixed_fourier S hS b hb hcop F H]
  have hz : (calibrationForSet S hS).residueMonoid H=0 := by
    change (calibrationForSet S hS).residue (Ideal.Quotient.mk _ H)=0
    apply MulChar.map_nonunit
    exact fun h => hH ((isUnit_quotient_span_iff _ _).mp h)
  rw [hz, star_zero]
  ring

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.PhysicalPoisson
namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CubicEisenstein GaussianShiftedPartition ConcreteTraceCRT
open EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O

lemma sexticGauss_frequency_congr (s : O) (hs : s≠0) (h k : O)
    (he : h-k ∈ (Ideal.span {s}:Ideal O)) : sexticGauss s hs h = sexticGauss s hs k := by
  have hmk := Ideal.Quotient.eq.mpr he
  simp only [sexticGauss, hmk]

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.FrequencySupport
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CubicEisenstein GaussianShiftedPartition CanonicalRowCompletion
open CenteredMomentCommonSupport CenteredMomentFourier
local notation "O" => ActualEisensteinCubic.O

lemma elementFourier_congr (c d : O) (hc : c≠0) (hd : d≠0) (f : O → ℂ) (H : O)
    (he : c=d) : elementFourier c hc f H = elementFourier d hd f H := by
  subst d
  rfl

lemma movingQuotient_mk (A s : O) (hs : s≠0) (m : O) :
    movingQuotient A s hs (Ideal.Quotient.mk _ m) =
      idealRowHom m (Ideal.span {A}) * sexticGauss s hs (-m) := by
  have hd : A*s ∣ representative (A*s) (Ideal.Quotient.mk _ m)-m :=
    Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp (representative_spec _ _))
  have hA : representative (A*s) (Ideal.Quotient.mk _ m)-m ∈ (Ideal.span {A}:Ideal O) :=
    Ideal.mem_span_singleton.mpr ((dvd_mul_right A s).trans hd)
  have hs' : -representative (A*s) (Ideal.Quotient.mk _ m)-(-m) ∈ (Ideal.span {s}:Ideal O) := by
    apply Ideal.mem_span_singleton.mpr
    rw [show -representative (A*s) (Ideal.Quotient.mk _ m)-(-m) =
      -(representative (A*s) (Ideal.Quotient.mk _ m)-m) by ring]
    exact dvd_neg.mpr ((dvd_mul_left s A).trans hd)
  unfold movingQuotient
  rw [idealRowHom_congr_mod _ _ _ hA, sexticGauss_frequency_congr s hs _ (-m) hs']

lemma physicalFourier_eq_element (C : CalibrationData) (A s : O) (hA : A≠0) (hs : s≠0) (H : O) :
    actualPhysicalFourier C A s hA hs H =
      elementFourier (C.generator*(A*s)) (mul_ne_zero C.generator_ne_zero (mul_ne_zero hA hs))
        (fun m => C.residueMonoid m * idealRowHom m (Ideal.span {A}) * sexticGauss s hs (-m)) H := by
  change elementFourier ((C.generator*A)*s) (mul_ne_zero (mul_ne_zero C.generator_ne_zero hA) hs)
    (fun m => C.residueMonoid m * idealRowHom m (Ideal.span {A}) * sexticGauss s hs (-m)) H = _
  apply elementFourier_congr
  exact mul_assoc _ _ _

lemma physicalFourier_eq_mixed (C : CalibrationData) (A s : O) (hA : A≠0) (hs : s≠0) (H : O) :
    actualPhysicalFourier C A s hA hs H =
      ∑' x : Residue (C.generator*(A*s)),
        C.residue (frequencyReduction C.generator (C.generator*(A*s)) (dvd_mul_right _ _) x) *
          movingQuotient A s hs (frequencyReduction (A*s) (C.generator*(A*s)) (dvd_mul_left _ _) x) *
          quotientTrace (C.generator*(A*s)) (mul_ne_zero C.generator_ne_zero (mul_ne_zero hA hs))
            (Ideal.Quotient.mk _ H*x) := by
  rw [physicalFourier_eq_element]
  unfold elementFourier
  apply tsum_congr
  intro x
  have he : Ideal.Quotient.mk (Ideal.span {C.generator*(A*s)})
      (representative (C.generator*(A*s)) x) = x := representative_spec _ _
  have hrA : frequencyReduction C.generator (C.generator*(A*s)) (dvd_mul_right _ _) x =
      Ideal.Quotient.mk _ (representative (C.generator*(A*s)) x) := by
    conv_lhs => rw [← he]
    rfl
  have hrB : frequencyReduction (A*s) (C.generator*(A*s)) (dvd_mul_left _ _) x =
      Ideal.Quotient.mk _ (representative (C.generator*(A*s)) x) := by
    conv_lhs => rw [← he]
    rfl
  rw [hrA, hrB, movingQuotient_mk]
  change _ = (C.residueMonoid _ * (_ * _)) * _

  ring

theorem actualPhysicalFourier_zero_off_calibration (S : Finset (Ideal O))
    (hS : ∀ P∈S, P.IsMaximal) (A s : O) (hA : A≠0) (hs : s≠0)
    (hcop : IsCoprime (calibrationForSet S hS).generator (A*s)) (H : O)
    (hH : ¬IsCoprime (calibrationForSet S hS).generator H) :
    actualPhysicalFourier (calibrationForSet S hS) A s hA hs H=0 := by
  rw [physicalFourier_eq_mixed]
  exact calibration_mixed_fourier_zero S hS (A*s) (mul_ne_zero hA hs) hcop (movingQuotient A s hs) H hH

theorem actualCongruenceCoefficient_zero_off_calibration (S : Finset (Ideal O))
    (hS : ∀ P∈S, P.IsMaximal) (A s : O) (hA : A≠0) (hs : s≠0)
    (hcop : IsCoprime (calibrationForSet S hS).generator (A*s)) (H : O)
    (hH : ¬IsCoprime (calibrationForSet S hS).generator H) :
    actualCongruenceCoefficient (calibrationForSet S hS) A s hA H=0 := by
  have he := actualPhysicalFourier_zero_off_calibration S hS A s hA hs hcop H hH
  rw [actualPhysicalFourier_eq] at he
  have hn : (Ideal.absNorm (Ideal.span {s}):ℂ)≠0 := by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hs)
  exact (mul_eq_zero.mp he).resolve_left hn

end SevenEighths.ProbePhysical
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

theorem CalibrationData.Xi_norm_one (C : CalibrationData) (a : O)
    (ha : Supported (Ideal.span {a})) (hcop : IsCoprime C.generator a) :
    ‖C.Xi a‖ = 1 := by
  let : Finite (O ⧸ Ideal.span {C.generator}) :=
    ConcreteTraceCRT.finite_quotient_span C.generator_ne_zero
  let : Fintype (O ⧸ Ideal.span {C.generator}) := Fintype.ofFinite _
  have hu := (CubicEisenstein.isUnit_quotient_span_iff C.generator a).mpr hcop
  have hξ : ‖C.residueMonoid a‖ = 1 := by
    exact (FiniteRayExpansion.norm_char_unit C.residue hu.unit)
  have hc : IsCoprime (Ideal.span {a} : Ideal O) (Ideal.span {C.generator}) :=
    (Ideal.isCoprime_span_singleton_iff a C.generator).mpr hcop.symm
  have h6 := idealRowHom_sixth_mask C.generator (Ideal.span {a}) ha
  rw [idealRowHom_argument_pow _ _ _ ha, if_pos hc] at h6
  change ‖C.residueMonoid a * idealRowHom C.generator (Ideal.span {a})‖ = 1
  rw [norm_mul, hξ, Complex.norm_eq_one_of_pow_eq_one h6 (by decide : (6 : ℕ) ≠ 0), mul_one]

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.CalibrationRemoval
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CubicEisenstein GaussianShiftedPartition CanonicalRowCompletion
open CanonicalQuadraticSieve ConcreteTraceCRT
open CenteredMomentCommonSupport CenteredMomentFourier CenteredMomentSupportedCorrelation
local notation "O" => ActualEisensteinCubic.O

lemma sexticGauss_unit_scale (s : O) (hs : Supported (Ideal.span {s}))
    (b h : O) (hcop : IsCoprime b s) :
    sexticGauss s (supportedElement_ne_zero s hs) (b*h) =
      (idealRowHom b (Ideal.span {s}))⁻¹ * sexticGauss s (supportedElement_ne_zero s hs) h := by
  let := finite_quotient_span (supportedElement_ne_zero s hs)
  let : Fintype (Residue s) := Fintype.ofFinite _
  let χ := supportedModulusCharacter s hs
  let ψ := quotientTrace s (supportedElement_ne_zero s hs)
  let u := residueUnit s b hcop.symm
  have he := gaussSum_mulShift_eq χ (ψ.mulShift (Ideal.Quotient.mk _ h)) u
  simp only [gaussSum, AddChar.mulShift_apply, MulChar.inv_apply_eq_inv', u, residueUnit_coe,
    χ, supportedModulusCharacter_mk] at he
  rw [← residueGauss_supported_mk s hs (b*h), ← residueGauss_supported_mk s hs h]
  simp only [residueGauss, tsum_fintype, map_mul]
  simpa only [ψ, mul_assoc, mul_comm, mul_left_comm] using he

lemma movingQuotient_unit_scale (A s : O) (hs : Supported (Ideal.span {s}))
    (b : O) (hcop : IsCoprime b s) (x : Residue (A*s)) :
    movingQuotient A s (supportedElement_ne_zero s hs) (Ideal.Quotient.mk _ b*x) =
      idealRowHom b (Ideal.span {A}) * (idealRowHom b (Ideal.span {s}))⁻¹ *
        movingQuotient A s (supportedElement_ne_zero s hs) x := by
  obtain ⟨m,rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [← map_mul, movingQuotient_mk, movingQuotient_mk, idealRowHom_argument_mul]
  rw [show -(b*m)=b*(-m) by ring, sexticGauss_unit_scale s hs b (-m) hcop]
  ring

theorem actualPhysicalFourier_calibration_factor (S : Finset (Ideal O))
    (hS : ∀ P∈S, P.IsMaximal) (A s : O) (hA : A≠0)
    (hs : Supported (Ideal.span {s}))
    (hcop : IsCoprime (calibrationForSet S hS).generator (A*s)) (H : O) :
    let C := calibrationForSet S hS
    actualPhysicalFourier C A s hA (supportedElement_ne_zero s hs) H =
      (C.residueMonoid (A*s) * star (C.residueMonoid H) *
        (Real.sqrt (elementNorm C.generator):ℂ) * C.tau *
        idealRowHom C.generator (Ideal.span {A}) * (idealRowHom C.generator (Ideal.span {s}))⁻¹) *
      barePhysicalFourier A s hA (supportedElement_ne_zero s hs) H := by
  dsimp only
  let C := calibrationForSet S hS
  have hcs : IsCoprime C.generator s := hcop.of_mul_right_right
  rw [physicalFourier_eq_mixed, calibration_mixed_fourier S hS (A*s)
    (mul_ne_zero hA (supportedElement_ne_zero s hs)) hcop]
  dsimp only [C] at hcs ⊢
  simp_rw [movingQuotient_unit_scale A s hs (calibrationForSet S hS).generator hcs]
  simp only [mul_assoc, tsum_mul_left]
  rfl

lemma barePhysicalFourier_eq (A s : O) (hA : A≠0) (hs : s≠0) (H : O) :
    barePhysicalFourier A s hA hs H =
      (Ideal.absNorm (Ideal.span {s}):ℂ)*bareCongruenceCoefficient A s hA H := by
  unfold bareCongruenceCoefficient
  rw [← fullFourier_eq_congruence A s hA hs]
  unfold barePhysicalFourier elementFourier fullFourier
  apply tsum_congr
  intro m
  rw [rawFourier_outer]
  have he : conductorReduction A s m = Ideal.Quotient.mk (Ideal.span {A}) (representative (A*s) m) := by
    conv_lhs => rw [← representative_spec (A*s) m]
    rfl
  rw [he]
  unfold outerQuotient
  rw [sexticGauss_coefficient_mk]

theorem actualCongruenceCoefficient_calibration_factor (S : Finset (Ideal O))
    (hS : ∀ P∈S, P.IsMaximal) (A s : O) (hA : A≠0)
    (hs : Supported (Ideal.span {s}))
    (hcop : IsCoprime (calibrationForSet S hS).generator (A*s)) (H : O) :
    let C := calibrationForSet S hS
    actualCongruenceCoefficient C A s hA H =
      (C.residueMonoid (A*s) * star (C.residueMonoid H) *
        (Real.sqrt (elementNorm C.generator):ℂ) * C.tau *
        idealRowHom C.generator (Ideal.span {A}) * (idealRowHom C.generator (Ideal.span {s}))⁻¹) *
      bareCongruenceCoefficient A s hA H := by
  dsimp only
  have he := actualPhysicalFourier_calibration_factor S hS A s hA hs hcop H
  dsimp only at he
  rw [actualPhysicalFourier_eq, barePhysicalFourier_eq] at he
  have hn : (Ideal.absNorm (Ideal.span {s}):ℂ)≠0 := by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr (supportedElement_ne_zero s hs))
  apply mul_left_cancel₀ hn
  rw [he]
  ring

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.CalibrationCancellation
namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CanonicalRowCompletion CanonicalQuadraticSieve CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

lemma Xi_apply (C : CalibrationData) (a : O) :
    C.Xi a = C.residueMonoid a * idealRowHom C.generator (Ideal.span {a}) := rfl

theorem calibration_coefficient_cancel (S : Finset (Ideal O)) (hS : ∀ P∈S, P.IsMaximal)
    (A s : O) (hA : Supported (Ideal.span {A})) (hs : Supported (Ideal.span {s}))
    (hcop : IsCoprime (calibrationForSet S hS).generator (A*s)) (H : O)
    (hH : IsCoprime (calibrationForSet S hS).generator H) :
    let C := calibrationForSet S hS
    actualCongruenceCoefficient C A s (supportedElement_ne_zero A hA) H *
      idealRowHom C.generator (Ideal.span {s}) /
        ((Real.sqrt (elementNorm C.generator):ℂ)*C.tau*C.residueMonoid s*star (C.residueMonoid H)) *
      (C.Xi A)⁻¹ = bareCongruenceCoefficient A s (supportedElement_ne_zero A hA) H := by
  dsimp only
  let C := calibrationForSet S hS
  have hcA : IsCoprime C.generator A := hcop.of_mul_right_left
  have hcs : IsCoprime C.generator s := hcop.of_mul_right_right
  have hXA : C.Xi A≠0 := by
    intro h
    have hn := C.Xi_norm_one A hA hcA
    rw [h, norm_zero] at hn
    norm_num at hn
  have hXs : C.Xi s≠0 := by
    intro h
    have hn := C.Xi_norm_one s hs hcs
    rw [h, norm_zero] at hn
    norm_num at hn
  rw [Xi_apply] at hXA hXs
  have hηA := left_ne_zero_of_mul hXA
  have hκA := right_ne_zero_of_mul hXA
  have hηs := left_ne_zero_of_mul hXs
  have hκs := right_ne_zero_of_mul hXs
  have hηH : C.residueMonoid H≠0 :=
    C.residue.apply_ne_zero_iff.mpr ((isUnit_quotient_span_iff C.generator H).mpr hH)
  have hηHstar : star (C.residueMonoid H)≠0 := star_ne_zero.mpr hηH
  have hτ : C.tau≠0 := calibrationForSet_tau_ne_zero S hS
  have hq : 0<elementNorm C.generator := by
    unfold elementNorm
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr C.generator_ne_zero))
  have hroot : (Real.sqrt (elementNorm C.generator):ℂ)≠0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hq).ne'
  have he := actualCongruenceCoefficient_calibration_factor S hS A s
    (supportedElement_ne_zero A hA) hs hcop H
  dsimp only at he
  rw [he, Xi_apply, map_mul]
  change _ = bareCongruenceCoefficient A s (supportedElement_ne_zero A hA) H
  dsimp only [C] at hηA hκA hηs hκs hηHstar hτ hroot
  field_simp

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.SourceCoefficient
namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open ProbePhase ProbeRow ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O

theorem sourceHighCoefficient_eq_bare (S : Finset (Ideal O)) (hS : ∀ P∈S,P.IsMaximal)
    (η : HeckeFamily.Character) (I : Ideal O) (hI : primaryGenerator I≠0)
    (A s : O) (hA : Supported (Ideal.span {A})) (hs : Supported (Ideal.span {s}))
    (hcop : IsCoprime (calibrationForSet S hS).generator (A*s)) (u a : O)
    (hH : IsCoprime (calibrationForSet S hS).generator (u*a^6)) :
    sourceHighCoefficient (calibrationForSet S hS) η I hI A s (supportedElement_ne_zero A hA) u a =
      bareSourceCoefficient η I hI A s (supportedElement_ne_zero A hA) (u*a^6) := by
  let C := calibrationForSet S hS
  have ha : IsCoprime C.generator a :=
    hH.of_isCoprime_of_dvd_right (by refine ⟨u*a^5,?_⟩; ring)
  have hval : C.residueMonoid (u*a^6)=C.residueMonoid u := by
    rw [map_mul,map_pow,calibrationForSet_residue_sixth S hS a ha,mul_one]
  have he := calibration_coefficient_cancel S hS A s hA hs hcop (u*a^6) hH
  dsimp only at he
  dsimp only [C] at hval
  rw [hval] at he
  unfold sourceHighCoefficient bareSourceCoefficient correctedFiniteCoefficient reciprocityCoefficient
  simp only [star_mul]
  calc
    _ = (actualCongruenceCoefficient (calibrationForSet S hS) A s (supportedElement_ne_zero A hA) (u*a^6) *
      idealRowHom (calibrationForSet S hS).generator (Ideal.span {s}) /
      ((Real.sqrt (elementNorm (calibrationForSet S hS).generator):ℂ)*(calibrationForSet S hS).tau*
       (calibrationForSet S hS).residueMonoid s*star ((calibrationForSet S hS).residueMonoid u)) *
      ((calibrationForSet S hS).Xi A)⁻¹) *
      (gaussTwo I hI * star (G A) * star (FiniteGaussPhase.angularFactor A) *
        targetMonoid η A * reciprocitySign A s) := by ring
    _ = _ := by rw [he]; ring

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.CoefficientDirect
namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve ProbeRow ProbePhase
local notation "O" => ActualEisensteinCubic.O

lemma div_mul_frequency_cancel (a b c m : ℂ) (hc : c≠0) :
    c*(a/(b*c)*m)=a/b*m := by
  simp only [div_eq_mul_inv,mul_inv_rev]
  calc
    _ = (c*c⁻¹)*(a*b⁻¹*m) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hc,one_mul]

theorem calibratedHighCoefficient_eq_bare_oai (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal)
    (η : HeckeFamily.Character) (I : Ideal O) (hI : primaryGenerator I≠0)
    (A s : O) (hA : Supported (Ideal.span {A})) (hs : Supported (Ideal.span {s}))
    (hcop : IsCoprime (calibrationForSet S hS).generator (A*s)) (H : O) :
    calibratedHighCoefficient (calibrationForSet S hS) η I hI A s (supportedElement_ne_zero A hA) H=
      star ((calibrationForSet S hS).residueMonoid H)*
        bareSourceCoefficient η I hI A s (supportedElement_ne_zero A hA) H := by
  let C := calibrationForSet S hS
  by_cases hH : IsCoprime C.generator H
  · have hn : star (C.residueMonoid H)≠0 := by
      apply star_ne_zero.mpr
      exact C.residue.apply_ne_zero_iff.mpr ((CubicEisenstein.isUnit_quotient_span_iff C.generator H).mpr hH)
    have he := sourceHighCoefficient_eq_bare S hS η I hI A s hA hs hcop H 1 (by simpa using hH)
    simp only [one_pow,mul_one] at he
    rw [←he]
    unfold sourceHighCoefficient calibratedHighCoefficient
    simp only [one_pow,mul_one]
    symm
    convert (preTransparency := .instances) div_mul_frequency_cancel
      (actualCongruenceCoefficient C A s (supportedElement_ne_zero A hA) H * idealRowHom C.generator (Ideal.span {s}))
      ((Real.sqrt (elementNorm C.generator):ℂ)*C.tau*C.residueMonoid s)
      (star (C.residueMonoid H))
      (gaussTwo I hI*star (FiniteGaussPhase.angularFactor A*ProbePhase.G A)*targetMonoid η A*(C.Xi A)⁻¹*reciprocitySign A s)
      hn using 1 <;> dsimp only [C] <;> ring
  · have hz := actualCongruenceCoefficient_zero_off_calibration S hS A s
      (supportedElement_ne_zero A hA) (supportedElement_ne_zero s hs) hcop H hH
    have hξ : C.residueMonoid H=0 := by
      change C.residue (Ideal.Quotient.mk _ H)=0
      apply MulChar.map_nonunit
      exact fun h=>hH ((CubicEisenstein.isUnit_quotient_span_iff _ _).mp h)
    dsimp only [C] at hξ
    simp only [calibratedHighCoefficient,hz,zero_mul,zero_div,hξ,star_zero]

end SevenEighths.ProbePhysical
end

end OAI
end

theorem solution : type_of% @OAI.SevenEighths.ProbePhysical.calibratedHighCoefficient_eq_bare_oai := @OAI.SevenEighths.ProbePhysical.calibratedHighCoefficient_eq_bare_oai
