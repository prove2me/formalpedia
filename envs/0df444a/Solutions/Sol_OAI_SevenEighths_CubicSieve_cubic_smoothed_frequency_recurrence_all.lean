-- Prove2me | solution 1 for OAI.SevenEighths.CubicSieve.cubic_smoothed_frequency_recurrence_all
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T02:58:12.352947+00:00
-- url     : https://prove2.me/submissions/bcc1beae-0576-4846-8af1-b0400a867d8a

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIHecke78B023
import Theorems.Thm_OAI_SevenEighths_CubicSieve_frequencyMajorant_summable

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.ChineseRemainder
namespace OAI

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
noncomputable section
open Finset Complex

open scoped Classical

open scoped Classical

namespace IdealGaussCRT

variable {T R S : Type*} [CommRing T] [CommRing R] [CommRing S]

theorem addChar_crt_factor (e : T ≃+* R × S) (ψ : AddChar T ℂ) (x : T) :
    ψ x = leftAddChar e ψ (e x).1 * rightAddChar e ψ (e x).2 := by
  let z := e x
  have hz : (z.1, (0 : S)) + ((0 : R), z.2) = z := by ext <;> simp
  calc
    ψ x = ψ (e.symm z) := by simp [z]
    _ = ψ (e.symm (z.1, 0) + e.symm (0, z.2)) := by rw [← map_add, hz]
    _ = _ := by rw [AddChar.map_add_eq_mul]; rfl

theorem gauss_sum_crt [Fintype T] [Fintype R] [Fintype S]
    (e : T ≃+* R × S) (χR : MulChar R ℂ) (χS : MulChar S ℂ)
    (ψ : AddChar T ℂ) :
    (∑ x : T, χR (e x).1 * χS (e x).2 * ψ x) =
      gaussSum χR (leftAddChar e ψ) * gaussSum χS (rightAddChar e ψ) := by
  simp_rw [addChar_crt_factor e ψ]
  let F : R × S → ℂ := fun z =>
    χR z.1 * χS z.2 * leftAddChar e ψ z.1 * rightAddChar e ψ z.2
  calc
    (∑ x : T,
      χR (e x).1 * χS (e x).2 *
        (leftAddChar e ψ (e x).1 * rightAddChar e ψ (e x).2)) =
        ∑ x : T, F (e x) := by congr 1; ext x; simp [F]; ring
    _ = ∑ z : R × S, F z := Equiv.sum_comp e.toEquiv F
    _ = ∑ z : R, ∑ w : S, F (z, w) := Fintype.sum_prod_type F
    _ = gaussSum χR (leftAddChar e ψ) * gaussSum χS (rightAddChar e ψ) := by
      simp only [F, gaussSum]
      rw [Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro z hz
      apply Finset.sum_congr rfl
      intro w hw
      ring

theorem gauss_sum_ideal_crt {A : Type*} [CommRing A]
    (I J : Ideal A) (h : IsCoprime I J)
    [Fintype (A ⧸ I * J)] [Fintype (A ⧸ I)] [Fintype (A ⧸ J)]
    (χI : MulChar (A ⧸ I) ℂ) (χJ : MulChar (A ⧸ J) ℂ)
    (ψ : AddChar (A ⧸ I * J) ℂ) :
    (∑ x : A ⧸ I * J,
      χI (Ideal.Quotient.factor (Ideal.mul_le_left : I * J ≤ I) x) *
      χJ (Ideal.Quotient.factor (Ideal.mul_le_right : I * J ≤ J) x) * ψ x) =
      gaussSum χI (leftAddChar (Ideal.quotientMulEquivQuotientProd I J h) ψ) *
      gaussSum χJ (rightAddChar (Ideal.quotientMulEquivQuotientProd I J h) ψ) := by
  let e := Ideal.quotientMulEquivQuotientProd I J h
  convert (preTransparency := .instances) gauss_sum_crt e χI χJ ψ using 1
  congr 1
  ext x
  simp only [e, Ideal.quotientMulEquivQuotientProd_fst,
    Ideal.quotientMulEquivQuotientProd_snd]

theorem crt_left_inverse_coordinate {A : Type*} [CommRing A]
    {a b u v : A} (hbez : u * a + v * b = 1) (x : A) :
    (Ideal.quotientMulEquivQuotientProd
      (Ideal.span {a}) (Ideal.span {b})
      (principal_coprime_of_bezout hbez)).symm
        (Ideal.Quotient.mk (Ideal.span {a}) x, 0) =
      Ideal.Quotient.mk ((Ideal.span {a}) * (Ideal.span {b})) (x * v * b) := by
  let I : Ideal A := Ideal.span {a}
  let J : Ideal A := Ideal.span {b}
  let e := Ideal.quotientMulEquivQuotientProd I J
    (principal_coprime_of_bezout hbez)
  apply e.injective
  apply Prod.ext
  · change (e (e.symm (Ideal.Quotient.mk I x, 0))).1 =
      (e (Ideal.Quotient.mk (I * J) (x * v * b))).1
    rw [e.apply_symm_apply]
    simp only [e, Ideal.quotientMulEquivQuotientProd_fst,
      Ideal.Quotient.factor_mk]
    apply Ideal.Quotient.eq.mpr
    change x - x * v * b ∈ I
    rw [Ideal.mem_span_singleton]
    refine ⟨x * u, ?_⟩
    calc
      x - x * v * b = x * (u * a + v * b) - x * v * b := by rw [hbez]; ring
      _ = a * (x * u) := by ring
  · change (e (e.symm (Ideal.Quotient.mk I x, 0))).2 =
      (e (Ideal.Quotient.mk (I * J) (x * v * b))).2
    rw [e.apply_symm_apply]
    simp only [e, Ideal.quotientMulEquivQuotientProd_snd,
      Ideal.Quotient.factor_mk]
    symm
    apply (Ideal.Quotient.eq_zero_iff_mem).mpr
    exact Ideal.mem_span_singleton.mpr ⟨x * v, by ring⟩

theorem crt_right_inverse_coordinate {A : Type*} [CommRing A]
    {a b u v : A} (hbez : u * a + v * b = 1) (y : A) :
    (Ideal.quotientMulEquivQuotientProd
      (Ideal.span {a}) (Ideal.span {b})
      (principal_coprime_of_bezout hbez)).symm
        (0, Ideal.Quotient.mk (Ideal.span {b}) y) =
      Ideal.Quotient.mk ((Ideal.span {a}) * (Ideal.span {b})) (y * u * a) := by
  let I : Ideal A := Ideal.span {a}
  let J : Ideal A := Ideal.span {b}
  let e := Ideal.quotientMulEquivQuotientProd I J
    (principal_coprime_of_bezout hbez)
  apply e.injective
  apply Prod.ext
  · change (e (e.symm (0, Ideal.Quotient.mk J y))).1 =
      (e (Ideal.Quotient.mk (I * J) (y * u * a))).1
    rw [e.apply_symm_apply]
    simp only [e, Ideal.quotientMulEquivQuotientProd_fst,
      Ideal.Quotient.factor_mk]
    symm
    apply (Ideal.Quotient.eq_zero_iff_mem).mpr
    exact Ideal.mem_span_singleton.mpr ⟨y * u, by ring⟩
  · change (e (e.symm (0, Ideal.Quotient.mk J y))).2 =
      (e (Ideal.Quotient.mk (I * J) (y * u * a))).2
    rw [e.apply_symm_apply]
    simp only [e, Ideal.quotientMulEquivQuotientProd_snd,
      Ideal.Quotient.factor_mk]
    apply Ideal.Quotient.eq.mpr
    change y - y * u * a ∈ J
    rw [Ideal.mem_span_singleton]
    refine ⟨y * v, ?_⟩
    calc
      y - y * u * a = y * (u * a + v * b) - y * u * a := by rw [hbez]; ring
      _ = b * (y * v) := by ring

theorem leftAddChar_traceProd {A : Type*} [CommRing A]
    (ι : A →+* ℂ) (ψ : AddChar ℂ ℂ) (lam : ℂ)
    {a b u v : A} (hbez : u * a + v * b = 1)
    (ha : ι a ≠ 0) (hb : ι b ≠ 0) (hlam : lam ≠ 0)
    (hbase : ∀ x : A, ψ (ι x / lam) = 1) :
    leftAddChar
      (Ideal.quotientMulEquivQuotientProd (Ideal.span {a}) (Ideal.span {b})
        (principal_coprime_of_bezout hbez))
      (traceProdChar ι ψ lam a b ha hb hlam hbase) =
      (traceModChar ι ψ lam a ha hlam hbase).mulShift
        (Ideal.Quotient.mk (Ideal.span {a}) v) := by
  ext z
  refine Quotient.inductionOn' z ?_
  intro x
  change traceProdChar ι ψ lam a b ha hb hlam hbase
      ((Ideal.quotientMulEquivQuotientProd (Ideal.span {a}) (Ideal.span {b})
        (principal_coprime_of_bezout hbez)).symm
        (Ideal.Quotient.mk (Ideal.span {a}) x, 0)) =
    (traceModChar ι ψ lam a ha hlam hbase).mulShift
      (Ideal.Quotient.mk (Ideal.span {a}) v)
      (Ideal.Quotient.mk (Ideal.span {a}) x)
  rw [crt_left_inverse_coordinate hbez x]
  simp only [traceProdChar_mk, AddChar.mulShift_apply, ← map_mul,
    traceModChar_mk]
  congr 1
  simp only [map_mul]
  field_simp

theorem rightAddChar_traceProd {A : Type*} [CommRing A]
    (ι : A →+* ℂ) (ψ : AddChar ℂ ℂ) (lam : ℂ)
    {a b u v : A} (hbez : u * a + v * b = 1)
    (ha : ι a ≠ 0) (hb : ι b ≠ 0) (hlam : lam ≠ 0)
    (hbase : ∀ x : A, ψ (ι x / lam) = 1) :
    rightAddChar
      (Ideal.quotientMulEquivQuotientProd (Ideal.span {a}) (Ideal.span {b})
        (principal_coprime_of_bezout hbez))
      (traceProdChar ι ψ lam a b ha hb hlam hbase) =
      (traceModChar ι ψ lam b hb hlam hbase).mulShift
        (Ideal.Quotient.mk (Ideal.span {b}) u) := by
  ext z
  refine Quotient.inductionOn' z ?_
  intro y
  change traceProdChar ι ψ lam a b ha hb hlam hbase
      ((Ideal.quotientMulEquivQuotientProd (Ideal.span {a}) (Ideal.span {b})
        (principal_coprime_of_bezout hbez)).symm
        (0, Ideal.Quotient.mk (Ideal.span {b}) y)) =
    (traceModChar ι ψ lam b hb hlam hbase).mulShift
      (Ideal.Quotient.mk (Ideal.span {b}) u)
      (Ideal.Quotient.mk (Ideal.span {b}) y)
  rw [crt_right_inverse_coordinate hbez y]
  simp only [traceProdChar_mk, AddChar.mulShift_apply, ← map_mul,
    traceModChar_mk]
  congr 1
  simp only [map_mul]
  field_simp

theorem bezout_inverse_right {A : Type*} [CommRing A]
    {a b u v : A} (hbez : u * a + v * b = 1) :
    (Ideal.Quotient.mk (Ideal.span {b}) a) *
      (Ideal.Quotient.mk (Ideal.span {b}) u) = 1 := by
  rw [← map_mul]
  apply Ideal.Quotient.eq.mpr
  change a * u - 1 ∈ Ideal.span {b}
  rw [Ideal.mem_span_singleton]
  refine ⟨-v, ?_⟩
  calc
    a * u - 1 = a * u - (u * a + v * b) := by rw [hbez]
    _ = b * -v := by ring

theorem gauss_shift_bezout_right {A : Type*} [CommRing A]
    {a b u v : A} [Fintype (A ⧸ Ideal.span {b})]
    (hbez : u * a + v * b = 1)
    (χ : MulChar (A ⧸ Ideal.span {b}) ℂ)
    (ψ : AddChar (A ⧸ Ideal.span {b}) ℂ) :
    gaussSum χ (ψ.mulShift (Ideal.Quotient.mk (Ideal.span {b}) u)) =
      χ (Ideal.Quotient.mk (Ideal.span {b}) a) * gaussSum χ ψ := by
  let ma := Ideal.Quotient.mk (Ideal.span {b}) a
  let mu := Ideal.Quotient.mk (Ideal.span {b}) u
  have hprod : ma * mu = 1 := bezout_inverse_right hbez
  have hu : IsUnit mu := IsUnit.of_mul_eq_one_right ma hprod
  have hχ : χ ma * χ mu = 1 := by rw [← map_mul, hprod, map_one]
  have hshift := gaussSum_mulShift χ ψ hu.unit
  have hshift' : χ mu * gaussSum χ (ψ.mulShift mu) = gaussSum χ ψ := by
    simpa only [hu.unit_spec] using hshift
  calc
    gaussSum χ (ψ.mulShift mu) =
        (χ ma * χ mu) * gaussSum χ (ψ.mulShift mu) := by rw [hχ, one_mul]
    _ = χ ma * (χ mu * gaussSum χ (ψ.mulShift mu)) := by ring
    _ = χ ma * gaussSum χ ψ := by rw [hshift']

theorem gauss_sum_trace_crt {A : Type*} [CommRing A]
    (ι : A →+* ℂ) (ψ : AddChar ℂ ℂ) (lam : ℂ)
    {a b u v : A} (hbez : u * a + v * b = 1)
    [Fintype (A ⧸ (Ideal.span {a}) * (Ideal.span {b}))]
    [Fintype (A ⧸ Ideal.span {a})]
    [Fintype (A ⧸ Ideal.span {b})]
    (ha : ι a ≠ 0) (hb : ι b ≠ 0) (hlam : lam ≠ 0)
    (hbase : ∀ x : A, ψ (ι x / lam) = 1)
    (χa : MulChar (A ⧸ Ideal.span {a}) ℂ)
    (χb : MulChar (A ⧸ Ideal.span {b}) ℂ) :
    (∑ x : A ⧸ (Ideal.span {a}) * (Ideal.span {b}),
      χa (Ideal.Quotient.factor
        (Ideal.mul_le_left : (Ideal.span {a}) * (Ideal.span {b}) ≤ Ideal.span {a}) x) *
      χb (Ideal.Quotient.factor
        (Ideal.mul_le_right : (Ideal.span {a}) * (Ideal.span {b}) ≤ Ideal.span {b}) x) *
      traceProdChar ι ψ lam a b ha hb hlam hbase x) =
      χa (Ideal.Quotient.mk (Ideal.span {a}) b) *
      χb (Ideal.Quotient.mk (Ideal.span {b}) a) *
      gaussSum χa (traceModChar ι ψ lam a ha hlam hbase) *
      gaussSum χb (traceModChar ι ψ lam b hb hlam hbase) := by
  let e := Ideal.quotientMulEquivQuotientProd (Ideal.span {a})
    (Ideal.span {b}) (principal_coprime_of_bezout hbez)
  have h := gauss_sum_ideal_crt (Ideal.span {a}) (Ideal.span {b})
    (principal_coprime_of_bezout hbez) χa χb
    (traceProdChar ι ψ lam a b ha hb hlam hbase)
  rw [leftAddChar_traceProd ι ψ lam hbez ha hb hlam hbase,
      rightAddChar_traceProd ι ψ lam hbez ha hb hlam hbase,
      gauss_shift_bezout_left hbez χa (traceModChar ι ψ lam a ha hlam hbase),
      gauss_shift_bezout_right hbez χb (traceModChar ι ψ lam b hb hlam hbase)] at h
  calc
    _ = (χa (Ideal.Quotient.mk (Ideal.span {a}) b) *
          gaussSum χa (traceModChar ι ψ lam a ha hlam hbase)) *
        (χb (Ideal.Quotient.mk (Ideal.span {b}) a) *
          gaussSum χb (traceModChar ι ψ lam b hb hlam hbase)) := h
    _ = _ := by ring

theorem gauss_sum_trace_crt_of_coprime {A : Type*} [CommRing A]
    (ι : A →+* ℂ) (ψ : AddChar ℂ ℂ) (lam : ℂ)
    (a b : A)
    (hcop : IsCoprime (Ideal.span {a}) (Ideal.span {b}))
    [Fintype (A ⧸ (Ideal.span {a}) * (Ideal.span {b}))]
    [Fintype (A ⧸ Ideal.span {a})]
    [Fintype (A ⧸ Ideal.span {b})]
    (ha : ι a ≠ 0) (hb : ι b ≠ 0) (hlam : lam ≠ 0)
    (hbase : ∀ x : A, ψ (ι x / lam) = 1)
    (χa : MulChar (A ⧸ Ideal.span {a}) ℂ)
    (χb : MulChar (A ⧸ Ideal.span {b}) ℂ) :
    (∑ x : A ⧸ (Ideal.span {a}) * (Ideal.span {b}),
      χa (Ideal.Quotient.factor
        (Ideal.mul_le_left : (Ideal.span {a}) * (Ideal.span {b}) ≤ Ideal.span {a}) x) *
      χb (Ideal.Quotient.factor
        (Ideal.mul_le_right : (Ideal.span {a}) * (Ideal.span {b}) ≤ Ideal.span {b}) x) *
      traceProdChar ι ψ lam a b ha hb hlam hbase x) =
      χa (Ideal.Quotient.mk (Ideal.span {a}) b) *
      χb (Ideal.Quotient.mk (Ideal.span {b}) a) *
      gaussSum χa (traceModChar ι ψ lam a ha hlam hbase) *
      gaussSum χb (traceModChar ι ψ lam b hb hlam hbase) := by
  obtain ⟨u, v, hbez⟩ := bezout_of_principal_coprime hcop
  exact gauss_sum_trace_crt ι ψ lam hbez ha hb hlam hbase χa χb

end IdealGaussCRT

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Arithmetic.EisensteinEmbedding
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

namespace ConcreteTraceCRT

open EisensteinEmbedding IdealGaussCRT

theorem gauss_sum_actual_O
    (ψ : AddChar ℂ ℂ)
    (hperiod : ∀ c d : ℤ,
      ψ (((c : ℂ) + (d : ℂ) * omega3) / eisLam) = 1)
    (a b : O) (ha : a ≠ 0) (hb : b ≠ 0)
    (hcop : IsCoprime (Ideal.span {a}) (Ideal.span {b}))
    [Fintype (O ⧸ (Ideal.span {a}) * (Ideal.span {b}))]
    [Fintype (O ⧸ Ideal.span {a})]
    [Fintype (O ⧸ Ideal.span {b})]
    (χa : MulChar (O ⧸ Ideal.span {a}) ℂ)
    (χb : MulChar (O ⧸ Ideal.span {b}) ℂ) :
    (∑ x : O ⧸ (Ideal.span {a}) * (Ideal.span {b}),
      χa (Ideal.Quotient.factor
        (Ideal.mul_le_left : (Ideal.span {a}) * (Ideal.span {b}) ≤ Ideal.span {a}) x) *
      χb (Ideal.Quotient.factor
        (Ideal.mul_le_right : (Ideal.span {a}) * (Ideal.span {b}) ≤ Ideal.span {b}) x) *
      eisTraceProdChar ψ hperiod a b ha hb x) =
      χa (Ideal.Quotient.mk (Ideal.span {a}) b) *
      χb (Ideal.Quotient.mk (Ideal.span {b}) a) *
      gaussSum χa (eisTraceModChar ψ hperiod a ha) *
      gaussSum χb (eisTraceModChar ψ hperiod b hb) := by
  simpa only [eisTraceProdChar, eisTraceModChar] using
    gauss_sum_trace_crt_of_coprime eisEmbedding ψ eisLam a b hcop
      (eisEmbedding_ne_zero ha) (eisEmbedding_ne_zero hb)
      eisLam_ne_zero (eisPeriod ψ hperiod) χa χb

end ConcreteTraceCRT

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.SecondPoissonScale
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

namespace EisensteinSchwartzPoisson
open MeasureTheory Filter LineDeriv
open scoped FourierTransform SchwartzMap Real RealInnerProductSpace

theorem fourier_prod_eq_iterated (f : LogPlane → ℂ) (hf : Integrable f) (ξ η : ℝ) :
    𝓕 f (WithLp.toLp 2 (ξ, η)) =
      𝓕 (fun x : ℝ => 𝓕 (fun y : ℝ => f (WithLp.toLp 2 (x, y))) η) ξ := by
  let w : LogPlane := WithLp.toLp 2 (ξ, η)
  let G : LogPlane → ℂ := fun z => Real.fourierChar (-⟪z, w⟫) • f z
  have hG : Integrable G := (Real.fourierIntegral_convergent_iff w).mpr hf
  have hGp : Integrable (fun z : ℝ × ℝ => G (WithLp.toLp 2 z)) :=
    (WithLp.volume_preserving_toLp ℝ ℝ).integrable_comp_of_integrable hG
  calc
    𝓕 f (WithLp.toLp 2 (ξ, η)) = ∫ z : LogPlane, G z := rfl
    _ = ∫ z : ℝ × ℝ, G (WithLp.toLp 2 z) :=
      ((WithLp.volume_preserving_toLp ℝ ℝ).integral_comp
        (MeasurableEquiv.toLp 2 (ℝ × ℝ)).measurableEmbedding G).symm
    _ = ∫ x : ℝ, ∫ y : ℝ, G (WithLp.toLp 2 (x, y)) := integral_prod _ hGp
    _ = 𝓕 (fun x : ℝ => 𝓕 (fun y : ℝ => f (WithLp.toLp 2 (x, y))) η) ξ := by
      simp only [Real.fourier_eq, Circle.smul_def, smul_eq_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        dsimp only
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun y => by
          simp only [G, w, WithLp.prod_inner_apply,
            neg_add, Real.fourierChar.map_add_eq_mul, Circle.smul_def, smul_eq_mul,
            Circle.coe_mul, mul_assoc]

theorem verticalMajorant_integrable (f : SchwartzMap ℂ ℂ) : Integrable (verticalMajorant f) :=
  integrable_inv_one_add_sq.const_mul _

theorem norm_le_verticalMajorant (f : SchwartzMap ℂ ℂ) (x y : ℝ) :
    ‖f (complexPoint x y)‖ ≤ verticalMajorant f y := by
  have h0 := SchwartzMap.norm_le_seminorm ℝ f (complexPoint x y)
  have h2 := SchwartzMap.norm_pow_mul_le_seminorm ℝ f 2 (complexPoint x y)
  have hy : y ^ 2 ≤ ‖complexPoint x y‖ ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, complexPoint]
    nlinarith [sq_nonneg x]
  have hym := mul_le_mul_of_nonneg_right hy (norm_nonneg (f (complexPoint x y)))
  have hden : 0 < 1 + y ^ 2 := by positivity
  rw [verticalMajorant, ← div_eq_mul_inv]
  apply (le_div_iff₀ hden).mpr
  nlinarith

theorem partialFourier_continuous (f : SchwartzMap ℂ ℂ) (η : ℝ) :
    Continuous (partialFourier f η) := by
  change Continuous (fun x : ℝ => ∫ y : ℝ,
    Real.fourierChar (-inner ℝ y η) • f (complexPoint x y))
  apply continuous_of_dominated
    (bound := verticalMajorant f)
  · intro x
    have hline : Continuous (fun y : ℝ => complexPoint x y) :=
      Complex.equivRealProdCLM.symm.continuous.comp (continuous_const.prodMk continuous_id)
    exact ((by fun_prop : Continuous (fun y : ℝ => Real.fourierChar (-inner ℝ y η))).smul
      (f.continuous.comp hline)).aestronglyMeasurable
  · intro x
    exact Eventually.of_forall fun y => by
      simpa only [Circle.smul_def, smul_eq_mul, norm_mul, Circle.norm_coe, one_mul] using
        norm_le_verticalMajorant f x y
  · exact verticalMajorant_integrable f
  · exact Eventually.of_forall fun y => by
      have hf : Continuous (fun x : ℝ => f (complexPoint x y)) :=
        f.continuous.comp (horizontal_isometry y).continuous
      exact continuous_const.smul hf

theorem partialFourier_integrable (f : SchwartzMap ℂ ℂ) (η : ℝ) :
    Integrable (partialFourier f η) := by
  let G : ℂ → ℂ := fun z => Real.fourierChar (-inner ℝ z.im η) • f z
  have hG : Integrable G := f.integrable.norm.mono'
    (by fun_prop : Continuous G).aestronglyMeasurable
    (Eventually.of_forall fun z => by
      simp only [G, Circle.smul_def, smul_eq_mul, norm_mul, Circle.norm_coe, one_mul]
      exact le_rfl)
  have hGp : Integrable (fun z : ℝ × ℝ => G (Complex.measurableEquivRealProd.symm z)) :=
    Complex.volume_preserving_equiv_real_prod.symm.integrable_comp_of_integrable hG
  change Integrable (fun x : ℝ => ∫ y : ℝ,
    Real.fourierChar (-inner ℝ y η) • f (complexPoint x y))
  simpa only [G, Complex.measurableEquivRealProd_symm_apply, complexPoint]
    using hGp.integral_prod_left

theorem fourier_partialFourier (f : SchwartzMap ℂ ℂ) (ξ η : ℝ) :
    𝓕 (partialFourier f η) ξ = 𝓕 (f : ℂ → ℂ) (complexPoint ξ η) := by
  let fp : SchwartzMap LogPlane ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ planeComplexIso.toContinuousLinearEquiv f
  have hprod := fourier_prod_eq_iterated (fp : LogPlane → ℂ) fp.integrable ξ η
  have hcoe : (fp : LogPlane → ℂ) = (f : ℂ → ℂ) ∘ planeComplexIso := rfl
  rw [hcoe, Real.fourier_comp_linearIsometry] at hprod
  change 𝓕 (fun x : ℝ => 𝓕 (fun y : ℝ => f (complexPoint x y)) η) ξ = _
  simpa only [Function.comp_apply, planeComplexIso_apply] using hprod.symm

theorem partialFourierSchwartz_apply (f : SchwartzMap ℂ ℂ) (η x : ℝ) :
    partialFourierSchwartz f η x = partialFourier f η x := by
  have heq : 𝓕 (partialFourier f η) =
      (horizontalSlice (𝓕 f) η : ℝ → ℂ) := by
    funext ξ
    rw [fourier_partialFourier, horizontalSlice_apply]
    exact (congrFun (SchwartzMap.fourier_coe f) (complexPoint ξ η)).symm
  have hi : Integrable (𝓕 (partialFourier f η)) := by
    rw [heq]
    exact (horizontalSlice (𝓕 f) η).integrable
  change (𝓕⁻ (horizontalSlice (𝓕 f) η)) x = _
  rw [congrFun (SchwartzMap.fourierInv_coe (horizontalSlice (𝓕 f) η)) x, ← heq]
  exact (partialFourier_integrable f η).fourierInv_fourier_eq hi
    (partialFourier_continuous f η).continuousAt

theorem partialFourierSchwartz_coe (f : SchwartzMap ℂ ℂ) (η : ℝ) :
    (partialFourierSchwartz f η : ℝ → ℂ) = partialFourier f η :=
  funext (partialFourierSchwartz_apply f η)

theorem horizontal_hasFDerivAt (η x : ℝ) :
    HasFDerivAt (fun y : ℝ => complexPoint y η) Complex.ofRealCLM x := by
  have heq : (fun y : ℝ => complexPoint y η) =
      (fun y : ℝ => Complex.ofRealCLM y + Complex.I * (η : ℂ)) := by
    funext y
    exact complexPoint_eq y η
  rw [heq]
  exact Complex.ofRealCLM.hasFDerivAt.add_const _

theorem horizontalSlice_lineDerivOp (F : SchwartzMap ℂ ℂ) (η : ℝ) :
    ∂_{(1 : ℝ)} (horizontalSlice F η) = horizontalSlice (∂_{(1 : ℂ)} F) η := by
  apply SchwartzMap.ext
  intro x
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv, horizontalSlice_apply,
    SchwartzMap.lineDerivOp_apply_eq_fderiv]
  have hcomp := (F.hasFDerivAt (complexPoint x η)).comp x (horizontal_hasFDerivAt η x)
  change fderiv ℝ (fun y : ℝ => F (complexPoint y η)) x (1 : ℝ) = _
  change fderiv ℝ ((F : ℂ → ℂ) ∘ (fun y => complexPoint y η)) x (1 : ℝ) = _
  rw [hcomp.fderiv]
  simp only [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, Complex.ofReal_one]

theorem horizontalSlice_lineDerivOp_twice (F : SchwartzMap ℂ ℂ) (η : ℝ) :
    ∂_{(1 : ℝ)} (∂_{(1 : ℝ)} (horizontalSlice F η)) =
      horizontalSlice (∂_{(1 : ℂ)} (∂_{(1 : ℂ)} F)) η := by
  rw [horizontalSlice_lineDerivOp, horizontalSlice_lineDerivOp]

theorem summable_norm_of_cauchy_product (F : ℤ × ℤ → ℂ) (C : ℝ)
    (hF : ∀ p, ‖F p‖ ≤ C *
      ((1 + (p.1 : ℝ) ^ 2)⁻¹ * (1 + (p.2 : ℝ) ^ 2)⁻¹)) :
    Summable (fun p => ‖F p‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hF
    (summable_int_cauchy_product.mul_left C)

theorem plane_schwartz_product_decay (F : SchwartzMap ℂ ℂ) (ξ η : ℝ) :
    ((1 + ξ ^ 2) * (1 + η ^ 2)) * ‖F (complexPoint ξ η)‖ ≤
      planeDecayConstant F := by
  let z := complexPoint ξ η
  have hz : ‖z‖ ^ 2 = ξ ^ 2 + η ^ 2 := by
    rw [Complex.sq_norm]
    simp [z, Complex.normSq_apply, complexPoint, sq]
  have h0 := SchwartzMap.norm_le_seminorm ℝ F z
  have h2 := SchwartzMap.norm_pow_mul_le_seminorm ℝ F 2 z
  have h4 := SchwartzMap.norm_pow_mul_le_seminorm ℝ F 4 z
  have hz4 : ‖z‖ ^ 4 = (ξ ^ 2 + η ^ 2) ^ 2 := by
    calc
      ‖z‖ ^ 4 = (‖z‖ ^ 2) ^ 2 := by ring
      _ = (ξ ^ 2 + η ^ 2) ^ 2 := congrArg (fun t : ℝ => t ^ 2) hz
  have hxy : ξ ^ 2 * η ^ 2 ≤ ‖z‖ ^ 4 := by
    rw [hz4]
    nlinarith [sq_nonneg (ξ ^ 2), sq_nonneg (η ^ 2),
      mul_nonneg (sq_nonneg ξ) (sq_nonneg η)]
  have hm := mul_le_mul_of_nonneg_right hxy (norm_nonneg (F z))
  rw [hz] at h2
  change ((1 + ξ ^ 2) * (1 + η ^ 2)) * ‖F z‖ ≤ _
  unfold planeDecayConstant
  nlinarith

theorem norm_horizontalSlice_le (F : SchwartzMap ℂ ℂ) (η ξ : ℝ) :
    ‖horizontalSlice F η ξ‖ ≤
      (planeDecayConstant F / (1 + η ^ 2)) * (1 + ξ ^ 2)⁻¹ := by
  rw [horizontalSlice_apply, ← div_eq_mul_inv, div_div]
  apply (le_div_iff₀ (by positivity : 0 < (1 + η ^ 2) * (1 + ξ ^ 2))).mpr
  nlinarith [plane_schwartz_product_decay F ξ η]

theorem norm_inverse_horizontalSlice_le (F : SchwartzMap ℂ ℂ) (η x : ℝ) :
    ‖(𝓕⁻ (horizontalSlice F η)) x‖ ≤
      (planeDecayConstant F / (1 + η ^ 2)) * Real.pi := by
  rw [congrFun (SchwartzMap.fourierInv_coe (horizontalSlice F η)) x,
    Real.fourierInv_eq]
  have hb : Integrable (fun ξ : ℝ =>
      (planeDecayConstant F / (1 + η ^ 2)) * (1 + ξ ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul _
  have h := norm_integral_le_of_norm_le
    (f := fun ξ : ℝ => Real.fourierChar (inner ℝ ξ x) • horizontalSlice F η ξ) hb (Eventually.of_forall fun ξ => by
    simpa only [Circle.smul_def, smul_eq_mul, norm_mul, Circle.norm_coe, one_mul] using
      norm_horizontalSlice_le F η ξ)
  simpa only [integral_const_mul, integral_univ_inv_one_add_sq] using h

theorem norm_inverse_lineDeriv (g : SchwartzMap ℝ ℂ) (x : ℝ) :
    ‖(𝓕⁻ (∂_{(1 : ℝ)} g)) x‖ =
      (2 * Real.pi) * |x| * ‖(𝓕⁻ g) x‖ := by
  have ht : (fun u : ℝ => inner ℝ u (1 : ℝ)).HasTemperateGrowth := by fun_prop
  have hc : ‖(-(2 * Real.pi * Complex.I) : ℂ)‖ = 2 * Real.pi := by
    simp [ Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [SchwartzMap.fourierInv_lineDerivOp_eq]
  simp only [_root_.smul_apply, SchwartzMap.smulLeftCLM_apply_apply ht,
    norm_smul, hc]
  simp [RCLike.inner_apply, Real.norm_eq_abs, mul_assoc]

theorem sq_mul_norm_inverse_le_second (g : SchwartzMap ℝ ℂ) (x : ℝ) :
    x ^ 2 * ‖(𝓕⁻ g) x‖ ≤ ‖(𝓕⁻ (∂_{(1 : ℝ)} (∂_{(1 : ℝ)} g))) x‖ := by
  rw [norm_inverse_lineDeriv, norm_inverse_lineDeriv]
  have hp : 1 ≤ (2 * Real.pi) ^ 2 := by nlinarith [Real.pi_gt_three]
  calc
    x ^ 2 * ‖(𝓕⁻ g) x‖ ≤ ((2 * Real.pi) ^ 2 * x ^ 2) * ‖(𝓕⁻ g) x‖ :=
      mul_le_mul_of_nonneg_right (le_mul_of_one_le_left (sq_nonneg x) hp) (norm_nonneg _)
    _ = ((2 * Real.pi) ^ 2 * |x| ^ 2) * ‖(𝓕⁻ g) x‖ := by rw [sq_abs]
    _ = _ := by ring

theorem inverse_horizontalSlice_product_decay (F : SchwartzMap ℂ ℂ) (η x : ℝ) :
    ((1 + x ^ 2) * (1 + η ^ 2)) * ‖(𝓕⁻ (horizontalSlice F η)) x‖ ≤
      Real.pi * (planeDecayConstant F +
        planeDecayConstant (∂_{(1 : ℂ)} (∂_{(1 : ℂ)} F))) := by
  have h0 := norm_inverse_horizontalSlice_le F η x
  have h2a := sq_mul_norm_inverse_le_second (horizontalSlice F η) x
  rw [horizontalSlice_lineDerivOp_twice] at h2a
  have h2 := h2a.trans
    (norm_inverse_horizontalSlice_le (∂_{(1 : ℂ)} (∂_{(1 : ℂ)} F)) η x)
  have hden : 0 < 1 + η ^ 2 := by positivity
  have h0' : ‖(𝓕⁻ (horizontalSlice F η)) x‖ * (1 + η ^ 2) ≤
      planeDecayConstant F * Real.pi := by
    apply (le_div_iff₀ hden).mp
    simpa only [div_mul_eq_mul_div] using h0
  have h2' : (x ^ 2 * ‖(𝓕⁻ (horizontalSlice F η)) x‖) * (1 + η ^ 2) ≤
      planeDecayConstant (∂_{(1 : ℂ)} (∂_{(1 : ℂ)} F)) * Real.pi := by
    apply (le_div_iff₀ hden).mp
    simpa only [div_mul_eq_mul_div] using h2
  nlinarith

theorem partialFourier_product_decay (f : SchwartzMap ℂ ℂ) (η x : ℝ) :
    ((1 + x ^ 2) * (1 + η ^ 2)) * ‖partialFourier f η x‖ ≤
      partialFourierDecayConstant f := by
  rw [← partialFourierSchwartz_apply]
  exact inverse_horizontalSlice_product_decay (𝓕 f) η x

theorem norm_partialFourier_le (f : SchwartzMap ℂ ℂ) (η x : ℝ) :
    ‖partialFourier f η x‖ ≤
      partialFourierDecayConstant f * ((1 + x ^ 2)⁻¹ * (1 + η ^ 2)⁻¹) := by
  rw [← mul_inv, ← div_eq_mul_inv]
  apply (le_div_iff₀ (by positivity : 0 < (1 + x ^ 2) * (1 + η ^ 2))).mpr
  nlinarith [partialFourier_product_decay f η x]

theorem partialFourier_gaussian_summable_norm (f : SchwartzMap ℂ ℂ) :
    Summable (fun p : ℤ × ℤ =>
      ‖partialFourier f (p.2 : ℝ) (p.1 : ℝ)‖) := by
  apply summable_norm_of_cauchy_product
    (fun p : ℤ × ℤ => partialFourier f (p.2 : ℝ) (p.1 : ℝ))
    (partialFourierDecayConstant f)
  intro p
  exact norm_partialFourier_le f (p.2 : ℝ) (p.1 : ℝ)

theorem partialFourier_gaussian_summable (f : SchwartzMap ℂ ℂ) :
    Summable (fun p : ℤ × ℤ => partialFourier f (p.2 : ℝ) (p.1 : ℝ)) :=
  (partialFourier_gaussian_summable_norm f).of_norm

theorem plane_lattice_summable_norm (f : 𝓢(ℂ, ℂ)) :
    Summable (fun p : ℤ × ℤ => ‖f (complexPoint (p.1 : ℝ) (p.2 : ℝ))‖) := by
  apply summable_norm_of_cauchy_product _ (planeDecayConstant f)
  intro p
  rw [← mul_inv, ← div_eq_mul_inv]
  apply (le_div_iff₀ (by positivity :
    0 < (1 + (p.1 : ℝ) ^ 2) * (1 + (p.2 : ℝ) ^ 2))).mpr
  nlinarith [plane_schwartz_product_decay f (p.1 : ℝ) (p.2 : ℝ)]

theorem plane_lattice_summable (f : 𝓢(ℂ, ℂ)) :
    Summable (fun p : ℤ × ℤ => f (complexPoint (p.1 : ℝ) (p.2 : ℝ))) :=
  (plane_lattice_summable_norm f).of_norm

theorem schwartz_poisson_zero (g : 𝓢(ℝ, ℂ)) :
    (∑' n : ℤ, g (n : ℝ)) = ∑' n : ℤ, 𝓕 (g : ℝ → ℂ) (n : ℝ) := by
  simpa [fourier_eval_zero, SchwartzMap.fourier_coe] using g.tsum_eq_tsum_fourier 0

theorem vertical_poisson (f : 𝓢(ℂ, ℂ)) (x : ℝ) :
    (∑' n : ℤ, f (complexPoint x (n : ℝ))) =
      ∑' n : ℤ, partialFourier f (n : ℝ) x := by
  exact schwartz_poisson_zero (verticalSlice f x)

private theorem horizontal_poisson (f : 𝓢(ℂ, ℂ)) (n : ℤ) :
    (∑' m : ℤ, partialFourier f (n : ℝ) (m : ℝ)) =
      ∑' k : ℤ, (𝓕 f) (complexPoint (k : ℝ) (n : ℝ)) := by
  have h := schwartz_poisson_zero (partialFourierSchwartz f n)
  simpa only [partialFourierSchwartz_apply, partialFourierSchwartz_coe,
    fourier_partialFourier, SchwartzMap.fourier_coe] using h

private theorem iterated_poisson_pair_sum
    (f g h : ℤ → ℤ → ℂ)
    (hf : Summable (Function.uncurry f))
    (hg : Summable (Function.uncurry g))
    (hh : Summable (Function.uncurry h))
    (hvertical : ∀ m, (∑' n, f m n) = ∑' n, h m n)
    (hhorizontal : ∀ n, (∑' m, h m n) = ∑' m, g m n) :
    (∑' p : ℤ × ℤ, f p.1 p.2) = ∑' p : ℤ × ℤ, g p.1 p.2 := by
  calc
    (∑' p : ℤ × ℤ, f p.1 p.2) = ∑' m, ∑' n, f m n := hf.tsum_prod
    _ = ∑' m, ∑' n, h m n := tsum_congr hvertical
    _ = ∑' n, ∑' m, h m n := hh.tsum_comm.symm
    _ = ∑' n, ∑' m, g m n := tsum_congr hhorizontal
    _ = ∑' m, ∑' n, g m n := hg.tsum_comm
    _ = ∑' p : ℤ × ℤ, g p.1 p.2 := hg.tsum_prod.symm

theorem integer_pair_poisson (f : 𝓢(ℂ, ℂ)) :
    (∑' p : ℤ × ℤ, f (complexPoint (p.1 : ℝ) (p.2 : ℝ))) =
      ∑' p : ℤ × ℤ, (𝓕 f) (complexPoint (p.1 : ℝ) (p.2 : ℝ)) := by
  exact iterated_poisson_pair_sum
    (fun m n => f (complexPoint (m : ℝ) (n : ℝ)))
    (fun m n : ℤ => (𝓕 f : 𝓢(ℂ, ℂ)) (complexPoint (m : ℝ) (n : ℝ)))
    (fun m n => partialFourier f (n : ℝ) (m : ℝ))
    (plane_lattice_summable f) (plane_lattice_summable (𝓕 f))
    (partialFourier_gaussian_summable f)
    (fun m => vertical_poisson f m) (horizontal_poisson f)

end EisensteinSchwartzPoisson

end

end OAI
end

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

namespace EisensteinSchwartzPoisson

section
open MeasureTheory
open scoped FourierTransform SchwartzMap RealInnerProductSpace

theorem integral_comp_linearEquiv (A : ℂ ≃L[ℝ] ℂ) (f : ℂ → ℂ) :
    (∫ x : ℂ, f (A x)) = inverseJacobian A • ∫ x : ℂ, f x := by
  have h := integral_map_equiv («μ» := (volume : Measure ℂ))
    A.toHomeomorph.toMeasurableEquiv f
  have hm : Measure.map A (volume : Measure ℂ) =
      ENNReal.ofReal (inverseJacobian A) • volume := by
    exact Measure.map_linearMap_addHaar_eq_smul_addHaar volume
      A.toLinearEquiv.isUnit_det'.ne_zero
  change (∫ y : ℂ, f y ∂Measure.map A volume) = (∫ x : ℂ, f (A x)) at h
  rw [hm, integral_smul_measure, ENNReal.toReal_ofReal (show 0 ≤ inverseJacobian A from abs_nonneg _)] at h
  exact h.symm

theorem inner_linear_dual (A : ℂ ≃L[ℝ] ℂ) (x y : ℂ) :
    inner ℝ (A x) (dualMap A y) = inner ℝ x y := by
  rw [dualMap, ContinuousLinearMap.adjoint_inner_right]
  simp

theorem fourier_comp_linearEquiv (A : ℂ ≃L[ℝ] ℂ) (f : ℂ → ℂ) (w : ℂ) :
    𝓕 (f ∘ A) w = inverseJacobian A • 𝓕 f (dualMap A w) := by
  let H : ℂ → ℂ := fun z => Real.fourierChar (-inner ℝ z (dualMap A w)) • f z
  calc
    𝓕 (f ∘ A) w = ∫ x : ℂ, H (A x) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        simp only [H, inner_linear_dual, Function.comp_apply]
        rfl
    _ = inverseJacobian A • ∫ z : ℂ, H z := integral_comp_linearEquiv A H
    _ = inverseJacobian A • 𝓕 f (dualMap A w) := rfl

theorem fourier_translate (f : ℂ → ℂ) (b w : ℂ) :
    𝓕 (fun z => f (z + b)) w =
      Real.fourierChar (inner ℝ b w) • 𝓕 f w := by
  exact congrFun
    (VectorFourier.fourierIntegral_comp_add_right Real.fourierChar
      (volume : Measure ℂ) (innerₗ ℂ) f b) w

theorem fourier_affinePullback (f : 𝓢(ℂ, ℂ)) (A : ℂ ≃L[ℝ] ℂ) (b w : ℂ) :
    (𝓕 (affinePullback f A b)) w =
      inverseJacobian A •
        (Real.fourierChar (inner ℝ b (dualMap A w)) • (𝓕 f) (dualMap A w)) := by
  rw [congrFun (SchwartzMap.fourier_coe _) w]
  change 𝓕 ((fun z => f (z + b)) ∘ A) w = _
  rw [fourier_comp_linearEquiv, fourier_translate]
  rw [congrFun (SchwartzMap.fourier_coe f) (dualMap A w)]

theorem affine_lattice_poisson (f : 𝓢(ℂ, ℂ)) (A : ℂ ≃L[ℝ] ℂ) (b : ℂ) :
    (∑' p : ℤ × ℤ, f (A (complexPoint (p.1 : ℝ) (p.2 : ℝ)) + b)) =
      inverseJacobian A • ∑' p : ℤ × ℤ,
        Real.fourierChar (inner ℝ b (dualMap A (complexPoint (p.1 : ℝ) (p.2 : ℝ)))) •
          (𝓕 f) (dualMap A (complexPoint (p.1 : ℝ) (p.2 : ℝ))) := by
  have h := integer_pair_poisson (affinePullback f A b)
  simp only [affinePullback_apply, fourier_affinePullback] at h
  rw [tsum_const_smul''] at h
  exact h

end

section
open MeasureTheory EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open scoped FourierTransform SchwartzMap RealInnerProductSpace

theorem eisensteinLatticeMap_point (c : ℂ) (hc : c ≠ 0) (p : ℤ × ℤ) :
    eisensteinLatticeMap c hc (complexPoint (p.1 : ℝ) (p.2 : ℝ)) =
      c * eisEmbedding (ActualEisensteinCoordinates.eval p.1 p.2) := by
  simp [eisensteinLatticeMap, complexPoint, eisEmbedding_eval, mul_comm]

theorem actual_eisenstein_coset_poisson (f : 𝓢(ℂ, ℂ)) (b c : O) (hc : c ≠ 0) :
    (∑' z : O, f (eisEmbedding (b + c * z))) =
      (2 / (Real.sqrt 3 * ‖eisEmbedding c‖ ^ 2)) • ∑' p : ℤ × ℤ,
        Real.fourierChar (inner ℝ (eisEmbedding b)
          (eisensteinDualFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p)) •
        (𝓕 f) (eisensteinDualFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p) := by
  let A := eisensteinLatticeMap (eisEmbedding c) (eisEmbedding_ne_zero hc)
  have h := affine_lattice_poisson f A (eisEmbedding b)
  rw [eisenstein_inverseJacobian] at h
  calc
    (∑' z : O, f (eisEmbedding (b + c * z))) =
        ∑' p : ℤ × ℤ, f (eisEmbedding (b + c * latticeCoordEquiv.symm p)) :=
      (latticeCoordEquiv.symm.tsum_eq _).symm
    _ = ∑' p : ℤ × ℤ,
        f (A (complexPoint (p.1 : ℝ) (p.2 : ℝ)) + eisEmbedding b) := by
      apply tsum_congr
      intro p
      congr 1
      rw [map_add, map_mul]
      change eisEmbedding b + eisEmbedding c *
          eisEmbedding (ActualEisensteinCoordinates.eval p.1 p.2) = _
      rw [← eisensteinLatticeMap_point]
      exact add_comm _ _
    _ = _ := h

theorem actual_eisenstein_coset_summable_norm (f : 𝓢(ℂ, ℂ)) (b c : O) (hc : c ≠ 0) :
    Summable (fun z : O => ‖f (eisEmbedding (b + c * z))‖) := by
  let A := eisensteinLatticeMap (eisEmbedding c) (eisEmbedding_ne_zero hc)
  have hp := plane_lattice_summable_norm (affinePullback f A (eisEmbedding b))
  have hpair : Summable (fun p : ℤ × ℤ =>
      ‖f (eisEmbedding (b + c * latticeCoordEquiv.symm p))‖) := by
    convert (preTransparency := .instances) hp using 1
    funext p
    rw [affinePullback_apply]
    apply congrArg norm
    apply congrArg f
    rw [map_add, map_mul]
    change eisEmbedding b + eisEmbedding c *
        eisEmbedding (ActualEisensteinCoordinates.eval p.1 p.2) = _
    rw [← eisensteinLatticeMap_point]
    exact add_comm _ _
  exact (latticeCoordEquiv.symm.summable_iff).mp hpair

theorem actual_eisenstein_summable_norm (f : 𝓢(ℂ, ℂ)) :
    Summable (fun z : O => ‖f (eisEmbedding z)‖) := by
  simpa using actual_eisenstein_coset_summable_norm f 0 1 one_ne_zero

theorem actual_eisenstein_periodic_summable (f : 𝓢(ℂ, ℂ))
    {R : Type*} [Fintype R] (q : O → R) (P : R → ℂ) :
    Summable (fun z : O => P (q z) * f (eisEmbedding z)) := by
  classical
  let C : ℝ := ∑ r : R, ‖P r‖
  have hP (r : R) : ‖P r‖ ≤ C :=
    Finset.single_le_sum (fun a _ => norm_nonneg (P a)) (Finset.mem_univ r)
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun z => norm_nonneg _) _
    ((actual_eisenstein_summable_norm f).mul_left C)
  intro z
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hP (q z)) (norm_nonneg _)

theorem actual_eisenstein_periodic_poisson (f : 𝓢(ℂ, ℂ)) (c : O) (hc : c ≠ 0)
    (P : O ⧸ Ideal.span {c} → ℂ) :
    letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
    letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    (∑' z : O, P (Ideal.Quotient.mk (Ideal.span {c}) z) * f (eisEmbedding z)) =
      ∑ r : O ⧸ Ideal.span {c}, P r *
        ((2 / (Real.sqrt 3 * ‖eisEmbedding c‖ ^ 2)) • ∑' p : ℤ × ℤ,
          Real.fourierChar (inner ℝ
            (eisEmbedding (GaussianShiftedPartition.representative c r))
            (eisensteinDualFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p)) •
          (𝓕 f) (eisensteinDualFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p)) := by
  classical
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  rw [GaussianAbelPartition.tsum_periodic_weighted_partition
    (Ideal.Quotient.mk (Ideal.span {c})) P (fun z => f (eisEmbedding z))
    (actual_eisenstein_periodic_summable f _ P)]
  apply Finset.sum_congr rfl
  intro r hr
  congr 1
  exact (GaussianFiberEquiv.fiber_tsum c hc r
    (GaussianShiftedPartition.representative c r)
    (GaussianShiftedPartition.representative_spec c r)
    (fun z => f (eisEmbedding z))).trans
      (actual_eisenstein_coset_poisson f _ c hc)

theorem inverseJacobian_pos (A : ℂ ≃L[ℝ] ℂ) : 0 < inverseJacobian A :=
  abs_pos.mpr (inv_ne_zero A.toLinearEquiv.isUnit_det'.ne_zero)

theorem dual_lattice_summable_norm (f : 𝓢(ℂ, ℂ)) (A : ℂ ≃L[ℝ] ℂ) :
    Summable (fun p : ℤ × ℤ =>
      ‖(𝓕 f) (dualMap A (complexPoint (p.1 : ℝ) (p.2 : ℝ)))‖) := by
  have hJ := inverseJacobian_pos A
  have hp := plane_lattice_summable_norm (𝓕 (affinePullback f A 0))
  have hn (p : ℤ × ℤ) :
      ‖(𝓕 (affinePullback f A 0)) (complexPoint (p.1 : ℝ) (p.2 : ℝ))‖ =
      inverseJacobian A * ‖(𝓕 f) (dualMap A (complexPoint (p.1 : ℝ) (p.2 : ℝ)))‖ := by
    rw [fourier_affinePullback]
    simp [ abs_of_pos hJ]
  simp_rw [hn] at hp
  have hi := hp.mul_left (inverseJacobian A)⁻¹
  simpa only [← mul_assoc, inv_mul_cancel₀ hJ.ne', one_mul] using hi

theorem finite_phase_sum {R : Type*} [Fintype R]
    (f : 𝓢(ℂ, ℂ)) (A : ℂ ≃L[ℝ] ℂ) (b : R → ℂ) (P : R → ℂ) :
    (∑ r : R, P r * (inverseJacobian A • ∑' p : ℤ × ℤ,
      Real.fourierChar (inner ℝ (b r) (dualMap A (complexPoint (p.1 : ℝ) (p.2 : ℝ)))) •
        (𝓕 f) (dualMap A (complexPoint (p.1 : ℝ) (p.2 : ℝ))))) =
    inverseJacobian A • ∑' p : ℤ × ℤ,
      (∑ r : R, P r * (Real.fourierChar (inner ℝ (b r)
        (dualMap A (complexPoint (p.1 : ℝ) (p.2 : ℝ)))) : ℂ)) *
        (𝓕 f) (dualMap A (complexPoint (p.1 : ℝ) (p.2 : ℝ))) := by
  classical
  have hs (r : R) : Summable (fun p : ℤ × ℤ =>
      P r * (Real.fourierChar (inner ℝ (b r)
        (dualMap A (complexPoint (p.1 : ℝ) (p.2 : ℝ)))) •
        (𝓕 f) (dualMap A (complexPoint (p.1 : ℝ) (p.2 : ℝ))))) := by
    apply Summable.mul_left
    apply Summable.of_norm
    simpa only [Circle.norm_smul] using dual_lattice_summable_norm f A
  simp_rw [mul_smul_comm, ← tsum_mul_left]
  rw [← Finset.smul_sum, ← Summable.tsum_finsetSum (fun r _ => hs r)]
  congr 1
  apply tsum_congr
  intro p
  simp only [Circle.smul_def, smul_eq_mul, Finset.sum_mul, mul_assoc]

theorem actual_eisenstein_periodic_fourier (f : 𝓢(ℂ, ℂ)) (c : O) (hc : c ≠ 0)
    (P : O ⧸ Ideal.span {c} → ℂ) :
    letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
    letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    (∑' z : O, P (Ideal.Quotient.mk (Ideal.span {c}) z) * f (eisEmbedding z)) =
      (2 / (Real.sqrt 3 * ‖eisEmbedding c‖ ^ 2)) • ∑' p : ℤ × ℤ,
        (∑ r : O ⧸ Ideal.span {c}, P r *
          (Real.fourierChar (inner ℝ
            (eisEmbedding (GaussianShiftedPartition.representative c r))
            (eisensteinDualFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p)) : ℂ)) *
          (𝓕 f) (eisensteinDualFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p) := by
  classical
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  rw [actual_eisenstein_periodic_poisson f c hc P]
  have h := finite_phase_sum f
    (eisensteinLatticeMap (eisEmbedding c) (eisEmbedding_ne_zero hc))
    (fun r => eisEmbedding (GaussianShiftedPartition.representative c r)) P
  rw [eisenstein_inverseJacobian] at h
  exact h

end

open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open scoped FourierTransform SchwartzMap RealInnerProductSpace

theorem dualMap_trans (A B : ℂ ≃L[ℝ] ℂ) (z : ℂ) :
    dualMap (A.trans B) z = dualMap B (dualMap A z) := by
  change (ContinuousLinearMap.adjoint
    (A.symm.toContinuousLinearMap.comp B.symm.toContinuousLinearMap)) z = _
  rw [ContinuousLinearMap.adjoint_comp]
  rfl

theorem dual_basis_apply (w : ℂ) (hw : w.im ≠ 0) (z : ℂ) :
    dualMap (basisEquiv w hw) z =
      complexPoint z.re ((z.im - w.re * z.re) / w.im) := by
  apply ext_inner_left ℝ
  intro v
  rw [dualMap, ContinuousLinearMap.adjoint_inner_right]
  change inner ℝ ((basisEquiv w hw).symm v) z = _
  simp only [basisEquiv_symm_apply, Complex.inner, complexPoint,
    Complex.mul_re,  Complex.conj_re, Complex.conj_im]
  field_simp [hw]
  ring

theorem dual_mul_apply (c : ℂ) (hc : c ≠ 0) (z : ℂ) :
    dualMap (complexMulEquiv c hc) z = (starRingEnd ℂ c)⁻¹ * z := by
  apply ext_inner_left ℝ
  intro v
  rw [dualMap, ContinuousLinearMap.adjoint_inner_right]
  change inner ℝ (c⁻¹ * v) z = _
  simp only [Complex.inner, map_mul, map_inv₀]
  congr 1
  ring

theorem eisensteinDualFrequency_explicit (c : ℂ) (hc : c ≠ 0) (p : ℤ × ℤ) :
    eisensteinDualFrequency c hc p =
      complexPoint (p.1 : ℝ) (((p.1 : ℝ) + 2 * (p.2 : ℝ)) / Real.sqrt 3) /
        starRingEnd ℂ c := by
  unfold eisensteinDualFrequency eisensteinLatticeMap scaledBasisEquiv
  rw [dualMap_trans, dual_basis_apply, dual_mul_apply]
  have he : complexPoint (complexPoint (p.1 : ℝ) (p.2 : ℝ)).re
      (((complexPoint (p.1 : ℝ) (p.2 : ℝ)).im - omega3.re *
        (complexPoint (p.1 : ℝ) (p.2 : ℝ)).re) / omega3.im) =
      complexPoint (p.1 : ℝ) (((p.1 : ℝ) + 2 * (p.2 : ℝ)) / Real.sqrt 3) := by
    apply Complex.ext
    · rfl
    · simp only [complexPoint, omega3_im]
      have hr : omega3.re = -(1 / 2 : ℝ) := by norm_num [omega3]
      rw [hr]
      ring
  rw [he]
  ring

theorem actual_eisenstein_poisson_explicit (f : 𝓢(ℂ, ℂ)) (c : O) (hc : c ≠ 0)
    (P : O ⧸ Ideal.span {c} → ℂ) :
    letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
    letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    (∑' z : O, P (Ideal.Quotient.mk (Ideal.span {c}) z) * f (eisEmbedding z)) =
      (2 / (Real.sqrt 3 * ‖eisEmbedding c‖ ^ 2)) • ∑' p : ℤ × ℤ,
        (∑ r : O ⧸ Ideal.span {c}, P r *
          (Real.fourierChar (inner ℝ
            (eisEmbedding (GaussianShiftedPartition.representative c r))
            (explicitDualFrequency (eisEmbedding c) p)) : ℂ)) *
          (𝓕 f) (explicitDualFrequency (eisEmbedding c) p) := by
  simpa only [eisensteinDualFrequency_explicit, explicitDualFrequency] using
    actual_eisenstein_periodic_fourier f c hc P

open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open scoped FourierTransform SchwartzMap RealInnerProductSpace ContDiff

end EisensteinSchwartzPoisson

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.SexticRadialPoisson
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

namespace ActualEisensteinCubic

theorem finiteSexticQuotientRow_inv_eq_star
    {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hc : Pairwise (Function.onFun IsCoprime P))
    [∀ i, Fintype (O ⧸ P i)]
    (hgood : ∀ i, lambda ∉ P i) (j : ι → ℕ)
    (h : O ⧸ ∏ i, P i) :
    (finiteSexticQuotientRow P hc hgood j h)⁻¹ =
      star (finiteSexticQuotientRow P hc hgood j h) := by
  classical
  simp only [finiteSexticQuotientRow, star_prod]
  rw [← Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [MulChar.star_apply', MulChar.inv_apply_eq_inv']

end ActualEisensteinCubic

namespace EisensteinSchwartzPoisson

open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic MeasureTheory
open scoped FourierTransform SchwartzMap RealInnerProductSpace

theorem explicitDualFrequency_eq_paperFrequency (c : ℂ) (p : ℤ × ℤ) :
    explicitDualFrequency c p = paperFrequency (eisEmbedding (dualFrequencyEquiv p) / c) := by
  have hs : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hnum : complexPoint (p.1 : ℝ)
      (((p.1 : ℝ) + 2 * (p.2 : ℝ)) / Real.sqrt 3) =
      (2 * Complex.I / (Real.sqrt 3 : ℂ)) *
        starRingEnd ℂ (eisEmbedding (dualFrequencyEquiv p)) := by
    rw [dualFrequencyEquiv_coordinates]
    apply Complex.ext <;>
      norm_num [complexPoint, Complex.div_re, Complex.div_im] <;>
      field_simp <;>
      simp only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  unfold explicitDualFrequency paperFrequency
  rw [map_div₀, hnum]
  ring

theorem explicitDualFrequency_phase (r c : ℂ) (p : ℤ × ℤ) :
    (Real.fourierChar (inner ℝ r (explicitDualFrequency c p)) : ℂ) =
      paperE (r * eisEmbedding (dualFrequencyEquiv p) / c) := by
  rw [explicitDualFrequency_eq_paperFrequency, fourierChar_paperFrequency]
  congr 1
  ring

theorem actual_eisenstein_paper_poisson (f : 𝓢(ℂ, ℂ)) (c : O) (hc : c ≠ 0)
    (P : O ⧸ Ideal.span {c} → ℂ) :
    letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
    letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    (∑' z : O, P (Ideal.Quotient.mk (Ideal.span {c}) z) * f (eisEmbedding z)) =
      (1 / ‖eisEmbedding c‖ ^ 2 : ℝ) • ∑' h : O,
        (∑ r : O ⧸ Ideal.span {c}, P r *
          paperE (eisEmbedding (GaussianShiftedPartition.representative c r) *
            eisEmbedding h / eisEmbedding c)) *
          paperFourier f (eisEmbedding h / eisEmbedding c) := by
  classical
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let A : O → ℂ := fun h => ∑ r : O ⧸ Ideal.span {c}, P r *
    paperE (eisEmbedding (GaussianShiftedPartition.representative c r) *
      eisEmbedding h / eisEmbedding c)
  have ht : (∑' h : O, A h * paperFourier f (eisEmbedding h / eisEmbedding c)) =
      (2 / Real.sqrt 3 : ℝ) • ∑' p : ℤ × ℤ,
        A (dualFrequencyEquiv p) *
          (𝓕 f) (explicitDualFrequency (eisEmbedding c) p) := by
    calc
      _ = ∑' p : ℤ × ℤ, A (dualFrequencyEquiv p) *
          paperFourier f (eisEmbedding (dualFrequencyEquiv p) / eisEmbedding c) :=
        (dualFrequencyEquiv.tsum_eq _).symm
      _ = ∑' p : ℤ × ℤ, (2 / Real.sqrt 3 : ℝ) •
          (A (dualFrequencyEquiv p) *
            (𝓕 f) (explicitDualFrequency (eisEmbedding c) p)) := by
        apply tsum_congr
        intro p
        rw [paperFourier_eq_standard, ← explicitDualFrequency_eq_paperFrequency]
        change A (dualFrequencyEquiv p) *
          ((2 / Real.sqrt 3 : ℝ) • (𝓕 f) (explicitDualFrequency (eisEmbedding c) p)) = _
        simp only [Algebra.smul_def]
        ring
      _ = _ := tsum_const_smul'' _
    rfl
  have hp := actual_eisenstein_poisson_explicit f c hc P
  simp_rw [explicitDualFrequency_phase] at hp
  change _ = (1 / ‖eisEmbedding c‖ ^ 2 : ℝ) •
    ∑' h : O, A h * paperFourier f (eisEmbedding h / eisEmbedding c)
  rw [ht, smul_smul]
  convert (preTransparency := .instances) hp using 1
  congr 1
  ring

theorem actual_eisenstein_paper_poisson_trace (f : 𝓢(ℂ, ℂ)) (c : O) (hc : c ≠ 0)
    (P : O ⧸ Ideal.span {c} → ℂ) :
    letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
    letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    let ψ := eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates c hc
    (∑' z : O, P (Ideal.Quotient.mk (Ideal.span {c}) z) * f (eisEmbedding z)) =
      (1 / ‖eisEmbedding c‖ ^ 2 : ℝ) • ∑' h : O,
        (∑ r : O ⧸ Ideal.span {c}, P r *
          ψ (Ideal.Quotient.mk (Ideal.span {c}) h * r)) *
          paperFourier f (eisEmbedding h / eisEmbedding c) := by
  classical
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  simpa only [eisTraceModChar_frequency] using actual_eisenstein_paper_poisson f c hc P

open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic MeasureTheory
open scoped FourierTransform SchwartzMap RealInnerProductSpace ContDiff

theorem paperFourier_comp_mul (f : ℂ → ℂ) (a : ℂ) (ha : a ≠ 0) (u : ℂ) :
    paperFourier (fun z => f (a * z)) u =
      (1 / ‖a‖ ^ 2 : ℝ) • paperFourier f (u / a) := by
  have hd : dualMap (complexMulEquiv a ha) (paperFrequency u) =
      paperFrequency (u / a) := by
    rw [dual_mul_apply]
    unfold paperFrequency
    rw [map_div₀]
    ring
  have hj : inverseJacobian (complexMulEquiv a ha) = 1 / ‖a‖ ^ 2 := by
    rw [inverseJacobian, complexMulEquiv_det, abs_inv,
      abs_of_nonneg (Complex.normSq_nonneg a), Complex.sq_norm]
    ring
  rw [paperFourier_eq_standard, paperFourier_eq_standard]
  have hF := fourier_comp_linearEquiv (complexMulEquiv a ha) f (paperFrequency u)
  simp only [Function.comp_def, complexMulEquiv_apply] at hF
  rw [hF, hd, hj, smul_smul, smul_smul]
  congr 1
  ring

theorem paperFourier_radial (W : ℝ → ℂ) (u : ℂ) :
    paperFourier (fun z => W (‖z‖ ^ 2)) u =
      paperRadialFourier W (‖u‖ ^ 2) := by
  unfold paperRadialFourier
  rw [Real.sqrt_sq (norm_nonneg u)]
  by_cases hu : u = 0
  · simp [hu]
  have hn : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  have hnC : (‖u‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn
  let a : ℂ := u / (‖u‖ : ℂ)
  have ha : a ≠ 0 := div_ne_zero hu hnC
  have hna : ‖a‖ = 1 := by
    simp [a, Complex.norm_real, hn]
  have hq : u / a = (‖u‖ : ℂ) := by
    dsimp [a]
    field_simp
  have hfun : (fun z : ℂ => W (‖a * z‖ ^ 2)) = fun z : ℂ => W (‖z‖ ^ 2) := by
    funext z
    rw [norm_mul, hna, one_mul]
  have hF := paperFourier_comp_mul (fun z => W (‖z‖ ^ 2)) a ha u
  rw [hfun, hna, hq] at hF
  simpa using hF

theorem inverseSqrt_norm_sq (K : ℝ) (hK : 0 < K) :
    ‖(Real.sqrt K : ℂ)⁻¹‖ ^ 2 = 1 / K := by
  rw [norm_inv, inv_pow]
  simp only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg K), Real.sq_sqrt hK.le, one_div]

theorem paperFourier_radial_scaled (W : ℝ → ℂ) (K : ℝ) (hK : 0 < K) (u : ℂ) :
    paperFourier (fun z => W (‖z‖ ^ 2 / K)) u =
      K • paperRadialFourier W (K * ‖u‖ ^ 2) := by
  let a : ℂ := (Real.sqrt K : ℂ)⁻¹
  have ha : a ≠ 0 := inverseSqrt_ne_zero K hK
  have hna : ‖a‖ ^ 2 = 1 / K := inverseSqrt_norm_sq K hK
  have hfun : (fun z : ℂ => W (‖a * z‖ ^ 2)) =
      fun z : ℂ => W (‖z‖ ^ 2 / K) := by
    funext z
    rw [norm_mul, mul_pow, hna]
    congr 1
    ring
  have hnorm : ‖u / a‖ ^ 2 = K * ‖u‖ ^ 2 := by
    rw [norm_div, div_pow, hna]
    field_simp
  have hF := paperFourier_comp_mul (fun z => W (‖z‖ ^ 2)) a ha u
  rw [hfun, hna, one_div_one_div, paperFourier_radial, hnorm] at hF
  exact hF

@[simp] theorem scaledRadialTest_apply (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) (z : ℂ) :
    scaledRadialTest W K hK z = W (‖z‖ ^ 2 / K) := by
  simp only [scaledRadialTest, affinePullback_apply, complexMulEquiv_apply,
    add_zero, radialTest_apply, norm_mul, mul_pow, inverseSqrt_norm_sq K hK]
  congr 1
  ring

theorem paperFourier_scaledRadialTest (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) (u : ℂ) :
    paperFourier (scaledRadialTest W K hK) u =
      K • paperRadialFourier W (K * ‖u‖ ^ 2) := by
  change paperFourier (fun z => scaledRadialTest W K hK z) u = _
  simp only [scaledRadialTest_apply]
  exact paperFourier_radial_scaled W K hK u

theorem actual_radial_paper_poisson_trace (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K)
    (c : O) (hc : c ≠ 0) (P : O ⧸ Ideal.span {c} → ℂ) :
    letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
    letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    let ψ := eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates c hc
    (∑' z : O, P (Ideal.Quotient.mk (Ideal.span {c}) z) * W (‖eisEmbedding z‖ ^ 2 / K)) =
      (K / ‖eisEmbedding c‖ ^ 2 : ℝ) • ∑' h : O,
        (∑ r : O ⧸ Ideal.span {c}, P r *
          ψ (Ideal.Quotient.mk (Ideal.span {c}) h * r)) *
          paperRadialFourier W (K * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2) := by
  classical
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let ψ := eisTraceModChar ShortDraftTrace.breveE
    ConcreteBreveE.breveE_period_coordinates c hc
  let A : O → ℂ := fun h => ∑ r : O ⧸ Ideal.span {c}, P r *
    ψ (Ideal.Quotient.mk (Ideal.span {c}) h * r)
  have ht : (∑' h : O, A h *
      paperFourier (scaledRadialTest W K hK) (eisEmbedding h / eisEmbedding c)) =
      K • ∑' h : O, A h *
        paperRadialFourier W (K * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2) := by
    calc
      _ = ∑' h : O, K • (A h *
          paperRadialFourier W (K * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2)) := by
        apply tsum_congr
        intro h
        rw [paperFourier_scaledRadialTest, norm_div, div_pow]
        have hr : K * (‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2) =
            K * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2 := by ring
        rw [hr]
        simp only [Algebra.smul_def]
        ring
      _ = _ := tsum_const_smul'' _
  have hp := actual_eisenstein_paper_poisson_trace (scaledRadialTest W K hK) c hc P
  change (∑' z : O, P (Ideal.Quotient.mk (Ideal.span {c}) z) *
    scaledRadialTest W K hK (eisEmbedding z)) =
    (1 / ‖eisEmbedding c‖ ^ 2 : ℝ) • ∑' h : O, A h *
      paperFourier (scaledRadialTest W K hK) (eisEmbedding h / eisEmbedding c) at hp
  rw [ht, smul_smul] at hp
  simpa only [scaledRadialTest_apply, one_div_mul_eq_div] using hp

end EisensteinSchwartzPoisson

open scoped BigOperators Classical SchwartzMap ContDiff

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

end EisensteinSchwartzPoisson

open scoped BigOperators Classical SchwartzMap ContDiff

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

end

open ActualEisensteinCubic
open IdealMobiusDivisorSum (idealDivisors mem_idealDivisors sum_moebius_divisors)

end CompletedGauss

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.Algebra
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
noncomputable section

theorem square_eq_star_of_fourth_eq (z : ℂ) (hz : z ^ 4 = z) : z ^ 2 = star z := by
  by_cases h0 : z = 0
  · simp [h0]
  have h3 : z ^ 3 = 1 := by
    apply mul_right_cancel₀ h0
    simpa only [← pow_succ, one_mul] using hz
  have hn := Complex.norm_eq_one_of_pow_eq_one h3 (by decide : (3 : ℕ) ≠ 0)
  change z ^ 2 = (starRingEnd ℂ) z
  rw [← Complex.inv_eq_conj hn]
  apply mul_right_cancel₀ h0
  rw [inv_mul_cancel₀ h0]
  simpa only [← pow_succ] using h3

variable {R : Type*} [CommRing R] [Finite Rˣ]

omit [Finite Rˣ] in
theorem cubic_fourth_eq (χ : MulChar R ℂ) (hχ : χ ^ 3 = 1) (x : R) :
    χ x ^ 4 = χ x := by
  have h : χ ^ 4 = χ := by
    rw [show (4 : ℕ) = 3 + 1 by decide, pow_add, hχ, one_mul, pow_one]
  rw [← MulChar.pow_apply' χ (by decide : (4 : ℕ) ≠ 0), h]

end
end SevenEighths.CubicSieve

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.Blocks
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators
noncomputable section

variable {a b n : Type*} [Fintype a] [Fintype b] [Fintype n]
  [DecidableEq n]

theorem squaredNorm_nonneg (A : Matrix a n ℂ) : 0 ≤ squaredNorm A := sq_nonneg _

end
end SevenEighths.CubicSieve

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.CompletedDyadicRows
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

open ActualEisensteinCubic

theorem two_pow_clog_le_double (n : ℕ) (hn : 1≤n) : 2^Nat.clog 2 n≤2*n := by
  by_cases h : n=1
  · simp [h]
  have hn1 : 1<n := lt_of_le_of_ne hn (Ne.symm h)
  have hl : 0<Nat.clog 2 n := Nat.clog_pos (by norm_num) hn1
  have hp := Nat.pow_pred_clog_lt_self (by norm_num : 1<2) hn1
  have he : (Nat.clog 2 n).pred+1=Nat.clog 2 n := Nat.succ_pred_eq_of_pos hl
  calc
    _ = 2^(Nat.clog 2 n).pred*2 := by rw [←he,pow_succ]; rfl
    _ ≤ n*2 := Nat.mul_le_mul_right 2 hp.le
    _ = _ := Nat.mul_comm _ _

open ActualEisensteinCubic CanonicalQuadraticSieve

end

open ActualEisensteinCubic CanonicalQuadraticSieve

end CompletedGauss

open scoped BigOperators Classical SchwartzMap

open MeasureTheory
open scoped BigOperators Classical

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

lemma cubicRow_norm_le_one (I : Ideal ActualEisensteinCubic.O) (hI : primaryGenerator I≠0) (x : ActualEisensteinCubic.O⧸I) :
    ‖cubicRow I hI x‖≤1 := by
  unfold cubicRow
  rw [norm_prod]
  apply Finset.prod_le_one
  · intro i hi; exact norm_nonneg _
  · intro i hi
    exact FiniteRayExpansion.norm_char_le_one _ _

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.Ideal
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem idealKernel_reciprocity (I J : Ideal Eis)
    (hI : primaryGenerator I ≠ 0) (hJ : primaryGenerator J ≠ 0) :
    idealKernel I J = idealKernel J I :=
  congrArg eisEmbedding (CubicJacobiGlobal.idealSymbol_reciprocity I J hI hJ)

theorem idealSymbol_fourth (I : Ideal Eis) (x : Eis) :
    (eisEmbedding (CubicJacobiGlobal.idealSymbol I x)) ^ 4 =
      eisEmbedding (CubicJacobiGlobal.idealSymbol I x) := by
  have hlocal (P : Ideal Eis) :
      (eisEmbedding (CubicJacobiGlobal.primeValue P x)) ^ 4 =
        eisEmbedding (CubicJacobiGlobal.primeValue P x) := by
    unfold CubicJacobiGlobal.primeValue
    split_ifs with h
    · let : P.IsMaximal := h.1
      let χ := actualSextic P h.2 ^ 2
      have hχ : χ ^ 3 = 1 := by
        dsimp [χ]
        rw [canonicalSextic_pow_two, MulChar.ringHomComp_pow, cubicChar_pow_three, MulChar.ringHomComp_one]
      simpa only [χ, canonicalSextic_pow_two, MulChar.ringHomComp_apply] using
        cubic_fourth_eq χ hχ (Ideal.Quotient.mk P x)
    · simp
  have hprod (S : Multiset (Ideal Eis)) :
      (eisEmbedding ((S.map (fun P => CubicJacobiGlobal.primeValue P x)).prod)) ^ 4 =
        eisEmbedding ((S.map (fun P => CubicJacobiGlobal.primeValue P x)).prod) := by
    induction S using Multiset.induction_on with
    | empty => simp
    | @cons P S ih =>
      simp only [Multiset.map_cons, Multiset.prod_cons, map_mul, mul_pow, hlocal, ih]
  by_cases hI : I = 0
  · simp [hI]
  · simpa only [CubicJacobiGlobal.idealSymbol, if_neg hI] using
      hprod (UniqueFactorizationMonoid.normalizedFactors I)

theorem mem_idealRange {X : ℝ} {I : Ideal Eis} :
    I ∈ idealRange X ↔ Admissible I ∧ (Ideal.absNorm I : ℝ) ≤ X := by
  rw [idealRange, Finset.mem_filter, mem_idealsUpTo]
  constructor
  · rintro ⟨⟨hp, hN⟩, ha⟩
    refine ⟨ha, ?_⟩
    have hX : 0 ≤ X := by
      by_contra hn
      have hz : ⌊X⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
      omega
    exact (Nat.cast_le.mpr hN).trans (Nat.floor_le hX)
  · rintro ⟨ha, hN⟩
    refine ⟨⟨Nat.one_le_iff_ne_zero.mpr ?_, Nat.le_floor hN⟩, ha⟩
    intro hz
    exact (primaryGenerator_ne_zero_ideal I ha.2) (Ideal.absNorm_eq_zero_iff.mp hz)

end
end SevenEighths.CubicSieve

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.Poisson
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson QuadraticInitialBound
open CompletedGauss ConcretePrimeRowBridge
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem canonical_finite_prime_gauss_transform_scalar_of_nontrivial
    {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hc : Pairwise (Function.onFun IsCoprime P))
    [Fintype (O ⧸ ∏ i, P i)] [∀ i, Fintype (O ⧸ P i)]
    (hgood : ∀ i, goodLambda ∉ P i)
    (j : ι → ℕ)
    (hχ : ∀ i, actualSextic (P i) (hgood i) ^ j i ≠ 1)
    (ψ : AddChar (O ⧸ ∏ i, P i) ℂ) (h : O ⧸ ∏ i, P i) :
    (∑ x : O ⧸ ∏ i, P i, finiteSexticQuotientRow P hc hgood j x * ψ (h * x)) =
      (finiteSexticQuotientRow P hc hgood j h)⁻¹ *
        ∑ x : O ⧸ ∏ i, P i, finiteSexticQuotientRow P hc hgood j x * ψ x := by
  let (i : ι) : Field (O ⧸ P i) := Ideal.Quotient.field (P i)
  exact IdealGaussCRT.gauss_transform_finite_crt_scalar (fun i => O ⧸ P i)
    (IdealGaussCRT.quotientProdEquivPi P hc)
    (fun i => actualSextic (P i) (hgood i) ^ j i) ψ
    hχ h

theorem canonical_finite_prime_gauss_transform_conj_of_nontrivial
    {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hc : Pairwise (Function.onFun IsCoprime P))
    [Fintype (O ⧸ ∏ i, P i)] [∀ i, Fintype (O ⧸ P i)]
    (hgood : ∀ i, goodLambda ∉ P i)
    (j : ι → ℕ)
    (hχ : ∀ i, actualSextic (P i) (hgood i) ^ j i ≠ 1)
    (ψ : AddChar (O ⧸ ∏ i, P i) ℂ) (h : O ⧸ ∏ i, P i) :
    (∑ x : O ⧸ ∏ i, P i, finiteSexticQuotientRow P hc hgood j x * ψ (h * x)) =
      star (finiteSexticQuotientRow P hc hgood j h) *
        ∑ x : O ⧸ ∏ i, P i, finiteSexticQuotientRow P hc hgood j x * ψ x := by
  rw [canonical_finite_prime_gauss_transform_scalar_of_nontrivial P hc hgood j hχ ψ,
    finiteSexticQuotientRow_inv_eq_star P hc hgood j h]

theorem canonical_principal_gauss_transform_of_nontrivial {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    [Fintype (O ⧸ ∏ i, P i)] [∀ i, Fintype (O ⧸ P i)]
    (hgood : ∀ i, goodLambda ∉ P i)
    (j : ι → ℕ)
    (hχ : ∀ i, actualSextic (P i) (hgood i) ^ j i ≠ 1)
    (c : O) (hc : Ideal.span {c} = ∏ i, P i)
    [Fintype (O ⧸ Ideal.span {c})]
    (ψ : AddChar (O ⧸ Ideal.span {c}) ℂ) (h : O ⧸ Ideal.span {c}) :
    (∑ r : O ⧸ Ideal.span {c}, principalSexticRow P hcop hgood j c hc r * ψ (h * r)) =
      star (principalSexticRow P hcop hgood j c hc h) *
        ∑ r : O ⧸ Ideal.span {c}, principalSexticRow P hcop hgood j c hc r * ψ r := by
  let e := Ideal.quotEquivOfEq hc
  let row := finiteSexticQuotientRow P hcop hgood j
  let φ : AddChar (O ⧸ ∏ i, P i) ℂ := ψ.compAddMonoidHom e.symm.toAddMonoidHom
  have hleft :
      (∑ r : O ⧸ Ideal.span {c}, row (e r) * ψ (h * r)) =
        ∑ x : O ⧸ ∏ i, P i, row x * φ (e h * x) := by
    rw [← Equiv.sum_comp e.toEquiv (fun x => row x * φ (e h * x))]
    apply Finset.sum_congr rfl
    intro r _
    change row (e r) * ψ (h * r) = row (e r) * ψ (e.symm (e h * e r))
    rw [← map_mul, e.symm_apply_apply]
  have hbase :
      (∑ r : O ⧸ Ideal.span {c}, row (e r) * ψ r) =
        ∑ x : O ⧸ ∏ i, P i, row x * φ x := by
    rw [← Equiv.sum_comp e.toEquiv (fun x => row x * φ x)]
    apply Finset.sum_congr rfl
    intro r _
    change row (e r) * ψ r = row (e r) * ψ (e.symm (e r))
    rw [e.symm_apply_apply]
  change (∑ r : O ⧸ Ideal.span {c}, row (e r) * ψ (h * r)) =
    star (row (e h)) * ∑ r : O ⧸ Ideal.span {c}, row (e r) * ψ r
  rw [hleft, hbase]
  exact canonical_finite_prime_gauss_transform_conj_of_nontrivial P hcop hgood j hχ φ (e h)

theorem cubicExponent_nonprincipal (P : Ideal O) [P.IsMaximal]
    (hg : goodLambda ∉ P) (negative : Bool) :
    actualSextic P hg ^ cubicExponent negative ≠ 1 := by
  let χ := actualSextic P hg ^ 2
  have hχ : χ ≠ 1 := by
    dsimp [χ]
    rw [canonicalSextic_pow_two P hg]
    exact (MulChar.ringHomComp_ne_one_iff eisEmbedding_injective).mpr (cubicChar_ne_one P hg)
  have h3 : χ ^ 3 = 1 := by
    dsimp [χ]
    rw [canonicalSextic_pow_two P hg, MulChar.ringHomComp_pow, cubicChar_pow_three P hg, MulChar.ringHomComp_one]
  have h2 : χ ^ 2 ≠ 1 := by
    intro h
    apply hχ
    calc
      χ = χ ^ 2 * χ := by rw [h, one_mul]
      _ = χ ^ 3 := (pow_succ χ 2).symm
      _ = 1 := h3
  cases negative with
  | false => simpa only [cubicExponent, Bool.false_eq_true, ite_false,
      ] using hχ
  | true =>
      have he : actualSextic P hg ^ 4 = χ ^ 2 := by
        rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul]
      simpa only [cubicExponent, ite_true, he] using h2

end
end SevenEighths.CubicSieve

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.Elements
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem elementCharacter_norm_le_one (I : Ideal O) (hI : primaryGenerator I ≠ 0) (x : O) :
    ‖elementCharacter I hI x‖ ≤ 1 := by
  change ‖eisEmbedding (CubicJacobiGlobal.idealSymbol I x)‖ ≤ 1
  rw [← CanonicalRowCompletion.idealRowHom_square, norm_pow]
  exact (pow_le_pow_left₀ (norm_nonneg _)
    (CanonicalRowCompletion.idealRowHom_norm x I) 2).trans_eq (by norm_num)

end
end SevenEighths.CubicSieve

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.Gcd
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open CanonicalQuadraticSieve (idealQuotient totalQuotient gcdPool)
noncomputable section
local notation "O" => ActualEisensteinCubic.O

lemma cubicRow_square_eq_star (I : Ideal O) (z : O) :
    cubicRow I z ^ 2 = star (cubicRow I z) :=
  square_eq_star_of_fourth_eq _ (idealSymbol_fourth I z)

lemma cubicRow_common_mask (D : Ideal O) (hD : primaryGenerator D ≠ 0) (z : O) :
    star (cubicRow D z) * cubicRow D z =
      if IsCoprime D (Ideal.span {z}) then 1 else 0 := by
  rw [← cubicRow_square_eq_star]
  calc
    _ = cubicRow D z ^ 3 := by ring
    _ = _ := idealSymbol_cube_mask D z hD

end
end SevenEighths.CubicSieve

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.FullNorm
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
noncomputable section
local notation "O" => ActualEisensteinCubic.O

lemma elementSieveNorm_nonneg (M N : ℝ) : 0 ≤ elementSieveNorm M N := squaredNorm_nonneg _

theorem element_family_squared_norm_le {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (rows : m → O) (cols : n → Ideal O)
    (hr : Function.Injective rows) (hc : Function.Injective cols)
    (M N : ℝ) (hrows : ∀ i, rows i ≠ 0 ∧ (Ideal.absNorm (Ideal.span {rows i}) : ℝ) ≤ M)
    (hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N) :
    squaredNorm (fun i j => cubicRow (cols j) (rows i)) ≤ elementSieveNorm M N := by
  let r : m → elementRange M := fun i => ⟨rows i, (mem_elementRange M (rows i)).mpr (hrows i)⟩
  let c : n → idealRange N := fun j => ⟨cols j, mem_idealRange.mpr (hcols j)⟩
  have hri : Function.Injective r := fun i j h => hr (congrArg Subtype.val h)
  have hci : Function.Injective c := fun i j h => hc (congrArg Subtype.val h)
  have h := FiniteSieveRestriction.submatrix_norm_le r hri c hci (elementMatrix M N)
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

theorem element_coprime_bilinear_bound {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (ε : ℝ) (hε : 0 < ε) (M N : ℝ) (hN : 0 ≤ N)
    (rows : m → O) (cols : n → Ideal O)
    (hr : Function.Injective rows) (hc : Function.Injective cols)
    (hrows : ∀ i, rows i ≠ 0 ∧ (Ideal.absNorm (Ideal.span {rows i}) : ℝ) ≤ M)
    (hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N)
    (a b : n → ℂ) :
    (∑ i, ‖∑ j, ∑ k, if IsCoprime (cols j) (cols k) then
      star (cubicRow (cols j) (rows i) * a j) * (cubicRow (cols k) (rows i) * b k) else 0‖) ^ 2 ≤
      (elementSieveNorm M N * (IdealCoprimeSieveOperator.supportConstant ε hε * N ^ ε) * ∑ j, ‖a j‖ ^ 2) *
      (elementSieveNorm M N * (IdealCoprimeSieveOperator.supportConstant ε hε * N ^ ε) * ∑ j, ‖b j‖ ^ 2) := by
  have hb := IdealCoprimeBilinearSieve.ideal_coprime_bilinear_operator_bound ε hε cols cols
    (fun j => primaryGenerator_ne_zero_ideal _ (hcols j).1.2)
    (fun j => primaryGenerator_ne_zero_ideal _ (hcols j).1.2)
    N N hN hN (fun j => (hcols j).2) (fun j => (hcols j).2)
    (fun i j => cubicRow (cols j) (rows i)) (fun i j => cubicRow (cols j) (rows i)) a b
  have hn := element_family_squared_norm_le rows cols hr hc M N hrows hcols
  have hfac : 0 ≤ IdealCoprimeSieveOperator.supportConstant ε hε * N ^ ε :=
    mul_nonneg (IdealCoprimeSieveOperator.supportConstant_pos ε hε).le (Real.rpow_nonneg hN _)
  apply hb.trans
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hn hfac) (by positivity)
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hn hfac) (by positivity)
  · positivity
  · exact mul_nonneg (mul_nonneg (elementSieveNorm_nonneg _ _) hfac) (by positivity)

end
end SevenEighths.CubicSieve

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.Gauss
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
noncomputable section
local notation "O" => ActualEisensteinCubic.O

lemma cubicQuotientCharacter_cube (I : Ideal O) (hI : Admissible I) :
    cubicQuotientCharacter I hI ^ 3 = 1 := by
  apply DFunLike.ext
  intro x
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [MulChar.pow_apply' _ (by decide : (3 : ℕ) ≠ 0), cubicQuotientCharacter_mk, cubicRow,
    idealSymbol_cube_mask I z hI.2]
  have hu : IsUnit (Ideal.Quotient.mk I z) ↔ IsCoprime I (Ideal.span {z}) := by
    rw [CubicEisenstein.isUnit_quotient_iff_sup, Ideal.isCoprime_iff_sup_eq]
  by_cases h : IsUnit (Ideal.Quotient.mk I z)
  · rw [if_pos (hu.mp h), MulChar.one_apply h]
  · rw [if_neg (fun hcop => h (hu.mpr hcop)), MulChar.map_nonunit _ h]

lemma cubicQuotientCharacter_neg_one (I : Ideal O) (hI : Admissible I) :
    cubicQuotientCharacter I hI (-1) = 1 := by
  have h3 := congrArg (fun χ : MulChar (O ⧸ I) ℂ => χ (-1)) (cubicQuotientCharacter_cube I hI)
  rw [MulChar.pow_apply' _ (by decide : (3 : ℕ) ≠ 0), MulChar.one_apply (isUnit_neg_one)] at h3
  have h2 : cubicQuotientCharacter I hI (-1) ^ 2 = 1 := by rw [← map_pow]; norm_num
  calc
    _ = cubicQuotientCharacter I hI (-1) ^ 2 * cubicQuotientCharacter I hI (-1) := by rw [h2, one_mul]
    _ = cubicQuotientCharacter I hI (-1) ^ 3 := by ring
    _ = 1 := h3

lemma principalCubicCharacter_neg_one (I : Ideal O) (hI : Admissible I) :
    principalCubicCharacter I hI (-1) = 1 := by
  change cubicQuotientCharacter I hI ((Ideal.quotEquivOfEq (primaryGenerator_spec I hI.2).1) (-1)) = 1
  rw [map_neg, map_one, cubicQuotientCharacter_neg_one]

lemma gaussTwo_eq_gaussSum (I : Ideal O) (hI : Admissible I) :
    let : Finite (O ⧸ Ideal.span {primaryGenerator I}) := finite_quotient_span hI.2
    let : Fintype (O ⧸ Ideal.span {primaryGenerator I}) := Fintype.ofFinite _
    gaussTwo I hI.2 = gaussSum (principalCubicCharacter I hI)
      (eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates
        (primaryGenerator I) hI.2) / (‖eisEmbedding (primaryGenerator I)‖ : ℂ) := by
  dsimp only [gaussTwo, gaussSum, principalCubicCharacter, quotientCharacterTransport, cubicQuotientCharacter]
  congr 1

lemma gaussSum_inverse_of_even {R : Type*} [CommRing R] [Fintype R]
    (χ : MulChar R ℂ) (ψ : AddChar R ℂ) (heven : χ (-1) = 1) :
    gaussSum χ⁻¹ ψ = star (gaussSum χ ψ) := by
  rw [star_gaussSum_eq]
  have hh : χ⁻¹ (-1) = 1 := by rw [← MulChar.star_apply', heven, star_one]
  have h := gaussSum_mulShift χ⁻¹ ψ (-1 : Rˣ)
  rw [Units.coe_neg_one, ← ψ.inv_mulShift, hh, one_mul] at h
  exact h.symm

lemma cubic_pair_cross_phase (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hcop : IsCoprime I J) :
    (principalCubicCharacter I hI)⁻¹ (Ideal.Quotient.mk _ (primaryGenerator J)) *
      principalCubicCharacter J hJ (Ideal.Quotient.mk _ (primaryGenerator I)) = 1 := by
  let : Finite (O ⧸ Ideal.span {primaryGenerator I}) := finite_quotient_span hI.2
  rw [← MulChar.star_apply', principalCubicCharacter_mk, principalCubicCharacter_mk]
  change star (idealKernel I J) * idealKernel J I = 1
  rw [← idealKernel_reciprocity I J hI.2 hJ.2]
  change star (cubicRow I (primaryGenerator J)) * cubicRow I (primaryGenerator J) = 1
  rw [cubicRow_common_mask I hI.2, (primaryGenerator_spec J hJ.2).1, if_pos hcop]

theorem cubicPairGauss_separation (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hcop : IsCoprime I J) :
    cubicPairGauss I J hI hJ = star (gaussTwo I hI.2) * gaussTwo J hJ.2 := by
  let : Finite (O ⧸ Ideal.span {primaryGenerator I}) := finite_quotient_span hI.2
  let : Fintype (O ⧸ Ideal.span {primaryGenerator I}) := Fintype.ofFinite _
  let : Finite (O ⧸ Ideal.span {primaryGenerator J}) := finite_quotient_span hJ.2
  let : Fintype (O ⧸ Ideal.span {primaryGenerator J}) := Fintype.ofFinite _
  let : Finite (O ⧸ (Ideal.span {primaryGenerator I}) * (Ideal.span {primaryGenerator J})) :=
    finite_quotient_product hI.2 hJ.2
  let : Fintype (O ⧸ (Ideal.span {primaryGenerator I}) * (Ideal.span {primaryGenerator J})) := Fintype.ofFinite _
  have hc : IsCoprime (Ideal.span {primaryGenerator I}) (Ideal.span {primaryGenerator J}) := by
    rwa [(primaryGenerator_spec I hI.2).1, (primaryGenerator_spec J hJ.2).1]
  dsimp only [cubicPairGauss]
  rw [gauss_sum_actual_O ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates
    (primaryGenerator I) (primaryGenerator J) hI.2 hJ.2 hc,
    cubic_pair_cross_phase I J hI hJ hcop, one_mul,
    gaussSum_inverse_of_even _ _ (principalCubicCharacter_neg_one I hI),
    gaussTwo_eq_gaussSum I hI, gaussTwo_eq_gaussSum J hJ]
  have halg (a b : ℂ) (x y : ℝ) :
      star a * b / ((x : ℂ) * (y : ℂ)) = star (a / (x : ℂ)) * (b / (y : ℂ)) := by
    simp only [star_div₀, Complex.star_def, Complex.conj_ofReal]
    ring
  exact halg _ _ _ _

end
end SevenEighths.CubicSieve

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.GaussNorm
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem gaussTwo_norm_one (I : Ideal O) (hI : Admissible I) : ‖gaussTwo I hI.2‖ = 1 := by
  let c := primaryGenerator I
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hI.2
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let (P : PrimeIndex I) : Fintype (O ⧸ P.val) := Fintype.ofFinite _
  let (P : PrimeIndex I) : Field (O ⧸ P.val) := Ideal.Quotient.field P.val
  have hc : Ideal.span {c} = ∏ P : PrimeIndex I, P.val :=
    (primaryGenerator_spec I hI.2).1.trans (primeIndex_product I hI).symm
  let e : (O ⧸ Ideal.span {c}) ≃+* ∀ P : PrimeIndex I, O ⧸ P.val :=
    (Ideal.quotEquivOfEq hc).trans
      (IdealGaussCRT.quotientProdEquivPi (fun P : PrimeIndex I => P.val)
        (CanonicalRowCompletion.primeIndex_pairwise_coprime I))
  let χ : ∀ P : PrimeIndex I, MulChar (O ⧸ P.val) ℂ :=
    fun P => actualSextic P.val (primeIndex_good I hI.2 P) ^ 2
  let ψ := eisTraceModChar ShortDraftTrace.breveE
    ConcreteBreveE.breveE_period_coordinates c hI.2
  have hψ : ψ.IsPrimitive := GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive c hI.2
  have hχ : ∀ P : PrimeIndex I, χ P ≠ 1 := fun P =>
    cubicExponent_nonprincipal P.val (primeIndex_good I hI.2 P) false
  have hnormsq := IdealGaussCRT.norm_gauss_finite_crt_sq (fun P : PrimeIndex I => O ⧸ P.val)
    e χ ψ hχ (fun P => IdealGaussCRT.coordinateAddChar_isPrimitive
      (fun P : PrimeIndex I => O ⧸ P.val) e ψ hψ P)
  have hrow (x : O ⧸ Ideal.span {c}) : (∏ P : PrimeIndex I, χ P (e x P)) =
      CompletedGauss.cubicRow I hI.2 ((Ideal.quotEquivOfEq (primaryGenerator_spec I hI.2).1) x) := by
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
    dsimp only [c] at z ⊢
    simp only [e, c, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
      IdealGaussCRT.quotientProdEquivPi_mk, CompletedGauss.cubicRow_mk, χ]
  simp_rw [hrow] at hnormsq
  have hcard : (Fintype.card (O ⧸ Ideal.span {c}) : ℝ) = ‖eisEmbedding c‖ ^ 2 := by
    symm
    simpa only [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card] using
      eisEmbedding_norm_sq_eq_absNorm_span c
  rw [hcard] at hnormsq
  have hnorm := (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hnormsq
  change ‖(∑ x : O ⧸ Ideal.span {c},
    CompletedGauss.cubicRow I hI.2 ((Ideal.quotEquivOfEq (primaryGenerator_spec I hI.2).1) x) * ψ x) /
    (‖eisEmbedding c‖ : ℂ)‖ = 1
  rw [norm_div, hnorm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  exact div_self (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hI.2))

end
end SevenEighths.CubicSieve

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.PairPrimes
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
noncomputable section
local notation "O" => ActualEisensteinCubic.O

lemma pairExponent_nonprincipal (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (P : PrimeIndex I ⊕ PrimeIndex J) :
    actualSextic (pairPrime I J P) (pairPrime_good I J hI hJ P) ^ pairExponent I J P ≠ 1 := by
  cases P with
  | inl P => exact cubicExponent_nonprincipal P.val (primeIndex_good I hI.2 P) true
  | inr P => exact cubicExponent_nonprincipal P.val (primeIndex_good J hJ.2 P) false

lemma primeIndex_cubic_row (I : Ideal O) (hI : Admissible I) (z : O) :
    finiteSexticRow (fun P : PrimeIndex I => P.val) (primeIndex_good I hI.2) (fun _ => 2) z =
      cubicRow I z := by
  exact (CompletedGauss.cubicRow_mk I hI.2 z).symm.trans
    (CubicEisenstein.cubicRow_eq_idealSymbol I hI.2 hI.1 z)

lemma primeIndex_conjugate_cubic_row (I : Ideal O) (hI : Admissible I) (z : O) :
    finiteSexticRow (fun P : PrimeIndex I => P.val) (primeIndex_good I hI.2) (fun _ => 4) z =
      star (cubicRow I z) := by
  have he : finiteSexticRow (fun P : PrimeIndex I => P.val) (primeIndex_good I hI.2) (fun _ => 4) z =
      (finiteSexticRow (fun P : PrimeIndex I => P.val) (primeIndex_good I hI.2) (fun _ => 2) z) ^ 2 := by
    simp only [finiteSexticRow, ← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro P hP
    rw [MulChar.pow_apply' _ (by decide : (4 : ℕ) ≠ 0),
      MulChar.pow_apply' _ (by decide : (2 : ℕ) ≠ 0), ← pow_mul]
  rw [he, primeIndex_cubic_row I hI, cubicRow_square_eq_star]

lemma pairPrime_row (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J) (z : O) :
    finiteSexticRow (pairPrime I J) (pairPrime_good I J hI hJ) (pairExponent I J) z =
      star (cubicRow I z) * cubicRow J z := by
  unfold finiteSexticRow
  rw [Fintype.prod_sum_type]
  change finiteSexticRow (fun P : PrimeIndex I => P.val) (primeIndex_good I hI.2) (fun _ => 4) z *
    finiteSexticRow (fun P : PrimeIndex J => P.val) (primeIndex_good J hJ.2) (fun _ => 2) z = _
  rw [primeIndex_conjugate_cubic_row I hI, primeIndex_cubic_row J hJ]

end
end SevenEighths.CubicSieve

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.PairPoisson
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open EisensteinSchwartzPoisson GaussGeneratorTransport
noncomputable section
local notation "O" => ActualEisensteinCubic.O

lemma pairPrincipalRow_mk (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hcop : IsCoprime I J) (z : O) :
    pairPrincipalRow I J hI hJ hcop (Ideal.Quotient.mk _ z) =
      star (cubicRow I z) * cubicRow J z := by
  unfold pairPrincipalRow
  rw [principalSexticRow_mk (pairPrime I J) (pairPrime_coprime I J hI hJ hcop)
    (pairPrime_good I J hI hJ) (pairExponent I J) _ (pairPrime_modulus I J hI hJ) z,
    pairPrime_row I J hI hJ]

lemma pairPrincipalGauss_eq (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hcop : IsCoprime I J) :
    principalNormalizedGauss (pairPrime I J) (pairPrime_coprime I J hI hJ hcop)
      (pairPrime_good I J hI hJ) (pairExponent I J)
      (primaryGenerator I * primaryGenerator J) (pairPrime_modulus I J hI hJ)
      (mul_ne_zero hI.2 hJ.2) = cubicPairGauss I J hI hJ := by
  let a := primaryGenerator I
  let b := primaryGenerator J
  let : Finite (O ⧸ Ideal.span {a * b}) := finite_quotient_span (mul_ne_zero hI.2 hJ.2)
  let : Fintype (O ⧸ Ideal.span {a * b}) := Fintype.ofFinite _
  let : Finite (O ⧸ (Ideal.span {a}) * (Ideal.span {b})) := finite_quotient_product hI.2 hJ.2
  let : Fintype (O ⧸ (Ideal.span {a}) * (Ideal.span {b})) := Fintype.ofFinite _
  let : Finite (O ⧸ Ideal.span {a}) := finite_quotient_span hI.2
  let e : (O ⧸ Ideal.span {a * b}) ≃+* (O ⧸ (Ideal.span {a}) * (Ideal.span {b})) :=
    Ideal.quotEquivOfEq (Ideal.span_singleton_mul_span_singleton a b).symm
  have hnorm : (‖eisEmbedding (a * b)‖ : ℂ) = (‖eisEmbedding a‖ : ℂ) * (‖eisEmbedding b‖ : ℂ) := by
    rw [map_mul, norm_mul, Complex.ofReal_mul]
  dsimp only [principalNormalizedGauss, cubicPairGauss]
  rw [hnorm]
  congr 1
  rw [← Equiv.sum_comp e.toEquiv]
  apply Finset.sum_congr rfl
  intro x hx
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
  change pairPrincipalRow I J hI hJ hcop (Ideal.Quotient.mk _ z) * _ = _
  rw [pairPrincipalRow_mk]
  simp only [e, a, b, RingEquiv.toEquiv_eq_coe, RingEquiv.coe_toEquiv, Ideal.quotEquivOfEq_mk, Ideal.Quotient.factor_mk]
  rw [← MulChar.star_apply', principalCubicCharacter_mk I hI, principalCubicCharacter_mk J hJ]
  congr 1

lemma pairPrincipalGauss_separation (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hcop : IsCoprime I J) :
    principalNormalizedGauss (pairPrime I J) (pairPrime_coprime I J hI hJ hcop)
      (pairPrime_good I J hI hJ) (pairExponent I J)
      (primaryGenerator I * primaryGenerator J) (pairPrime_modulus I J hI hJ)
      (mul_ne_zero hI.2 hJ.2) = star (gaussTwo I hI.2) * gaussTwo J hJ.2 := by
  rw [pairPrincipalGauss_eq I J hI hJ hcop, cubicPairGauss_separation I J hI hJ hcop]

theorem cubic_pair_poisson (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hcop : IsCoprime I J) (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    (∑' z : O, (star (cubicRow I z) * cubicRow J z) * W (‖eisEmbedding z‖ ^ 2 / M)) =
      ((M : ℂ) * (star (gaussTwo I hI.2) * gaussTwo J hJ.2) /
        (‖eisEmbedding (primaryGenerator I * primaryGenerator J)‖ : ℂ)) *
      ∑' h : O, (cubicRow I h * star (cubicRow J h)) *
        paperRadialFourier W (M * ‖eisEmbedding h‖ ^ 2 /
          ‖eisEmbedding (primaryGenerator I * primaryGenerator J)‖ ^ 2) := by
  let c := primaryGenerator I * primaryGenerator J
  have hc0 : c ≠ 0 := mul_ne_zero hI.2 hJ.2
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc0
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let e := Ideal.quotEquivOfEq (pairPrime_modulus I J hI hJ)
  let : Fintype (O ⧸ ∏ P, pairPrime I J P) := Fintype.ofEquiv (O ⧸ Ideal.span {c}) e.toEquiv
  let (P : PrimeIndex I ⊕ PrimeIndex J) : Fintype (O ⧸ pairPrime I J P) := Fintype.ofFinite _
  let row := pairPrincipalRow I J hI hJ hcop
  let ψ := eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates c hc0
  let G := ∑ r : O ⧸ Ideal.span {c}, row r * ψ r
  have ht (h : O) :
      (∑ r : O ⧸ Ideal.span {c}, row r * ψ (Ideal.Quotient.mk (Ideal.span {c}) h * r)) =
        (cubicRow I h * star (cubicRow J h)) * G := by
    have hh := canonical_principal_gauss_transform_of_nontrivial (pairPrime I J)
      (pairPrime_coprime I J hI hJ hcop) (pairPrime_good I J hI hJ) (pairExponent I J)
      (pairExponent_nonprincipal I J hI hJ) c (pairPrime_modulus I J hI hJ) ψ
      (Ideal.Quotient.mk (Ideal.span {c}) h)
    change (∑ r, row r * ψ (Ideal.Quotient.mk (Ideal.span {c}) h * r)) =
      star (row (Ideal.Quotient.mk (Ideal.span {c}) h)) * G at hh
    change (∑ r, row r * ψ (Ideal.Quotient.mk (Ideal.span {c}) h * r)) =
      star (pairPrincipalRow I J hI hJ hcop (Ideal.Quotient.mk _ h)) * G at hh
    rw [pairPrincipalRow_mk I J hI hJ hcop h, star_mul, star_star,
      mul_comm (star (cubicRow J h)) (cubicRow I h)] at hh
    exact hh
  have hp := actual_radial_paper_poisson_trace W M hM c hc0 row
  change (∑' z : O, row (Ideal.Quotient.mk (Ideal.span {c}) z) * W (‖eisEmbedding z‖ ^ 2 / M)) =
      (M / ‖eisEmbedding c‖ ^ 2 : ℝ) • ∑' h : O,
        (∑ r : O ⧸ Ideal.span {c}, row r * ψ (Ideal.Quotient.mk (Ideal.span {c}) h * r)) *
          paperRadialFourier W (M * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2) at hp
  simp_rw [ht] at hp
  have hsum : (∑' h : O, ((cubicRow I h * star (cubicRow J h)) * G) *
      paperRadialFourier W (M * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2)) =
      G * ∑' h : O, (cubicRow I h * star (cubicRow J h)) *
        paperRadialFourier W (M * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro h
    ring
  rw [hsum] at hp
  have hrow (z : O) : row (Ideal.Quotient.mk (Ideal.span {c}) z) =
      star (cubicRow I z) * cubicRow J z :=
    pairPrincipalRow_mk I J hI hJ hcop z
  simp_rw [hrow] at hp
  rw [hp]
  have hn : (‖eisEmbedding c‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hc0))
  have hGauss := pairPrincipalGauss_separation I J hI hJ hcop
  change G / (‖eisEmbedding c‖ : ℂ) = star (gaussTwo I hI.2) * gaussTwo J hJ.2 at hGauss
  have hG := (div_eq_iff hn).mp hGauss
  change ((M / ‖eisEmbedding c‖ ^ 2 : ℝ) : ℂ) * (G * _) = _
  rw [← mul_assoc]
  congr 1
  change ((M / ‖eisEmbedding c‖ ^ 2 : ℝ) : ℂ) * G =
    (M : ℂ) * (star (gaussTwo I hI.2) * gaussTwo J hJ.2) / (‖eisEmbedding c‖ : ℂ)
  rw [hG]
  push_cast
  field_simp [hn]

end
end SevenEighths.CubicSieve

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.KernelTransfer
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open EisensteinSchwartzPoisson FourierBridge
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem cubic_radial_kernel_transfer (W : 𝓢(ℝ, ℂ)) (Lr Lc : ℝ)
    (hLr : 0 ≤ Lr) (hLc : 0 ≤ Lc) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ∀ {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
        (ε : ℝ) (hε : 0 < ε) (M N : ℝ) (_hN : 0 ≤ N)
        (rows : m → O) (cols : n → Ideal O)
        (_hr : Function.Injective rows) (_hc : Function.Injective cols)
        (_hrows : ∀ i, rows i ≠ 0 ∧ (Ideal.absNorm (Ideal.span {rows i}) : ℝ) ≤ M)
        (_hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N)
        (a b : n → ℂ) (E : ℝ) (_hE : 0 ≤ E)
        (_ha : (∑ j, ‖a j‖ ^ 2) ≤ E) (_hb : (∑ j, ‖b j‖ ^ 2) ≤ E)
        (x : m → ℝ) (y : n → ℝ) (_hx : ∀ i, |x i| ≤ Lr) (_hy : ∀ j, |y j| ≤ Lc),
        (1 + R) ^ A *
          (∑ i, ‖∑ j, ∑ k, (if IsCoprime (cols j) (cols k) then
            star (cubicRow (cols j) (rows i) * a j) *
              (cubicRow (cols k) (rows i) * b k) else 0) *
            paperRadialFourier W (R * Real.exp (x i + (y j + y k)))‖) ≤
          C * (elementSieveNorm M N *
            (IdealCoprimeSieveOperator.supportConstant ε hε * N ^ ε) * E) := by
  obtain ⟨C, hC, htransfer⟩ := QuadraticKernelTransfer.radial_matrix_kernel_transfer
    W Lr (2 * Lc) hLr (by positivity) A
  refine ⟨C, hC, ?_⟩
  intro R hR m n _ _ _ _ ε hε M N hN rows cols hr hc hrows hcols a b E hE ha hb x y hx hy
  let c : m → n × n → ℂ := fun i p => if IsCoprime (cols p.1) (cols p.2) then
    star (cubicRow (cols p.1) (rows i) * a p.1) *
      (cubicRow (cols p.2) (rows i) * b p.2) else 0
  let H := elementSieveNorm M N * (IdealCoprimeSieveOperator.supportConstant ε hε * N ^ ε) * E
  have hfac : 0 ≤ elementSieveNorm M N * (IdealCoprimeSieveOperator.supportConstant ε hε * N ^ ε) :=
    mul_nonneg (elementSieveNorm_nonneg _ _)
      (mul_nonneg (IdealCoprimeSieveOperator.supportConstant_pos ε hε).le (Real.rpow_nonneg hN _))
  have hH : 0 ≤ H := mul_nonneg hfac hE
  have hyy (p : n × n) : |y p.1 + y p.2| ≤ 2 * Lc :=
    (abs_add_le _ _).trans (by linarith [hy p.1, hy p.2])
  have hphase (t : ℝ) : (∑ i, ‖∑ p : n × n, c i p * logPhase t (y p.1 + y p.2)‖) ≤ H := by
    let aTwist : n → ℂ := fun j => a j * star (logPhase t (y j))
    let bTwist : n → ℂ := fun j => b j * logPhase t (y j)
    have ha' : (∑ j, ‖aTwist j‖ ^ 2) ≤ E := by simpa only [aTwist, norm_mul, norm_star, logPhase_norm, mul_one] using ha
    have hb' : (∑ j, ‖bTwist j‖ ^ 2) ≤ E := by simpa only [bTwist, norm_mul, logPhase_norm, mul_one] using hb
    have he (i : m) : (∑ p : n × n, c i p * logPhase t (y p.1 + y p.2)) =
        ∑ j, ∑ k, if IsCoprime (cols j) (cols k) then
          star (cubicRow (cols j) (rows i) * aTwist j) *
            (cubicRow (cols k) (rows i) * bTwist k) else 0 := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk
      dsimp only [c, aTwist, bTwist]
      split_ifs
      · rw [logPhase_add]
        simp only [star_mul, star_star]
        ring
      · simp only [zero_mul]
    simp_rw [he]
    have hbil := element_coprime_bilinear_bound ε hε M N hN rows cols hr hc hrows hcols aTwist bTwist
    apply (sq_le_sq₀ (by positivity) hH).mp
    apply hbil.trans
    calc
      _ ≤ (elementSieveNorm M N * (IdealCoprimeSieveOperator.supportConstant ε hε * N ^ ε) * E) *
          (elementSieveNorm M N * (IdealCoprimeSieveOperator.supportConstant ε hε * N ^ ε) * E) :=
        mul_le_mul (mul_le_mul_of_nonneg_left ha' hfac) (mul_le_mul_of_nonneg_left hb' hfac)
          (by positivity) hH
      _ = H ^ 2 := by ring
  have ht := htransfer R hR c x (fun p : n × n => y p.1 + y p.2) H hH hx hyy hphase
  simpa only [Fintype.sum_prod_type, c, H] using ht

end
end SevenEighths.CubicSieve

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.FrequencyShell
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open EisensteinSchwartzPoisson FourierBridge
noncomputable section
local notation "O" => ActualEisensteinCubic.O

lemma log_shell_ratio (K q : ℝ) (hK : 0 < K) (hq : K / 2 ≤ q ∧ q ≤ K) :
    |Real.log (q / K)| ≤ 4 := by
  apply CanonicalQuadraticSieve.middleRatio_log_bound
  constructor
  · apply (le_div_iff₀ hK).mpr
    linarith [hq.1]
  · apply (div_le_iff₀ hK).mpr
    linarith [hq.2]

lemma log_inverse_shell_ratio (N q : ℝ) (hN : 0 < N) (hq : N / 2 ≤ q ∧ q ≤ N) :
    |Real.log (N / q)| ≤ 4 := by
  have hq0 : 0 < q := by linarith [hq.1]
  apply CanonicalQuadraticSieve.middleRatio_log_bound
  constructor
  · apply (le_div_iff₀ hq0).mpr
    linarith [hq.2]
  · apply (div_le_iff₀ hq0).mpr
    linarith [hq.1]

lemma radial_product_log_identity (M K N q u v : ℝ)
    (hK : 0 < K) (hN : 0 < N) (hq : 0 < q) (hu : 0 < u) (hv : 0 < v) :
    (M * K / N ^ 2) * Real.exp (Real.log (q / K) + (Real.log (N / u) + Real.log (N / v))) =
      M * q / (u * v) := by
  rw [Real.exp_add, Real.exp_add, Real.exp_log (div_pos hq hK),
    Real.exp_log (div_pos hN hu), Real.exp_log (div_pos hN hv)]
  field_simp

theorem cubic_frequency_shell_bound (W : 𝓢(ℝ, ℂ)) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
        (ε : ℝ) (hε : 0 < ε) (M K N : ℝ) (_hM : 0 < M) (_hK : 0 < K) (_hN : 0 < N)
        (rows : m → O) (cols : n → Ideal O)
        (_hr : Function.Injective rows) (_hc : Function.Injective cols)
        (_hrows : ∀ i, K / 2 ≤ (Ideal.absNorm (Ideal.span {rows i}) : ℝ) ∧
          (Ideal.absNorm (Ideal.span {rows i}) : ℝ) ≤ K)
        (_hcols : ∀ j, Admissible (cols j) ∧ N / 2 ≤ (Ideal.absNorm (cols j) : ℝ) ∧
          (Ideal.absNorm (cols j) : ℝ) ≤ N)
        (a b : n → ℂ) (E : ℝ) (_hE : 0 ≤ E)
        (_ha : (∑ j, ‖a j‖ ^ 2) ≤ E) (_hb : (∑ j, ‖b j‖ ^ 2) ≤ E),
        (1 + M * K / N ^ 2) ^ A *
          (∑ i, ‖∑ j, ∑ k, (if IsCoprime (cols j) (cols k) then
            star (cubicRow (cols j) (rows i) * a j) *
              (cubicRow (cols k) (rows i) * b k) else 0) *
            paperRadialFourier W (M * (Ideal.absNorm (Ideal.span {rows i}) : ℝ) /
              ((Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ)))‖) ≤
          C * (elementSieveNorm K N *
            (IdealCoprimeSieveOperator.supportConstant ε hε * N ^ ε) * E) := by
  obtain ⟨C, hC, ht⟩ := cubic_radial_kernel_transfer W 4 4 (by norm_num) (by norm_num) A
  refine ⟨C, hC, ?_⟩
  intro m n _ _ _ _ ε hε M K N hM hK hN rows cols hr hc hrows hcols a b E hE ha hb
  have hq (i : m) : 0 < (Ideal.absNorm (Ideal.span {rows i}) : ℝ) := by linarith [(hrows i).1]
  have hn (j : n) : 0 < (Ideal.absNorm (cols j) : ℝ) := by linarith [(hcols j).2.1]
  have hr0 (i : m) : rows i ≠ 0 := by
    intro hz
    simpa [hz] using hq i
  have hp := ht (M * K / N ^ 2) (by positivity) ε hε K N hN.le rows cols hr hc
    (fun i => ⟨hr0 i, (hrows i).2⟩) (fun j => ⟨(hcols j).1, (hcols j).2.2⟩)
    a b E hE ha hb
    (fun i => Real.log ((Ideal.absNorm (Ideal.span {rows i}) : ℝ) / K))
    (fun j => Real.log (N / (Ideal.absNorm (cols j) : ℝ)))
    (fun i => log_shell_ratio K _ hK (hrows i))
    (fun j => log_inverse_shell_ratio N _ hN (hcols j).2)
  simp_rw [radial_product_log_identity M K N _ _ _ hK hN (hq _) (hn _) (hn _)] at hp
  exact hp

end
end SevenEighths.CubicSieve

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.DualCoefficients
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open EisensteinSchwartzPoisson
noncomputable section
local notation "O" => ActualEisensteinCubic.O

lemma cubicDualCoefficient_norm_sq {n : Type*}
    (cols : n → Ideal O) (hc : ∀ j, Admissible (cols j)) (a : n → ℂ) (j : n) :
    ‖cubicDualCoefficient cols hc a j‖ ^ 2 = ‖a j‖ ^ 2 / (Ideal.absNorm (cols j) : ℝ) := by
  simp only [cubicDualCoefficient, norm_div, norm_star, norm_mul, gaussTwo_norm_one _ (hc j),
    mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), div_pow,
    primaryGenerator_norm_sq _ (hc j).2]

lemma cubicDualCoefficient_energy {n : Type*} [Fintype n]
    (cols : n → Ideal O) (hc : ∀ j, Admissible (cols j)) (a : n → ℂ)
    (N : ℝ) (hN : 0 < N) (hcols : ∀ j, N / 2 ≤ (Ideal.absNorm (cols j) : ℝ)) :
    (∑ j, ‖cubicDualCoefficient cols hc a j‖ ^ 2) ≤ (2 / N) * ∑ j, ‖a j‖ ^ 2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  rw [cubicDualCoefficient_norm_sq]
  calc
    _ ≤ ‖a j‖ ^ 2 / (N / 2) :=
      div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (hcols j)
    _ = _ := by field_simp

lemma cubicDualRow_eq_gram {n : Type*} [Fintype n]
    (cols : n → Ideal O) (hc : ∀ j, Admissible (cols j)) (a : n → ℂ)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (h : O) :
    cubicDualRow cols hc a W M h =
      ∑ j, ∑ k, (if IsCoprime (cols j) (cols k) then
        star (cubicRow (cols j) h * cubicDualCoefficient cols hc a j) *
          (cubicRow (cols k) h * cubicDualCoefficient cols hc a k) else 0) *
        paperRadialFourier W (M * (Ideal.absNorm (Ideal.span {h}) : ℝ) /
          ((Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ))) := by
  unfold cubicDualRow
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  rw [isCoprime_comm (x := cols k) (y := cols j)]
  by_cases hcop : IsCoprime (cols j) (cols k)
  · rw [if_pos hcop, if_pos hcop]
    have hscale : (Ideal.absNorm (cols k) : ℝ) * (Ideal.absNorm (cols j) : ℝ) =
        (Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ) := mul_comm _ _
    rw [hscale]
    congr 1
    simp only [cubicDualCoefficient, star_mul, star_div₀, Complex.star_def, Complex.conj_ofReal, Complex.conj_conj]
    ring
  · simp only [if_neg hcop, zero_mul]

lemma cubicRow_zero_of_ne_one (I : Ideal O) (hI : Admissible I) (hI1 : I ≠ 1) :
    cubicRow I 0 = 0 := by
  have hI_top : I ≠ ⊤ := by simpa only [Ideal.one_eq_top] using hI1
  have hcop : ¬ IsCoprime I (Ideal.span {(0 : O)}) := by
    simpa only [Ideal.isCoprime_iff_sup_eq, Ideal.span_singleton_zero, sup_bot_eq] using hI_top
  have h := idealSymbol_cube_mask I 0 hI.2
  rw [if_neg hcop] at h
  exact eq_zero_of_pow_eq_zero h

end
end SevenEighths.CubicSieve

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.DualShell
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open EisensteinSchwartzPoisson
noncomputable section
local notation "O" => ActualEisensteinCubic.O

lemma cubicDualRow_zero {n : Type*} [Fintype n]
    (cols : n → Ideal O) (hc : ∀ j, Admissible (cols j))
    (hunit : ∀ j, cols j ≠ 1) (a : n → ℂ) (W : 𝓢(ℝ, ℂ)) (M : ℝ) :
    cubicDualRow cols hc a W M 0 = 0 := by
  unfold cubicDualRow
  apply Finset.sum_eq_zero
  intro j hj
  apply Finset.sum_eq_zero
  intro k hk
  rw [cubicRow_zero_of_ne_one _ (hc j) (hunit j)]
  simp

theorem cubic_dual_shell_bound (W : 𝓢(ℝ, ℂ)) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
        (ε : ℝ) (hε : 0 < ε) (M K N : ℝ) (_hM : 0 < M) (_hK : 0 < K) (_hN : 0 < N)
        (rows : m → O) (cols : n → Ideal O)
        (_hr : Function.Injective rows) (_hc : Function.Injective cols)
        (_hrows : ∀ i, K / 2 ≤ (Ideal.absNorm (Ideal.span {rows i}) : ℝ) ∧
          (Ideal.absNorm (Ideal.span {rows i}) : ℝ) ≤ K)
        (hcols : ∀ j, Admissible (cols j) ∧ N / 2 ≤ (Ideal.absNorm (cols j) : ℝ) ∧
          (Ideal.absNorm (cols j) : ℝ) ≤ N) (a : n → ℂ),
        (1 + M * K / N ^ 2) ^ A *
          (∑ i, ‖cubicDualRow cols (fun j => (hcols j).1) a W M (rows i)‖) ≤
          C * (elementSieveNorm K N *
            (IdealCoprimeSieveOperator.supportConstant ε hε * N ^ ε) *
              ((2 / N) * ∑ j, ‖a j‖ ^ 2)) := by
  obtain ⟨C, hC, hb⟩ := cubic_frequency_shell_bound W A
  refine ⟨C, hC, ?_⟩
  intro m n _ _ _ _ ε hε M K N hM hK hN rows cols hr hc hrows hcols a
  have he := cubicDualCoefficient_energy cols (fun j => (hcols j).1) a N hN
    (fun j => (hcols j).2.1)
  have h := hb ε hε M K N hM hK hN rows cols hr hc hrows hcols
    (cubicDualCoefficient cols (fun j => (hcols j).1) a)
    (cubicDualCoefficient cols (fun j => (hcols j).1) a)
    ((2 / N) * ∑ j, ‖a j‖ ^ 2) (by positivity) he he
  simpa only [cubicDualRow_eq_gram] using h

end
end SevenEighths.CubicSieve

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.FrequencyDyads
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
noncomputable section
local notation "O" => ActualEisensteinCubic.O

lemma frequencyDyad_bounds (j : ℕ) (h : O) (hh : h ∈ frequencyDyad j) :
    h ≠ 0 ∧ (2 : ℝ)^j / 2 ≤ (Ideal.absNorm (Ideal.span {h}) : ℝ) ∧
      (Ideal.absNorm (Ideal.span {h}) : ℝ) ≤ (2 : ℝ)^j := by
  obtain ⟨hn, hj⟩ := (mem_frequencyDyad h j).mp hh
  have hnorm : Ideal.absNorm (Ideal.span {h}) ≠ 0 := by
    exact Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hn)
  have hu := Nat.le_pow_clog (by norm_num : 1 < 2) (Ideal.absNorm (Ideal.span {h}))
  have hl := two_pow_clog_le_double _ (Nat.one_le_iff_ne_zero.mpr hnorm)
  rw [hj] at hu hl
  refine ⟨hn, ?_, by exact_mod_cast hu⟩
  have hr : (2 : ℝ)^j ≤ 2 * (Ideal.absNorm (Ideal.span {h}) : ℝ) := by exact_mod_cast hl
  linarith

theorem tsum_frequencyDyads_with_zero (f : O → ℂ) (hf : Summable f) :
    (∑' h : O, f h) = f 0 + ∑' j : ℕ, ∑ h : frequencyDyad j, f h.val := by
  have he : (∑' h : O, f h) = f 0 + ∑' h : {h : O // h ≠ 0}, f h.val := by
    have hs := (hf.sum_add_tsum_compl (s := {0})).symm
    have hset : ((↑({0} : Finset O) : Set O)ᶜ) = {h : O | h ≠ 0} := by
      ext h
      simp
    rw [hset] at hs
    simpa only [Finset.sum_singleton, Set.coe_ofPred] using hs
  rw [he]
  congr 1
  let g := (fun h : {h : O // h ≠ 0} => f h.val) ∘ frequencyDyadicEquiv.symm
  have hg : Summable g := frequencyDyadicEquiv.symm.summable_iff.mpr (hf.subtype _)
  calc
    _ = ∑' h, g h := (frequencyDyadicEquiv.symm.tsum_eq _).symm
    _ = ∑' j, ∑' h, g ⟨j,h⟩ := Summable.tsum_sigma' (fun _ => (hasSum_fintype _).summable) hg
    _ = _ := by
      apply tsum_congr
      intro j
      rw [tsum_fintype]
      rfl

end
end SevenEighths.CubicSieve

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.Smoothed
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open EisensteinSchwartzPoisson
noncomputable section
local notation "O" => ActualEisensteinCubic.O

lemma cubicRow_norm_le_one (I : Ideal O) (hI : Admissible I) (z : O) : ‖cubicRow I z‖ ≤ 1 :=
  elementCharacter_norm_le_one I hI.2 z

lemma cubic_pair_fourier_summable (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (W : 𝓢(ℝ, ℂ)) (t : ℝ) (ht : 0 < t) :
    Summable (fun h : O => (cubicRow I h * star (cubicRow J h)) *
      paperRadialFourier W (t * ‖eisEmbedding h‖ ^ 2)) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun h => norm_nonneg _) _
    (paperRadialFourier_lattice_summable_norm W t ht)
  intro h
  simp only [norm_mul, norm_star]
  exact (mul_le_mul_of_nonneg_right
    ((mul_le_mul_of_nonneg_right (cubicRow_norm_le_one I hI h) (norm_nonneg _)).trans
      (by simpa only [one_mul] using cubicRow_norm_le_one J hJ h))
    (norm_nonneg _)).trans_eq (one_mul _)

lemma pair_modulus_norm_sq (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J) :
    ‖eisEmbedding (primaryGenerator I * primaryGenerator J)‖ ^ 2 =
      (Ideal.absNorm I : ℝ) * (Ideal.absNorm J : ℝ) := by
  rw [map_mul, norm_mul, mul_pow, primaryGenerator_norm_sq I hI.2, primaryGenerator_norm_sq J hJ.2]

lemma cubicDualRow_summable {n : Type*} [Fintype n]
    (cols : n → Ideal O) (hc : ∀ j, Admissible (cols j))
    (a : n → ℂ) (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    Summable (cubicDualRow cols hc a W M) := by
  apply summable_sum
  intro j hj
  apply summable_sum
  intro k hk
  by_cases hcop : IsCoprime (cols j) (cols k)
  · simp only [if_pos hcop]
    have hjN : 0 < (Ideal.absNorm (cols j) : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (primaryGenerator_ne_zero_ideal _ (hc j).2))
    have hkN : 0 < (Ideal.absNorm (cols k) : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (primaryGenerator_ne_zero_ideal _ (hc k).2))
    have hs := (cubic_pair_fourier_summable (cols j) (cols k) (hc j) (hc k) W
      (M / ((Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ))) (by positivity)).mul_left
      (star (a j) * a k * (star (gaussTwo (cols j) (hc j).2) * gaussTwo (cols k) (hc k).2) /
        ((‖eisEmbedding (primaryGenerator (cols j))‖ : ℂ) * (‖eisEmbedding (primaryGenerator (cols k))‖ : ℂ)))
    convert (preTransparency := .instances) hs using 1
    ext z
    rw [eisEmbedding_norm_sq_eq_absNorm_span]
    rw [show M / ((Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ)) *
      (Ideal.absNorm (Ideal.span {z}) : ℝ) = M * (Ideal.absNorm (Ideal.span {z}) : ℝ) /
        ((Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ)) by ring]
    try simp only [mul_assoc]
  · simp only [if_neg hcop]
    exact summable_zero

lemma cubicDualRow_tsum {n : Type*} [Fintype n]
    (cols : n → Ideal O) (hc : ∀ j, Admissible (cols j))
    (a : n → ℂ) (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    (∑' h : O, cubicDualRow cols hc a W M h) =
      ∑ j, ∑ k, if IsCoprime (cols j) (cols k) then
        (star (a j) * a k * (star (gaussTwo (cols j) (hc j).2) * gaussTwo (cols k) (hc k).2) /
          ((‖eisEmbedding (primaryGenerator (cols j))‖ : ℂ) * (‖eisEmbedding (primaryGenerator (cols k))‖ : ℂ))) *
          ∑' h : O, (cubicRow (cols j) h * star (cubicRow (cols k) h)) *
            paperRadialFourier W (M * (Ideal.absNorm (Ideal.span {h}) : ℝ) /
              ((Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ))) else 0 := by
  have hs (j k : n) : Summable (fun h : O => (cubicRow (cols j) h * star (cubicRow (cols k) h)) *
      paperRadialFourier W (M * (Ideal.absNorm (Ideal.span {h}) : ℝ) /
        ((Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ)))) := by
    have hjN : 0 < (Ideal.absNorm (cols j) : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (primaryGenerator_ne_zero_ideal _ (hc j).2))
    have hkN : 0 < (Ideal.absNorm (cols k) : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (primaryGenerator_ne_zero_ideal _ (hc k).2))
    convert (preTransparency := .instances) cubic_pair_fourier_summable (cols j) (cols k) (hc j) (hc k) W
      (M / ((Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ))) (by positivity) using 1
    ext z
    rw [eisEmbedding_norm_sq_eq_absNorm_span]
    rw [show M / ((Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ)) *
      (Ideal.absNorm (Ideal.span {z}) : ℝ) = M * (Ideal.absNorm (Ideal.span {z}) : ℝ) /
        ((Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ)) by ring]
    try simp only [mul_assoc]
  unfold cubicDualRow
  rw [Summable.tsum_finsetSum (fun j hj => summable_sum (fun k hk => by
    split_ifs
    · simpa only [mul_assoc] using (hs j k).mul_left
        (star (a j) * a k * (star (gaussTwo (cols j) (hc j).2) * gaussTwo (cols k) (hc k).2) /
          ((‖eisEmbedding (primaryGenerator (cols j))‖ : ℂ) * (‖eisEmbedding (primaryGenerator (cols k))‖ : ℂ)))
    · exact summable_zero))]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Summable.tsum_finsetSum (fun k hk => by
    split_ifs
    · simpa only [mul_assoc] using (hs j k).mul_left
        (star (a j) * a k * (star (gaussTwo (cols j) (hc j).2) * gaussTwo (cols k) (hc k).2) /
          ((‖eisEmbedding (primaryGenerator (cols j))‖ : ℂ) * (‖eisEmbedding (primaryGenerator (cols k))‖ : ℂ)))
    · exact summable_zero)]
  apply Finset.sum_congr rfl
  intro k hk
  split_ifs <;> simp only [tsum_zero, mul_assoc, tsum_mul_left]

theorem cubicSmoothedCoprime_poisson {n : Type*} [Fintype n]
    (cols : n → Ideal O) (hc : ∀ j, Admissible (cols j))
    (a : n → ℂ) (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    cubicSmoothedCoprime cols a W M =
      (M : ℂ) * ∑' h : O, cubicDualRow cols hc a W M h := by
  rw [cubicDualRow_tsum cols hc a W M hM]
  unfold cubicSmoothedCoprime
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hcop : IsCoprime (cols j) (cols k)
  · rw [if_pos hcop, if_pos hcop, cubic_pair_poisson _ _ (hc j) (hc k) hcop W M hM]
    rw [pair_modulus_norm_sq _ _ (hc j) (hc k)]
    simp_rw [eisEmbedding_norm_sq_eq_absNorm_span]
    rw [map_mul, norm_mul, Complex.ofReal_mul]
    ring
  · simp only [if_neg hcop, mul_zero]

end
end SevenEighths.CubicSieve

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.ZeroMode
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open EisensteinSchwartzPoisson
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem cubicDualRow_zero_bound {n : Type*} [Fintype n] [DecidableEq n]
    (cols : n → Ideal O) (hc : ∀ j, Admissible (cols j))
    (hinj : Function.Injective cols) (a : n → ℂ) (W : 𝓢(ℝ, ℂ)) (M N : ℝ)
    (hN : 0 < N) (hcols : ∀ j, N/2 ≤ (Ideal.absNorm (cols j) : ℝ)) :
    ‖cubicDualRow cols hc a W M 0‖ ≤
      ((2/N) * ∑ j, ‖a j‖^2) * ‖paperRadialFourier W 0‖ := by
  by_cases hu : ∃ j, cols j = 1
  · obtain ⟨j₀, hj₀⟩ := hu
    have ho (j : n) (hj : j ≠ j₀) : cols j ≠ 1 := by
      intro he
      exact hj (hinj (he.trans hj₀.symm))
    have he : cubicDualRow cols hc a W M 0 =
        (star (cubicDualCoefficient cols hc a j₀) * cubicDualCoefficient cols hc a j₀) *
          paperRadialFourier W 0 := by
      rw [cubicDualRow_eq_gram]
      rw [Finset.sum_eq_single j₀]
      · rw [Finset.sum_eq_single j₀]
        · simp only [hj₀, cubicRow_one, one_mul, Ideal.span_singleton_zero,
            Ideal.absNorm_bot, Nat.cast_zero, mul_zero, zero_div, if_pos isCoprime_one_left]
        · intro k hk hkj
          rw [cubicRow_zero_of_ne_one _ (hc k) (ho k hkj)]
          simp
        · simp
      · intro j hj hjj
        rw [cubicRow_zero_of_ne_one _ (hc j) (ho j hjj)]
        simp
      · simp
    rw [he, norm_mul, norm_mul, norm_star, ← pow_two]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact (Finset.single_le_sum (fun j hj => sq_nonneg ‖cubicDualCoefficient cols hc a j‖)
      (Finset.mem_univ j₀)).trans (cubicDualCoefficient_energy cols hc a N hN hcols)
  · have hz : ∀ j, cols j ≠ 1 := fun j hj => hu ⟨j,hj⟩
    rw [cubicDualRow_zero cols hc hz a W M, norm_zero]
    positivity

end
end SevenEighths.CubicSieve

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.Recurrence
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open EisensteinSchwartzPoisson
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem cubic_smoothed_frequency_recurrence_all_oai (W : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {n : Type*} [Fintype n] [DecidableEq n]
        (ε : ℝ) (hε : 0 < ε) (M N : ℝ) (_hM : 0 < M) (_hN : 1 ≤ N)
        (cols : n → Ideal O) (_hc : Function.Injective cols)
        (_hcols : ∀ j, Admissible (cols j) ∧ N / 2 ≤ (Ideal.absNorm (cols j) : ℝ) ∧
          (Ideal.absNorm (cols j) : ℝ) ≤ N)
        (a : n → ℂ),
        ‖cubicSmoothedCoprime cols a W M‖ ≤
          M * (((2 / N) * ∑ j, ‖a j‖^2) * ‖paperRadialFourier W 0‖ + C * (IdealCoprimeSieveOperator.supportConstant ε hε * N^ε) *
            ((2 / N) * ∑ j, ‖a j‖^2) * ∑' l : ℕ, frequencyMajorant M N l) := by
  obtain ⟨C, hC, hshell⟩ := cubic_dual_shell_bound W 3
  refine ⟨C, hC, ?_⟩
  intro n _ _ ε hε M N hM hN cols hc hcols a
  have hN0 : 0 < N := by linarith
  let f : O → ℂ := cubicDualRow cols (fun j => (hcols j).1) a W M
  let B : ℝ := C * (IdealCoprimeSieveOperator.supportConstant ε hε * N^ε) *
    ((2 / N) * ∑ j, ‖a j‖^2)
  have hf : Summable f := cubicDualRow_summable cols (fun j => (hcols j).1) a W M hM
  have hblock (l : ℕ) : ‖∑ h : frequencyDyad l, f h.val‖ ≤ B * frequencyMajorant M N l := by
    have hp := hshell ε hε M ((2 : ℝ)^l) N hM (by positivity) hN0
      (fun h : frequencyDyad l => h.val) cols Subtype.val_injective hc
      (fun h => (frequencyDyad_bounds l h.val h.property).2) hcols a
    have hd : 0 < (1 + M * (2 : ℝ)^l / N^2)^3 := by positivity
    have hs : (∑ h : frequencyDyad l, ‖f h.val‖) ≤ B * frequencyMajorant M N l := by
      have he : B * frequencyMajorant M N l =
          (C * (elementSieveNorm ((2 : ℝ)^l) N *
            (IdealCoprimeSieveOperator.supportConstant ε hε * N^ε) *
              ((2 / N) * ∑ j, ‖a j‖^2))) / (1 + M * (2 : ℝ)^l / N^2)^3 := by
        dsimp only [B, frequencyMajorant]
        ring
      rw [he]
      apply (le_div_iff₀ hd).mpr
      simpa only [mul_comm] using hp
    exact (norm_sum_le _ _).trans hs
  have hg : Summable (fun l => B * frequencyMajorant M N l) :=
    (frequencyMajorant_summable M N hM hN).mul_left B
  have hb := (hg.of_norm_bounded hblock).hasSum.norm_le_of_bounded hg.hasSum hblock
  rw [tsum_mul_left] at hb
  rw [cubicSmoothedCoprime_poisson cols (fun j => (hcols j).1) a W M hM, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM]
  change M * ‖∑' h : O, f h‖ ≤ _
  rw [tsum_frequencyDyads_with_zero f hf]
  apply mul_le_mul_of_nonneg_left _ hM.le
  exact (norm_add_le _ _).trans (add_le_add
    (cubicDualRow_zero_bound cols (fun j => (hcols j).1) hc a W M N hN0
      (fun j => (hcols j).2.1)) hb)

end
end SevenEighths.CubicSieve

end OAI
end

theorem solution.{u_1} : type_of% @OAI.SevenEighths.CubicSieve.cubic_smoothed_frequency_recurrence_all_oai.{u_1} := @OAI.SevenEighths.CubicSieve.cubic_smoothed_frequency_recurrence_all_oai.{u_1}
