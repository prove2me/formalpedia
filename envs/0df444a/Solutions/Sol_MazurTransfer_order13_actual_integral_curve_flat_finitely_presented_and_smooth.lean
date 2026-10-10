-- Prove2me | solution 1 for MazurTransfer.order13_actual_integral_curve_flat_finitely_presented_and_smooth
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-10T01:15:29.156071+00:00
-- url     : https://prove2.me/submissions/ad4b5ff0-24fa-4595-b9b0-e631e26ef65a

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: flatness, local finite presentation and conditional smoothness
of the literal two-chart order-thirteen curve over actual commutative rings.
Named downstream consumer: actual compatible good-reduction models at 3 and 5.
The hypothesis that 104 is a unit is explicit and applies only to smoothness.
-/
import Mathlib
import Definitions.Def_MazurTransfer_Order13ExplicitCurve


section
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Literal curve: MazurTheorem at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c.
Design boundary: flatness and local finite presentation of the literal
two-chart curve over any commutative base ring. These conclusions do not
assert smoothness, good reduction, or a Jacobian family.
Named downstream consumer: the actual integral model used to establish
compatible good reduction of the order-thirteen Jacobian.
-/

noncomputable section
universe u
open Polynomial CategoryTheory AlgebraicGeometry

namespace MazurTransfer.Order13IntegralCurve

variable (R : Type u) [CommRing R]

theorem quadraticCoordinateRing_flat (f : Polynomial R) :
    Module.Flat R (AdjoinRoot (X ^ 2 - C f)) := by
  let : Module.Free (Polynomial R) (AdjoinRoot (X ^ 2 - C f)) :=
    (Polynomial.monic_X_pow_sub_C f (by decide)).free_adjoinRoot
  exact Module.Flat.trans R (Polynomial R) (AdjoinRoot (X ^ 2 - C f))

theorem quadraticCoordinateRing_finitePresentation (f : Polynomial R) :
    Algebra.FinitePresentation R (AdjoinRoot (X ^ 2 - C f)) := by
  infer_instance

open MazurTorsion.XOneThirteenProjectiveCurve

theorem ordinaryChartToBase_flat :
    Flat (ordinaryChartToBase R) := by
  have : Module.Flat R (MazurTorsion.XOneThirteenAffineCurve.CoordinateRing R) :=
    quadraticCoordinateRing_flat R _
  unfold ordinaryChartToBase
  rw [Flat.SpecMap_iff]
  change (algebraMap R (MazurTorsion.XOneThirteenAffineCurve.CoordinateRing R)).Flat
  exact RingHom.flat_algebraMap_iff.mpr inferInstance

theorem reciprocalChartToBase_flat :
    Flat (reciprocalChartToBase R) := by
  have : Module.Flat R (ReciprocalRing R) := quadraticCoordinateRing_flat R _
  unfold reciprocalChartToBase
  rw [Flat.SpecMap_iff]
  change (algebraMap R (ReciprocalRing R)).Flat
  exact RingHom.flat_algebraMap_iff.mpr inferInstance

theorem ordinaryChartToBase_locallyOfFinitePresentation :
    LocallyOfFinitePresentation (ordinaryChartToBase R) := by
  unfold ordinaryChartToBase
  rw [LocallyOfFinitePresentation.SpecMap_iff]
  change (algebraMap R (MazurTorsion.XOneThirteenAffineCurve.CoordinateRing R)).FinitePresentation
  exact RingHom.finitePresentation_algebraMap.mpr inferInstance

theorem reciprocalChartToBase_locallyOfFinitePresentation :
    LocallyOfFinitePresentation (reciprocalChartToBase R) := by
  unfold reciprocalChartToBase
  rw [LocallyOfFinitePresentation.SpecMap_iff]
  change (algebraMap R (ReciprocalRing R)).FinitePresentation
  exact RingHom.finitePresentation_algebraMap.mpr inferInstance

theorem curveToBase_flat : Flat (curveToBase R) := by
  haveI : IsZariskiLocalAtSource (@Flat.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
      (P := @Flat.{u}) (Q := @RingHom.Flat.{u,u})
  apply IsZariskiLocalAtSource.of_openCover (P := @Flat)
    (f := curveToBase R) (glueData R).openCover
  intro i
  cases i
  · change Flat (ordinaryChartMap R ≫ curveToBase R)
    rw [ordinaryChartMap_curveToBase]
    exact ordinaryChartToBase_flat R
  · change Flat (reciprocalChartMap R ≫ curveToBase R)
    rw [reciprocalChartMap_curveToBase]
    exact reciprocalChartToBase_flat R

theorem curveToBase_locallyOfFinitePresentation :
    LocallyOfFinitePresentation (curveToBase R) := by
  haveI : IsZariskiLocalAtSource (@LocallyOfFinitePresentation.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
      (P := @LocallyOfFinitePresentation.{u}) (Q := @RingHom.FinitePresentation.{u,u})
  apply IsZariskiLocalAtSource.of_openCover (P := @LocallyOfFinitePresentation)
    (f := curveToBase R) (glueData R).openCover
  intro i
  cases i
  · change LocallyOfFinitePresentation (ordinaryChartMap R ≫ curveToBase R)
    rw [ordinaryChartMap_curveToBase]
    exact ordinaryChartToBase_locallyOfFinitePresentation R
  · change LocallyOfFinitePresentation (reciprocalChartMap R ≫ curveToBase R)
    rw [reciprocalChartMap_curveToBase]
    exact reciprocalChartToBase_locallyOfFinitePresentation R

end MazurTransfer.Order13IntegralCurve

#print axioms MazurTransfer.Order13IntegralCurve.quadraticCoordinateRing_flat
#print axioms MazurTransfer.Order13IntegralCurve.quadraticCoordinateRing_finitePresentation
#print axioms MazurTransfer.Order13IntegralCurve.curveToBase_flat
#print axioms MazurTransfer.Order13IntegralCurve.curveToBase_locallyOfFinitePresentation

end
end

section
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Generalizes the complete checked hyperelliptic coordinate lifting proof
in the MazurTheorem good-characteristic geometry bridge.
Design boundary: genuine algebra smoothness over a commutative base ring
when the sextic and derivative are coprime and 2 is a unit. The proof
constructs lifts across every square-zero ideal, without a field hypothesis.
Named downstream consumer: the integral order-thirteen curve with 104 inverted.
-/

noncomputable section
namespace MazurTransfer.IntegralHyperellipticCoordinates
open Polynomial
universe u
variable (K : Type u) [CommRing K]

theorem hyperelliptic_coordinate_smooth (f : Polynomial K) (hf : IsCoprime f f.derivative) (h2 : IsUnit (2 : K)) :
    Algebra.Smooth K (AdjoinRoot
      ((X ^ 2 - C f) : Polynomial (Polynomial K))) := by
  let q : Polynomial (Polynomial K) := X ^ 2 - C f
  have hroot : AdjoinRoot.root q ^ 2 = AdjoinRoot.of q f := by
    apply sub_eq_zero.mp
    simpa only [q, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C] using
      AdjoinRoot.eval₂_root q
  obtain ⟨u, hu⟩ := h2
  have hinv : (2 : K) * ↑(u⁻¹) = 1 := by
    rw [← hu]
    simp
  obtain ⟨a, b, hab⟩ := hf
  have : Algebra.FormallySmooth K (AdjoinRoot q) := by
    apply Algebra.FormallySmooth.of_comp_surjective
    intro B _ _ I hI φ
    obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (φ (AdjoinRoot.of q X))
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (φ (AdjoinRoot.root q))
    have hφpoly : φ.comp (AdjoinRoot.ofAlgHom K q) =
        aeval (φ (AdjoinRoot.of q X)) := by
      apply Polynomial.algHom_ext
      simp
    have hφrelation : φ (AdjoinRoot.root q) ^ 2 =
        aeval (φ (AdjoinRoot.of q X)) f := by
      calc
        _ = φ (AdjoinRoot.of q f) := by
          simpa only [_root_.map_pow] using congrArg φ hroot
        _ = _ := DFunLike.congr_fun hφpoly f
    let e : B := y ^ 2 - aeval x f
    have hmap : (Ideal.Quotient.mkₐ K I).comp (aeval x) =
        aeval (Ideal.Quotient.mk I x) := by
      apply Polynomial.algHom_ext
      simp
    have hmapf : Ideal.Quotient.mkₐ K I (aeval x f) =
        aeval (Ideal.Quotient.mk I x) f := DFunLike.congr_fun hmap f
    have he0 : Ideal.Quotient.mkₐ K I e = 0 := by
      change Ideal.Quotient.mkₐ K I (y ^ 2 - aeval x f) = 0
      rw [_root_.map_sub, _root_.map_pow, hmapf]
      change Ideal.Quotient.mk I y ^ 2 - aeval (Ideal.Quotient.mk I x) f = 0
      rw [hx, hy, hφrelation, sub_self]
    have heI : e ∈ I := by
      apply (Ideal.Quotient.eq_zero_iff_mem).mp
      exact he0
    have sqzero {z : B} (hz : z ∈ I) : z ^ 2 = 0 := by
      have hz2 := Ideal.mul_mem_mul hz hz
      rw [← pow_two, hI] at hz2
      simpa only [Ideal.mem_bot, pow_two] using hz2
    have he2 : e ^ 2 = 0 := sqzero heI
    let av : B := aeval x a
    let bv : B := aeval x b
    let c : B := algebraMap K B ↑(u⁻¹)
    have hc : (2 : B) * c = 1 := by
      calc
        _ = algebraMap K B ((2 : K) * ↑(u⁻¹)) := by
          simp only [c, _root_.map_mul, _root_.map_ofNat]
        _ = 1 := by rw [hinv, _root_.map_one]
    let dx : B := e * bv
    let dy : B := -(e * av * y * c)
    have hdxI : dx ∈ I := I.mul_mem_right bv heI
    have hdyI : dy ∈ I := I.neg_mem
      (I.mul_mem_right c (I.mul_mem_right y (I.mul_mem_right av heI)))
    have hdx2 : dx ^ 2 = 0 := sqzero hdxI
    have hdy2 : dy ^ 2 = 0 := sqzero hdyI
    have hjac : av * aeval x f + bv * aeval x f.derivative = 1 := by
      simpa only [av, bv, _root_.map_add, _root_.map_mul, _root_.map_one] using
        congrArg (aeval x) hab
    have hjac' : av * y ^ 2 + bv * aeval x f.derivative = 1 + av * e := by
      calc
        _ = (av * aeval x f + bv * aeval x f.derivative) + av * e := by
          dsimp [e]
          ring
        _ = _ := by rw [hjac]
    have hdyterm : 2 * y * dy = -(e * av * y ^ 2) := by
      calc
        _ = -(e * av * y ^ 2 * (2 * c)) := by dsimp [dy]; ring
        _ = _ := by rw [hc]; ring
    have hlift : (y + dy) ^ 2 = aeval (x + dx) f := by
      rw [aeval_add_of_sq_eq_zero f x dx hdx2]
      apply sub_eq_zero.mp
      calc
        _ = (y ^ 2 - aeval x f) + 2 * y * dy + dy ^ 2 -
            aeval x f.derivative * dx := by ring
        _ = e - e * (av * y ^ 2 + bv * aeval x f.derivative) := by
          rw [hdyterm, hdy2]
          dsimp [e, dx]
          ring
        _ = 0 := by rw [hjac']; ring_nf; rw [he2]; ring
    let ψ : AdjoinRoot q →ₐ[K] B :=
      AdjoinRoot.liftAlgHom q (aeval (x + dx)) (y + dy) (by
        simp only [q, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
        exact sub_eq_zero.mpr hlift)
    refine ⟨ψ, ?_⟩
    apply AdjoinRoot.algHom_ext'
    · apply Polynomial.algHom_ext
      simp only [AlgHom.comp_apply, AdjoinRoot.coe_ofAlgHom,
        ψ, AdjoinRoot.liftAlgHom_of, aeval_X]
      change Ideal.Quotient.mk I (x + dx) = φ (AdjoinRoot.of q X)
      simp only [_root_.map_add, dx, _root_.map_mul]
      change Ideal.Quotient.mk I x + Ideal.Quotient.mkₐ K I e *
        Ideal.Quotient.mk I bv = _
      rw [he0, zero_mul, add_zero, hx]
    · simp only [AlgHom.comp_apply, ψ, AdjoinRoot.liftAlgHom_root]
      change Ideal.Quotient.mk I (y + dy) = φ (AdjoinRoot.root q)
      simp only [_root_.map_add, dy, _root_.map_neg, _root_.map_mul]
      change Ideal.Quotient.mk I y + -(Ideal.Quotient.mkₐ K I e *
        Ideal.Quotient.mk I av * Ideal.Quotient.mk I y * Ideal.Quotient.mk I c) = _
      rw [he0, zero_mul, zero_mul, zero_mul, neg_zero, add_zero, hy]
  exact { formallySmooth := inferInstance, finitePresentation := inferInstance }

end MazurTransfer.IntegralHyperellipticCoordinates

#print axioms MazurTransfer.IntegralHyperellipticCoordinates.hyperelliptic_coordinate_smooth

end
end

section
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Literal curve: MazurTheorem at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c.
Design boundary: smoothness of the actual two-chart integral curve over any
commutative ring in which 104 is a unit. Explicit integral Bezout identities
and square-zero lifting prove the assertion; no smooth model is assumed.
Named downstream consumer: compatible good reduction of the order-thirteen
curve and its Picard scheme at the primes 3 and 5.
-/

noncomputable section
universe u
open Polynomial CategoryTheory AlgebraicGeometry
open MazurTorsion.XOneThirteenAffineCurve
open MazurTorsion.XOneThirteenProjectiveCurve

namespace MazurTransfer.Order13IntegralSmoothCurve
variable (K : Type u) [CommRing K] (h104 : IsUnit (104 : K))
include h104

theorem sexticPolynomial_isCoprime_derivative : IsCoprime (sexticPolynomial K) (sexticPolynomial K).derivative := by
  obtain ⟨u, hu⟩ := h104
  have hinv : ↑(u⁻¹) * (104 : K) = 1 := by
    rw [← hu]
    simp
  let A : Polynomial K := 300 * X ^ 4 + 416 * X ^ 3 + 54 * X ^ 2 + 252 * X + 548
  let B : Polynomial K := -50 * X ^ 5 - 86 * X ^ 4 - 21 * X ^ 3 - 87 * X ^ 2 -
    278 * X - 111
  have hbezout : A * sexticPolynomial K + B * (sexticPolynomial K).derivative = C 104 := by
    simp only [A, B, sexticPolynomial, derivative_add, derivative_mul, derivative_pow,
      derivative_X, derivative_natCast, mul_zero, zero_add, add_zero, mul_one, Polynomial.C_ofNat, _root_.map_natCast]
    norm_num
    ring
  refine ⟨C (↑(u⁻¹) : K) * A, C (↑(u⁻¹) : K) * B, ?_⟩
  calc
    _ = C (↑(u⁻¹) : K) * (A * sexticPolynomial K + B * (sexticPolynomial K).derivative) := by ring
    _ = C (↑(u⁻¹) : K) * C 104 := by rw [hbezout]
    _ = 1 := by rw [← map_mul, hinv, C_1]


theorem reciprocalPolynomial_isCoprime_derivative : IsCoprime (reciprocalPolynomial K) (reciprocalPolynomial K).derivative := by
  obtain ⟨u, hu⟩ := h104
  have hinv : ↑(u⁻¹) * (104 : K) = 1 := by
    rw [← hu]
    simp
  let A : Polynomial K := 300 * X ^ 4 + 784 * X ^ 3 + 606 * X ^ 2 - 192 * X + 234
  let B : Polynomial K := -50 * X ^ 5 - 164 * X ^ 4 - 177 * X ^ 3 + 40 * X ^ 2 -
    73 * X - 65
  have hbezout : A * reciprocalPolynomial K + B * (reciprocalPolynomial K).derivative = C 104 := by
    simp only [A, B, reciprocalPolynomial, derivative_add, derivative_sub,
      derivative_mul, derivative_pow, derivative_X, derivative_natCast,
      mul_zero, zero_add, add_zero, mul_one, Polynomial.C_ofNat, _root_.map_natCast]
    norm_num
    ring
  refine ⟨C (↑(u⁻¹) : K) * A, C (↑(u⁻¹) : K) * B, ?_⟩
  calc
    _ = C (↑(u⁻¹) : K) * (A * reciprocalPolynomial K + B *
      (reciprocalPolynomial K).derivative) := by ring
    _ = 1 := by rw [hbezout, ← C_mul, hinv, C_1]


theorem two_isUnit : IsUnit (2 : K) := by
  have h : IsUnit ((2 : K) * 52) := by
    convert h104 using 1; norm_num
  exact (IsUnit.mul_iff.mp h).1

theorem ordinaryCoordinateRing_smooth :
    Algebra.Smooth K (CoordinateRing K) :=
  IntegralHyperellipticCoordinates.hyperelliptic_coordinate_smooth K
    (sexticPolynomial K) (sexticPolynomial_isCoprime_derivative K h104) (two_isUnit K h104)

theorem reciprocalRing_smooth : Algebra.Smooth K (ReciprocalRing K) :=
  IntegralHyperellipticCoordinates.hyperelliptic_coordinate_smooth K
    (reciprocalPolynomial K) (reciprocalPolynomial_isCoprime_derivative K h104) (two_isUnit K h104)

theorem ordinaryChartToBase_smooth : Smooth (ordinaryChartToBase K) := by
  unfold ordinaryChartToBase
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
  exact RingHom.smooth_algebraMap.mpr (ordinaryCoordinateRing_smooth K h104)

theorem reciprocalChartToBase_smooth : Smooth (reciprocalChartToBase K) := by
  unfold reciprocalChartToBase
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
  exact RingHom.smooth_algebraMap.mpr (reciprocalRing_smooth K h104)

theorem curveToBase_smooth : Smooth (curveToBase K) := by
  have : IsZariskiLocalAtSource (@Smooth.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
      (P := @Smooth.{u}) (Q := @RingHom.Smooth.{u,u})
  apply IsZariskiLocalAtSource.of_openCover (P := @Smooth)
    (f := curveToBase K) (glueData K).openCover
  intro i
  cases i
  · change Smooth (ordinaryChartMap K ≫ curveToBase K)
    rw [ordinaryChartMap_curveToBase]
    exact ordinaryChartToBase_smooth K h104
  · change Smooth (reciprocalChartMap K ≫ curveToBase K)
    rw [reciprocalChartMap_curveToBase]
    exact reciprocalChartToBase_smooth K h104

end MazurTransfer.Order13IntegralSmoothCurve

#print axioms MazurTransfer.Order13IntegralSmoothCurve.sexticPolynomial_isCoprime_derivative
#print axioms MazurTransfer.Order13IntegralSmoothCurve.reciprocalPolynomial_isCoprime_derivative
#print axioms MazurTransfer.Order13IntegralSmoothCurve.curveToBase_smooth

end
end

open CategoryTheory AlgebraicGeometry

theorem solution.{u}
    (R : Type u) [CommRing R] :
    Flat (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase R) ∧
    LocallyOfFinitePresentation (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase R) ∧
    (IsUnit (104 : R) →
      Smooth (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase R)) := by
  exact ⟨MazurTransfer.Order13IntegralCurve.curveToBase_flat R,
    MazurTransfer.Order13IntegralCurve.curveToBase_locallyOfFinitePresentation R,
    fun h104 => MazurTransfer.Order13IntegralSmoothCurve.curveToBase_smooth R h104⟩

#print axioms solution
