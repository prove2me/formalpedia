-- Prove2me | solution 1 for MazurTransfer.order13_actual_integral_chart_polynomials_coprime
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T05:00:48.085981+00:00
-- url     : https://prove2.me/submissions/614fe298-f99b-4dd5-9dac-337a1b049cb4

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Literal curve: MazurTheorem at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c.
Design boundary: smoothness of the actual two-chart integral curve over any
commutative ring in which 104 is a unit. Explicit integral Bezout identities
and square-zero lifting prove the assertion; no smooth model is assumed.
Named downstream consumer: compatible good reduction of the order-thirteen
curve and its Picard scheme at the primes 3 and 5.
-/
import Mathlib
import Definitions.Def_MazurTransfer_Order13ExplicitCurve
noncomputable section
universe u
namespace Order13IntegralChartCoprimePublicProof20261017
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

end MazurTransfer.Order13IntegralSmoothCurve
end Order13IntegralChartCoprimePublicProof20261017
open Polynomial
open MazurTorsion.XOneThirteenAffineCurve MazurTorsion.XOneThirteenProjectiveCurve
theorem solution (R : Type u) [CommRing R] (h104 : IsUnit (104 : R)) :
    IsCoprime (sexticPolynomial R) (sexticPolynomial R).derivative ∧
      IsCoprime (reciprocalPolynomial R) (reciprocalPolynomial R).derivative := by
  exact ⟨Order13IntegralChartCoprimePublicProof20261017.MazurTransfer.Order13IntegralSmoothCurve.sexticPolynomial_isCoprime_derivative R h104,
    Order13IntegralChartCoprimePublicProof20261017.MazurTransfer.Order13IntegralSmoothCurve.reciprocalPolynomial_isCoprime_derivative R h104⟩
#print axioms solution
