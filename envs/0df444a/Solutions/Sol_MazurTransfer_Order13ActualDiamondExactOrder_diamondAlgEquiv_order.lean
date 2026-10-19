-- Prove2me | solution 1 for MazurTransfer.Order13ActualDiamondExactOrder.diamondAlgEquiv_order
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T11:54:48.642674+00:00
-- url     : https://prove2.me/submissions/48198ca3-ab9e-47e3-90d2-06c8fb1b6fec

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual function-field automorphism has exact order
six; its cube is a nontrivial hyperelliptic involution. Named downstream
consumer: the actual Picard action used by the nineteen-isogeny descent.
-/
import Definitions.Def_MazurTransfer_Order13ActualDiamondFunctionFieldAutomorphism

noncomputable section
open MazurTransfer
open Polynomial
open MazurTorsion.XOneThirteenAffineCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13PellActualOrdinaryChart Order13ChartOverlapFunctionField
open Order13ActualOrdinaryPolynomialTranscendence Order13ActualDiamondFunctionFieldMap
open Order13ActualDiamondFunctionFieldAutomorphism Order13DiamondSexticSymmetry
local instance : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩
local instance : CharZero (actualCurveFunctionField ℚ) := algebraRat.charZero _
local instance : Algebra ℚ (actualCurveFunctionField ℚ) := actualCurveFunctionFieldAlgebra ℚ

namespace MazurTransfer.DiamondExactOrderHelpers20261017
theorem yImage_ne_zero : yImage ℚ ≠ 0 := by
  have Hp : sexticPolynomial ℚ ≠ 0 := by
    intro H
    have H6 := congrArg (fun p : Polynomial ℚ => p.coeff 6) H
    norm_num [sexticPolynomial, Polynomial.coeff_X, Polynomial.coeff_one] at H6
  have He : aeval (xImage ℚ) (sexticPolynomial ℚ) =
      Order13PellChartCertificate.sextic (xImage ℚ) := by
    simp only [sexticPolynomial, Order13PellChartCertificate.sextic,
      map_add, map_mul, map_pow, map_ofNat, map_one, aeval_X]
  have Hne := (map_ne_zero_iff (aeval (xImage ℚ))
    (transcendental_iff_injective.mp xImage_transcendental)).mpr Hp
  rw [He, ← yImage_sq] at Hne
  intro H
  apply Hne
  simp only [H, zero_pow (by decide : 2 ≠ 0)]

theorem diamondX_ne_xImage : diamondX (xImage ℚ) ≠ xImage ℚ := by
  intro H
  have Hden := xImage_add_one_ne_zero
  have Hmul : -1 = xImage ℚ * (xImage ℚ + 1) := (div_eq_iff Hden).mp H
  have He : xImage ℚ ^ 2 + xImage ℚ + 1 = 0 := by linear_combination -Hmul
  apply xImage_transcendental
  refine ⟨X ^ 2 + X + 1, ?_, ?_⟩
  · intro H
    have H2 := congrArg (fun p : Polynomial ℚ => p.coeff 2) H
    norm_num [Polynomial.coeff_X, Polynomial.coeff_one] at H2
  · simpa only [map_add, map_pow, map_one, aeval_X] using He

theorem diamondAlgEquiv_pow_six : diamondAlgEquiv ^ 6 = 1 := by
  apply AlgEquiv.ext
  intro b
  exact RingHom.congr_fun diamondThird_square b

theorem diamondAlgEquiv_cube_ne_one : diamondAlgEquiv ^ 3 ≠ 1 := by
  intro H
  have Hy := congrArg (fun f : actualCurveFunctionField ℚ ≃ₐ[ℚ] actualCurveFunctionField ℚ =>
    f (yImage ℚ)) H
  change diamondThird (yImage ℚ) = yImage ℚ at Hy
  rw [diamondThird_y] at Hy
  have Hz : (2 : actualCurveFunctionField ℚ) * yImage ℚ = 0 := by linear_combination -Hy
  rcases mul_eq_zero.mp Hz with H2 | Hy
  · norm_num at H2
  · exact yImage_ne_zero Hy

theorem diamondAlgEquiv_square_ne_one : diamondAlgEquiv ^ 2 ≠ 1 := by
  intro H
  have Hx := congrArg (fun f : actualCurveFunctionField ℚ ≃ₐ[ℚ] actualCurveFunctionField ℚ =>
    f (xImage ℚ)) H
  change diamondSecond (xImage ℚ) = xImage ℚ at Hx
  have H3 := diamondThird_x
  change diamondFieldMap (diamondSecond (xImage ℚ)) = xImage ℚ at H3
  rw [Hx, diamondFieldMap_x] at H3
  exact diamondX_ne_xImage H3

end MazurTransfer.DiamondExactOrderHelpers20261017
open MazurTransfer.DiamondExactOrderHelpers20261017
theorem solution : orderOf diamondAlgEquiv = 6 := by
  apply orderOf_eq_of_pow_and_pow_div_prime (by decide) diamondAlgEquiv_pow_six
  intro p hp hd
  have Hp : p = 2 ∨ p = 3 := by
    have Hd : p ∣ 2 * 3 := hd
    rcases hp.dvd_mul.mp Hd with H2 | H3
    · exact Or.inl ((Nat.dvd_prime (by decide : Nat.Prime 2)).mp H2 |>.resolve_left hp.ne_one)
    · exact Or.inr ((Nat.dvd_prime (by decide : Nat.Prime 3)).mp H3 |>.resolve_left hp.ne_one)
  rcases Hp with rfl | rfl
  · exact diamondAlgEquiv_cube_ne_one
  · exact diamondAlgEquiv_square_ne_one

#print axioms solution
