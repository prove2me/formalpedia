-- Prove2me | solution 1 for MazurTransfer.order13_actual_affine_scheme_integral
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T19:47:36.80734+00:00
-- url     : https://prove2.me/submissions/21f2f4ac-8032-4d19-8ee9-ef94c8135e54

import Mathlib

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.RingTheory.AdjoinRoot

/-!
# The affine order-thirteen curve as an actual scheme

This file constructs the affine chart

`y² = x⁶ + 2x⁵ + x⁴ + 2x³ + 6x² + 4x + 1`

as the spectrum of its quadratic coordinate algebra.  Its functor of
points is then identified with the elementary pairs satisfying the displayed
equation.  This is the first object-level bridge from the finite point
certificates to algebraic geometry: the target is an actual `Scheme`, not a
renaming of the certificate type.

The affine chart omits both normalized points at infinity.  Accordingly,
this file makes no projectivity, Picard, or Jacobian claim; those require the
reciprocal chart and their geometric gluing.
-/

namespace MazurTorsion.XOneThirteenAffineCurve

universe u

open Polynomial
open _root_.AlgebraicGeometry

variable (K : Type u) [CommRing K]

/-- The order-thirteen sextic over an arbitrary coefficient ring. -/
noncomputable def sexticPolynomial : Polynomial K :=
  X ^ 6 + 2 * X ^ 5 + X ^ 4 + 2 * X ^ 3 +
    6 * X ^ 2 + 4 * X + 1

/-- The monic quadratic equation in the ordinate, with coefficients in
`K[x]`. -/
noncomputable def affineEquation : Polynomial (Polynomial K) :=
  X ^ 2 - C (sexticPolynomial K)

/-- Coordinate algebra of the affine order-thirteen chart. -/
abbrev CoordinateRing := AdjoinRoot (affineEquation K)

/-- The abscissa in the affine coordinate algebra. -/
noncomputable def xCoordinate : CoordinateRing K :=
  AdjoinRoot.of (affineEquation K) X

/-- The ordinate in the affine coordinate algebra. -/
noncomputable def yCoordinate : CoordinateRing K :=
  AdjoinRoot.root (affineEquation K)

/-- The defining equation holds inside the coordinate algebra. -/
private theorem of_sexticPolynomial_eq_aeval :
    AdjoinRoot.of (affineEquation K) (sexticPolynomial K) =
      aeval (xCoordinate K) (sexticPolynomial K) := by
  have hhom :
      AdjoinRoot.ofAlgHom K (affineEquation K) =
        aeval (xCoordinate K) := by
    apply Polynomial.algHom_ext
    simp [xCoordinate]
  exact DFunLike.congr_fun hhom (sexticPolynomial K)

/-- The defining equation holds inside the coordinate algebra. -/
theorem yCoordinate_sq :
    yCoordinate K ^ 2 =
      aeval (xCoordinate K) (sexticPolynomial K) := by
  rw [← of_sexticPolynomial_eq_aeval]
  change AdjoinRoot.mk (affineEquation K) (X ^ 2) =
    AdjoinRoot.mk (affineEquation K) (C (sexticPolynomial K))
  rw [AdjoinRoot.mk_eq_mk]
  refine ⟨1, ?_⟩
  simp [affineEquation]

/-- The affine curve as an actual affine scheme. -/
noncomputable abbrev scheme : Scheme :=
  Spec (.of (CoordinateRing K))

/-- Elementary affine solutions over a `K`-algebra `A`. -/
def Solution (A : Type*) [CommRing A] [Algebra K A] :=
  {p : A × A // p.2 ^ 2 = aeval p.1 (sexticPolynomial K)}

variable {K}
variable (A : Type*) [CommRing A] [Algebra K A]

/-- A solution evaluates the coordinate algebra in the target algebra. -/
noncomputable def solutionToAlgHom (p : Solution K A) :
    CoordinateRing K →ₐ[K] A :=
  AdjoinRoot.liftAlgHom (affineEquation K) (aeval p.1.1) p.1.2 (by
    simpa [affineEquation, Polynomial.aeval_def] using
      sub_eq_zero.mpr p.property)

@[simp]
theorem solutionToAlgHom_x (p : Solution K A) :
    solutionToAlgHom A p (xCoordinate K) = p.1.1 := by
  simp [solutionToAlgHom, xCoordinate]

@[simp]
theorem solutionToAlgHom_y (p : Solution K A) :
    solutionToAlgHom A p (yCoordinate K) = p.1.2 := by
  simp [solutionToAlgHom, yCoordinate]

/-- An algebra point of the affine scheme recovers its two coordinates. -/
noncomputable def algHomToSolution
    (φ : CoordinateRing K →ₐ[K] A) : Solution K A :=
  ⟨(φ (xCoordinate K), φ (yCoordinate K)), by
    rw [← map_pow, yCoordinate_sq]
    simp [xCoordinate, Polynomial.aeval_def]⟩

@[simp]
theorem algHomToSolution_fst
    (φ : CoordinateRing K →ₐ[K] A) :
    (algHomToSolution A φ).1.1 = φ (xCoordinate K) := rfl

@[simp]
theorem algHomToSolution_snd
    (φ : CoordinateRing K →ₐ[K] A) :
    (algHomToSolution A φ).1.2 = φ (yCoordinate K) := rfl

/-- The elementary equation and the affine scheme's algebra-valued points
are canonically equivalent. -/
noncomputable def solutionEquivAlgHom :
    Solution K A ≃ (CoordinateRing K →ₐ[K] A) where
  toFun := solutionToAlgHom A
  invFun := algHomToSolution A
  left_inv p := by
    apply Subtype.ext
    ext <;> simp
  right_inv φ := by
    apply AdjoinRoot.algHom_ext'
    · apply Polynomial.algHom_ext
      simp [solutionToAlgHom, algHomToSolution, xCoordinate]
    · simp [solutionToAlgHom, algHomToSolution, yCoordinate]

@[simp]
theorem solutionEquivAlgHom_apply_x (p : Solution K A) :
    solutionEquivAlgHom A p (xCoordinate K) = p.1.1 := by
  exact solutionToAlgHom_x A p

@[simp]
theorem solutionEquivAlgHom_apply_y (p : Solution K A) :
    solutionEquivAlgHom A p (yCoordinate K) = p.1.2 := by
  exact solutionToAlgHom_y A p

/-! ## Literal scheme-valued points over prime coefficient rings -/

variable (K : Type u) [CommRing K]

/-- Morphisms from `Spec K` to the affine curve.  When every ring
endomorphism of `K` is the identity (in particular for a prime field), these
are exactly the `K`-algebra points above. -/
abbrev SchemePoint := Spec (.of K) ⟶ scheme K

private noncomputable def ringHomToAlgHom
    [Subsingleton (K →+* K)]
    (φ : CoordinateRing K →+* K) : CoordinateRing K →ₐ[K] K where
  __ := φ
  commutes' r := by
    change (φ.comp (algebraMap K (CoordinateRing K))) r =
      (RingHom.id K) r
    exact DFunLike.congr_fun (Subsingleton.elim _ _) r

/-- Over a ring with a unique endomorphism, forgetting the algebra structure
on an affine point loses no information. -/
private noncomputable def algHomEquivRingHom
    [Subsingleton (K →+* K)] :
    (CoordinateRing K →ₐ[K] K) ≃ (CoordinateRing K →+* K) where
  toFun φ := φ.toRingHom
  invFun := ringHomToAlgHom K
  left_inv φ := by
    apply AlgHom.coe_ringHom_injective
    rfl
  right_inv φ := rfl

private noncomputable def ringHomEquivCommRingCatHom :
    (CoordinateRing K →+* K) ≃
      (CommRingCat.of (CoordinateRing K) ⟶ CommRingCat.of K) where
  toFun := CommRingCat.ofHom
  invFun φ := φ.hom
  left_inv φ := rfl
  right_inv φ := by
    apply CommRingCat.hom_ext
    rfl

/-- Algebra-valued points are literally morphisms of affine schemes over a
prime coefficient ring. -/
noncomputable def algHomEquivSchemePoint
    [Subsingleton (K →+* K)] :
    (CoordinateRing K →ₐ[K] K) ≃ SchemePoint K :=
  (algHomEquivRingHom K).trans <|
    (ringHomEquivCommRingCatHom K).trans <|
      (Spec.homEquiv
        (R := .of (CoordinateRing K)) (S := .of K)).symm

/-- The displayed affine equation is canonically equivalent to the actual
`Spec K`-points of the affine curve. -/
noncomputable def solutionEquivSchemePoint
    [Subsingleton (K →+* K)] :
    Solution K K ≃ SchemePoint K :=
  (solutionEquivAlgHom K).trans (algHomEquivSchemePoint K)

end MazurTorsion.XOneThirteenAffineCurve

/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Design boundary: the actual quadratic coordinate algebra of the order-13
affine chart. The named downstream consumer `coordinateRing_isDomain` uses
the irreducibility certificate below. No smoothness, genus, or Jacobian
assertion is assumed in this interface.
-/

noncomputable section

open Polynomial

namespace MazurTorsion.XOneThirteenAffineCurve

variable (K : Type*) [Field K] [CharZero K]

theorem sexticPolynomial_separable : (sexticPolynomial K).Separable := by
  let A : Polynomial K := 300 * X ^ 4 + 416 * X ^ 3 + 54 * X ^ 2 + 252 * X + 548
  let B : Polynomial K := -50 * X ^ 5 - 86 * X ^ 4 - 21 * X ^ 3 - 87 * X ^ 2 -
    278 * X - 111
  have hbezout : A * sexticPolynomial K + B * (sexticPolynomial K).derivative = C 104 := by
    simp only [A, B, sexticPolynomial, derivative_add, derivative_mul, derivative_pow,
      derivative_X, derivative_natCast, mul_zero, zero_add, add_zero, mul_one, Polynomial.C_ofNat, _root_.map_natCast]
    norm_num
    ring
  rw [separable_def']
  refine ⟨C ((104 : K)⁻¹) * A, C ((104 : K)⁻¹) * B, ?_⟩
  calc
    _ = C ((104 : K)⁻¹) * (A * sexticPolynomial K + B * (sexticPolynomial K).derivative) := by ring
    _ = C ((104 : K)⁻¹) * C 104 := by rw [hbezout]
    _ = 1 := by rw [← map_mul]; norm_num

theorem sexticPolynomial_not_square (q : Polynomial K) : q ^ 2 ≠ sexticPolynomial K := by
  intro hq
  have hunit : IsUnit q := (sexticPolynomial_separable K).squarefree q (by
    rw [← hq, pow_two])
  have hdegree : (sexticPolynomial K).natDegree = 0 :=
    Polynomial.natDegree_eq_zero_of_isUnit (hq ▸ hunit.pow 2)
  have hdegree6 : (sexticPolynomial K).natDegree = 6 := by
    unfold sexticPolynomial
    compute_degree!
  omega

theorem sexticPolynomial_fraction_not_square (q : RatFunc K) :
    q ^ 2 ≠ algebraMap (Polynomial K) (RatFunc K) (sexticPolynomial K) := by
  intro hq
  have hIntegral : IsIntegral (Polynomial K) (q ^ 2) := by
    rw [hq]
    exact isIntegral_algebraMap
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow
    (R := Polynomial K) (K := RatFunc K) (by decide : 0 < 2) hIntegral
  apply sexticPolynomial_not_square K r
  apply IsFractionRing.injective (Polynomial K) (RatFunc K)
  rw [map_pow, hr, hq]

theorem affineEquation_irreducible : Irreducible (affineEquation K) := by
  have hmonic : (affineEquation K).Monic := by
    unfold affineEquation
    exact monic_X_pow_sub_C _ (by decide : 2 ≠ 0)
  apply (hmonic.irreducible_iff_irreducible_map_fraction_map (K := RatFunc K)).mpr
  simp only [affineEquation, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
  exact X_pow_sub_C_irreducible_of_prime (by decide : Nat.Prime 2)
    (sexticPolynomial_fraction_not_square K)

theorem coordinateRing_isDomain : IsDomain (CoordinateRing K) :=
  AdjoinRoot.isDomain_of_prime (affineEquation_irreducible K).prime

theorem affineScheme_isIntegral : _root_.AlgebraicGeometry.IsIntegral (scheme K) := by
  letI := coordinateRing_isDomain K
  exact inferInstance

end MazurTorsion.XOneThirteenAffineCurve

theorem solution (K : Type*) [Field K] [CharZero K] :
    _root_.AlgebraicGeometry.IsIntegral
      (_root_.AlgebraicGeometry.Spec (CommRingCat.of (AdjoinRoot
        ((Polynomial.X ^ 2 - Polynomial.C
          ((Polynomial.X : Polynomial K) ^ 6 + 2 * Polynomial.X ^ 5 +
            Polynomial.X ^ 4 + 2 * Polynomial.X ^ 3 + 6 * Polynomial.X ^ 2 +
            4 * Polynomial.X + 1)) : Polynomial (Polynomial K))))) := by
  exact MazurTorsion.XOneThirteenAffineCurve.affineScheme_isIntegral K
