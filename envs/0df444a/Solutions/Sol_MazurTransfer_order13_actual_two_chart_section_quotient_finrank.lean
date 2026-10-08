-- Prove2me | solution 1 for MazurTransfer.order13_actual_two_chart_section_quotient_finrank
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T21:25:16.735626+00:00
-- url     : https://prove2.me/submissions/00e25afa-8f0b-4ba7-8512-ddca5c5f9540

import Mathlib

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/


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
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/


/-!
# The two-chart order-thirteen curve

This file constructs the reciprocal chart of the genus-two model of
`X₁(13)` and identifies its punctured chart with the punctured affine chart.
The checked transition is

`x = z⁻¹`, `y = w z⁻³`.

The eventual glued scheme is therefore built from actual affine spectra and
an actual isomorphism of principal localizations.  No properness, smoothness,
or Jacobian assertion is hidden in the construction.
-/

noncomputable section

namespace MazurTorsion.XOneThirteenProjectiveCurve

universe u

open Polynomial
open _root_.AlgebraicGeometry
open CategoryTheory

variable (K : Type u) [CommRing K]

/-- The reciprocal sextic `z⁶ f(1/z)`. -/
noncomputable def reciprocalPolynomial : Polynomial K :=
  X ^ 6 + 4 * X ^ 5 + 6 * X ^ 4 + 2 * X ^ 3 +
    X ^ 2 + 2 * X + 1

/-- The monic quadratic equation of the reciprocal chart. -/
noncomputable def reciprocalEquation : Polynomial (Polynomial K) :=
  X ^ 2 - C (reciprocalPolynomial K)

/-- Coordinate algebra of the reciprocal chart. -/
abbrev ReciprocalRing := AdjoinRoot (reciprocalEquation K)

/-- Reciprocal abscissa. -/
noncomputable def zCoordinate : ReciprocalRing K :=
  AdjoinRoot.of (reciprocalEquation K) X

/-- Reciprocal ordinate. -/
noncomputable def wCoordinate : ReciprocalRing K :=
  AdjoinRoot.root (reciprocalEquation K)

private theorem of_reciprocalPolynomial_eq_aeval :
    AdjoinRoot.of (reciprocalEquation K) (reciprocalPolynomial K) =
      aeval (zCoordinate K) (reciprocalPolynomial K) := by
  have hhom :
      AdjoinRoot.ofAlgHom K (reciprocalEquation K) =
        aeval (zCoordinate K) := by
    apply Polynomial.algHom_ext
    simp [zCoordinate]
  exact DFunLike.congr_fun hhom (reciprocalPolynomial K)

/-- The reciprocal equation holds in its coordinate algebra. -/
theorem wCoordinate_sq :
    wCoordinate K ^ 2 =
      aeval (zCoordinate K) (reciprocalPolynomial K) := by
  rw [← of_reciprocalPolynomial_eq_aeval]
  change AdjoinRoot.mk (reciprocalEquation K) (X ^ 2) =
    AdjoinRoot.mk (reciprocalEquation K) (C (reciprocalPolynomial K))
  rw [AdjoinRoot.mk_eq_mk]
  refine ⟨1, ?_⟩
  simp [reciprocalEquation]

/-- The reciprocal affine chart. -/
noncomputable abbrev reciprocalScheme : Scheme :=
  Spec (.of (ReciprocalRing K))

/-- The punctured ordinary chart, obtained by inverting `x`. -/
abbrev OrdinaryOverlapRing :=
  Localization.Away (XOneThirteenAffineCurve.xCoordinate K)

/-- The punctured reciprocal chart, obtained by inverting `z`. -/
abbrev ReciprocalOverlapRing := Localization.Away (zCoordinate K)

private noncomputable def ordinaryXInReciprocalOverlap :
    ReciprocalOverlapRing K :=
  IsLocalization.Away.invSelf (zCoordinate K)

private noncomputable def ordinaryYInReciprocalOverlap :
    ReciprocalOverlapRing K :=
  algebraMap (ReciprocalRing K) (ReciprocalOverlapRing K) (wCoordinate K) *
    ordinaryXInReciprocalOverlap K ^ 3

private theorem z_mul_ordinaryXInReciprocalOverlap :
    algebraMap (ReciprocalRing K) (ReciprocalOverlapRing K) (zCoordinate K) *
      ordinaryXInReciprocalOverlap K = 1 := by
  exact IsLocalization.Away.mul_invSelf (zCoordinate K)

private theorem ordinaryXInReciprocalOverlap_isUnit :
    IsUnit (ordinaryXInReciprocalOverlap K) := by
  let z : ReciprocalOverlapRing K :=
    algebraMap (ReciprocalRing K) (ReciprocalOverlapRing K) (zCoordinate K)
  let x : ReciprocalOverlapRing K := ordinaryXInReciprocalOverlap K
  have hzx : z * x = 1 := z_mul_ordinaryXInReciprocalOverlap K
  exact ⟨
    { val := x
      inv := z
      val_inv := by simpa [mul_comm] using hzx
      inv_val := hzx }, rfl⟩

private theorem ordinary_coordinates_satisfy_equation :
    ordinaryYInReciprocalOverlap K ^ 2 =
      aeval (ordinaryXInReciprocalOverlap K)
        (XOneThirteenAffineCurve.sexticPolynomial K) := by
  let B := ReciprocalRing K
  let L := ReciprocalOverlapRing K
  let z : L := algebraMap B L (zCoordinate K)
  let w : L := algebraMap B L (wCoordinate K)
  let x : L := ordinaryXInReciprocalOverlap K
  have hzx : z * x = 1 := z_mul_ordinaryXInReciprocalOverlap K
  have hw : w ^ 2 =
      aeval z (reciprocalPolynomial K) := by
    change (algebraMap B L (wCoordinate K)) ^ 2 = _
    rw [← map_pow, wCoordinate_sq]
    rw [Polynomial.aeval_def, Polynomial.aeval_def,
      Polynomial.hom_eval₂]
    rw [← IsScalarTower.algebraMap_eq K B L]
  have hterm (n m : ℕ) : z ^ n * x ^ (n + m) = x ^ m := by
    rw [pow_add, ← mul_assoc, ← mul_pow, hzx, one_pow, one_mul]
  have hreciprocal :
      (z ^ 6 + 4 * z ^ 5 + 6 * z ^ 4 + 2 * z ^ 3 +
          z ^ 2 + 2 * z + 1) * x ^ 6 =
        x ^ 6 + 2 * x ^ 5 + x ^ 4 + 2 * x ^ 3 +
          6 * x ^ 2 + 4 * x + 1 := by
    calc
      _ = z ^ 6 * x ^ 6 + 4 * (z ^ 5 * x ^ 6) +
          6 * (z ^ 4 * x ^ 6) + 2 * (z ^ 3 * x ^ 6) +
          (z ^ 2 * x ^ 6) + 2 * (z * x ^ 6) + x ^ 6 := by ring
      _ = 1 + 4 * x + 6 * x ^ 2 + 2 * x ^ 3 +
          x ^ 4 + 2 * x ^ 5 + x ^ 6 := by
        rw [show z ^ 6 * x ^ 6 = 1 by simpa using hterm 6 0,
          show z ^ 5 * x ^ 6 = x by simpa using hterm 5 1,
          show z ^ 4 * x ^ 6 = x ^ 2 by simpa using hterm 4 2,
          show z ^ 3 * x ^ 6 = x ^ 3 by simpa using hterm 3 3,
          show z ^ 2 * x ^ 6 = x ^ 4 by simpa using hterm 2 4,
          show z * x ^ 6 = x ^ 5 by simpa using hterm 1 5]
      _ = _ := by ring
  change (w * x ^ 3) ^ 2 = _
  rw [show (w * x ^ 3) ^ 2 = w ^ 2 * x ^ 6 by ring, hw]
  simpa [XOneThirteenAffineCurve.sexticPolynomial,
    reciprocalPolynomial, Polynomial.aeval_natCast, map_ofNat] using hreciprocal

/-- Evaluation of the ordinary coordinate algebra on the reciprocal
overlap. -/
noncomputable def ordinaryToReciprocalBase :
    XOneThirteenAffineCurve.CoordinateRing K →ₐ[K]
      ReciprocalOverlapRing K :=
  XOneThirteenAffineCurve.solutionToAlgHom (ReciprocalOverlapRing K)
    ⟨(ordinaryXInReciprocalOverlap K,
      ordinaryYInReciprocalOverlap K),
      ordinary_coordinates_satisfy_equation K⟩

@[simp]
theorem ordinaryToReciprocalBase_x :
    ordinaryToReciprocalBase K
        (XOneThirteenAffineCurve.xCoordinate K) =
      ordinaryXInReciprocalOverlap K := by
  exact XOneThirteenAffineCurve.solutionToAlgHom_x _ _

@[simp]
theorem ordinaryToReciprocalBase_y :
    ordinaryToReciprocalBase K
        (XOneThirteenAffineCurve.yCoordinate K) =
      ordinaryYInReciprocalOverlap K := by
  exact XOneThirteenAffineCurve.solutionToAlgHom_y _ _

/-- The transition homomorphism on principal localizations. -/
noncomputable def ordinaryToReciprocal :
    OrdinaryOverlapRing K →ₐ[K] ReciprocalOverlapRing K :=
  IsLocalization.Away.liftAlgHom
    (XOneThirteenAffineCurve.xCoordinate K)
    (f := ordinaryToReciprocalBase K)
    (by simpa using ordinaryXInReciprocalOverlap_isUnit K)

@[simp]
theorem ordinaryToReciprocal_algebraMap
    (a : XOneThirteenAffineCurve.CoordinateRing K) :
    ordinaryToReciprocal K
        (algebraMap (XOneThirteenAffineCurve.CoordinateRing K)
          (OrdinaryOverlapRing K) a) =
      ordinaryToReciprocalBase K a := by
  simp [ordinaryToReciprocal, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq]

private noncomputable def reciprocalZInOrdinaryOverlap :
    OrdinaryOverlapRing K :=
  IsLocalization.Away.invSelf
    (XOneThirteenAffineCurve.xCoordinate K)

private noncomputable def reciprocalWInOrdinaryOverlap :
    OrdinaryOverlapRing K :=
  algebraMap (XOneThirteenAffineCurve.CoordinateRing K)
      (OrdinaryOverlapRing K) (XOneThirteenAffineCurve.yCoordinate K) *
    reciprocalZInOrdinaryOverlap K ^ 3

private theorem x_mul_reciprocalZInOrdinaryOverlap :
    algebraMap (XOneThirteenAffineCurve.CoordinateRing K)
        (OrdinaryOverlapRing K) (XOneThirteenAffineCurve.xCoordinate K) *
      reciprocalZInOrdinaryOverlap K = 1 := by
  exact IsLocalization.Away.mul_invSelf
    (XOneThirteenAffineCurve.xCoordinate K)

private theorem reciprocalZInOrdinaryOverlap_isUnit :
    IsUnit (reciprocalZInOrdinaryOverlap K) := by
  let x : OrdinaryOverlapRing K :=
    algebraMap (XOneThirteenAffineCurve.CoordinateRing K)
      (OrdinaryOverlapRing K) (XOneThirteenAffineCurve.xCoordinate K)
  let z : OrdinaryOverlapRing K := reciprocalZInOrdinaryOverlap K
  have hxz : x * z = 1 := x_mul_reciprocalZInOrdinaryOverlap K
  exact ⟨
    { val := z
      inv := x
      val_inv := by simpa [mul_comm] using hxz
      inv_val := hxz }, rfl⟩

private theorem reciprocal_coordinates_satisfy_equation :
    reciprocalWInOrdinaryOverlap K ^ 2 =
      aeval (reciprocalZInOrdinaryOverlap K)
        (reciprocalPolynomial K) := by
  let A := XOneThirteenAffineCurve.CoordinateRing K
  let L := OrdinaryOverlapRing K
  let x : L := algebraMap A L (XOneThirteenAffineCurve.xCoordinate K)
  let y : L := algebraMap A L (XOneThirteenAffineCurve.yCoordinate K)
  let z : L := reciprocalZInOrdinaryOverlap K
  have hxz : x * z = 1 := x_mul_reciprocalZInOrdinaryOverlap K
  have hy : y ^ 2 =
      aeval x (XOneThirteenAffineCurve.sexticPolynomial K) := by
    change (algebraMap A L (XOneThirteenAffineCurve.yCoordinate K)) ^ 2 = _
    rw [← map_pow, XOneThirteenAffineCurve.yCoordinate_sq]
    rw [Polynomial.aeval_def, Polynomial.aeval_def,
      Polynomial.hom_eval₂]
    rw [← IsScalarTower.algebraMap_eq K A L]
  have hterm (n m : ℕ) : x ^ n * z ^ (n + m) = z ^ m := by
    rw [pow_add, ← mul_assoc, ← mul_pow, hxz, one_pow, one_mul]
  have hreciprocal :
      (x ^ 6 + 2 * x ^ 5 + x ^ 4 + 2 * x ^ 3 +
          6 * x ^ 2 + 4 * x + 1) * z ^ 6 =
        z ^ 6 + 4 * z ^ 5 + 6 * z ^ 4 + 2 * z ^ 3 +
          z ^ 2 + 2 * z + 1 := by
    calc
      _ = x ^ 6 * z ^ 6 + 2 * (x ^ 5 * z ^ 6) +
          (x ^ 4 * z ^ 6) + 2 * (x ^ 3 * z ^ 6) +
          6 * (x ^ 2 * z ^ 6) + 4 * (x * z ^ 6) + z ^ 6 := by ring
      _ = 1 + 2 * z + z ^ 2 + 2 * z ^ 3 +
          6 * z ^ 4 + 4 * z ^ 5 + z ^ 6 := by
        rw [show x ^ 6 * z ^ 6 = 1 by simpa using hterm 6 0,
          show x ^ 5 * z ^ 6 = z by simpa using hterm 5 1,
          show x ^ 4 * z ^ 6 = z ^ 2 by simpa using hterm 4 2,
          show x ^ 3 * z ^ 6 = z ^ 3 by simpa using hterm 3 3,
          show x ^ 2 * z ^ 6 = z ^ 4 by simpa using hterm 2 4,
          show x * z ^ 6 = z ^ 5 by simpa using hterm 1 5]
      _ = _ := by ring
  change (y * z ^ 3) ^ 2 = _
  rw [show (y * z ^ 3) ^ 2 = y ^ 2 * z ^ 6 by ring, hy]
  simpa [XOneThirteenAffineCurve.sexticPolynomial,
    reciprocalPolynomial, Polynomial.aeval_natCast, map_ofNat]
    using hreciprocal

/-- Evaluation of the reciprocal coordinate algebra on the ordinary
overlap. -/
noncomputable def reciprocalToOrdinaryBase :
    ReciprocalRing K →ₐ[K] OrdinaryOverlapRing K :=
  AdjoinRoot.liftAlgHom (reciprocalEquation K)
    (aeval (reciprocalZInOrdinaryOverlap K))
    (reciprocalWInOrdinaryOverlap K) (by
      simpa [reciprocalEquation, Polynomial.aeval_def] using
        sub_eq_zero.mpr (reciprocal_coordinates_satisfy_equation K))

@[simp]
theorem reciprocalToOrdinaryBase_z :
    reciprocalToOrdinaryBase K (zCoordinate K) =
      reciprocalZInOrdinaryOverlap K := by
  simp [reciprocalToOrdinaryBase, zCoordinate]

@[simp]
theorem reciprocalToOrdinaryBase_w :
    reciprocalToOrdinaryBase K (wCoordinate K) =
      reciprocalWInOrdinaryOverlap K := by
  simp [reciprocalToOrdinaryBase, wCoordinate]

/-- The inverse transition homomorphism on principal localizations. -/
noncomputable def reciprocalToOrdinary :
    ReciprocalOverlapRing K →ₐ[K] OrdinaryOverlapRing K :=
  IsLocalization.Away.liftAlgHom (zCoordinate K)
    (f := reciprocalToOrdinaryBase K)
    (by simpa using reciprocalZInOrdinaryOverlap_isUnit K)

@[simp]
theorem reciprocalToOrdinary_algebraMap (b : ReciprocalRing K) :
    reciprocalToOrdinary K
        (algebraMap (ReciprocalRing K) (ReciprocalOverlapRing K) b) =
      reciprocalToOrdinaryBase K b := by
  simp [reciprocalToOrdinary, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq]

private theorem reciprocalToOrdinary_ordinaryX :
    reciprocalToOrdinary K (ordinaryXInReciprocalOverlap K) =
      algebraMap (XOneThirteenAffineCurve.CoordinateRing K)
        (OrdinaryOverlapRing K) (XOneThirteenAffineCurve.xCoordinate K) := by
  let A := XOneThirteenAffineCurve.CoordinateRing K
  let LA := OrdinaryOverlapRing K
  let LB := ReciprocalOverlapRing K
  let x : LA := algebraMap A LA (XOneThirteenAffineCurve.xCoordinate K)
  let z : LA := reciprocalZInOrdinaryOverlap K
  let φ := reciprocalToOrdinary K
  have hxz : x * z = 1 := x_mul_reciprocalZInOrdinaryOverlap K
  have hzφraw :
      φ (algebraMap (ReciprocalRing K) LB (zCoordinate K)) *
        φ (ordinaryXInReciprocalOverlap K) = 1
      := by
    rw [← map_mul, z_mul_ordinaryXInReciprocalOverlap, map_one]
  have hzφ : z * φ (ordinaryXInReciprocalOverlap K) = 1 := by
    rw [reciprocalToOrdinary_algebraMap,
      reciprocalToOrdinaryBase_z] at hzφraw
    exact hzφraw
  change φ (ordinaryXInReciprocalOverlap K) = x
  calc
    φ (ordinaryXInReciprocalOverlap K) =
        1 * φ (ordinaryXInReciprocalOverlap K) := by rw [one_mul]
    _ = (x * z) * φ (ordinaryXInReciprocalOverlap K) := by rw [hxz]
    _ = x * (z * φ (ordinaryXInReciprocalOverlap K)) := by rw [mul_assoc]
    _ = x * 1 := by rw [hzφ]
    _ = x := by rw [mul_one]

private theorem reciprocalToOrdinary_ordinaryY :
    reciprocalToOrdinary K (ordinaryYInReciprocalOverlap K) =
      algebraMap (XOneThirteenAffineCurve.CoordinateRing K)
        (OrdinaryOverlapRing K) (XOneThirteenAffineCurve.yCoordinate K) := by
  let A := XOneThirteenAffineCurve.CoordinateRing K
  let LA := OrdinaryOverlapRing K
  let x : LA := algebraMap A LA (XOneThirteenAffineCurve.xCoordinate K)
  let y : LA := algebraMap A LA (XOneThirteenAffineCurve.yCoordinate K)
  let z : LA := reciprocalZInOrdinaryOverlap K
  have hxz : x * z = 1 := x_mul_reciprocalZInOrdinaryOverlap K
  change reciprocalToOrdinary K
      (algebraMap (ReciprocalRing K) (ReciprocalOverlapRing K)
          (wCoordinate K) * ordinaryXInReciprocalOverlap K ^ 3) = y
  rw [map_mul, map_pow, reciprocalToOrdinary_algebraMap,
    reciprocalToOrdinaryBase_w, reciprocalToOrdinary_ordinaryX]
  change (y * z ^ 3) * x ^ 3 = y
  calc
    (y * z ^ 3) * x ^ 3 = y * (z ^ 3 * x ^ 3) := by ring
    _ = y * (z * x) ^ 3 := by rw [mul_pow]
    _ = y * 1 ^ 3 := by rw [mul_comm z x, hxz]
    _ = y := by simp

/-- One direction of the transition law is checked on the entire localized
coordinate algebra. -/
theorem reciprocalToOrdinary_comp_ordinaryToReciprocal :
    (reciprocalToOrdinary K).comp (ordinaryToReciprocal K) =
      AlgHom.id K (OrdinaryOverlapRing K) := by
  apply IsLocalization.algHom_ext
    (Submonoid.powers (XOneThirteenAffineCurve.xCoordinate K))
  apply AdjoinRoot.algHom_ext'
  · apply Polynomial.algHom_ext
    change reciprocalToOrdinary K
        (ordinaryToReciprocal K
          (algebraMap (XOneThirteenAffineCurve.CoordinateRing K)
            (OrdinaryOverlapRing K) (XOneThirteenAffineCurve.xCoordinate K))) =
      algebraMap (XOneThirteenAffineCurve.CoordinateRing K)
        (OrdinaryOverlapRing K) (XOneThirteenAffineCurve.xCoordinate K)
    rw [ordinaryToReciprocal_algebraMap, ordinaryToReciprocalBase_x,
      reciprocalToOrdinary_ordinaryX]
  · change reciprocalToOrdinary K
        (ordinaryToReciprocal K
          (algebraMap (XOneThirteenAffineCurve.CoordinateRing K)
            (OrdinaryOverlapRing K) (XOneThirteenAffineCurve.yCoordinate K))) =
      algebraMap (XOneThirteenAffineCurve.CoordinateRing K)
        (OrdinaryOverlapRing K) (XOneThirteenAffineCurve.yCoordinate K)
    rw [ordinaryToReciprocal_algebraMap, ordinaryToReciprocalBase_y,
      reciprocalToOrdinary_ordinaryY]

private theorem ordinaryToReciprocal_reciprocalZ :
    ordinaryToReciprocal K (reciprocalZInOrdinaryOverlap K) =
      algebraMap (ReciprocalRing K) (ReciprocalOverlapRing K)
        (zCoordinate K) := by
  let A := XOneThirteenAffineCurve.CoordinateRing K
  let LA := OrdinaryOverlapRing K
  let LB := ReciprocalOverlapRing K
  let x : LB := ordinaryXInReciprocalOverlap K
  let z : LB := algebraMap (ReciprocalRing K) LB (zCoordinate K)
  let φ := ordinaryToReciprocal K
  have hzx : z * x = 1 := z_mul_ordinaryXInReciprocalOverlap K
  have hxφraw :
      φ (algebraMap A LA (XOneThirteenAffineCurve.xCoordinate K)) *
        φ (reciprocalZInOrdinaryOverlap K) = 1
      := by
    rw [← map_mul, x_mul_reciprocalZInOrdinaryOverlap, map_one]
  have hxφ : x * φ (reciprocalZInOrdinaryOverlap K) = 1 := by
    rw [ordinaryToReciprocal_algebraMap,
      ordinaryToReciprocalBase_x] at hxφraw
    exact hxφraw
  change φ (reciprocalZInOrdinaryOverlap K) = z
  calc
    φ (reciprocalZInOrdinaryOverlap K) =
        1 * φ (reciprocalZInOrdinaryOverlap K) := by rw [one_mul]
    _ = (z * x) * φ (reciprocalZInOrdinaryOverlap K) := by rw [hzx]
    _ = z * (x * φ (reciprocalZInOrdinaryOverlap K)) := by rw [mul_assoc]
    _ = z * 1 := by rw [hxφ]
    _ = z := by rw [mul_one]

private theorem ordinaryToReciprocal_reciprocalW :
    ordinaryToReciprocal K (reciprocalWInOrdinaryOverlap K) =
      algebraMap (ReciprocalRing K) (ReciprocalOverlapRing K)
        (wCoordinate K) := by
  let B := ReciprocalRing K
  let LB := ReciprocalOverlapRing K
  let z : LB := algebraMap B LB (zCoordinate K)
  let w : LB := algebraMap B LB (wCoordinate K)
  let x : LB := ordinaryXInReciprocalOverlap K
  have hzx : z * x = 1 := z_mul_ordinaryXInReciprocalOverlap K
  change ordinaryToReciprocal K
      (algebraMap (XOneThirteenAffineCurve.CoordinateRing K)
          (OrdinaryOverlapRing K) (XOneThirteenAffineCurve.yCoordinate K) *
        reciprocalZInOrdinaryOverlap K ^ 3) = w
  rw [map_mul, map_pow, ordinaryToReciprocal_algebraMap,
    ordinaryToReciprocalBase_y, ordinaryToReciprocal_reciprocalZ]
  change (w * x ^ 3) * z ^ 3 = w
  calc
    (w * x ^ 3) * z ^ 3 = w * (x ^ 3 * z ^ 3) := by ring
    _ = w * (x * z) ^ 3 := by rw [mul_pow]
    _ = w * 1 ^ 3 := by rw [mul_comm x z, hzx]
    _ = w := by simp

/-- The other direction of the transition law is checked on the entire
localized coordinate algebra. -/
theorem ordinaryToReciprocal_comp_reciprocalToOrdinary :
    (ordinaryToReciprocal K).comp (reciprocalToOrdinary K) =
      AlgHom.id K (ReciprocalOverlapRing K) := by
  apply IsLocalization.algHom_ext (Submonoid.powers (zCoordinate K))
  apply AdjoinRoot.algHom_ext'
  · apply Polynomial.algHom_ext
    change ordinaryToReciprocal K
        (reciprocalToOrdinary K
          (algebraMap (ReciprocalRing K) (ReciprocalOverlapRing K)
            (zCoordinate K))) =
      algebraMap (ReciprocalRing K) (ReciprocalOverlapRing K)
        (zCoordinate K)
    rw [reciprocalToOrdinary_algebraMap, reciprocalToOrdinaryBase_z,
      ordinaryToReciprocal_reciprocalZ]
  · change ordinaryToReciprocal K
        (reciprocalToOrdinary K
          (algebraMap (ReciprocalRing K) (ReciprocalOverlapRing K)
            (wCoordinate K))) =
      algebraMap (ReciprocalRing K) (ReciprocalOverlapRing K)
        (wCoordinate K)
    rw [reciprocalToOrdinary_algebraMap, reciprocalToOrdinaryBase_w,
      ordinaryToReciprocal_reciprocalW]

/-- The checked algebra equivalence between the two principal
localizations. -/
noncomputable def overlapAlgEquiv :
    OrdinaryOverlapRing K ≃ₐ[K] ReciprocalOverlapRing K :=
  AlgEquiv.ofAlgHom (ordinaryToReciprocal K) (reciprocalToOrdinary K)
    (ordinaryToReciprocal_comp_reciprocalToOrdinary K)
    (reciprocalToOrdinary_comp_ordinaryToReciprocal K)

/-- The corresponding isomorphism of punctured affine schemes. -/
noncomputable def overlapSchemeIso :
    Spec (.of (OrdinaryOverlapRing K)) ≅
      Spec (.of (ReciprocalOverlapRing K)) :=
  Scheme.Spec.mapIso
    (overlapAlgEquiv K).toRingEquiv.toCommRingCatIso.symm.op

@[simp]
theorem overlapSchemeIso_hom :
    (overlapSchemeIso K).hom =
      Spec.map (CommRingCat.ofHom (reciprocalToOrdinary K).toRingHom) := by
  rfl

@[simp]
theorem overlapSchemeIso_inv :
    (overlapSchemeIso K).inv =
      Spec.map (CommRingCat.ofHom (ordinaryToReciprocal K).toRingHom) := by
  rfl

/-- The two affine charts used in the compactification. -/
inductive Chart : Type u
  | ordinary
  | reciprocal
  deriving DecidableEq

/-- The affine scheme belonging to a chart. -/
noncomputable abbrev chartScheme : Chart → Scheme
  | .ordinary => XOneThirteenAffineCurve.scheme K
  | .reciprocal => reciprocalScheme K

/-- For distinct charts, the principal-open overlap as viewed from the
first chart. -/
noncomputable abbrev overlapScheme :
    ∀ i j : Chart, i ≠ j → Scheme
  | .ordinary, .reciprocal, _ => Spec (.of (OrdinaryOverlapRing K))
  | .reciprocal, .ordinary, _ => Spec (.of (ReciprocalOverlapRing K))
  | .ordinary, .ordinary, h => (h rfl).elim
  | .reciprocal, .reciprocal, h => (h rfl).elim

/-- Each overlap is included as the principal open where the corresponding
abscissa is invertible. -/
noncomputable def overlapInclusion :
    ∀ i j : Chart, (h : i ≠ j) →
      overlapScheme K i j h ⟶ chartScheme K i
  | .ordinary, .reciprocal, _ =>
      Spec.map (CommRingCat.ofHom
        (algebraMap (XOneThirteenAffineCurve.CoordinateRing K)
          (OrdinaryOverlapRing K)))
  | .reciprocal, .ordinary, _ =>
      Spec.map (CommRingCat.ofHom
        (algebraMap (ReciprocalRing K) (ReciprocalOverlapRing K)))
  | .ordinary, .ordinary, h => (h rfl).elim
  | .reciprocal, .reciprocal, h => (h rfl).elim

/-- The transition isomorphism, oriented from the first chart's overlap to
the second chart's overlap. -/
noncomputable def overlapTransition :
    ∀ i j : Chart, (h : i ≠ j) →
      overlapScheme K i j h ⟶ overlapScheme K j i h.symm
  | .ordinary, .reciprocal, _ => (overlapSchemeIso K).hom
  | .reciprocal, .ordinary, _ => (overlapSchemeIso K).inv
  | .ordinary, .ordinary, h => (h rfl).elim
  | .reciprocal, .reciprocal, h => (h rfl).elim

private theorem overlapInclusion_open
    (i j : Chart) (h : i ≠ j) :
    IsOpenImmersion (overlapInclusion K i j h) := by
  rcases i with (_ | _) <;> rcases j with (_ | _)
  · exact (h rfl).elim
  · exact IsOpenImmersion.of_isLocalization
      (XOneThirteenAffineCurve.xCoordinate K)
  · exact IsOpenImmersion.of_isLocalization (zCoordinate K)
  · exact (h rfl).elim

private theorem overlapInclusion_mono
    (i j : Chart) (h : i ≠ j) :
    CategoryTheory.Mono (overlapInclusion K i j h) := by
  haveI : IsOpenImmersion (overlapInclusion K i j h) :=
    overlapInclusion_open K i j h
  infer_instance

/-- Two-chart categorical gluing datum.  Triple-overlap coherence is
vacuous because three pairwise distinct charts do not exist. -/
noncomputable abbrev categoricalGlueData :
    CategoryTheory.GlueData' Scheme.{u} where
  J := Chart
  U := chartScheme K
  V := overlapScheme K
  f := overlapInclusion K
  f_mono := overlapInclusion_mono K
  f_hasPullback := by
    intro i j k hij hik
    infer_instance
  t := overlapTransition K
  t' := by
    intro i j k hij hik hjk
    rcases i with (_ | _) <;> rcases j with (_ | _) <;>
      rcases k with (_ | _) <;> contradiction
  t_fac := by
    intro i j k hij hik hjk
    rcases i with (_ | _) <;> rcases j with (_ | _) <;>
      rcases k with (_ | _) <;> contradiction
  t_inv := by
    intro i j hij
    rcases i with (_ | _) <;> rcases j with (_ | _)
    · exact (hij rfl).elim
    · exact (overlapSchemeIso K).hom_inv_id
    · exact (overlapSchemeIso K).inv_hom_id
    · exact (hij rfl).elim
  cocycle := by
    intro i j k hij hik hjk
    rcases i with (_ | _) <;> rcases j with (_ | _) <;>
      rcases k with (_ | _) <;> contradiction

private theorem categoricalGlueData_f'_open (i j : Chart) :
    IsOpenImmersion ((categoricalGlueData K).f' i j) := by
  classical
  delta CategoryTheory.GlueData'.f'
  by_cases h : i = j
  · simp only [dif_pos h]
    exact IsOpenImmersion.of_isIso _
  · simp only [dif_neg h]
    haveI : IsOpenImmersion (overlapInclusion K i j h) :=
      overlapInclusion_open K i j h
    exact IsOpenImmersion.comp _ _

/-- Scheme-theoretic gluing data obtained from the checked two-chart
transition. -/
noncomputable abbrev glueData : Scheme.GlueData.{u} where
  toGlueData := CategoryTheory.GlueData.ofGlueData' (categoricalGlueData K)
  f_open := categoricalGlueData_f'_open K

/-- The actual two-chart scheme attached to the order-thirteen sextic. -/
noncomputable def curveScheme : Scheme := (glueData K).glued

/-- The ordinary affine chart as an open subscheme of the glued curve. -/
noncomputable def ordinaryChartMap :
    XOneThirteenAffineCurve.scheme K ⟶ curveScheme K :=
  (glueData K).ι Chart.ordinary

/-- The reciprocal affine chart as an open subscheme of the glued curve. -/
noncomputable def reciprocalChartMap :
    reciprocalScheme K ⟶ curveScheme K :=
  (glueData K).ι Chart.reciprocal

instance ordinaryChartMap_isOpenImmersion :
    IsOpenImmersion (ordinaryChartMap K) := by
  dsimp [ordinaryChartMap]
  exact Scheme.GlueData.ι_isOpenImmersion (glueData K) Chart.ordinary

instance reciprocalChartMap_isOpenImmersion :
    IsOpenImmersion (reciprocalChartMap K) := by
  dsimp [reciprocalChartMap]
  exact Scheme.GlueData.ι_isOpenImmersion (glueData K) Chart.reciprocal

/-! ## The curve over its coefficient ring -/

/-- Structure morphism of the ordinary affine chart. -/
noncomputable def ordinaryChartToBase :
    XOneThirteenAffineCurve.scheme K ⟶ Spec (.of K) :=
  Spec.map (CommRingCat.ofHom
    (algebraMap K (XOneThirteenAffineCurve.CoordinateRing K)))

/-- Structure morphism of the reciprocal affine chart. -/
noncomputable def reciprocalChartToBase :
    reciprocalScheme K ⟶ Spec (.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K (ReciprocalRing K)))

/-- The chartwise structure maps. -/
noncomputable def chartToBase :
    ∀ i : Chart, chartScheme K i ⟶ Spec (.of K)
  | .ordinary => ordinaryChartToBase K
  | .reciprocal => reciprocalChartToBase K

private theorem ordinary_ne_reciprocal :
    (Chart.ordinary : Chart.{u}) ≠ Chart.reciprocal := by
  intro h
  cases h

private theorem reciprocal_ne_ordinary :
    (Chart.reciprocal : Chart.{u}) ≠ Chart.ordinary := by
  intro h
  cases h

private theorem ordinary_reciprocal_base_compatible :
    Spec.map (CommRingCat.ofHom
        (algebraMap (XOneThirteenAffineCurve.CoordinateRing K)
          (OrdinaryOverlapRing K))) ≫
        ordinaryChartToBase K =
      Spec.map (CommRingCat.ofHom
          (reciprocalToOrdinary K).toRingHom) ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap (ReciprocalRing K) (ReciprocalOverlapRing K))) ≫
        reciprocalChartToBase K := by
  simp only [ordinaryChartToBase, reciprocalChartToBase]
  rw [← Spec.map_comp, ← Category.assoc, ← Spec.map_comp,
    ← Spec.map_comp]
  rw [Spec.map_inj]
  apply CommRingCat.hom_ext
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom]
  ext k
  simp only [RingHom.coe_comp, Function.comp_apply]
  rw [← IsScalarTower.algebraMap_apply K
    (XOneThirteenAffineCurve.CoordinateRing K) (OrdinaryOverlapRing K)]
  simp

private theorem reciprocal_ordinary_base_compatible :
    Spec.map (CommRingCat.ofHom
        (algebraMap (ReciprocalRing K) (ReciprocalOverlapRing K))) ≫
        reciprocalChartToBase K =
      Spec.map (CommRingCat.ofHom
          (ordinaryToReciprocal K).toRingHom) ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap (XOneThirteenAffineCurve.CoordinateRing K)
            (OrdinaryOverlapRing K))) ≫
        ordinaryChartToBase K := by
  simp only [ordinaryChartToBase, reciprocalChartToBase]
  rw [← Spec.map_comp, ← Category.assoc, ← Spec.map_comp,
    ← Spec.map_comp]
  rw [Spec.map_inj]
  apply CommRingCat.hom_ext
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom]
  ext k
  simp only [RingHom.coe_comp, Function.comp_apply]
  rw [← IsScalarTower.algebraMap_apply K
    (ReciprocalRing K) (ReciprocalOverlapRing K)]
  simp

private theorem chartToBase_transition_compatible
    (i j : Chart) (h : i ≠ j) :
    overlapInclusion K i j h ≫ chartToBase K i =
      overlapTransition K i j h ≫
        overlapInclusion K j i h.symm ≫ chartToBase K j := by
  rcases i with (_ | _) <;> rcases j with (_ | _)
  · exact (h rfl).elim
  · exact ordinary_reciprocal_base_compatible K
  · exact reciprocal_ordinary_base_compatible K
  · exact (h rfl).elim

/-- The structure morphism obtained by gluing the two affine algebra
structures. -/
noncomputable def curveToBase : curveScheme K ⟶ Spec (.of K) :=
  by
    letI := Scheme.GlueData.instHasMulticoequalizerDiagram (glueData K)
    exact Limits.Multicoequalizer.desc (glueData K).toGlueData.diagram
      (Spec (.of K)) (chartToBase K) (by
      rintro ⟨i, j⟩
      simp only [CategoryTheory.GlueData.diagram_fst,
        CategoryTheory.GlueData.diagram_snd]
      rcases i with (_ | _) <;> rcases j with (_ | _)
      · dsimp [glueData, categoricalGlueData,
          CategoryTheory.GlueData.ofGlueData',
          CategoryTheory.GlueData'.f', chartToBase,
          Limits.MultispanShape.prod]
        simp
      · dsimp [glueData, categoricalGlueData,
          CategoryTheory.GlueData.ofGlueData',
          CategoryTheory.GlueData'.f', chartToBase,
          ordinary_ne_reciprocal, reciprocal_ne_ordinary,
          Limits.MultispanShape.prod]
        simp only [dif_neg ordinary_ne_reciprocal,
          dif_neg reciprocal_ne_ordinary, Category.assoc]
        simp only [CategoryTheory.eqToHom_trans_assoc,
          CategoryTheory.eqToHom_refl, Category.id_comp]
        rw [CategoryTheory.cancel_epi]
        exact chartToBase_transition_compatible K _ _
          ordinary_ne_reciprocal
      · dsimp [glueData, categoricalGlueData,
          CategoryTheory.GlueData.ofGlueData',
          CategoryTheory.GlueData'.f', chartToBase,
          ordinary_ne_reciprocal, reciprocal_ne_ordinary,
          Limits.MultispanShape.prod]
        simp only [dif_neg ordinary_ne_reciprocal,
          dif_neg reciprocal_ne_ordinary, Category.assoc]
        simp only [CategoryTheory.eqToHom_trans_assoc,
          CategoryTheory.eqToHom_refl, Category.id_comp]
        rw [CategoryTheory.cancel_epi]
        exact chartToBase_transition_compatible K _ _
          reciprocal_ne_ordinary
      · dsimp [glueData, categoricalGlueData,
          CategoryTheory.GlueData.ofGlueData',
          CategoryTheory.GlueData'.f', chartToBase,
          Limits.MultispanShape.prod]
        simp)

@[simp, reassoc]
theorem ordinaryChartMap_curveToBase :
    ordinaryChartMap K ≫ curveToBase K = ordinaryChartToBase K := by
  letI := Scheme.GlueData.instHasMulticoequalizerDiagram (glueData K)
  unfold ordinaryChartMap curveToBase
  apply Limits.Multicoequalizer.π_desc

@[simp, reassoc]
theorem reciprocalChartMap_curveToBase :
    reciprocalChartMap K ≫ curveToBase K = reciprocalChartToBase K := by
  letI := Scheme.GlueData.instHasMulticoequalizerDiagram (glueData K)
  unfold reciprocalChartMap curveToBase
  apply Limits.Multicoequalizer.π_desc

end MazurTorsion.XOneThirteenProjectiveCurve

/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Design boundary: an actual localized quadratic coordinate algebra is
equivalent to the quadratic algebra over Laurent polynomials. Named downstream
consumer: the two-chart Cech quotient of the order-thirteen curve.
This does not assert a genus or a sheaf-cohomology comparison.
-/

noncomputable section
namespace MazurTransfer.HyperellipticLaurentOverlap
open Polynomial

variable (K : Type*) [CommRing K] (f : Polynomial K)

instance : IsScalarTower K (Polynomial K) (LaurentPolynomial K) :=
  IsScalarTower.of_algebraMap_eq fun k => by
    rw [LaurentPolynomial.algebraMap_eq_toLaurent, Polynomial.algebraMap_eq,
      Polynomial.toLaurent_C]
    exact (LaurentPolynomial.C_eq_algebraMap k).symm

def equation : Polynomial (Polynomial K) := X ^ 2 - C f
abbrev Chart := AdjoinRoot (equation K f)
def x : Chart K f := AdjoinRoot.of (equation K f) X
def y : Chart K f := AdjoinRoot.root (equation K f)
abbrev Overlap := Localization.Away (x K f)
abbrev laurentEquation : Polynomial (LaurentPolynomial K) := X ^ 2 - C f.toLaurent
abbrev LaurentChart := AdjoinRoot (laurentEquation K f)

def toLaurentBase : Chart K f →ₐ[K] LaurentChart K f :=
  AdjoinRoot.liftAlgHom (equation K f)
    ((AdjoinRoot.ofAlgHom K (laurentEquation K f)).comp Polynomial.toLaurentAlg)
    (AdjoinRoot.root (laurentEquation K f)) (by
      have h := AdjoinRoot.eval₂_root (laurentEquation K f)
      change Polynomial.eval₂ _ _ (X ^ 2 - C f.toLaurent) = 0 at h
      rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
        Polynomial.eval₂_C] at h
      change Polynomial.eval₂ _ _ (X ^ 2 - C f) = 0
      rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
        Polynomial.eval₂_C]
      exact h)

@[simp] theorem toLaurentBase_x :
    toLaurentBase K f (x K f) =
      AdjoinRoot.of (laurentEquation K f) (LaurentPolynomial.T 1) := by
  simp [toLaurentBase, x]

@[simp] theorem toLaurentBase_y :
    toLaurentBase K f (y K f) = AdjoinRoot.root (laurentEquation K f) := by
  simp [toLaurentBase, y]

def toLaurent : Overlap K f →ₐ[K] LaurentChart K f :=
  IsLocalization.Away.liftAlgHom (x K f) (by
    rw [toLaurentBase_x]
    exact (LaurentPolynomial.isUnit_T (1 : ℤ)).map (AdjoinRoot.of (laurentEquation K f)))

@[simp] theorem toLaurent_algebraMap (a : Chart K f) :
    toLaurent K f (algebraMap (Chart K f) (Overlap K f) a) = toLaurentBase K f a := by
  simp [toLaurent, IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]

theorem coefficient_X_unit : IsUnit
    (((Algebra.algHom K (Chart K f) (Overlap K f)).comp
      (AdjoinRoot.ofAlgHom K (equation K f))) X) := by
  change IsUnit (algebraMap (Chart K f) (Overlap K f) (x K f))
  exact IsLocalization.Away.algebraMap_isUnit (x K f)

def fromLaurentCoefficients : LaurentPolynomial K →ₐ[K] Overlap K f :=
  IsLocalization.Away.liftAlgHom (X : Polynomial K)
    (f := (Algebra.algHom K (Chart K f) (Overlap K f)).comp
      (AdjoinRoot.ofAlgHom K (equation K f))) (coefficient_X_unit K f)

@[simp] theorem fromLaurentCoefficients_toLaurent (p : Polynomial K) :
    fromLaurentCoefficients K f p.toLaurent =
      algebraMap (Chart K f) (Overlap K f) (AdjoinRoot.of (equation K f) p) := by
  change fromLaurentCoefficients K f
    (algebraMap (Polynomial K) (LaurentPolynomial K) p) = _
  exact IsLocalization.Away.lift_eq (X : Polynomial K) (coefficient_X_unit K f) p

def fromLaurent : LaurentChart K f →ₐ[K] Overlap K f :=
  AdjoinRoot.liftAlgHom (laurentEquation K f) (fromLaurentCoefficients K f)
    (algebraMap (Chart K f) (Overlap K f) (y K f)) (by
      have h := AdjoinRoot.eval₂_root (equation K f)
      change Polynomial.eval₂ _ _ (X ^ 2 - C f) = 0 at h
      rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
        Polynomial.eval₂_C] at h
      have hm := congrArg (algebraMap (Chart K f) (Overlap K f)) h
      change Polynomial.eval₂ _ _ (X ^ 2 - C f.toLaurent) = 0
      rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
        Polynomial.eval₂_C]
      change (algebraMap (Chart K f) (Overlap K f) (y K f)) ^ 2 -
        fromLaurentCoefficients K f f.toLaurent = 0
      rw [fromLaurentCoefficients_toLaurent]
      simpa only [map_sub, map_pow, map_zero, y] using hm)

@[simp] theorem fromLaurent_root :
    fromLaurent K f (AdjoinRoot.root (laurentEquation K f)) =
      algebraMap (Chart K f) (Overlap K f) (y K f) := by
  simp [fromLaurent]

theorem fromLaurent_comp_toLaurent :
    (fromLaurent K f).comp (toLaurent K f) = AlgHom.id K (Overlap K f) := by
  apply IsLocalization.algHom_ext (Submonoid.powers (x K f))
  apply AdjoinRoot.algHom_ext'
  · apply Polynomial.algHom_ext
    change fromLaurent K f (toLaurent K f
      (algebraMap (Chart K f) (Overlap K f) (x K f))) =
      algebraMap (Chart K f) (Overlap K f) (x K f)
    rw [toLaurent_algebraMap, toLaurentBase_x]
    rw [← Polynomial.toLaurent_X]
    change AdjoinRoot.liftAlgHom _ _ _ _ (AdjoinRoot.of _ _) = _
    rw [AdjoinRoot.liftAlgHom_of, fromLaurentCoefficients_toLaurent]
    rfl
  · change fromLaurent K f (toLaurent K f
      (algebraMap (Chart K f) (Overlap K f) (y K f))) =
      algebraMap (Chart K f) (Overlap K f) (y K f)
    simp

theorem toLaurent_comp_fromLaurent :
    (toLaurent K f).comp (fromLaurent K f) = AlgHom.id K (LaurentChart K f) := by
  apply AdjoinRoot.algHom_ext'
  · apply IsLocalization.algHom_ext (Submonoid.powers (X : Polynomial K))
    apply Polynomial.algHom_ext
    change toLaurent K f (fromLaurent K f (AdjoinRoot.of (laurentEquation K f)
      (Polynomial.toLaurent X))) = AdjoinRoot.of (laurentEquation K f) (Polynomial.toLaurent X)
    change toLaurent K f (AdjoinRoot.liftAlgHom _ _ _ _ (AdjoinRoot.of _ _)) = _
    rw [AdjoinRoot.liftAlgHom_of, fromLaurentCoefficients_toLaurent,
      toLaurent_algebraMap]
    simpa only [x, Polynomial.toLaurent_X] using toLaurentBase_x K f
  · simp

def overlapAlgEquiv : Overlap K f ≃ₐ[K] LaurentChart K f :=
  AlgEquiv.ofAlgHom (toLaurent K f) (fromLaurent K f)
    (toLaurent_comp_fromLaurent K f) (fromLaurent_comp_toLaurent K f)

end MazurTransfer.HyperellipticLaurentOverlap

#print axioms MazurTransfer.HyperellipticLaurentOverlap.overlapAlgEquiv

/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Design boundary: coefficient coordinates for the monic quadratic algebra.
Named downstream consumer: actual hyperelliptic overlap and chart sections.
-/

noncomputable section
namespace MazurTransfer.QuadraticCoordinates
open Polynomial Module
variable (R : Type*) [CommRing R] [Nontrivial R] (f : R)

abbrev equation : Polynomial R := X ^ 2 - C f

def powerBasis : PowerBasis R (AdjoinRoot (equation R f)) :=
  AdjoinRoot.powerBasis' (Polynomial.monic_X_pow_sub_C f (by decide))

theorem powerBasis_dim : (powerBasis R f).dim = 2 := by
  change (X ^ 2 - C f).natDegree = 2
  exact Polynomial.natDegree_X_pow_sub_C

def basis : Basis (Fin 2) R (AdjoinRoot (equation R f)) :=
  (powerBasis R f).basis.reindex (finCongr (powerBasis_dim R f))

theorem basis_zero : basis R f 0 = 1 := by
  rw [basis, Basis.reindex_apply]
  calc
    _ = (powerBasis R f).gen ^ ((finCongr (powerBasis_dim R f)).symm 0).val :=
      (powerBasis R f).basis_eq_pow _
    _ = 1 := by simp

theorem basis_one : basis R f 1 = AdjoinRoot.root (equation R f) := by
  rw [basis, Basis.reindex_apply]
  calc
    _ = (powerBasis R f).gen ^ ((finCongr (powerBasis_dim R f)).symm 1).val :=
      (powerBasis R f).basis_eq_pow _
    _ = (powerBasis R f).gen := by simp
    _ = AdjoinRoot.root (equation R f) := rfl

def coordinates : AdjoinRoot (equation R f) ≃ₗ[R] R × R :=
  (basis R f).equivFun.trans (LinearEquiv.finTwoArrow R R)

theorem coordinates_symm (v : R × R) :
    (coordinates R f).symm v = AdjoinRoot.of (equation R f) v.1 +
      AdjoinRoot.of (equation R f) v.2 * AdjoinRoot.root (equation R f) := by
  rw [coordinates, LinearEquiv.trans_symm, LinearEquiv.trans_apply,
    Basis.equivFun_symm_apply]
  simp [Fin.sum_univ_two, basis_zero, basis_one, Algebra.smul_def, AdjoinRoot.algebraMap_eq]

theorem coordinates_of_add_of_mul_root (a b : R) :
    coordinates R f (AdjoinRoot.of (equation R f) a +
      AdjoinRoot.of (equation R f) b * AdjoinRoot.root (equation R f)) = (a, b) := by
  rw [← coordinates_symm R f (a, b), LinearEquiv.apply_symm_apply]

end MazurTransfer.QuadraticCoordinates

#print axioms MazurTransfer.QuadraticCoordinates.coordinates_symm

/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Design boundary: compute the quotient of Laurent coefficient pairs by the
two chart images with transitions x = z^-1 and y = w z^-3.
Named downstream consumer: the actual order-thirteen two-chart Cech quotient.
This algebraic coefficient calculation alone is not a genus theorem.
-/

noncomputable section
namespace MazurTransfer.LaurentTwoChartCoefficientQuotient

variable (K : Type*) [Field K]
abbrev LaurentCoefficients := ℤ →₀ K
abbrev ChartCoefficients := ℕ →₀ K
abbrev OverlapCoefficients := LaurentCoefficients K × LaurentCoefficients K

def ordinary : (ChartCoefficients K × ChartCoefficients K) →ₗ[K] OverlapCoefficients K :=
  (Finsupp.lmapDomain K K (fun n : ℕ => (n : ℤ))).prodMap
    (Finsupp.lmapDomain K K (fun n : ℕ => (n : ℤ)))

def reciprocal : (ChartCoefficients K × ChartCoefficients K) →ₗ[K] OverlapCoefficients K :=
  (Finsupp.lmapDomain K K (fun n : ℕ => -(n : ℤ))).prodMap
    (Finsupp.lmapDomain K K (fun n : ℕ => -(n : ℤ) - 3))

def boundaries : Submodule K (OverlapCoefficients K) := (ordinary K).range ⊔ (reciprocal K).range

def survivingCoefficients : OverlapCoefficients K →ₗ[K] K × K where
  toFun v := (v.2 (-1), v.2 (-2))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem range_lmapDomain_eq_supported (e : ℕ → ℤ) :
    (Finsupp.lmapDomain K K e).range = Finsupp.supported K K (Set.range e) := by
  rw [Finsupp.range_lmapDomain, Finsupp.supported_eq_span_single]
  congr 1
  ext z
  simp

theorem ordinary_range : (ordinary K).range =
    (Finsupp.supported K K {n : ℤ | 0 ≤ n}).prod
      (Finsupp.supported K K {n : ℤ | 0 ≤ n}) := by
  rw [ordinary, LinearMap.range_prodMap, range_lmapDomain_eq_supported]
  congr 2 <;> ext z <;> simp

theorem reciprocal_range : (reciprocal K).range =
    (Finsupp.supported K K {n : ℤ | n ≤ 0}).prod
      (Finsupp.supported K K {n : ℤ | n ≤ -3}) := by
  rw [reciprocal, LinearMap.range_prodMap, range_lmapDomain_eq_supported,
    range_lmapDomain_eq_supported]
  have h₀ : Set.range (fun n : ℕ => -(n : ℤ)) = {n : ℤ | n ≤ 0} := by
    ext z
    constructor
    · rintro ⟨n, rfl⟩; simp
    · intro hz
      change z ≤ 0 at hz
      refine ⟨(-z).toNat, ?_⟩
      change -((-z).toNat : ℤ) = z
      rw [Int.toNat_of_nonneg (by omega)]
      omega
  have h₃ : Set.range (fun n : ℕ => -(n : ℤ) - 3) = {n : ℤ | n ≤ -3} := by
    ext z
    constructor
    · rintro ⟨n, rfl⟩; simp
    · intro hz
      change z ≤ -3 at hz
      refine ⟨(-z-3).toNat, ?_⟩
      change -((-z-3).toNat : ℤ) - 3 = z
      rw [Int.toNat_of_nonneg (by omega)]
      omega
  rw [h₀, h₃]

theorem boundaries_eq_kernel : boundaries K = (survivingCoefficients K).ker := by
  rw [boundaries, ordinary_range, reciprocal_range]
  apply le_antisymm
  · apply sup_le
    · intro v hv
      rw [LinearMap.mem_ker]
      have hy := hv.2
      have h₁ := (Finsupp.mem_supported' K v.2).mp hy (-1) (by simp)
      have h₂ := (Finsupp.mem_supported' K v.2).mp hy (-2) (by simp)
      exact Prod.ext h₁ h₂
    · intro v hv
      rw [LinearMap.mem_ker]
      have hy := hv.2
      have h₁ := (Finsupp.mem_supported' K v.2).mp hy (-1) (by simp)
      have h₂ := (Finsupp.mem_supported' K v.2).mp hy (-2) (by simp)
      exact Prod.ext h₁ h₂
  · intro v hv
    have hzero : v.2 (-1) = 0 ∧ v.2 (-2) = 0 := by
      change (v.2 (-1), v.2 (-2)) = (0, 0) at hv
      exact Prod.mk.inj hv
    let positive (a : ℤ →₀ K) := a.filter (fun n => 0 ≤ n)
    let negative (a : ℤ →₀ K) := a.filter (fun n => n < 0)
    refine Submodule.mem_sup.mpr ⟨(positive v.1, positive v.2), ?_,
      (negative v.1, negative v.2), ?_, ?_⟩
    · constructor <;> apply (Finsupp.mem_supported' K _).mpr <;>
        intro n hn <;> change ¬ 0 ≤ n at hn <;> simp [positive, hn]
    · constructor
      · apply (Finsupp.mem_supported' K _).mpr
        intro n hn
        simp only [Set.mem_ofPred_eq, not_le] at hn
        simp [negative, show ¬ n < 0 by omega]
      · apply (Finsupp.mem_supported' K _).mpr
        intro n hn
        simp only [Set.mem_ofPred_eq, not_le] at hn
        by_cases hp : 0 ≤ n
        · simp [negative, show ¬ n < 0 by omega]
        · have hn' : n = -1 ∨ n = -2 := by omega
          rcases hn' with rfl | rfl <;> simp [negative, hzero.1, hzero.2]
    · apply Prod.ext <;> ext n <;> by_cases hn : 0 ≤ n <;>
        simp [positive, negative, hn, show n < 0 ↔ ¬ 0 ≤ n by omega]

theorem survivingCoefficients_surjective : Function.Surjective (survivingCoefficients K) := by
  rintro ⟨a, b⟩
  let v : ℤ →₀ K := Finsupp.single (-1) a + Finsupp.single (-2) b
  refine ⟨(0, v), ?_⟩
  change (v (-1), v (-2)) = (a, b)
  simp [v]

def quotientEquiv : (OverlapCoefficients K ⧸ boundaries K) ≃ₗ[K] K × K :=
  (Submodule.quotEquivOfEq _ _ (boundaries_eq_kernel K)).trans
    ((survivingCoefficients K).quotKerEquivOfSurjective (survivingCoefficients_surjective K))

theorem quotient_finrank : Module.finrank K (OverlapCoefficients K ⧸ boundaries K) = 2 := by
  rw [(quotientEquiv K).finrank_eq]
  simp

end MazurTransfer.LaurentTwoChartCoefficientQuotient

#print axioms MazurTransfer.LaurentTwoChartCoefficientQuotient.quotient_finrank

/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Design boundary: the quotient of the actual overlap coordinate algebra by
the sum of the images of the two actual chart algebras.
Named downstream consumer: comparison with genuine structure-sheaf H1.
This file makes no genus claim without that comparison.
-/

noncomputable section
namespace MazurTransfer.Order13ActualCechQuotient
open Polynomial Module
open MazurTorsion.XOneThirteenAffineCurve
open MazurTorsion.XOneThirteenProjectiveCurve

variable (K : Type*) [Field K]
abbrev QuadraticLaurentRing := HyperellipticLaurentOverlap.LaurentChart K (sexticPolynomial K)

def overlapAlgEquiv : OrdinaryOverlapRing K ≃ₐ[K] QuadraticLaurentRing K :=
  HyperellipticLaurentOverlap.overlapAlgEquiv K (sexticPolynomial K)

def overlapCoordinates : OrdinaryOverlapRing K ≃ₗ[K] LaurentTwoChartCoefficientQuotient.OverlapCoefficients K :=
  (overlapAlgEquiv K).toLinearEquiv.trans
    (((QuadraticCoordinates.coordinates (LaurentPolynomial K) (sexticPolynomial K).toLaurent).restrictScalars K).trans
      ((AddMonoidAlgebra.coeffLinearEquiv K).prodCongr (AddMonoidAlgebra.coeffLinearEquiv K)))

def ordinaryCoordinates : CoordinateRing K ≃ₗ[K] LaurentTwoChartCoefficientQuotient.ChartCoefficients K × LaurentTwoChartCoefficientQuotient.ChartCoefficients K :=
  ((QuadraticCoordinates.coordinates (Polynomial K) (sexticPolynomial K)).restrictScalars K).trans
    (((Polynomial.toFinsuppIsoLinear K).trans (AddMonoidAlgebra.coeffLinearEquiv K)).prodCongr
      ((Polynomial.toFinsuppIsoLinear K).trans (AddMonoidAlgebra.coeffLinearEquiv K)))

def reciprocalCoordinates : ReciprocalRing K ≃ₗ[K] LaurentTwoChartCoefficientQuotient.ChartCoefficients K × LaurentTwoChartCoefficientQuotient.ChartCoefficients K :=
  ((QuadraticCoordinates.coordinates (Polynomial K) (reciprocalPolynomial K)).restrictScalars K).trans
    (((Polynomial.toFinsuppIsoLinear K).trans (AddMonoidAlgebra.coeffLinearEquiv K)).prodCongr
      ((Polynomial.toFinsuppIsoLinear K).trans (AddMonoidAlgebra.coeffLinearEquiv K)))

theorem overlapCoordinates_of_add_of_mul_root (a b : LaurentPolynomial K) :
    overlapCoordinates K ((overlapAlgEquiv K).symm
      (AdjoinRoot.of (HyperellipticLaurentOverlap.laurentEquation K (sexticPolynomial K)) a +
        AdjoinRoot.of (HyperellipticLaurentOverlap.laurentEquation K (sexticPolynomial K)) b *
          AdjoinRoot.root (HyperellipticLaurentOverlap.laurentEquation K (sexticPolynomial K)))) = (a.coeff, b.coeff) := by
  change ((AddMonoidAlgebra.coeffLinearEquiv K).prodCongr (AddMonoidAlgebra.coeffLinearEquiv K))
    (QuadraticCoordinates.coordinates (LaurentPolynomial K) (sexticPolynomial K).toLaurent
      ((overlapAlgEquiv K) ((overlapAlgEquiv K).symm _))) = _
  rw [AlgEquiv.apply_symm_apply]
  change ((AddMonoidAlgebra.coeffLinearEquiv K).prodCongr (AddMonoidAlgebra.coeffLinearEquiv K))
    (QuadraticCoordinates.coordinates (LaurentPolynomial K) (sexticPolynomial K).toLaurent
      (AdjoinRoot.of (QuadraticCoordinates.equation _ _) a + AdjoinRoot.of (QuadraticCoordinates.equation _ _) b *
        AdjoinRoot.root (QuadraticCoordinates.equation _ _))) = _
  rw [QuadraticCoordinates.coordinates_of_add_of_mul_root]
  rfl

theorem laurent_inverse_coordinate :
    overlapAlgEquiv K (IsLocalization.Away.invSelf (xCoordinate K)) =
      AdjoinRoot.of (HyperellipticLaurentOverlap.laurentEquation K (sexticPolynomial K)) (LaurentPolynomial.T (-1)) := by
  let o := AdjoinRoot.of (HyperellipticLaurentOverlap.laurentEquation K (sexticPolynomial K))
  have hu : IsUnit (o (LaurentPolynomial.T 1)) :=
    (LaurentPolynomial.isUnit_T (1 : ℤ)).map o
  apply hu.mul_left_cancel
  have hx : overlapAlgEquiv K (algebraMap (CoordinateRing K) (OrdinaryOverlapRing K) (xCoordinate K)) =
      o (LaurentPolynomial.T 1) := by
    change HyperellipticLaurentOverlap.toLaurent K (sexticPolynomial K)
      (algebraMap _ _ (HyperellipticLaurentOverlap.x K (sexticPolynomial K))) = _
    rw [HyperellipticLaurentOverlap.toLaurent_algebraMap]
    exact HyperellipticLaurentOverlap.toLaurentBase_x K (sexticPolynomial K)
  rw [← hx, ← map_mul, IsLocalization.Away.mul_invSelf, map_one, hx]
  change 1 = o (LaurentPolynomial.T 1) * o (LaurentPolynomial.T (-1))
  rw [← map_mul, ← LaurentPolynomial.T_add]
  simp only [Int.reduceAdd, LaurentPolynomial.T_zero, map_one]

theorem reciprocal_z_laurent :
    overlapAlgEquiv K (reciprocalToOrdinaryBase K (zCoordinate K)) =
      AdjoinRoot.of (HyperellipticLaurentOverlap.laurentEquation K (sexticPolynomial K)) (LaurentPolynomial.T (-1)) := by
  rw [reciprocalToOrdinaryBase_z]
  exact laurent_inverse_coordinate K

theorem reciprocal_w_laurent :
    overlapAlgEquiv K (reciprocalToOrdinaryBase K (wCoordinate K)) =
      AdjoinRoot.of (HyperellipticLaurentOverlap.laurentEquation K (sexticPolynomial K)) (LaurentPolynomial.T (-3)) *
        AdjoinRoot.root (HyperellipticLaurentOverlap.laurentEquation K (sexticPolynomial K)) := by
  rw [reciprocalToOrdinaryBase_w]
  change overlapAlgEquiv K
    (algebraMap (CoordinateRing K) (OrdinaryOverlapRing K) (yCoordinate K) *
      (IsLocalization.Away.invSelf (xCoordinate K)) ^ 3) = _
  rw [map_mul, map_pow, laurent_inverse_coordinate]
  have hy : overlapAlgEquiv K (algebraMap (CoordinateRing K) (OrdinaryOverlapRing K) (yCoordinate K)) =
      AdjoinRoot.root (HyperellipticLaurentOverlap.laurentEquation K (sexticPolynomial K)) := by
    change HyperellipticLaurentOverlap.toLaurent K (sexticPolynomial K)
      (algebraMap _ _ (HyperellipticLaurentOverlap.y K (sexticPolynomial K))) = _
    rw [HyperellipticLaurentOverlap.toLaurent_algebraMap]
    exact HyperellipticLaurentOverlap.toLaurentBase_y K (sexticPolynomial K)
  rw [hy, ← map_pow, LaurentPolynomial.T_pow]
  norm_num only
  rw [mul_comm]

theorem invert_toLaurent_coeff (p : Polynomial K) :
    (LaurentPolynomial.invert p.toLaurent).coeff =
      Finsupp.mapDomain (fun n : ℕ => -(n : ℤ)) p.toFinsupp.coeff := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simpa only [map_add, AddMonoidAlgebra.coeff_add, Polynomial.toFinsupp_add,
        Finsupp.mapDomain_add] using congrArg₂ (· + ·) hp hq
  | monomial n a =>
      rw [Polynomial.toLaurent_C_mul_T]
      rw [map_mul, LaurentPolynomial.invert_C, LaurentPolynomial.invert_T,
        ← LaurentPolynomial.single_eq_C_mul_T]
      simp only [AddMonoidAlgebra.coeff_single, Polynomial.toFinsupp_monomial, Finsupp.mapDomain_single]

theorem invert_toLaurent_shift_coeff (p : Polynomial K) :
    (LaurentPolynomial.invert p.toLaurent * LaurentPolynomial.T (-3)).coeff =
      Finsupp.mapDomain (fun n : ℕ => -(n : ℤ) - 3) p.toFinsupp.coeff := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simpa only [map_add, add_mul, AddMonoidAlgebra.coeff_add, Polynomial.toFinsupp_add,
        Finsupp.mapDomain_add] using congrArg₂ (· + ·) hp hq
  | monomial n a =>
      rw [Polynomial.toLaurent_C_mul_T]
      rw [map_mul, LaurentPolynomial.invert_C, LaurentPolynomial.invert_T,
        LaurentPolynomial.mul_T_assoc, ← LaurentPolynomial.single_eq_C_mul_T]
      simp only [AddMonoidAlgebra.coeff_single, Polynomial.toFinsupp_monomial, Finsupp.mapDomain_single]
      rfl

def actualBoundaries : Submodule K (OrdinaryOverlapRing K) :=
  (Algebra.algHom K (CoordinateRing K) (OrdinaryOverlapRing K)).toLinearMap.range ⊔
    (reciprocalToOrdinaryBase K).toLinearMap.range

theorem ordinary_laurent (p : Polynomial K) :
    overlapAlgEquiv K (algebraMap (CoordinateRing K) (OrdinaryOverlapRing K)
      (AdjoinRoot.of (affineEquation K) p)) =
        AdjoinRoot.of (HyperellipticLaurentOverlap.laurentEquation K (sexticPolynomial K)) p.toLaurent := by
  change HyperellipticLaurentOverlap.toLaurent K (sexticPolynomial K)
    (algebraMap _ _ (AdjoinRoot.of (HyperellipticLaurentOverlap.equation K (sexticPolynomial K)) p)) = _
  rw [HyperellipticLaurentOverlap.toLaurent_algebraMap]
  simp [HyperellipticLaurentOverlap.toLaurentBase]

theorem ordinary_y_laurent :
    overlapAlgEquiv K (algebraMap (CoordinateRing K) (OrdinaryOverlapRing K) (yCoordinate K)) =
      AdjoinRoot.root (HyperellipticLaurentOverlap.laurentEquation K (sexticPolynomial K)) := by
  change HyperellipticLaurentOverlap.toLaurent K (sexticPolynomial K)
    (algebraMap _ _ (HyperellipticLaurentOverlap.y K (sexticPolynomial K))) = _
  rw [HyperellipticLaurentOverlap.toLaurent_algebraMap]
  exact HyperellipticLaurentOverlap.toLaurentBase_y K (sexticPolynomial K)

theorem reciprocal_laurent (p : Polynomial K) :
    overlapAlgEquiv K (reciprocalToOrdinaryBase K (AdjoinRoot.of (reciprocalEquation K) p)) =
      AdjoinRoot.of (HyperellipticLaurentOverlap.laurentEquation K (sexticPolynomial K))
        (LaurentPolynomial.invert p.toLaurent) := by
  have h : ((overlapAlgEquiv K).toAlgHom.comp (reciprocalToOrdinaryBase K)).comp
      (AdjoinRoot.ofAlgHom K (reciprocalEquation K)) =
    (AdjoinRoot.ofAlgHom K (HyperellipticLaurentOverlap.laurentEquation K (sexticPolynomial K))).comp
      (LaurentPolynomial.invert.toAlgHom.comp Polynomial.toLaurentAlg) := by
    apply Polynomial.algHom_ext
    change overlapAlgEquiv K (reciprocalToOrdinaryBase K (zCoordinate K)) =
      AdjoinRoot.of (HyperellipticLaurentOverlap.laurentEquation K (sexticPolynomial K))
        (LaurentPolynomial.invert (Polynomial.toLaurent (X : Polynomial K)))
    rw [Polynomial.toLaurent_X, LaurentPolynomial.invert_T]
    exact reciprocal_z_laurent K
  exact DFunLike.congr_fun h p

theorem ordinary_diagram (a : CoordinateRing K) :
    overlapCoordinates K (algebraMap (CoordinateRing K) (OrdinaryOverlapRing K) a) =
      LaurentTwoChartCoefficientQuotient.ordinary K (ordinaryCoordinates K a) := by
  let p := QuadraticCoordinates.coordinates (Polynomial K) (sexticPolynomial K) a
  have ha : a = AdjoinRoot.of (affineEquation K) p.1 +
      AdjoinRoot.of (affineEquation K) p.2 * yCoordinate K := by
    exact (QuadraticCoordinates.coordinates_symm (Polynomial K) (sexticPolynomial K) p).symm.trans
      ((QuadraticCoordinates.coordinates (Polynomial K) (sexticPolynomial K)).symm_apply_apply a) |>.symm
  have he : overlapAlgEquiv K (algebraMap (CoordinateRing K) (OrdinaryOverlapRing K) a) =
      AdjoinRoot.of (HyperellipticLaurentOverlap.laurentEquation K (sexticPolynomial K)) p.1.toLaurent +
        AdjoinRoot.of (HyperellipticLaurentOverlap.laurentEquation K (sexticPolynomial K)) p.2.toLaurent *
          AdjoinRoot.root (HyperellipticLaurentOverlap.laurentEquation K (sexticPolynomial K)) := by
    rw [ha, map_add, map_mul, map_add, map_mul, ordinary_laurent, ordinary_laurent,
      ordinary_y_laurent]
  have he' := congrArg (overlapAlgEquiv K).symm he
  rw [AlgEquiv.symm_apply_apply] at he'
  rw [he', overlapCoordinates_of_add_of_mul_root]
  rfl

theorem reciprocal_diagram (a : ReciprocalRing K) :
    overlapCoordinates K (reciprocalToOrdinaryBase K a) =
      LaurentTwoChartCoefficientQuotient.reciprocal K (reciprocalCoordinates K a) := by
  let p := QuadraticCoordinates.coordinates (Polynomial K) (reciprocalPolynomial K) a
  have ha : a = AdjoinRoot.of (reciprocalEquation K) p.1 +
      AdjoinRoot.of (reciprocalEquation K) p.2 * wCoordinate K := by
    exact (QuadraticCoordinates.coordinates_symm (Polynomial K) (reciprocalPolynomial K) p).symm.trans
      ((QuadraticCoordinates.coordinates (Polynomial K) (reciprocalPolynomial K)).symm_apply_apply a) |>.symm
  have he : overlapAlgEquiv K (reciprocalToOrdinaryBase K a) =
      AdjoinRoot.of (HyperellipticLaurentOverlap.laurentEquation K (sexticPolynomial K))
        (LaurentPolynomial.invert p.1.toLaurent) +
        AdjoinRoot.of (HyperellipticLaurentOverlap.laurentEquation K (sexticPolynomial K))
          (LaurentPolynomial.invert p.2.toLaurent * LaurentPolynomial.T (-3)) *
          AdjoinRoot.root (HyperellipticLaurentOverlap.laurentEquation K (sexticPolynomial K)) := by
    rw [ha, map_add, map_mul, map_add, map_mul, reciprocal_laurent, reciprocal_laurent,
      reciprocal_w_laurent, map_mul]
    ring
  have he' := congrArg (overlapAlgEquiv K).symm he
  rw [AlgEquiv.symm_apply_apply] at he'
  rw [he', overlapCoordinates_of_add_of_mul_root, invert_toLaurent_coeff,
    invert_toLaurent_shift_coeff]
  rfl

theorem actualBoundaries_image :
    (actualBoundaries K).map (overlapCoordinates K).toLinearMap =
      LaurentTwoChartCoefficientQuotient.boundaries K := by
  rw [actualBoundaries, LaurentTwoChartCoefficientQuotient.boundaries, Submodule.map_sup]
  congr 1
  · ext v
    constructor
    · rintro ⟨u, ⟨a, rfl⟩, rfl⟩
      exact ⟨ordinaryCoordinates K a, (ordinary_diagram K a).symm⟩
    · rintro ⟨c, rfl⟩
      refine ⟨algebraMap (CoordinateRing K) (OrdinaryOverlapRing K)
        ((ordinaryCoordinates K).symm c), ⟨(ordinaryCoordinates K).symm c, rfl⟩, ?_⟩
      change overlapCoordinates K
        (algebraMap (CoordinateRing K) (OrdinaryOverlapRing K) ((ordinaryCoordinates K).symm c)) = _
      rw [ordinary_diagram, LinearEquiv.apply_symm_apply]
  · ext v
    constructor
    · rintro ⟨u, ⟨a, rfl⟩, rfl⟩
      exact ⟨reciprocalCoordinates K a, (reciprocal_diagram K a).symm⟩
    · rintro ⟨c, rfl⟩
      refine ⟨reciprocalToOrdinaryBase K ((reciprocalCoordinates K).symm c),
        ⟨(reciprocalCoordinates K).symm c, rfl⟩, ?_⟩
      change overlapCoordinates K
        (reciprocalToOrdinaryBase K ((reciprocalCoordinates K).symm c)) = _
      rw [reciprocal_diagram, LinearEquiv.apply_symm_apply]

def quotientEquiv : (OrdinaryOverlapRing K ⧸ actualBoundaries K) ≃ₗ[K] K × K :=
  (Submodule.Quotient.equiv (actualBoundaries K) (LaurentTwoChartCoefficientQuotient.boundaries K)
    (overlapCoordinates K) (actualBoundaries_image K)).trans
      (LaurentTwoChartCoefficientQuotient.quotientEquiv K)

theorem actual_two_chart_section_quotient_finrank :
    Module.finrank K (OrdinaryOverlapRing K ⧸ actualBoundaries K) = 2 := by
  rw [(quotientEquiv K).finrank_eq]
  simp

def reciprocalPolynomialSections : (Polynomial K × Polynomial K) →ₗ[K] OrdinaryOverlapRing K :=
  let coeff := (Polynomial.aeval (IsLocalization.Away.invSelf (xCoordinate K)) :
    Polynomial K →ₐ[K] OrdinaryOverlapRing K).toLinearMap
  coeff.coprod ((LinearMap.mulRight K
    (algebraMap (CoordinateRing K) (OrdinaryOverlapRing K) (yCoordinate K) *
      (IsLocalization.Away.invSelf (xCoordinate K)) ^ 3)).comp coeff)

theorem reciprocal_sections_formula (p : Polynomial K × Polynomial K) :
    reciprocalToOrdinaryBase K
      (AdjoinRoot.of (reciprocalEquation K) p.1 +
        AdjoinRoot.of (reciprocalEquation K) p.2 * wCoordinate K) =
      reciprocalPolynomialSections K p := by
  rw [map_add, map_mul]
  simp only [reciprocalToOrdinaryBase, AdjoinRoot.liftAlgHom_of,
    wCoordinate, AdjoinRoot.liftAlgHom_root]
  rfl

theorem reciprocal_polynomial_sections_range :
    (reciprocalToOrdinaryBase K).toLinearMap.range =
      (reciprocalPolynomialSections K).range := by
  ext v
  constructor
  · rintro ⟨a, rfl⟩
    let p := QuadraticCoordinates.coordinates (Polynomial K) (reciprocalPolynomial K) a
    refine ⟨p, ?_⟩
    rw [← reciprocal_sections_formula]
    apply congrArg (reciprocalToOrdinaryBase K)
    exact (QuadraticCoordinates.coordinates_symm (Polynomial K) (reciprocalPolynomial K) p).symm.trans
      ((QuadraticCoordinates.coordinates (Polynomial K) (reciprocalPolynomial K)).symm_apply_apply a)
  · rintro ⟨p, rfl⟩
    exact ⟨AdjoinRoot.of (reciprocalEquation K) p.1 +
      AdjoinRoot.of (reciprocalEquation K) p.2 * wCoordinate K,
      reciprocal_sections_formula K p⟩

theorem actual_quotient_finrank_polynomial_sections :
    Module.finrank K (OrdinaryOverlapRing K ⧸
      ((Algebra.algHom K (CoordinateRing K) (OrdinaryOverlapRing K)).toLinearMap.range ⊔
        (reciprocalPolynomialSections K).range)) = 2 := by
  rw [← reciprocal_polynomial_sections_range]
  exact actual_two_chart_section_quotient_finrank K

end MazurTransfer.Order13ActualCechQuotient

#print axioms MazurTransfer.Order13ActualCechQuotient.overlapCoordinates
#print axioms MazurTransfer.Order13ActualCechQuotient.reciprocal_w_laurent
#print axioms MazurTransfer.Order13ActualCechQuotient.actual_two_chart_section_quotient_finrank
#print axioms MazurTransfer.Order13ActualCechQuotient.actual_quotient_finrank_polynomial_sections


theorem solution (K : Type*) [Field K] :
    let f : Polynomial K := Polynomial.X ^ 6 + 2 * Polynomial.X ^ 5 +
      Polynomial.X ^ 4 + 2 * Polynomial.X ^ 3 + 6 * Polynomial.X ^ 2 +
      4 * Polynomial.X + 1
    let q : Polynomial (Polynomial K) := Polynomial.X ^ 2 - Polynomial.C f
    let A := AdjoinRoot q
    let x : A := AdjoinRoot.of q Polynomial.X
    let y : A := AdjoinRoot.root q
    let L := Localization.Away x
    let ordinary : A →ₗ[K] L := (Algebra.algHom K A L).toLinearMap
    let coeff : Polynomial K →ₗ[K] L :=
      (Polynomial.aeval (IsLocalization.Away.invSelf x) : Polynomial K →ₐ[K] L).toLinearMap
    let reciprocal : (Polynomial K × Polynomial K) →ₗ[K] L :=
      coeff.coprod ((LinearMap.mulRight K
        (algebraMap A L y * (IsLocalization.Away.invSelf x) ^ 3)).comp coeff)
    Module.finrank K (L ⧸ (ordinary.range ⊔ reciprocal.range)) = 2 := by
  exact MazurTransfer.Order13ActualCechQuotient.actual_quotient_finrank_polynomial_sections K

#print axioms solution
