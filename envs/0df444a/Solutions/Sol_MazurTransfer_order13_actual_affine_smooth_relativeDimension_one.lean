-- Prove2me | solution 1 for MazurTransfer.order13_actual_affine_smooth_relativeDimension_one
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T21:50:03.733321+00:00
-- url     : https://prove2.me/submissions/88b51b59-091c-4821-84c6-61970f246ac1

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

Design boundary: the actual Kaehler differential module of the quadratic
hyperelliptic coordinate algebra. Named downstream consumer: smoothness of
relative dimension one for the actual order-thirteen chart morphisms.
No genus or Jacobian assertion is assumed.
-/

noncomputable section
namespace MazurTransfer.HyperellipticCoordinateDifferentials
open Polynomial Module
variable (K : Type*) [Field K] (f : Polynomial K)

abbrev equation : Polynomial (Polynomial K) := X ^ 2 - C f
abbrev CoordinateRing := AdjoinRoot (equation K f)
def x : CoordinateRing K f := AdjoinRoot.of (equation K f) X
def y : CoordinateRing K f := AdjoinRoot.root (equation K f)
abbrev of : Polynomial K →+* CoordinateRing K f := AdjoinRoot.of (equation K f)

theorem y_sq : y K f ^ 2 = of K f f := by
  have h := AdjoinRoot.eval₂_root (equation K f)
  rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C] at h
  exact sub_eq_zero.mp h

theorem of_eq_aeval (p : Polynomial K) : of K f p = aeval (x K f) p := by
  have h : AdjoinRoot.ofAlgHom K (equation K f) = aeval (x K f) := by
    apply Polynomial.algHom_ext
    simp [x]
  exact DFunLike.congr_fun h p

abbrev Dual := TrivSqZeroExt (CoordinateRing K f) (CoordinateRing K f)

theorem aeval_dual (p : Polynomial K) (a da : CoordinateRing K f) :
    aeval (TrivSqZeroExt.inl a + TrivSqZeroExt.inr da : Dual K f) p =
      TrivSqZeroExt.inl (aeval a p) + TrivSqZeroExt.inr (aeval a p.derivative * da) := by
  have hsq : (TrivSqZeroExt.inr da : Dual K f) ^ 2 = 0 := by
    rw [pow_two, TrivSqZeroExt.inr_mul_inr]
  have hmap : (TrivSqZeroExt.inlAlgHom K (CoordinateRing K f) (CoordinateRing K f)).comp
      (aeval a) = aeval (TrivSqZeroExt.inl a : Dual K f) := by
    apply Polynomial.algHom_ext
    simp
  rw [aeval_add_of_sq_eq_zero p _ _ hsq]
  rw [← DFunLike.congr_fun hmap p, ← DFunLike.congr_fun hmap p.derivative]
  change TrivSqZeroExt.inl (aeval a p) +
    TrivSqZeroExt.inl (aeval a p.derivative) * TrivSqZeroExt.inr da = _
  rw [TrivSqZeroExt.inl_mul_inr]
  rfl

def dualX : Dual K f := TrivSqZeroExt.inl (x K f) + TrivSqZeroExt.inr (2 * y K f)
def dualY : Dual K f := TrivSqZeroExt.inl (y K f) + TrivSqZeroExt.inr (of K f f.derivative)

theorem dual_relation : dualY K f ^ 2 = aeval (dualX K f) f := by
  rw [dualX, aeval_dual]
  apply TrivSqZeroExt.ext
  · simp [dualY, pow_two, ← of_eq_aeval, ← y_sq]
  · simp only [dualY, pow_two, TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_add,
      TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero,
      TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add,
      ← of_eq_aeval, smul_eq_mul, op_smul_eq_smul]
    ring

def dualSection : CoordinateRing K f →ₐ[K] Dual K f :=
  AdjoinRoot.liftAlgHom (equation K f) (aeval (dualX K f)) (dualY K f) (by
    rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
    exact sub_eq_zero.mpr (dual_relation K f))

@[simp] theorem dualSection_x : dualSection K f (x K f) = dualX K f := by
  simp [dualSection, x]

@[simp] theorem dualSection_y : dualSection K f (y K f) = dualY K f := by
  simp [dualSection, y]

theorem dualSection_fst :
    (TrivSqZeroExt.fstHom K (CoordinateRing K f) (CoordinateRing K f)).comp
      (dualSection K f) = AlgHom.id K (CoordinateRing K f) := by
  apply AdjoinRoot.algHom_ext'
  · apply Polynomial.algHom_ext
    change (dualSection K f (x K f)).fst = x K f
    rw [dualSection_x]
    simp [dualX]
  · change (dualSection K f (y K f)).fst = y K f
    rw [dualSection_y]
    simp [dualY]

def tangentDerivation : Derivation K (CoordinateRing K f) (CoordinateRing K f) where
  toLinearMap := ((TrivSqZeroExt.sndHom (CoordinateRing K f) (CoordinateRing K f)).restrictScalars K).comp
    (dualSection K f).toLinearMap
  map_one_eq_zero' := by
    change (dualSection K f 1).snd = 0
    simp
  leibniz' a b := by
    change (dualSection K f (a * b)).snd =
      a • (dualSection K f b).snd + b • (dualSection K f a).snd
    have ha : (dualSection K f a).fst = a := DFunLike.congr_fun (dualSection_fst K f) a
    have hb : (dualSection K f b).fst = b := DFunLike.congr_fun (dualSection_fst K f) b
    rw [map_mul, TrivSqZeroExt.snd_mul, ha, hb]
    simp [smul_eq_mul, mul_comm]

@[simp] theorem tangentDerivation_x : tangentDerivation K f (x K f) = 2 * y K f := by
  change (dualSection K f (x K f)).snd = _
  rw [dualSection_x]
  simp [dualX]

@[simp] theorem tangentDerivation_y : tangentDerivation K f (y K f) = of K f f.derivative := by
  change (dualSection K f (y K f)).snd = _
  rw [dualSection_y]
  simp [dualY]

theorem derivation_of {M : Type*} [AddCommGroup M] [Module (CoordinateRing K f) M]
    [Module K M] [IsScalarTower K (CoordinateRing K f) M]
    (d : Derivation K (CoordinateRing K f) M) (p : Polynomial K) :
    d (of K f p) = of K f p.derivative • d (x K f) := by
  rw [of_eq_aeval, d.map_aeval, ← of_eq_aeval]

theorem derivation_relation {M : Type*} [AddCommGroup M] [Module (CoordinateRing K f) M]
    [Module K M] [IsScalarTower K (CoordinateRing K f) M]
    (d : Derivation K (CoordinateRing K f) M) :
    (2 * y K f) • d (y K f) = of K f f.derivative • d (x K f) := by
  have h := congrArg d (y_sq K f)
  rw [pow_two, d.leibniz, derivation_of] at h
  simpa only [two_mul, add_smul] using h

theorem kaehler_equiv (hf : f.Separable) (h2 : (2 : K) ≠ 0) :
    Nonempty (Ω[CoordinateRing K f⁄K] ≃ₗ[CoordinateRing K f] CoordinateRing K f) := by
  rw [separable_def'] at hf
  obtain ⟨a, b, hab⟩ := hf
  let A := CoordinateRing K f
  let d := KaehlerDifferential.D K A
  let c : A := algebraMap K A ((2 : K)⁻¹)
  have hc : (2 : A) * c = 1 := by
    calc
      _ = algebraMap K A ((2 : K) * (2 : K)⁻¹) := by simp only [c, map_mul, map_ofNat]
      _ = 1 := by rw [mul_inv_cancel₀ h2, map_one]
  let w : Ω[A⁄K] := (of K f a * y K f * c) • d (x K f) + of K f b • d (y K f)
  have hcoef : of K f a * y K f ^ 2 + of K f b * of K f f.derivative = 1 := by
    rw [y_sq]
    exact (by simpa only [map_add, map_mul, map_one] using congrArg (of K f) hab)
  have hcoeffirst : (2 * y K f) * (of K f a * y K f * c) = of K f a * y K f ^ 2 := by
    calc
      _ = (of K f a * y K f ^ 2) * (2 * c) := by ring
      _ = _ := by rw [hc, mul_one]
  have hrel := derivation_relation K f d
  have hx : (2 * y K f) • w = d (x K f) := by
    calc
      _ = ((2 * y K f) * (of K f a * y K f * c)) • d (x K f) +
          of K f b • ((2 * y K f) • d (y K f)) := by
        dsimp only [w]
        rw [smul_add, smul_smul, smul_comm (2 * y K f) (of K f b)]
      _ = (of K f a * y K f ^ 2) • d (x K f) +
          (of K f b * of K f f.derivative) • d (x K f) := by
        rw [hcoeffirst, hrel, smul_smul]
      _ = _ := by rw [← add_smul, hcoef, one_smul]
  have hy : of K f f.derivative • w = d (y K f) := by
    calc
      _ = (of K f a * y K f * c) • (of K f f.derivative • d (x K f)) +
          (of K f b * of K f f.derivative) • d (y K f) := by
        dsimp only [w]
        simp only [smul_add, smul_smul]
        rw [mul_comm (of K f f.derivative) (of K f a * y K f * c),
          mul_comm (of K f f.derivative) (of K f b)]
      _ = (of K f a * y K f ^ 2) • d (y K f) +
          (of K f b * of K f f.derivative) • d (y K f) := by
        rw [← hrel, smul_smul, mul_comm (of K f a * y K f * c) (2 * y K f), hcoeffirst]
      _ = _ := by rw [← add_smul, hcoef, one_smul]
  let W := Submodule.span A ({w} : Set Ω[A⁄K])
  have hw : w ∈ W := Submodule.subset_span (Set.mem_singleton w)
  have hdx : d (x K f) ∈ W := hx ▸ W.smul_mem (2 * y K f) hw
  have hdy : d (y K f) ∈ W := hy ▸ W.smul_mem (of K f f.derivative) hw
  have hspan : W = ⊤ := by
    apply top_unique
    rw [← KaehlerDifferential.span_range_derivation K A]
    apply Submodule.span_le.mpr
    rintro _ ⟨z, rfl⟩
    let p := QuadraticCoordinates.coordinates (Polynomial K) f z
    have hz : z = of K f p.1 + of K f p.2 * y K f := by
      calc
        _ = (QuadraticCoordinates.coordinates (Polynomial K) f).symm p :=
          ((QuadraticCoordinates.coordinates (Polynomial K) f).symm_apply_apply z).symm
        _ = _ := QuadraticCoordinates.coordinates_symm (Polynomial K) f p
    rw [hz, d.map_add, d.leibniz, derivation_of, derivation_of]
    exact W.add_mem (W.smul_mem _ hdx)
      (W.add_mem (W.smul_mem _ hdy) (W.smul_mem _ (W.smul_mem _ hdx)))
  let l : Ω[A⁄K] →ₗ[A] A := (tangentDerivation K f).liftKaehlerDifferential
  have hl : l w = 1 := by
    change (tangentDerivation K f).liftKaehlerDifferential
      ((of K f a * y K f * c) • KaehlerDifferential.D K A (x K f) +
        of K f b • KaehlerDifferential.D K A (y K f)) = 1
    rw [map_add, map_smul, map_smul, Derivation.liftKaehlerDifferential_comp_D,
      Derivation.liftKaehlerDifferential_comp_D, tangentDerivation_x, tangentDerivation_y]
    simp only [smul_eq_mul]
    rw [mul_comm (of K f a * y K f * c) (2 * y K f), hcoeffirst, hcoef]
  have hinj : Function.Injective (LinearMap.toSpanSingleton A Ω[A⁄K] w) := by
    intro r s h
    have hh := congrArg l h
    simpa only [LinearMap.toSpanSingleton_apply, map_smul, hl, smul_eq_mul, mul_one] using hh
  have hsurj : Function.Surjective (LinearMap.toSpanSingleton A Ω[A⁄K] w) := by
    rw [← LinearMap.range_eq_top, LinearMap.range_toSpanSingleton]
    exact hspan
  exact ⟨(LinearEquiv.ofBijective (LinearMap.toSpanSingleton A Ω[A⁄K] w) ⟨hinj, hsurj⟩).symm⟩

end MazurTransfer.HyperellipticCoordinateDifferentials

#print axioms MazurTransfer.HyperellipticCoordinateDifferentials.tangentDerivation
#print axioms MazurTransfer.HyperellipticCoordinateDifferentials.kaehler_equiv

/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Design boundary: relative dimension one from genuine Kaehler differentials
for smooth domain algebras. Named downstream consumer: the actual order-thirteen
chart morphisms. This uses genuine localization of the differential module.
-/

noncomputable section
open Module
namespace MazurTransfer
universe u
variable (R S : Type u) [CommRing R] [CommRing S] [IsDomain S] [Algebra R S]

theorem locally_standardSmooth_relativeDimension_one_of_kaehler_equiv
    [Algebra.Smooth R S] (he : Nonempty (Ω[S⁄R] ≃ₗ[S] S)) :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1) (algebraMap R S) := by
  classical
  obtain ⟨e⟩ := he
  let b : Basis Unit S Ω[S⁄R] := (Basis.singleton Unit S).map e.symm
  obtain ⟨s, hs, h⟩ := Algebra.Smooth.exists_span_eq_top_isStandardSmooth R S
  have hs' : Ideal.span {x : S | x ∈ s ∧ x ≠ 0} = ⊤ := by
    apply top_unique
    rw [← hs]
    apply Ideal.span_le.mpr
    intro x hx
    by_cases hz : x = 0
    · subst x
      exact Ideal.zero_mem _
    · exact Ideal.subset_span ⟨hx, hz⟩
  refine ⟨_, hs', fun x hx ↦ ?_⟩
  let T := Localization.Away x
  have : IsDomain T := Localization.Away.isDomain hx.2
  have : Algebra.IsStandardSmooth R T := h x hx.1
  let bT : Basis Unit T Ω[T⁄R] := b.ofIsLocalizedModule T (Submonoid.powers x)
    (KaehlerDifferential.map R R S T)
  rw [← IsScalarTower.algebraMap_eq R S T]
  change RingHom.IsStandardSmoothOfRelativeDimension 1 (algebraMap R T)
  rw [RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
  apply (Algebra.IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth 1).mpr
  simp only [rank_eq_card_basis bT, Cardinal.mk_fintype, Fintype.card_unique,
    Nat.cast_one]

end MazurTransfer
#print axioms MazurTransfer.locally_standardSmooth_relativeDimension_one_of_kaehler_equiv

/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Design boundary: genuine smoothness of a quadratic hyperelliptic coordinate
algebra over a field of characteristic different from two. Named downstream consumer: smoothness of
MazurTorsion.XOneThirteenAffineCurve.scheme and the two-chart curve.
The polynomial separability hypothesis is explicit and separately checked
for the actual order-thirteen sextic.
-/

noncomputable section
open Polynomial

namespace MazurTransfer

universe u
variable (K : Type u) [Field K]

theorem hyperelliptic_coordinate_smooth (f : Polynomial K) (hf : f.Separable) (h2 : (2 : K) ≠ 0) :
    Algebra.Smooth K (AdjoinRoot
      ((X ^ 2 - C f) : Polynomial (Polynomial K))) := by
  let q : Polynomial (Polynomial K) := X ^ 2 - C f
  have hroot : AdjoinRoot.root q ^ 2 = AdjoinRoot.of q f := by
    apply sub_eq_zero.mp
    simpa only [q, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C] using
      AdjoinRoot.eval₂_root q
  rw [separable_def'] at hf
  obtain ⟨a, b, hab⟩ := hf
  haveI : Algebra.FormallySmooth K (AdjoinRoot q) := by
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
    let c : B := algebraMap K B ((2 : K)⁻¹)
    have hc : (2 : B) * c = 1 := by
      calc
        _ = algebraMap K B ((2 : K) * (2 : K)⁻¹) := by
          simp only [c, _root_.map_mul, _root_.map_ofNat]
        _ = 1 := by rw [mul_inv_cancel₀ h2, _root_.map_one]
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

end MazurTransfer

#print axioms MazurTransfer.hyperelliptic_coordinate_smooth

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

#print axioms MazurTorsion.XOneThirteenAffineCurve.coordinateRing_isDomain

#print axioms MazurTorsion.XOneThirteenAffineCurve.affineScheme_isIntegral

/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Design boundary: the actual reciprocal coordinate algebra and the reduced
two-chart gluing. The downstream consumers `reciprocalScheme_isIntegral`
and `curveScheme_isReduced` use the coordinate-domain certificates.
No Jacobian, genus, or rank-zero assertion is assumed.
-/

noncomputable section

open Polynomial
open _root_.AlgebraicGeometry

namespace MazurTorsion.XOneThirteenProjectiveCurve

theorem reciprocalPolynomial_affineSwap (K : Type*) [CommRing K] :
    aeval (-(X : Polynomial K) - 1) (reciprocalPolynomial K) =
      XOneThirteenAffineCurve.sexticPolynomial K := by
  simp only [reciprocalPolynomial, _root_.map_add, _root_.map_mul,
    _root_.map_pow, _root_.map_ofNat, aeval_X, _root_.map_one]
  unfold XOneThirteenAffineCurve.sexticPolynomial
  ring

variable (K : Type*) [Field K] [CharZero K]

theorem reciprocalPolynomial_not_square (q : Polynomial K) :
    q ^ 2 ≠ reciprocalPolynomial K := by
  intro hq
  have h := congrArg (aeval (-(X : Polynomial K) - 1)) hq
  rw [_root_.map_pow, reciprocalPolynomial_affineSwap] at h
  exact XOneThirteenAffineCurve.sexticPolynomial_not_square K _ h

theorem reciprocalPolynomial_fraction_not_square (q : RatFunc K) :
    q ^ 2 ≠ algebraMap (Polynomial K) (RatFunc K) (reciprocalPolynomial K) := by
  intro hq
  have hIntegral : IsIntegral (Polynomial K) (q ^ 2) := by
    rw [hq]
    exact isIntegral_algebraMap
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow
    (R := Polynomial K) (K := RatFunc K) (by decide : 0 < 2) hIntegral
  apply reciprocalPolynomial_not_square K r
  apply IsFractionRing.injective (Polynomial K) (RatFunc K)
  rw [_root_.map_pow, hr, hq]

theorem reciprocalEquation_irreducible : Irreducible (reciprocalEquation K) := by
  have hmonic : (reciprocalEquation K).Monic := by
    unfold reciprocalEquation
    exact monic_X_pow_sub_C _ (by decide : 2 ≠ 0)
  apply (hmonic.irreducible_iff_irreducible_map_fraction_map (K := RatFunc K)).mpr
  simp only [reciprocalEquation, Polynomial.map_sub, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.map_C]
  exact X_pow_sub_C_irreducible_of_prime (by decide : Nat.Prime 2)
    (reciprocalPolynomial_fraction_not_square K)

theorem reciprocalRing_isDomain : IsDomain (ReciprocalRing K) :=
  AdjoinRoot.isDomain_of_prime (reciprocalEquation_irreducible K).prime

theorem reciprocalScheme_isIntegral : _root_.AlgebraicGeometry.IsIntegral (reciprocalScheme K) := by
  letI := reciprocalRing_isDomain K
  exact inferInstance

theorem curveScheme_isReduced : _root_.AlgebraicGeometry.IsReduced (curveScheme K) := by
  letI := XOneThirteenAffineCurve.affineScheme_isIntegral K
  letI := reciprocalScheme_isIntegral K
  letI : ∀ i : (glueData K).openCover.I₀,
      _root_.AlgebraicGeometry.IsReduced ((glueData K).openCover.X i) := by
    intro i
    cases i
    · change _root_.AlgebraicGeometry.IsReduced (XOneThirteenAffineCurve.scheme K)
      infer_instance
    · change _root_.AlgebraicGeometry.IsReduced (reciprocalScheme K)
      infer_instance
  exact _root_.AlgebraicGeometry.IsReduced.of_openCover (curveScheme K) (glueData K).openCover

end MazurTorsion.XOneThirteenProjectiveCurve

#print axioms MazurTorsion.XOneThirteenProjectiveCurve.reciprocalScheme_isIntegral
#print axioms MazurTorsion.XOneThirteenProjectiveCurve.curveScheme_isReduced

/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Design boundary: genuine scheme smoothness of the unchanged order-thirteen
model over a characteristic-zero field. Named downstream consumer:
`curveToBase_smooth`, for the subsequent curve/Picard interface.
-/

noncomputable section
open Polynomial _root_.AlgebraicGeometry CategoryTheory

namespace MazurTorsion.XOneThirteenProjectiveCurve
universe u
variable (K : Type u) [Field K] [CharZero K]

theorem ordinaryCoordinateRing_smooth : Algebra.Smooth K
    (XOneThirteenAffineCurve.CoordinateRing K) :=
  MazurTransfer.hyperelliptic_coordinate_smooth K
    (XOneThirteenAffineCurve.sexticPolynomial K)
    (XOneThirteenAffineCurve.sexticPolynomial_separable K) (by norm_num)

theorem reciprocalPolynomial_separable : (reciprocalPolynomial K).Separable := by
  let A : Polynomial K := 300 * X ^ 4 + 784 * X ^ 3 + 606 * X ^ 2 - 192 * X + 234
  let B : Polynomial K := -50 * X ^ 5 - 164 * X ^ 4 - 177 * X ^ 3 + 40 * X ^ 2 -
    73 * X - 65
  have hbezout : A * reciprocalPolynomial K + B * (reciprocalPolynomial K).derivative = C 104 := by
    simp only [A, B, reciprocalPolynomial, derivative_add, derivative_sub,
      derivative_mul, derivative_pow, derivative_X, derivative_natCast,
      mul_zero, zero_add, add_zero, mul_one, Polynomial.C_ofNat, _root_.map_natCast]
    norm_num
    ring
  rw [separable_def']
  refine ⟨C ((104 : K)⁻¹) * A, C ((104 : K)⁻¹) * B, ?_⟩
  calc
    _ = C ((104 : K)⁻¹) * (A * reciprocalPolynomial K + B *
      (reciprocalPolynomial K).derivative) := by ring
    _ = 1 := by rw [hbezout, ← C_mul]; norm_num

theorem reciprocalRing_smooth : Algebra.Smooth K (ReciprocalRing K) :=
  MazurTransfer.hyperelliptic_coordinate_smooth K (reciprocalPolynomial K)
    (reciprocalPolynomial_separable K) (by norm_num)

theorem ordinaryChartToBase_smooth : Smooth (ordinaryChartToBase K) := by
  unfold ordinaryChartToBase
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
  exact RingHom.smooth_algebraMap.mpr (ordinaryCoordinateRing_smooth K)

theorem reciprocalChartToBase_smooth : Smooth (reciprocalChartToBase K) := by
  unfold reciprocalChartToBase
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
  exact RingHom.smooth_algebraMap.mpr (reciprocalRing_smooth K)

theorem curveToBase_smooth : Smooth (curveToBase K) := by
  haveI : IsZariskiLocalAtSource (@Smooth.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
      (P := @Smooth.{u}) (Q := @RingHom.Smooth.{u,u})
  apply IsZariskiLocalAtSource.of_openCover (P := @Smooth.{u})
    (f := curveToBase K) (glueData K).openCover
  intro i
  cases i
  · change Smooth (ordinaryChartMap K ≫ curveToBase K)
    rw [ordinaryChartMap_curveToBase]
    exact ordinaryChartToBase_smooth K
  · change Smooth (reciprocalChartMap K ≫ curveToBase K)
    rw [reciprocalChartMap_curveToBase]
    exact reciprocalChartToBase_smooth K

end MazurTorsion.XOneThirteenProjectiveCurve

#print axioms MazurTorsion.XOneThirteenProjectiveCurve.curveToBase_smooth

/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Design boundary: actual relative-dimension-one smoothness of the unchanged
order-thirteen glued curve. Named downstream consumer: the official FLT
smooth-proper-curve scheme-to-genus comparison. No genus assertion is assumed.
-/

noncomputable section
open Polynomial _root_.AlgebraicGeometry CategoryTheory
namespace MazurTorsion.XOneThirteenProjectiveCurve
universe u
variable (K : Type u) [Field K] [CharZero K]

theorem ordinaryCoordinateRing_kaehler_equiv :
    Nonempty (Ω[XOneThirteenAffineCurve.CoordinateRing K⁄K] ≃ₗ[
      XOneThirteenAffineCurve.CoordinateRing K] XOneThirteenAffineCurve.CoordinateRing K) :=
  MazurTransfer.HyperellipticCoordinateDifferentials.kaehler_equiv K
    (XOneThirteenAffineCurve.sexticPolynomial K)
    (XOneThirteenAffineCurve.sexticPolynomial_separable K) (by norm_num)

theorem reciprocalRing_kaehler_equiv :
    Nonempty (Ω[ReciprocalRing K⁄K] ≃ₗ[ReciprocalRing K] ReciprocalRing K) :=
  MazurTransfer.HyperellipticCoordinateDifferentials.kaehler_equiv K
    (reciprocalPolynomial K) (reciprocalPolynomial_separable K) (by norm_num)

theorem ordinaryChartToBase_smooth_relativeDimension_one :
    SmoothOfRelativeDimension 1 (ordinaryChartToBase K) := by
  have : IsDomain (XOneThirteenAffineCurve.CoordinateRing K) :=
    XOneThirteenAffineCurve.coordinateRing_isDomain K
  have : Algebra.Smooth K (XOneThirteenAffineCurve.CoordinateRing K) :=
    ordinaryCoordinateRing_smooth K
  unfold ordinaryChartToBase
  rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)]
  exact MazurTransfer.locally_standardSmooth_relativeDimension_one_of_kaehler_equiv K
    (XOneThirteenAffineCurve.CoordinateRing K) (ordinaryCoordinateRing_kaehler_equiv K)

theorem reciprocalChartToBase_smooth_relativeDimension_one :
    SmoothOfRelativeDimension 1 (reciprocalChartToBase K) := by
  have : IsDomain (ReciprocalRing K) := reciprocalRing_isDomain K
  have : Algebra.Smooth K (ReciprocalRing K) := reciprocalRing_smooth K
  unfold reciprocalChartToBase
  rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)]
  exact MazurTransfer.locally_standardSmooth_relativeDimension_one_of_kaehler_equiv K
    (ReciprocalRing K) (reciprocalRing_kaehler_equiv K)

theorem curveToBase_smooth_relativeDimension_one :
    SmoothOfRelativeDimension 1 (curveToBase K) := by
  haveI : IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{u} 1) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
      (P := @SmoothOfRelativeDimension.{u} 1)
      (Q := @RingHom.Locally.{u}
        (@RingHom.IsStandardSmoothOfRelativeDimension.{u,u} 1))
  apply IsZariskiLocalAtSource.of_openCover (P := @SmoothOfRelativeDimension.{u} 1)
    (f := curveToBase K) (glueData K).openCover
  intro i
  cases i
  · change SmoothOfRelativeDimension 1 (ordinaryChartMap K ≫ curveToBase K)
    rw [ordinaryChartMap_curveToBase]
    exact ordinaryChartToBase_smooth_relativeDimension_one K
  · change SmoothOfRelativeDimension 1 (reciprocalChartMap K ≫ curveToBase K)
    rw [reciprocalChartMap_curveToBase]
    exact reciprocalChartToBase_smooth_relativeDimension_one K

end MazurTorsion.XOneThirteenProjectiveCurve
#print axioms MazurTorsion.XOneThirteenProjectiveCurve.ordinaryCoordinateRing_kaehler_equiv
#print axioms MazurTorsion.XOneThirteenProjectiveCurve.reciprocalRing_kaehler_equiv
#print axioms MazurTorsion.XOneThirteenProjectiveCurve.curveToBase_smooth_relativeDimension_one


theorem solution (K : Type*) [Field K] [CharZero K] :
    let f : Polynomial K := Polynomial.X ^ 6 + 2 * Polynomial.X ^ 5 +
      Polynomial.X ^ 4 + 2 * Polynomial.X ^ 3 + 6 * Polynomial.X ^ 2 +
      4 * Polynomial.X + 1
    let A := AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C f)
    AlgebraicGeometry.SmoothOfRelativeDimension 1
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap K A))) := by
  exact MazurTorsion.XOneThirteenProjectiveCurve.ordinaryChartToBase_smooth_relativeDimension_one K

#print axioms solution
