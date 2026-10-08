-- Prove2me | solution 1 for MazurTransfer.order13_actual_affine_scheme_smooth
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T20:46:44.31316+00:00
-- url     : https://prove2.me/submissions/5b64756b-9d83-4416-bc51-bd37e0f923a2

import Mathlib
import Theorems.Thm_MazurTransfer_hyperelliptic_coordinate_smooth

/- Whole mathematical module, with header imports supplied above or by preceding modules. -/
section
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

end

/- Whole mathematical module, with header imports supplied above or by preceding modules. -/
section
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

end
end

/- Whole mathematical module, with header imports supplied above or by preceding modules. -/
section
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

end
end

/- Whole mathematical module, with header imports supplied above or by preceding modules. -/
section
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

end
end

/- Whole mathematical module, with header imports supplied above or by preceding modules. -/
section
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

end
end

theorem solution (K : Type*) [Field K] [CharZero K] :
    _root_.AlgebraicGeometry.Smooth
      (_root_.AlgebraicGeometry.Spec.map (CommRingCat.ofHom
        (algebraMap K (AdjoinRoot
        ((Polynomial.X ^ 2 - Polynomial.C
          ((Polynomial.X : Polynomial K) ^ 6 + 2 * Polynomial.X ^ 5 +
            Polynomial.X ^ 4 + 2 * Polynomial.X ^ 3 + 6 * Polynomial.X ^ 2 +
            4 * Polynomial.X + 1)) : Polynomial (Polynomial K)))))) := by
  exact MazurTorsion.XOneThirteenProjectiveCurve.ordinaryChartToBase_smooth K
