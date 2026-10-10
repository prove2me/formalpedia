-- Prove2me | solution 1 for MazurTransfer.order13_actual_whole_curve_base_change_isomorphism
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-10T02:03:37.324274+00:00
-- url     : https://prove2.me/submissions/05e8a0e7-e373-41bc-ba69-639c44991e72

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: an actual whole glued-curve base-change isomorphism with
literal scalar and coordinate preservation on both charts. Named downstream
consumer: compatible integral curve and Picard families for torsion reduction.
No model, fibre identification, properness, or Picard family is assumed.
-/
import Mathlib
import Definitions.Def_MazurTransfer_Order13ExplicitCurve


section
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Literal curve: MazurTheorem at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c.
Design boundary: actual base-change algebra isomorphisms for both quadratic
coordinate charts. No identification of the glued scheme is assumed.
Named downstream consumer: constructing and identifying the rational and
finite-field fibres of the actual integral order-thirteen curve.
-/

noncomputable section
namespace MazurTransfer.Order13CoordinateBaseChange
open Polynomial Algebra TensorProduct
universe u v
variable (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]

def quadraticCoordinateRingEquiv (f : Polynomial R) :
    S ⊗[R] AdjoinRoot (X ^ 2 - C f) ≃ₐ[S]
      AdjoinRoot (X ^ 2 - C (f.map (algebraMap R S))) := by
  let p : Polynomial (Polynomial R) := X ^ 2 - C f
  let q : Polynomial (S ⊗[R] Polynomial R) :=
    p.map Algebra.TensorProduct.includeRight.toRingHom
  let e : S ⊗[R] Polynomial R ≃ₐ[S] Polynomial S :=
    (polyEquivTensor' R S).symm
  have hq : q.map e = X ^ 2 - C (f.map (algebraMap R S)) := by
    simp [q, p, e, Polynomial.map_sub, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_C,
      polyEquivTensor_symm_apply_tmul_eq_smul]
  exact (AdjoinRoot.tensorAlgEquiv p q rfl).trans
    (AdjoinRoot.mapAlgEquiv e q _ (hq ▸ Associated.refl _))

theorem sexticPolynomial_map :
    (MazurTorsion.XOneThirteenAffineCurve.sexticPolynomial R).map (algebraMap R S) =
      MazurTorsion.XOneThirteenAffineCurve.sexticPolynomial S := by
  simp [MazurTorsion.XOneThirteenAffineCurve.sexticPolynomial]

theorem reciprocalPolynomial_map :
    (MazurTorsion.XOneThirteenProjectiveCurve.reciprocalPolynomial R).map (algebraMap R S) =
      MazurTorsion.XOneThirteenProjectiveCurve.reciprocalPolynomial S := by
  simp [MazurTorsion.XOneThirteenProjectiveCurve.reciprocalPolynomial]

def ordinaryCoordinateRingEquiv :
    S ⊗[R] MazurTorsion.XOneThirteenAffineCurve.CoordinateRing R ≃ₐ[S]
      MazurTorsion.XOneThirteenAffineCurve.CoordinateRing S := by
  exact (quadraticCoordinateRingEquiv R S
      (MazurTorsion.XOneThirteenAffineCurve.sexticPolynomial R)).trans
    (AdjoinRoot.algEquivOfEq S _ (MazurTorsion.XOneThirteenAffineCurve.affineEquation S)
      (by rw [sexticPolynomial_map R S]; rfl))

def reciprocalCoordinateRingEquiv :
    S ⊗[R] MazurTorsion.XOneThirteenProjectiveCurve.ReciprocalRing R ≃ₐ[S]
      MazurTorsion.XOneThirteenProjectiveCurve.ReciprocalRing S := by
  exact (quadraticCoordinateRingEquiv R S
      (MazurTorsion.XOneThirteenProjectiveCurve.reciprocalPolynomial R)).trans
    (AdjoinRoot.algEquivOfEq S _ (MazurTorsion.XOneThirteenProjectiveCurve.reciprocalEquation S)
      (by rw [reciprocalPolynomial_map R S]; rfl))

end MazurTransfer.Order13CoordinateBaseChange

#print axioms MazurTransfer.Order13CoordinateBaseChange.quadraticCoordinateRingEquiv
#print axioms MazurTransfer.Order13CoordinateBaseChange.ordinaryCoordinateRingEquiv
#print axioms MazurTransfer.Order13CoordinateBaseChange.reciprocalCoordinateRingEquiv

end
end

section
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual quadratic chart base-change isomorphisms preserve
the abscissa and ordinate generators. Named downstream consumer: checking
compatibility with the literal reciprocal localization transition when
identifying the glued integral curve's rational and finite-field fibres.
-/

noncomputable section
namespace MazurTransfer.Order13CoordinateBaseChange
open Polynomial Algebra TensorProduct
universe u v
variable (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]

theorem quadraticCoordinateRingEquiv_root (f : Polynomial R) :
    quadraticCoordinateRingEquiv R S f (1 ⊗ₜ[R] AdjoinRoot.root (X ^ 2 - C f)) =
      AdjoinRoot.root (X ^ 2 - C (f.map (algebraMap R S))) := by
  unfold quadraticCoordinateRingEquiv
  rw [AlgEquiv.trans_apply, AdjoinRoot.tensorAlgEquiv_root]
  rw [AdjoinRoot.coe_mapAlgEquiv, AdjoinRoot.map_root]

theorem quadraticCoordinateRingEquiv_of (f p : Polynomial R) :
    quadraticCoordinateRingEquiv R S f (1 ⊗ₜ[R] AdjoinRoot.of (X ^ 2 - C f) p) =
      AdjoinRoot.of (X ^ 2 - C (f.map (algebraMap R S))) (p.map (algebraMap R S)) := by
  unfold quadraticCoordinateRingEquiv
  rw [AlgEquiv.trans_apply, AdjoinRoot.tensorAlgEquiv_of]
  rw [AdjoinRoot.coe_mapAlgEquiv, AdjoinRoot.map_of]
  change AdjoinRoot.of (X ^ 2 - C (f.map (algebraMap R S)))
    ((polyEquivTensor R S).symm (1 ⊗ₜ[R] p)) = _
  apply congrArg (AdjoinRoot.of (X ^ 2 - C (f.map (algebraMap R S))))
  exact (polyEquivTensor_symm_apply_tmul_eq_smul R S 1 p).trans (one_smul S _)

theorem quadraticEquationEquiv_of (p q : Polynomial (Polynomial S))
    (h : p = q) (s : Polynomial S) :
    AdjoinRoot.algEquivOfEq S p q h (AdjoinRoot.of p s) = AdjoinRoot.of q s := by
  cases h
  simp [AdjoinRoot.algEquivOfEq, AdjoinRoot.algEquivOfAssociated,
    AdjoinRoot.mapAlgEquiv, AdjoinRoot.mapAlgHom, AdjoinRoot.map]

theorem ordinaryCoordinateRingEquiv_y :
    ordinaryCoordinateRingEquiv R S
      (1 ⊗ₜ[R] MazurTorsion.XOneThirteenAffineCurve.yCoordinate R) =
      MazurTorsion.XOneThirteenAffineCurve.yCoordinate S := by
  have h : (X ^ 2 - C ((MazurTorsion.XOneThirteenAffineCurve.sexticPolynomial R).map (algebraMap R S)) :
      Polynomial (Polynomial S)) = MazurTorsion.XOneThirteenAffineCurve.affineEquation S := by
    rw [sexticPolynomial_map R S]
    rfl
  change (AdjoinRoot.algEquivOfEq S _ (MazurTorsion.XOneThirteenAffineCurve.affineEquation S) h)
    (quadraticCoordinateRingEquiv R S (MazurTorsion.XOneThirteenAffineCurve.sexticPolynomial R)
      (1 ⊗ₜ[R] AdjoinRoot.root (X ^ 2 - C (MazurTorsion.XOneThirteenAffineCurve.sexticPolynomial R)))) =
    AdjoinRoot.root (MazurTorsion.XOneThirteenAffineCurve.affineEquation S)
  rw [quadraticCoordinateRingEquiv_root, AdjoinRoot.algEquivOfEq_root]

theorem ordinaryCoordinateRingEquiv_x :
    ordinaryCoordinateRingEquiv R S
      (1 ⊗ₜ[R] MazurTorsion.XOneThirteenAffineCurve.xCoordinate R) =
      MazurTorsion.XOneThirteenAffineCurve.xCoordinate S := by
  have h : (X ^ 2 - C ((MazurTorsion.XOneThirteenAffineCurve.sexticPolynomial R).map (algebraMap R S)) :
      Polynomial (Polynomial S)) = MazurTorsion.XOneThirteenAffineCurve.affineEquation S := by
    rw [sexticPolynomial_map R S]
    rfl
  change (AdjoinRoot.algEquivOfEq S _ (MazurTorsion.XOneThirteenAffineCurve.affineEquation S) h)
    (quadraticCoordinateRingEquiv R S (MazurTorsion.XOneThirteenAffineCurve.sexticPolynomial R)
      (1 ⊗ₜ[R] AdjoinRoot.of (X ^ 2 - C (MazurTorsion.XOneThirteenAffineCurve.sexticPolynomial R)) X)) =
    AdjoinRoot.of (MazurTorsion.XOneThirteenAffineCurve.affineEquation S) X
  rw [quadraticCoordinateRingEquiv_of, Polynomial.map_X, quadraticEquationEquiv_of]

theorem reciprocalCoordinateRingEquiv_w :
    reciprocalCoordinateRingEquiv R S
      (1 ⊗ₜ[R] MazurTorsion.XOneThirteenProjectiveCurve.wCoordinate R) =
      MazurTorsion.XOneThirteenProjectiveCurve.wCoordinate S := by
  have h : (X ^ 2 - C ((MazurTorsion.XOneThirteenProjectiveCurve.reciprocalPolynomial R).map (algebraMap R S)) :
      Polynomial (Polynomial S)) = MazurTorsion.XOneThirteenProjectiveCurve.reciprocalEquation S := by
    rw [reciprocalPolynomial_map R S]
    rfl
  change (AdjoinRoot.algEquivOfEq S _ (MazurTorsion.XOneThirteenProjectiveCurve.reciprocalEquation S) h)
    (quadraticCoordinateRingEquiv R S (MazurTorsion.XOneThirteenProjectiveCurve.reciprocalPolynomial R)
      (1 ⊗ₜ[R] AdjoinRoot.root (X ^ 2 - C (MazurTorsion.XOneThirteenProjectiveCurve.reciprocalPolynomial R)))) =
    AdjoinRoot.root (MazurTorsion.XOneThirteenProjectiveCurve.reciprocalEquation S)
  rw [quadraticCoordinateRingEquiv_root, AdjoinRoot.algEquivOfEq_root]

theorem reciprocalCoordinateRingEquiv_z :
    reciprocalCoordinateRingEquiv R S
      (1 ⊗ₜ[R] MazurTorsion.XOneThirteenProjectiveCurve.zCoordinate R) =
      MazurTorsion.XOneThirteenProjectiveCurve.zCoordinate S := by
  have h : (X ^ 2 - C ((MazurTorsion.XOneThirteenProjectiveCurve.reciprocalPolynomial R).map (algebraMap R S)) :
      Polynomial (Polynomial S)) = MazurTorsion.XOneThirteenProjectiveCurve.reciprocalEquation S := by
    rw [reciprocalPolynomial_map R S]
    rfl
  change (AdjoinRoot.algEquivOfEq S _ (MazurTorsion.XOneThirteenProjectiveCurve.reciprocalEquation S) h)
    (quadraticCoordinateRingEquiv R S (MazurTorsion.XOneThirteenProjectiveCurve.reciprocalPolynomial R)
      (1 ⊗ₜ[R] AdjoinRoot.of (X ^ 2 - C (MazurTorsion.XOneThirteenProjectiveCurve.reciprocalPolynomial R)) X)) =
    AdjoinRoot.of (MazurTorsion.XOneThirteenProjectiveCurve.reciprocalEquation S) X
  rw [quadraticCoordinateRingEquiv_of, Polynomial.map_X, quadraticEquationEquiv_of]

end MazurTransfer.Order13CoordinateBaseChange

#print axioms MazurTransfer.Order13CoordinateBaseChange.quadraticCoordinateRingEquiv_root
#print axioms MazurTransfer.Order13CoordinateBaseChange.quadraticCoordinateRingEquiv_of
#print axioms MazurTransfer.Order13CoordinateBaseChange.ordinaryCoordinateRingEquiv_x
#print axioms MazurTransfer.Order13CoordinateBaseChange.ordinaryCoordinateRingEquiv_y
#print axioms MazurTransfer.Order13CoordinateBaseChange.reciprocalCoordinateRingEquiv_z
#print axioms MazurTransfer.Order13CoordinateBaseChange.reciprocalCoordinateRingEquiv_w

end
end

section
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: actual change-of-base ring maps on the two quadratic
charts and their principal-open overlaps, preserving coordinates and
their distinguished inverses. Named downstream consumer: compatibility
of the order-thirteen gluing transition with arbitrary base change.
-/

noncomputable section
namespace MazurTransfer.Order13CoordinateBaseChange
open Polynomial Algebra TensorProduct
universe u v
variable (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
open MazurTorsion.XOneThirteenAffineCurve
open MazurTorsion.XOneThirteenProjectiveCurve

def ordinaryRingMap : CoordinateRing R →+* CoordinateRing S :=
  (ordinaryCoordinateRingEquiv R S).toRingHom.comp
    (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := CoordinateRing R)).toRingHom

def reciprocalRingMap : ReciprocalRing R →+* ReciprocalRing S :=
  (reciprocalCoordinateRingEquiv R S).toRingHom.comp
    (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := ReciprocalRing R)).toRingHom

theorem ordinaryRingMap_x : ordinaryRingMap R S (xCoordinate R) = xCoordinate S :=
  ordinaryCoordinateRingEquiv_x R S

theorem ordinaryRingMap_y : ordinaryRingMap R S (yCoordinate R) = yCoordinate S :=
  ordinaryCoordinateRingEquiv_y R S

theorem reciprocalRingMap_z : reciprocalRingMap R S (zCoordinate R) = zCoordinate S :=
  reciprocalCoordinateRingEquiv_z R S

theorem reciprocalRingMap_w : reciprocalRingMap R S (wCoordinate R) = wCoordinate S :=
  reciprocalCoordinateRingEquiv_w R S

theorem ordinaryRingMap_algebraMap (r : R) :
    ordinaryRingMap R S (algebraMap R (CoordinateRing R) r) =
      algebraMap S (CoordinateRing S) (algebraMap R S r) := by
  change ordinaryCoordinateRingEquiv R S (1 ⊗ₜ[R] algebraMap R (CoordinateRing R) r) = _
  rw [← Algebra.TensorProduct.algebraMap_apply',
    IsScalarTower.algebraMap_apply R S (S ⊗[R] CoordinateRing R)]
  exact (ordinaryCoordinateRingEquiv R S).commutes _

theorem reciprocalRingMap_algebraMap (r : R) :
    reciprocalRingMap R S (algebraMap R (ReciprocalRing R) r) =
      algebraMap S (ReciprocalRing S) (algebraMap R S r) := by
  change reciprocalCoordinateRingEquiv R S (1 ⊗ₜ[R] algebraMap R (ReciprocalRing R) r) = _
  rw [← Algebra.TensorProduct.algebraMap_apply',
    IsScalarTower.algebraMap_apply R S (S ⊗[R] ReciprocalRing R)]
  exact (reciprocalCoordinateRingEquiv R S).commutes _

def localizationAwayMap {A : Type*} [CommRing A] {B : Type*} [CommRing B]
    (f : A →+* B) (x : A) (y : B) (h : f x = y) :
    Localization.Away x →+* Localization.Away y :=
  IsLocalization.Away.lift x
    (g := (algebraMap B (Localization.Away y)).comp f)
    (by
      change IsUnit (algebraMap B (Localization.Away y) (f x))
      rw [h]
      exact IsLocalization.Away.algebraMap_isUnit y)

theorem localizationAwayMap_algebraMap {A : Type*} [CommRing A] {B : Type*} [CommRing B]
    (f : A →+* B) (x : A) (y : B) (h : f x = y) (a : A) :
    localizationAwayMap f x y h (algebraMap A (Localization.Away x) a) =
      algebraMap B (Localization.Away y) (f a) :=
  IsLocalization.Away.lift_eq x _ a

theorem localizationAwayMap_invSelf {A : Type*} [CommRing A] {B : Type*} [CommRing B]
    (f : A →+* B) (x : A) (y : B) (h : f x = y) :
    localizationAwayMap f x y h (IsLocalization.Away.invSelf x) =
      IsLocalization.Away.invSelf y := by
  have hu : IsUnit (algebraMap B (Localization.Away y) y) :=
    IsLocalization.Away.algebraMap_isUnit y
  apply hu.mul_right_inj.mp
  calc
    _ = localizationAwayMap f x y h
        (algebraMap A (Localization.Away x) x * IsLocalization.Away.invSelf x) := by
      rw [map_mul, localizationAwayMap_algebraMap, h]
    _ = 1 := by rw [IsLocalization.Away.mul_invSelf, map_one]
    _ = _ := (IsLocalization.Away.mul_invSelf y).symm

def ordinaryOverlapRingMap : OrdinaryOverlapRing R →+* OrdinaryOverlapRing S :=
  localizationAwayMap (ordinaryRingMap R S) (xCoordinate R) (xCoordinate S)
    (ordinaryRingMap_x R S)

def reciprocalOverlapRingMap : ReciprocalOverlapRing R →+* ReciprocalOverlapRing S :=
  localizationAwayMap (reciprocalRingMap R S) (zCoordinate R) (zCoordinate S)
    (reciprocalRingMap_z R S)

theorem ordinaryOverlapRingMap_algebraMap (a : CoordinateRing R) :
    ordinaryOverlapRingMap R S (algebraMap (CoordinateRing R) (OrdinaryOverlapRing R) a) =
      algebraMap (CoordinateRing S) (OrdinaryOverlapRing S) (ordinaryRingMap R S a) :=
  localizationAwayMap_algebraMap _ _ _ _ a

theorem reciprocalOverlapRingMap_algebraMap (a : ReciprocalRing R) :
    reciprocalOverlapRingMap R S (algebraMap (ReciprocalRing R) (ReciprocalOverlapRing R) a) =
      algebraMap (ReciprocalRing S) (ReciprocalOverlapRing S) (reciprocalRingMap R S a) :=
  localizationAwayMap_algebraMap _ _ _ _ a

theorem ordinaryOverlapRingMap_invSelf :
    ordinaryOverlapRingMap R S (IsLocalization.Away.invSelf (xCoordinate R)) =
      IsLocalization.Away.invSelf (xCoordinate S) :=
  localizationAwayMap_invSelf _ _ _ _

theorem reciprocalOverlapRingMap_invSelf :
    reciprocalOverlapRingMap R S (IsLocalization.Away.invSelf (zCoordinate R)) =
      IsLocalization.Away.invSelf (zCoordinate S) :=
  localizationAwayMap_invSelf _ _ _ _

end MazurTransfer.Order13CoordinateBaseChange

#print axioms MazurTransfer.Order13CoordinateBaseChange.ordinaryRingMap_x
#print axioms MazurTransfer.Order13CoordinateBaseChange.reciprocalRingMap_w
#print axioms MazurTransfer.Order13CoordinateBaseChange.localizationAwayMap_invSelf
#print axioms MazurTransfer.Order13CoordinateBaseChange.ordinaryOverlapRingMap_invSelf
#print axioms MazurTransfer.Order13CoordinateBaseChange.reciprocalOverlapRingMap_invSelf

end
end

section
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the literal reciprocal transition commutes with the actual
chart and localization change-of-base ring maps on the entire overlap rings.
Named downstream consumer: identification of the glued integral curve's
base-changed scheme with the literal order-thirteen curve over the new base.
This does not yet construct a glued scheme isomorphism or a Picard family.
-/

noncomputable section
namespace MazurTransfer.Order13CoordinateBaseChange
open Polynomial Algebra TensorProduct
universe u v
variable (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
open MazurTorsion.XOneThirteenAffineCurve
open MazurTorsion.XOneThirteenProjectiveCurve

theorem ordinaryOverlapRingMap_scalar (r : R) :
    ordinaryOverlapRingMap R S (algebraMap R (OrdinaryOverlapRing R) r) =
      algebraMap S (OrdinaryOverlapRing S) (algebraMap R S r) := by
  rw [IsScalarTower.algebraMap_apply R (CoordinateRing R) (OrdinaryOverlapRing R),
    ordinaryOverlapRingMap_algebraMap, ordinaryRingMap_algebraMap,
    ← IsScalarTower.algebraMap_apply S (CoordinateRing S) (OrdinaryOverlapRing S)]

theorem reciprocalOverlapRingMap_scalar (r : R) :
    reciprocalOverlapRingMap R S (algebraMap R (ReciprocalOverlapRing R) r) =
      algebraMap S (ReciprocalOverlapRing S) (algebraMap R S r) := by
  rw [IsScalarTower.algebraMap_apply R (ReciprocalRing R) (ReciprocalOverlapRing R),
    reciprocalOverlapRingMap_algebraMap, reciprocalRingMap_algebraMap,
    ← IsScalarTower.algebraMap_apply S (ReciprocalRing S) (ReciprocalOverlapRing S)]

theorem ordinaryTransition_x :
    ordinaryToReciprocal R
      (algebraMap (CoordinateRing R) (OrdinaryOverlapRing R) (xCoordinate R)) =
      IsLocalization.Away.invSelf (zCoordinate R) := by
  rw [ordinaryToReciprocal_algebraMap]
  exact ordinaryToReciprocalBase_x R

theorem ordinaryTransition_y :
    ordinaryToReciprocal R
      (algebraMap (CoordinateRing R) (OrdinaryOverlapRing R) (yCoordinate R)) =
      algebraMap (ReciprocalRing R) (ReciprocalOverlapRing R) (wCoordinate R) *
        IsLocalization.Away.invSelf (zCoordinate R) ^ 3 := by
  rw [ordinaryToReciprocal_algebraMap]
  exact ordinaryToReciprocalBase_y R

theorem ordinaryTransition_natural :
    (reciprocalOverlapRingMap R S).comp (ordinaryToReciprocal R).toRingHom =
      (ordinaryToReciprocal S).toRingHom.comp (ordinaryOverlapRingMap R S) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (xCoordinate R))
  apply AdjoinRoot.ringHom_ext
  · apply Polynomial.ringHom_ext
    · intro r
      change reciprocalOverlapRingMap R S
          (ordinaryToReciprocal R (algebraMap R (OrdinaryOverlapRing R) r)) =
        ordinaryToReciprocal S
          (ordinaryOverlapRingMap R S (algebraMap R (OrdinaryOverlapRing R) r))
      rw [(ordinaryToReciprocal R).commutes, reciprocalOverlapRingMap_scalar,
        ordinaryOverlapRingMap_scalar, (ordinaryToReciprocal S).commutes]
    · change reciprocalOverlapRingMap R S
          (ordinaryToReciprocal R
            (algebraMap (CoordinateRing R) (OrdinaryOverlapRing R) (xCoordinate R))) =
        ordinaryToReciprocal S
          (ordinaryOverlapRingMap R S
            (algebraMap (CoordinateRing R) (OrdinaryOverlapRing R) (xCoordinate R)))
      rw [ordinaryTransition_x, reciprocalOverlapRingMap_invSelf,
        ordinaryOverlapRingMap_algebraMap, ordinaryRingMap_x, ordinaryTransition_x]
  · change reciprocalOverlapRingMap R S
        (ordinaryToReciprocal R
          (algebraMap (CoordinateRing R) (OrdinaryOverlapRing R) (yCoordinate R))) =
      ordinaryToReciprocal S
        (ordinaryOverlapRingMap R S
          (algebraMap (CoordinateRing R) (OrdinaryOverlapRing R) (yCoordinate R)))
    rw [ordinaryTransition_y, map_mul, map_pow,
      reciprocalOverlapRingMap_algebraMap, reciprocalRingMap_w,
      reciprocalOverlapRingMap_invSelf, ordinaryOverlapRingMap_algebraMap,
      ordinaryRingMap_y, ordinaryTransition_y]

theorem ordinaryTransition_left_inverse (a : OrdinaryOverlapRing R) :
    reciprocalToOrdinary R (ordinaryToReciprocal R a) = a := by
  simpa only [AlgHom.comp_apply, AlgHom.id_apply] using
    DFunLike.congr_fun (reciprocalToOrdinary_comp_ordinaryToReciprocal R) a

theorem ordinaryTransition_right_inverse (a : ReciprocalOverlapRing R) :
    ordinaryToReciprocal R (reciprocalToOrdinary R a) = a := by
  simpa only [AlgHom.comp_apply, AlgHom.id_apply] using
    DFunLike.congr_fun (ordinaryToReciprocal_comp_reciprocalToOrdinary R) a

theorem reciprocalTransition_natural :
    (ordinaryOverlapRingMap R S).comp (reciprocalToOrdinary R).toRingHom =
      (reciprocalToOrdinary S).toRingHom.comp (reciprocalOverlapRingMap R S) := by
  ext a
  have h := DFunLike.congr_fun (ordinaryTransition_natural R S) (reciprocalToOrdinary R a)
  change reciprocalOverlapRingMap R S
      (ordinaryToReciprocal R (reciprocalToOrdinary R a)) =
    ordinaryToReciprocal S (ordinaryOverlapRingMap R S (reciprocalToOrdinary R a)) at h
  rw [ordinaryTransition_right_inverse] at h
  change ordinaryOverlapRingMap R S (reciprocalToOrdinary R a) =
    reciprocalToOrdinary S (reciprocalOverlapRingMap R S a)
  rw [h, ordinaryTransition_left_inverse]

end MazurTransfer.Order13CoordinateBaseChange

#print axioms MazurTransfer.Order13CoordinateBaseChange.ordinaryTransition_natural
#print axioms MazurTransfer.Order13CoordinateBaseChange.reciprocalTransition_natural

end
end

section
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: actual scheme isomorphisms from the base-changed ordinary
and reciprocal charts to the literal charts over the new base ring.
Named downstream consumer: gluing these affine fibre identifications along
the checked reciprocal transition to identify the actual entire curve family.
-/

noncomputable section
namespace MazurTransfer.Order13ChartSchemeBaseChange
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MazurTorsion.XOneThirteenAffineCurve
open MazurTorsion.XOneThirteenProjectiveCurve
universe u
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

def ordinaryChartIso :
    pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (ordinaryChartToBase R) ≅ MazurTorsion.XOneThirteenAffineCurve.scheme S :=
  (pullbackSpecIso R S (CoordinateRing R)).trans
    (Scheme.Spec.mapIso
      (Order13CoordinateBaseChange.ordinaryCoordinateRingEquiv R S).symm.toRingEquiv.toCommRingCatIso.op)

def reciprocalChartIso :
    pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (reciprocalChartToBase R) ≅ reciprocalScheme S :=
  (pullbackSpecIso R S (ReciprocalRing R)).trans
    (Scheme.Spec.mapIso
      (Order13CoordinateBaseChange.reciprocalCoordinateRingEquiv R S).symm.toRingEquiv.toCommRingCatIso.op)

theorem ordinaryChartIso_inv_fst :
    (ordinaryChartIso R S).inv ≫
      pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R S)))
        (ordinaryChartToBase R) = ordinaryChartToBase S := by
  change (Spec.map (CommRingCat.ofHom
      (Order13CoordinateBaseChange.ordinaryCoordinateRingEquiv R S).toRingHom) ≫
      (pullbackSpecIso R S (CoordinateRing R)).inv) ≫ pullback.fst _ _ = _
  rw [Category.assoc, pullbackSpecIso_inv_fst']
  unfold ordinaryChartToBase
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext s
  exact (Order13CoordinateBaseChange.ordinaryCoordinateRingEquiv R S).commutes s

theorem ordinaryChartIso_inv_snd :
    (ordinaryChartIso R S).inv ≫
      pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R S)))
        (ordinaryChartToBase R) =
      Spec.map (CommRingCat.ofHom (Order13CoordinateBaseChange.ordinaryRingMap R S)) := by
  change (Spec.map (CommRingCat.ofHom
      (Order13CoordinateBaseChange.ordinaryCoordinateRingEquiv R S).toRingHom) ≫
      (pullbackSpecIso R S (CoordinateRing R)).inv) ≫ pullback.snd _ _ = _
  rw [Category.assoc, pullbackSpecIso_inv_snd, ← Spec.map_comp]
  rfl

theorem reciprocalChartIso_inv_fst :
    (reciprocalChartIso R S).inv ≫
      pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R S)))
        (reciprocalChartToBase R) = reciprocalChartToBase S := by
  change (Spec.map (CommRingCat.ofHom
      (Order13CoordinateBaseChange.reciprocalCoordinateRingEquiv R S).toRingHom) ≫
      (pullbackSpecIso R S (ReciprocalRing R)).inv) ≫ pullback.fst _ _ = _
  rw [Category.assoc, pullbackSpecIso_inv_fst']
  unfold reciprocalChartToBase
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext s
  exact (Order13CoordinateBaseChange.reciprocalCoordinateRingEquiv R S).commutes s

theorem reciprocalChartIso_inv_snd :
    (reciprocalChartIso R S).inv ≫
      pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R S)))
        (reciprocalChartToBase R) =
      Spec.map (CommRingCat.ofHom (Order13CoordinateBaseChange.reciprocalRingMap R S)) := by
  change (Spec.map (CommRingCat.ofHom
      (Order13CoordinateBaseChange.reciprocalCoordinateRingEquiv R S).toRingHom) ≫
      (pullbackSpecIso R S (ReciprocalRing R)).inv) ≫ pullback.snd _ _ = _
  rw [Category.assoc, pullbackSpecIso_inv_snd, ← Spec.map_comp]
  rfl

end MazurTransfer.Order13ChartSchemeBaseChange

#print axioms MazurTransfer.Order13ChartSchemeBaseChange.ordinaryChartIso
#print axioms MazurTransfer.Order13ChartSchemeBaseChange.reciprocalChartIso
#print axioms MazurTransfer.Order13ChartSchemeBaseChange.ordinaryChartIso_inv_fst
#print axioms MazurTransfer.Order13ChartSchemeBaseChange.ordinaryChartIso_inv_snd
#print axioms MazurTransfer.Order13ChartSchemeBaseChange.reciprocalChartIso_inv_fst
#print axioms MazurTransfer.Order13ChartSchemeBaseChange.reciprocalChartIso_inv_snd

end
end

section
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Adapts the complete checked two-chart descent proof of MazurTheorem at
54d43d8dda8a6fcf069cc02a815f850d762c5c0c to an arbitrary target scheme.
Design boundary: the actual universal gluing morphism for compatible chart
maps. Named downstream consumer: the genuine change-of-base morphism of the
literal integral order-thirteen curve, with compatibility proved separately.
-/

noncomputable section
namespace MazurTransfer.Order13GluedCurveMaps
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MazurTorsion.XOneThirteenProjectiveCurve
universe u
variable (K : Type u) [CommRing K]

private theorem ordinary_ne_reciprocal : (Chart.ordinary : Chart.{u}) ≠ Chart.reciprocal := by
  intro h
  cases h

private theorem reciprocal_ne_ordinary : (Chart.reciprocal : Chart.{u}) ≠ Chart.ordinary := by
  intro h
  cases h

def desc {Y : Scheme.{u}} (δ : ∀ i : Chart.{u}, chartScheme K i ⟶ Y)
    (hδ : ∀ (i j : Chart.{u}) (h : i ≠ j),
      overlapInclusion K i j h ≫ δ i =
        overlapTransition K i j h ≫ overlapInclusion K j i h.symm ≫ δ j) :
    curveScheme K ⟶ Y := by
    letI := Scheme.GlueData.instHasMulticoequalizerDiagram (glueData K)
    exact Limits.Multicoequalizer.desc (glueData K).toGlueData.diagram
      Y δ (by
      rintro ⟨i, j⟩
      simp only [CategoryTheory.GlueData.diagram_fst,
        CategoryTheory.GlueData.diagram_snd]
      rcases i with (_ | _) <;> rcases j with (_ | _)
      · dsimp [glueData, categoricalGlueData,
          CategoryTheory.GlueData.ofGlueData',
          CategoryTheory.GlueData'.f',
          Limits.MultispanShape.prod]
        simp
      · dsimp [glueData, categoricalGlueData,
          CategoryTheory.GlueData.ofGlueData',
          CategoryTheory.GlueData'.f',
          ordinary_ne_reciprocal, reciprocal_ne_ordinary,
          Limits.MultispanShape.prod]
        simp only [dif_neg ordinary_ne_reciprocal,
          dif_neg reciprocal_ne_ordinary, Category.assoc]
        simp only [CategoryTheory.eqToHom_trans_assoc,
          CategoryTheory.eqToHom_refl, Category.id_comp]
        rw [CategoryTheory.cancel_epi]
        exact hδ _ _
          ordinary_ne_reciprocal
      · dsimp [glueData, categoricalGlueData,
          CategoryTheory.GlueData.ofGlueData',
          CategoryTheory.GlueData'.f',
          ordinary_ne_reciprocal, reciprocal_ne_ordinary,
          Limits.MultispanShape.prod]
        simp only [dif_neg ordinary_ne_reciprocal,
          dif_neg reciprocal_ne_ordinary, Category.assoc]
        simp only [CategoryTheory.eqToHom_trans_assoc,
          CategoryTheory.eqToHom_refl, Category.id_comp]
        rw [CategoryTheory.cancel_epi]
        exact hδ _ _
          reciprocal_ne_ordinary
      · dsimp [glueData, categoricalGlueData,
          CategoryTheory.GlueData.ofGlueData',
          CategoryTheory.GlueData'.f',
          Limits.MultispanShape.prod]
        simp)

theorem chartMap_desc {Y : Scheme.{u}} (δ : ∀ i : Chart.{u}, chartScheme K i ⟶ Y)
    (hδ : ∀ (i j : Chart.{u}) (h : i ≠ j),
      overlapInclusion K i j h ≫ δ i =
        overlapTransition K i j h ≫ overlapInclusion K j i h.symm ≫ δ j)
    (i : Chart.{u}) :
    (glueData K).ι i ≫ desc K δ hδ = δ i := by
  letI := Scheme.GlueData.instHasMulticoequalizerDiagram (glueData K)
  unfold desc
  apply Multicoequalizer.π_desc

end MazurTransfer.Order13GluedCurveMaps

#print axioms MazurTransfer.Order13GluedCurveMaps.desc
#print axioms MazurTransfer.Order13GluedCurveMaps.chartMap_desc

end
end

section
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual change-of-base morphism of the literal glued
order-thirteen curve, built from the checked coordinate and overlap maps.
Named downstream consumer: constructing the isomorphism from its base change
to the literal curve over the new ring. No such isomorphism is assumed.
-/

noncomputable section
namespace MazurTransfer.Order13ActualCurveBaseChange
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MazurTorsion.XOneThirteenAffineCurve
open MazurTorsion.XOneThirteenProjectiveCurve
open MazurTransfer.Order13CoordinateBaseChange
universe u
variable (K : Type u) [CommRing K]

theorem ordinary_reciprocal_glue :
    Spec.map (CommRingCat.ofHom (algebraMap (CoordinateRing K) (OrdinaryOverlapRing K))) ≫
      ordinaryChartMap K =
    Spec.map (CommRingCat.ofHom (reciprocalToOrdinary K).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (ReciprocalRing K) (ReciprocalOverlapRing K))) ≫
        reciprocalChartMap K := by
  letI := Scheme.GlueData.instHasMulticoequalizerDiagram (glueData K)
  have hor : (Chart.ordinary : Chart.{u}) ≠ Chart.reciprocal := by intro h; cases h
  have hro : (Chart.reciprocal : Chart.{u}) ≠ Chart.ordinary := hor.symm
  have H := Scheme.GlueData.glue_condition (glueData K) Chart.ordinary Chart.reciprocal
  dsimp [glueData, categoricalGlueData, CategoryTheory.GlueData.ofGlueData',
    CategoryTheory.GlueData'.f', ordinaryChartMap, reciprocalChartMap] at H
  simp only [dif_neg hor, dif_neg hro, Category.assoc,
    CategoryTheory.eqToHom_trans_assoc, CategoryTheory.eqToHom_refl, Category.id_comp] at H
  rw [CategoryTheory.cancel_epi] at H
  exact H.symm

theorem reciprocal_ordinary_glue :
    Spec.map (CommRingCat.ofHom (algebraMap (ReciprocalRing K) (ReciprocalOverlapRing K))) ≫
      reciprocalChartMap K =
    Spec.map (CommRingCat.ofHom (ordinaryToReciprocal K).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (CoordinateRing K) (OrdinaryOverlapRing K))) ≫
        ordinaryChartMap K := by
  have H := congrArg (fun f => (overlapSchemeIso K).inv ≫ f) (ordinary_reciprocal_glue K)
  rw [← overlapSchemeIso_hom K] at H
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp] at H
  exact H.symm

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

@[reassoc]
theorem ordinary_inclusion_natural :
    Spec.map (CommRingCat.ofHom (ordinaryOverlapRingMap R S)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (CoordinateRing R) (OrdinaryOverlapRing R))) =
    Spec.map (CommRingCat.ofHom (algebraMap (CoordinateRing S) (OrdinaryOverlapRing S))) ≫
      Spec.map (CommRingCat.ofHom (ordinaryRingMap R S)) := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact ordinaryOverlapRingMap_algebraMap R S a

@[reassoc]
theorem reciprocal_inclusion_natural :
    Spec.map (CommRingCat.ofHom (reciprocalOverlapRingMap R S)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (ReciprocalRing R) (ReciprocalOverlapRing R))) =
    Spec.map (CommRingCat.ofHom (algebraMap (ReciprocalRing S) (ReciprocalOverlapRing S))) ≫
      Spec.map (CommRingCat.ofHom (reciprocalRingMap R S)) := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact reciprocalOverlapRingMap_algebraMap R S a

theorem ordinary_transition_natural :
    Spec.map (CommRingCat.ofHom (ordinaryOverlapRingMap R S)) ≫
      Spec.map (CommRingCat.ofHom (reciprocalToOrdinary R).toRingHom) =
    Spec.map (CommRingCat.ofHom (reciprocalToOrdinary S).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (reciprocalOverlapRingMap R S)) := by
  have H := congrArg (fun f : ReciprocalOverlapRing R →+* OrdinaryOverlapRing S =>
    Spec.map (CommRingCat.ofHom f)) (reciprocalTransition_natural R S)
  exact (Spec.map_comp (CommRingCat.ofHom (reciprocalToOrdinary R).toRingHom)
    (CommRingCat.ofHom (ordinaryOverlapRingMap R S))).symm.trans
    (H.trans (Spec.map_comp (CommRingCat.ofHom (reciprocalOverlapRingMap R S))
      (CommRingCat.ofHom (reciprocalToOrdinary S).toRingHom)))

theorem reciprocal_transition_natural :
    Spec.map (CommRingCat.ofHom (reciprocalOverlapRingMap R S)) ≫
      Spec.map (CommRingCat.ofHom (ordinaryToReciprocal R).toRingHom) =
    Spec.map (CommRingCat.ofHom (ordinaryToReciprocal S).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (ordinaryOverlapRingMap R S)) := by
  have H := congrArg (fun f : OrdinaryOverlapRing R →+* ReciprocalOverlapRing S =>
    Spec.map (CommRingCat.ofHom f)) (ordinaryTransition_natural R S)
  exact (Spec.map_comp (CommRingCat.ofHom (ordinaryToReciprocal R).toRingHom)
    (CommRingCat.ofHom (reciprocalOverlapRingMap R S))).symm.trans
    (H.trans (Spec.map_comp (CommRingCat.ofHom (ordinaryOverlapRingMap R S))
      (CommRingCat.ofHom (ordinaryToReciprocal S).toRingHom)))

def chartMapToOriginal : ∀ i : Chart.{u}, chartScheme S i ⟶ curveScheme R
  | .ordinary => Spec.map (CommRingCat.ofHom (ordinaryRingMap R S)) ≫ ordinaryChartMap R
  | .reciprocal => Spec.map (CommRingCat.ofHom (reciprocalRingMap R S)) ≫ reciprocalChartMap R

theorem chartMapToOriginal_compatible (i j : Chart.{u}) (h : i ≠ j) :
    overlapInclusion S i j h ≫ chartMapToOriginal R S i =
      overlapTransition S i j h ≫ overlapInclusion S j i h.symm ≫ chartMapToOriginal R S j := by
  cases i <;> cases j
  · exact (h rfl).elim
  · change Spec.map (CommRingCat.ofHom (algebraMap (CoordinateRing S) (OrdinaryOverlapRing S))) ≫
        Spec.map (CommRingCat.ofHom (ordinaryRingMap R S)) ≫ ordinaryChartMap R = _
    rw [← ordinary_inclusion_natural_assoc, ordinary_reciprocal_glue,
      ← Category.assoc, ordinary_transition_natural, Category.assoc,
      reciprocal_inclusion_natural_assoc]
    rfl
  · change Spec.map (CommRingCat.ofHom (algebraMap (ReciprocalRing S) (ReciprocalOverlapRing S))) ≫
        Spec.map (CommRingCat.ofHom (reciprocalRingMap R S)) ≫ reciprocalChartMap R = _
    rw [← reciprocal_inclusion_natural_assoc, reciprocal_ordinary_glue,
      ← Category.assoc, reciprocal_transition_natural, Category.assoc,
      ordinary_inclusion_natural_assoc]
    rfl
  · exact (h rfl).elim

def curveMap : curveScheme S ⟶ curveScheme R :=
  Order13GluedCurveMaps.desc S (chartMapToOriginal R S) (chartMapToOriginal_compatible R S)

@[reassoc]
theorem ordinaryChartMap_curveMap :
    ordinaryChartMap S ≫ curveMap R S =
      Spec.map (CommRingCat.ofHom (ordinaryRingMap R S)) ≫ ordinaryChartMap R :=
  Order13GluedCurveMaps.chartMap_desc S (chartMapToOriginal R S)
    (chartMapToOriginal_compatible R S) Chart.ordinary

@[reassoc]
theorem reciprocalChartMap_curveMap :
    reciprocalChartMap S ≫ curveMap R S =
      Spec.map (CommRingCat.ofHom (reciprocalRingMap R S)) ≫ reciprocalChartMap R :=
  Order13GluedCurveMaps.chartMap_desc S (chartMapToOriginal R S)
    (chartMapToOriginal_compatible R S) Chart.reciprocal

end MazurTransfer.Order13ActualCurveBaseChange

#print axioms MazurTransfer.Order13ActualCurveBaseChange.ordinary_reciprocal_glue
#print axioms MazurTransfer.Order13ActualCurveBaseChange.curveMap
#print axioms MazurTransfer.Order13ActualCurveBaseChange.ordinaryChartMap_curveMap
#print axioms MazurTransfer.Order13ActualCurveBaseChange.reciprocalChartMap_curveMap

end
end

section
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: base compatibility and the actual canonical morphism from
our literal order-thirteen curve to the fibre product of the original curve.
Named downstream consumer: the whole glued-curve base-change isomorphism.
No isomorphism, properness, or compatibility hypothesis is supplied.
-/

noncomputable section
namespace MazurTransfer.Order13ActualCurveBaseChange
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MazurTorsion.XOneThirteenAffineCurve
open MazurTorsion.XOneThirteenProjectiveCurve
open MazurTransfer.Order13CoordinateBaseChange
universe u
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

theorem ordinary_base_natural :
    Spec.map (CommRingCat.ofHom (ordinaryRingMap R S)) ≫ ordinaryChartToBase R =
      ordinaryChartToBase S ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
  change Spec.map (CommRingCat.ofHom (ordinaryRingMap R S)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (CoordinateRing R))) =
    Spec.map (CommRingCat.ofHom (algebraMap S (CoordinateRing S))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R S))
  have h : (ordinaryRingMap R S).comp (algebraMap R (CoordinateRing R)) =
      (algebraMap S (CoordinateRing S)).comp (algebraMap R S) :=
    RingHom.ext (ordinaryRingMap_algebraMap R S)
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext h)

theorem reciprocal_base_natural :
    Spec.map (CommRingCat.ofHom (reciprocalRingMap R S)) ≫ reciprocalChartToBase R =
      reciprocalChartToBase S ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
  change Spec.map (CommRingCat.ofHom (reciprocalRingMap R S)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (ReciprocalRing R))) =
    Spec.map (CommRingCat.ofHom (algebraMap S (ReciprocalRing S))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R S))
  have h : (reciprocalRingMap R S).comp (algebraMap R (ReciprocalRing R)) =
      (algebraMap S (ReciprocalRing S)).comp (algebraMap R S) :=
    RingHom.ext (reciprocalRingMap_algebraMap R S)
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext h)

theorem curveMap_base :
    curveMap R S ≫ curveToBase R =
      curveToBase S ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
  letI := Scheme.GlueData.instHasMulticoequalizerDiagram (glueData S)
  apply (glueData S).openCover.hom_ext
  intro i
  cases i
  · change ordinaryChartMap S ≫ (curveMap R S ≫ curveToBase R) =
      ordinaryChartMap S ≫ (curveToBase S ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)))
    rw [ordinaryChartMap_curveMap_assoc, ordinaryChartMap_curveToBase,
      ← Category.assoc, ordinaryChartMap_curveToBase]
    exact ordinary_base_natural R S
  · change reciprocalChartMap S ≫ (curveMap R S ≫ curveToBase R) =
      reciprocalChartMap S ≫ (curveToBase S ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)))
    rw [reciprocalChartMap_curveMap_assoc, reciprocalChartMap_curveToBase,
      ← Category.assoc, reciprocalChartMap_curveToBase]
    exact reciprocal_base_natural R S

def curveBaseChangeLift : curveScheme S ⟶
    pullback (Spec.map (CommRingCat.ofHom (algebraMap R S))) (curveToBase R) :=
  pullback.lift (curveToBase S) (curveMap R S) (curveMap_base R S).symm

@[reassoc]
theorem curveBaseChangeLift_fst :
    curveBaseChangeLift R S ≫ pullback.fst _ _ = curveToBase S :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem curveBaseChangeLift_snd :
    curveBaseChangeLift R S ≫ pullback.snd _ _ = curveMap R S :=
  pullback.lift_snd _ _ _

end MazurTransfer.Order13ActualCurveBaseChange

#print axioms MazurTransfer.Order13ActualCurveBaseChange.curveMap_base
#print axioms MazurTransfer.Order13ActualCurveBaseChange.curveBaseChangeLift
#print axioms MazurTransfer.Order13ActualCurveBaseChange.curveBaseChangeLift_fst
#print axioms MazurTransfer.Order13ActualCurveBaseChange.curveBaseChangeLift_snd

end
end

section
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: both actual localized-chart change-of-base squares are
scheme-theoretic pullbacks. Named downstream consumer: cartesianity of the
chart inclusions in the actual whole glued curve change-of-base map.
-/

noncomputable section
namespace MazurTransfer.Order13ActualCurveBaseChange
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MazurTorsion.XOneThirteenAffineCurve
open MazurTorsion.XOneThirteenProjectiveCurve
open MazurTransfer.Order13CoordinateBaseChange
universe u
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

theorem ordinaryOverlap_isPullback :
    IsPullback (Spec.map (CommRingCat.ofHom (ordinaryOverlapRingMap R S)))
      (Spec.map (CommRingCat.ofHom (algebraMap (CoordinateRing S) (OrdinaryOverlapRing S))))
      (Spec.map (CommRingCat.ofHom (algebraMap (CoordinateRing R) (OrdinaryOverlapRing R))))
      (Spec.map (CommRingCat.ofHom (ordinaryRingMap R S))) := by
  letI : IsLocalization ((Submonoid.powers (xCoordinate R)).map (ordinaryRingMap R S))
      (OrdinaryOverlapRing S) := by
    rw [Submonoid.map_powers, ordinaryRingMap_x]
    infer_instance
  have h : (ordinaryOverlapRingMap R S).comp
      (algebraMap (CoordinateRing R) (OrdinaryOverlapRing R)) =
      (algebraMap (CoordinateRing S) (OrdinaryOverlapRing S)).comp (ordinaryRingMap R S) :=
    RingHom.ext (ordinaryOverlapRingMap_algebraMap R S)
  exact (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_of_isLocalization (ordinaryRingMap R S)
      (ordinaryOverlapRingMap R S) h (Submonoid.powers (xCoordinate R)))).flip

theorem reciprocalOverlap_isPullback :
    IsPullback (Spec.map (CommRingCat.ofHom (reciprocalOverlapRingMap R S)))
      (Spec.map (CommRingCat.ofHom (algebraMap (ReciprocalRing S) (ReciprocalOverlapRing S))))
      (Spec.map (CommRingCat.ofHom (algebraMap (ReciprocalRing R) (ReciprocalOverlapRing R))))
      (Spec.map (CommRingCat.ofHom (reciprocalRingMap R S))) := by
  letI : IsLocalization ((Submonoid.powers (zCoordinate R)).map (reciprocalRingMap R S))
      (ReciprocalOverlapRing S) := by
    rw [Submonoid.map_powers, reciprocalRingMap_z]
    infer_instance
  have h : (reciprocalOverlapRingMap R S).comp
      (algebraMap (ReciprocalRing R) (ReciprocalOverlapRing R)) =
      (algebraMap (ReciprocalRing S) (ReciprocalOverlapRing S)).comp (reciprocalRingMap R S) :=
    RingHom.ext (reciprocalOverlapRingMap_algebraMap R S)
  exact (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_of_isLocalization (reciprocalRingMap R S)
      (reciprocalOverlapRingMap R S) h (Submonoid.powers (zCoordinate R)))).flip

end MazurTransfer.Order13ActualCurveBaseChange

#print axioms MazurTransfer.Order13ActualCurveBaseChange.ordinaryOverlap_isPullback
#print axioms MazurTransfer.Order13ActualCurveBaseChange.reciprocalOverlap_isPullback

end
end

section
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: identify the literal localized overlap as the actual
intersection of the two affine charts in our glued curve.
Named downstream consumer: cartesianity and whole-curve base-change.
-/

noncomputable section
namespace MazurTransfer.Order13ActualCurveBaseChange
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MazurTorsion.XOneThirteenAffineCurve
open MazurTorsion.XOneThirteenProjectiveCurve
universe u
variable (K : Type u) [CommRing K]

theorem ordinary_reciprocal_intersection :
    IsPullback
      (Spec.map (CommRingCat.ofHom (algebraMap (CoordinateRing K) (OrdinaryOverlapRing K))))
      (Spec.map (CommRingCat.ofHom (reciprocalToOrdinary K).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (ReciprocalRing K) (ReciprocalOverlapRing K))))
      (ordinaryChartMap K) (reciprocalChartMap K) := by
  classical
  letI := Scheme.GlueData.instHasMulticoequalizerDiagram (glueData K)
  have hor : (Chart.ordinary : Chart.{u}) ≠ Chart.reciprocal := by intro h; cases h
  have hro : (Chart.reciprocal : Chart.{u}) ≠ Chart.ordinary := hor.symm
  have comm : CommSq
      (Spec.map (CommRingCat.ofHom (algebraMap (CoordinateRing K) (OrdinaryOverlapRing K))))
      (Spec.map (CommRingCat.ofHom (reciprocalToOrdinary K).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (ReciprocalRing K) (ReciprocalOverlapRing K))))
      (ordinaryChartMap K) (reciprocalChartMap K) :=
    ⟨by simpa only [Category.assoc] using ordinary_reciprocal_glue K⟩
  have hpt : (glueData K).V ⟨Chart.ordinary, Chart.reciprocal⟩ =
      Spec (CommRingCat.of (OrdinaryOverlapRing K)) := by
    dsimp only [glueData, categoricalGlueData, CategoryTheory.GlueData.ofGlueData']
    exact dif_neg hor
  apply IsPullback.of_isLimit' comm
  refine IsLimit.ofIsoLimit
    ((glueData K).vPullbackConeIsLimit Chart.ordinary Chart.reciprocal) ?_
  refine PullbackCone.ext (eqToIso hpt) ?_ ?_
  · change (glueData K).f Chart.ordinary Chart.reciprocal =
        (eqToIso hpt).hom ≫
          Spec.map (CommRingCat.ofHom (algebraMap (CoordinateRing K) (OrdinaryOverlapRing K)))
    dsimp only [glueData, categoricalGlueData,
      CategoryTheory.GlueData.ofGlueData', CategoryTheory.GlueData'.f']
    simp only [dif_neg hor]
    rfl
  · change (glueData K).t Chart.ordinary Chart.reciprocal ≫
        (glueData K).f Chart.reciprocal Chart.ordinary =
      (eqToIso hpt).hom ≫
        (Spec.map (CommRingCat.ofHom (reciprocalToOrdinary K).toRingHom) ≫
          Spec.map (CommRingCat.ofHom (algebraMap (ReciprocalRing K) (ReciprocalOverlapRing K))))
    dsimp only [glueData, categoricalGlueData,
      CategoryTheory.GlueData.ofGlueData', CategoryTheory.GlueData'.f']
    simp only [dif_neg hor, dif_neg hro, Category.assoc,
      eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rfl

theorem reciprocal_ordinary_intersection :
    IsPullback
      (Spec.map (CommRingCat.ofHom (algebraMap (ReciprocalRing K) (ReciprocalOverlapRing K))))
      (Spec.map (CommRingCat.ofHom (ordinaryToReciprocal K).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (CoordinateRing K) (OrdinaryOverlapRing K))))
      (reciprocalChartMap K) (ordinaryChartMap K) := by
  apply (ordinary_reciprocal_intersection K).flip.of_iso'
    (overlapSchemeIso K).symm (Iso.refl (reciprocalScheme K))
    (Iso.refl (MazurTorsion.XOneThirteenAffineCurve.scheme K)) (Iso.refl (curveScheme K))
  · simp only [Iso.symm_hom, Iso.refl_hom, Category.comp_id]
    rw [← overlapSchemeIso_hom, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  · simp only [Iso.symm_hom, overlapSchemeIso_inv, Iso.refl_hom, Category.comp_id]
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]

end MazurTransfer.Order13ActualCurveBaseChange
#print axioms MazurTransfer.Order13ActualCurveBaseChange.ordinary_reciprocal_intersection

#print axioms MazurTransfer.Order13ActualCurveBaseChange.reciprocal_ordinary_intersection

end
end

section
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual overlap pullbacks also viewed in the opposite
chart coordinates. Named downstream consumer: the full glued curve chart
preimage identification, before whole-curve base-change.
-/

noncomputable section
namespace MazurTransfer.Order13ActualCurveBaseChange
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MazurTorsion.XOneThirteenAffineCurve
open MazurTorsion.XOneThirteenProjectiveCurve
open MazurTransfer.Order13CoordinateBaseChange
universe u
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

theorem ordinaryOverlapOverReciprocal_isPullback :
    IsPullback (Spec.map (CommRingCat.ofHom (ordinaryOverlapRingMap R S)))
      (Spec.map (CommRingCat.ofHom (reciprocalToOrdinary S).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (ReciprocalRing S) (ReciprocalOverlapRing S))))
      (Spec.map (CommRingCat.ofHom (reciprocalToOrdinary R).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (ReciprocalRing R) (ReciprocalOverlapRing R))))
      (Spec.map (CommRingCat.ofHom (reciprocalRingMap R S))) := by
  apply (reciprocalOverlap_isPullback R S).of_iso'
    (overlapSchemeIso S) (overlapSchemeIso R)
    (Iso.refl (reciprocalScheme S)) (Iso.refl (reciprocalScheme R))
  · rw [overlapSchemeIso_hom, overlapSchemeIso_hom, ordinary_transition_natural]
  · simp only [overlapSchemeIso_hom, Iso.refl_hom, Category.comp_id]
  · simp only [overlapSchemeIso_hom, Iso.refl_hom, Category.comp_id]
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]

theorem reciprocalOverlapOverOrdinary_isPullback :
    IsPullback (Spec.map (CommRingCat.ofHom (reciprocalOverlapRingMap R S)))
      (Spec.map (CommRingCat.ofHom (ordinaryToReciprocal S).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (CoordinateRing S) (OrdinaryOverlapRing S))))
      (Spec.map (CommRingCat.ofHom (ordinaryToReciprocal R).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (CoordinateRing R) (OrdinaryOverlapRing R))))
      (Spec.map (CommRingCat.ofHom (ordinaryRingMap R S))) := by
  apply (ordinaryOverlap_isPullback R S).of_iso'
    (overlapSchemeIso S).symm (overlapSchemeIso R).symm
    (Iso.refl (MazurTorsion.XOneThirteenAffineCurve.scheme S))
    (Iso.refl (MazurTorsion.XOneThirteenAffineCurve.scheme R))
  · simp only [Iso.symm_hom, overlapSchemeIso_inv]
    exact (reciprocal_transition_natural R S).symm
  · simp only [Iso.symm_hom, overlapSchemeIso_inv, Iso.refl_hom, Category.comp_id]
  · simp only [Iso.symm_hom, overlapSchemeIso_inv, Iso.refl_hom, Category.comp_id]
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]

end MazurTransfer.Order13ActualCurveBaseChange
#print axioms MazurTransfer.Order13ActualCurveBaseChange.ordinaryOverlapOverReciprocal_isPullback
#print axioms MazurTransfer.Order13ActualCurveBaseChange.reciprocalOverlapOverOrdinary_isPullback

end
end

section
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the two actual affine charts are their whole-curve
change-of-base preimages. Named downstream consumer: proving the canonical
whole-curve fibre-product morphism is an isomorphism, without assuming a
chart dictionary or preimage compatibility.
-/

noncomputable section
namespace MazurTransfer.Order13ActualCurveBaseChange
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MazurTorsion.XOneThirteenAffineCurve
open MazurTorsion.XOneThirteenProjectiveCurve
open MazurTransfer.Order13CoordinateBaseChange
universe u
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

theorem ordinaryChartPreimage_isPullback :
    IsPullback (Spec.map (CommRingCat.ofHom (ordinaryRingMap R S)))
      (ordinaryChartMap S) (ordinaryChartMap R) (curveMap R S) := by
  letI := Scheme.GlueData.instHasMulticoequalizerDiagram (glueData S)
  have localOff : IsPullback
      (Spec.map (CommRingCat.ofHom (reciprocalToOrdinary S).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (ReciprocalRing S) (ReciprocalOverlapRing S))))
      (Spec.map (CommRingCat.ofHom (algebraMap (CoordinateRing S) (OrdinaryOverlapRing S))) ≫
        Spec.map (CommRingCat.ofHom (ordinaryRingMap R S)))
      (reciprocalChartMap S ≫ curveMap R S) (ordinaryChartMap R) := by
    have H := (ordinaryOverlapOverReciprocal_isPullback R S).flip.paste_vert
      (ordinary_reciprocal_intersection R).flip
    rw [ordinary_inclusion_natural, ← reciprocalChartMap_curveMap] at H
    exact H
  have global : IsPullback (ordinaryChartMap S)
      (Spec.map (CommRingCat.ofHom (ordinaryRingMap R S)))
      (curveMap R S) (ordinaryChartMap R) := by
    apply Scheme.isPullback_of_openCover _ _ _ _ (glueData S).openCover
    intro i
    cases i
    · change IsPullback (pullback.snd (ordinaryChartMap S) (ordinaryChartMap S))
        (pullback.fst (ordinaryChartMap S) (ordinaryChartMap S) ≫
          Spec.map (CommRingCat.ofHom (ordinaryRingMap R S)))
        (ordinaryChartMap S ≫ curveMap R S) (ordinaryChartMap R)
      letI := (IsPullback.of_hasPullback (ordinaryChartMap S) (ordinaryChartMap S)).isIso_snd_iso_of_mono
      apply IsPullback.of_horiz_isIso_mono
      constructor
      rw [← Category.assoc, ← pullback.condition, Category.assoc,
        ordinaryChartMap_curveMap, ← Category.assoc]
    · change IsPullback (pullback.snd (ordinaryChartMap S) (reciprocalChartMap S))
        (pullback.fst (ordinaryChartMap S) (reciprocalChartMap S) ≫
          Spec.map (CommRingCat.ofHom (ordinaryRingMap R S)))
        (reciprocalChartMap S ≫ curveMap R S) (ordinaryChartMap R)
      apply localOff.of_iso (ordinary_reciprocal_intersection S).isoPullback
        (Iso.refl (reciprocalScheme S))
        (Iso.refl (MazurTorsion.XOneThirteenAffineCurve.scheme R)) (Iso.refl (curveScheme R))
      · simp only [Iso.refl_hom, Category.comp_id, IsPullback.isoPullback_hom_snd]
      · simp only [Iso.refl_hom, Category.comp_id, IsPullback.isoPullback_hom_fst_assoc]
      · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
      · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  exact global.flip

theorem reciprocalChartPreimage_isPullback :
    IsPullback (Spec.map (CommRingCat.ofHom (reciprocalRingMap R S)))
      (reciprocalChartMap S) (reciprocalChartMap R) (curveMap R S) := by
  letI := Scheme.GlueData.instHasMulticoequalizerDiagram (glueData S)
  have localOff : IsPullback
      (Spec.map (CommRingCat.ofHom (ordinaryToReciprocal S).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (CoordinateRing S) (OrdinaryOverlapRing S))))
      (Spec.map (CommRingCat.ofHom (algebraMap (ReciprocalRing S) (ReciprocalOverlapRing S))) ≫
        Spec.map (CommRingCat.ofHom (reciprocalRingMap R S)))
      (ordinaryChartMap S ≫ curveMap R S) (reciprocalChartMap R) := by
    have H := (reciprocalOverlapOverOrdinary_isPullback R S).flip.paste_vert
      (reciprocal_ordinary_intersection R).flip
    rw [reciprocal_inclusion_natural, ← ordinaryChartMap_curveMap] at H
    exact H
  have global : IsPullback (reciprocalChartMap S)
      (Spec.map (CommRingCat.ofHom (reciprocalRingMap R S)))
      (curveMap R S) (reciprocalChartMap R) := by
    apply Scheme.isPullback_of_openCover _ _ _ _ (glueData S).openCover
    intro i
    cases i
    · change IsPullback (pullback.snd (reciprocalChartMap S) (ordinaryChartMap S))
        (pullback.fst (reciprocalChartMap S) (ordinaryChartMap S) ≫
          Spec.map (CommRingCat.ofHom (reciprocalRingMap R S)))
        (ordinaryChartMap S ≫ curveMap R S) (reciprocalChartMap R)
      apply localOff.of_iso (reciprocal_ordinary_intersection S).isoPullback
        (Iso.refl (MazurTorsion.XOneThirteenAffineCurve.scheme S))
        (Iso.refl (reciprocalScheme R)) (Iso.refl (curveScheme R))
      · simp only [Iso.refl_hom, Category.comp_id, IsPullback.isoPullback_hom_snd]
      · simp only [Iso.refl_hom, Category.comp_id, IsPullback.isoPullback_hom_fst_assoc]
      · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
      · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    · change IsPullback (pullback.snd (reciprocalChartMap S) (reciprocalChartMap S))
        (pullback.fst (reciprocalChartMap S) (reciprocalChartMap S) ≫
          Spec.map (CommRingCat.ofHom (reciprocalRingMap R S)))
        (reciprocalChartMap S ≫ curveMap R S) (reciprocalChartMap R)
      letI := (IsPullback.of_hasPullback (reciprocalChartMap S) (reciprocalChartMap S)).isIso_snd_iso_of_mono
      apply IsPullback.of_horiz_isIso_mono
      constructor
      rw [← Category.assoc, ← pullback.condition, Category.assoc,
        reciprocalChartMap_curveMap, ← Category.assoc]
  exact global.flip

end MazurTransfer.Order13ActualCurveBaseChange
#print axioms MazurTransfer.Order13ActualCurveBaseChange.ordinaryChartPreimage_isPullback
#print axioms MazurTransfer.Order13ActualCurveBaseChange.reciprocalChartPreimage_isPullback

end
end

section
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: for arbitrary commutative base rings, the whole literal
order-thirteen glued curve over the new ring is the scheme-theoretic base
change of the original curve. Named downstream consumer: the compatible
actual integral curve family and its Picard family used in good reduction.
No chart dictionary, isomorphism, or fibre compatibility is assumed.
-/

noncomputable section
namespace MazurTransfer.Order13ActualCurveBaseChange
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MazurTorsion.XOneThirteenAffineCurve
open MazurTorsion.XOneThirteenProjectiveCurve
open MazurTransfer.Order13CoordinateBaseChange
open MazurTransfer.Order13ChartSchemeBaseChange
universe u
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

theorem ordinaryChartBase_isPullback :
    IsPullback (Spec.map (CommRingCat.ofHom (ordinaryRingMap R S)))
      (ordinaryChartToBase S) (ordinaryChartToBase R)
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  have comm : CommSq (ordinaryChartToBase S)
      (Spec.map (CommRingCat.ofHom (ordinaryRingMap R S)))
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) (ordinaryChartToBase R) :=
    ⟨(ordinary_base_natural R S).symm⟩
  exact (IsPullback.of_iso_pullback comm (ordinaryChartIso R S).symm
    (ordinaryChartIso_inv_fst R S) (ordinaryChartIso_inv_snd R S)).flip

theorem reciprocalChartBase_isPullback :
    IsPullback (Spec.map (CommRingCat.ofHom (reciprocalRingMap R S)))
      (reciprocalChartToBase S) (reciprocalChartToBase R)
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  have comm : CommSq (reciprocalChartToBase S)
      (Spec.map (CommRingCat.ofHom (reciprocalRingMap R S)))
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) (reciprocalChartToBase R) :=
    ⟨(reciprocal_base_natural R S).symm⟩
  exact (IsPullback.of_iso_pullback comm (reciprocalChartIso R S).symm
    (reciprocalChartIso_inv_fst R S) (reciprocalChartIso_inv_snd R S)).flip

theorem wholeCurve_isPullback :
    IsPullback (curveMap R S) (curveToBase S) (curveToBase R)
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  letI := Scheme.GlueData.instHasMulticoequalizerDiagram (glueData R)
  apply Scheme.isPullback_of_openCover _ _ _ _ (glueData R).openCover
  intro i
  cases i
  · change IsPullback (pullback.snd (curveMap R S) (ordinaryChartMap R))
      (pullback.fst (curveMap R S) (ordinaryChartMap R) ≫ curveToBase S)
      (ordinaryChartMap R ≫ curveToBase R)
      (Spec.map (CommRingCat.ofHom (algebraMap R S)))
    rw [ordinaryChartMap_curveToBase]
    apply (ordinaryChartBase_isPullback R S).of_iso
      (ordinaryChartPreimage_isPullback R S).flip.isoPullback
      (Iso.refl (MazurTorsion.XOneThirteenAffineCurve.scheme R))
      (Iso.refl (Spec (CommRingCat.of S))) (Iso.refl (Spec (CommRingCat.of R)))
    · simp only [Iso.refl_hom, Category.comp_id, IsPullback.isoPullback_hom_snd]
    · simp only [Iso.refl_hom, Category.comp_id, IsPullback.isoPullback_hom_fst_assoc,
        ordinaryChartMap_curveToBase]
    · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · change IsPullback (pullback.snd (curveMap R S) (reciprocalChartMap R))
      (pullback.fst (curveMap R S) (reciprocalChartMap R) ≫ curveToBase S)
      (reciprocalChartMap R ≫ curveToBase R)
      (Spec.map (CommRingCat.ofHom (algebraMap R S)))
    rw [reciprocalChartMap_curveToBase]
    apply (reciprocalChartBase_isPullback R S).of_iso
      (reciprocalChartPreimage_isPullback R S).flip.isoPullback
      (Iso.refl (reciprocalScheme R))
      (Iso.refl (Spec (CommRingCat.of S))) (Iso.refl (Spec (CommRingCat.of R)))
    · simp only [Iso.refl_hom, Category.comp_id, IsPullback.isoPullback_hom_snd]
    · simp only [Iso.refl_hom, Category.comp_id, IsPullback.isoPullback_hom_fst_assoc,
        reciprocalChartMap_curveToBase]
    · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]

def wholeCurveBaseChangeIso :
    pullback (Spec.map (CommRingCat.ofHom (algebraMap R S))) (curveToBase R) ≅ curveScheme S :=
  (wholeCurve_isPullback R S).flip.isoPullback.symm

theorem wholeCurveBaseChangeIso_inv_eq :
    (wholeCurveBaseChangeIso R S).inv = curveBaseChangeLift R S := by
  apply pullback.hom_ext
  · exact (wholeCurve_isPullback R S).flip.isoPullback_hom_fst.trans
      (curveBaseChangeLift_fst R S).symm
  · exact (wholeCurve_isPullback R S).flip.isoPullback_hom_snd.trans
      (curveBaseChangeLift_snd R S).symm

theorem curveBaseChangeLift_isIso : IsIso (curveBaseChangeLift R S) := by
  rw [← wholeCurveBaseChangeIso_inv_eq]
  infer_instance

theorem wholeCurveBaseChangeIso_inv_fst :
    (wholeCurveBaseChangeIso R S).inv ≫ pullback.fst _ _ = curveToBase S := by
  rw [wholeCurveBaseChangeIso_inv_eq, curveBaseChangeLift_fst]

theorem wholeCurveBaseChangeIso_inv_snd :
    (wholeCurveBaseChangeIso R S).inv ≫ pullback.snd _ _ = curveMap R S := by
  rw [wholeCurveBaseChangeIso_inv_eq, curveBaseChangeLift_snd]

end MazurTransfer.Order13ActualCurveBaseChange
#print axioms MazurTransfer.Order13ActualCurveBaseChange.wholeCurve_isPullback
#print axioms MazurTransfer.Order13ActualCurveBaseChange.wholeCurveBaseChangeIso
#print axioms MazurTransfer.Order13ActualCurveBaseChange.curveBaseChangeLift_isIso
#print axioms MazurTransfer.Order13ActualCurveBaseChange.wholeCurveBaseChangeIso_inv_fst
#print axioms MazurTransfer.Order13ActualCurveBaseChange.wholeCurveBaseChangeIso_inv_snd

end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MazurTorsion.XOneThirteenAffineCurve
open MazurTorsion.XOneThirteenProjectiveCurve

theorem solution.{u}
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] :
    ∃ (e : pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))
          (curveToBase R) ≅ curveScheme S)
      (φA : CoordinateRing R →+* CoordinateRing S)
      (φB : ReciprocalRing R →+* ReciprocalRing S),
      e.inv ≫ pullback.fst _ _ = curveToBase S ∧
      ordinaryChartMap S ≫ e.inv ≫ pullback.snd _ _ =
        Spec.map (CommRingCat.ofHom φA) ≫ ordinaryChartMap R ∧
      reciprocalChartMap S ≫ e.inv ≫ pullback.snd _ _ =
        Spec.map (CommRingCat.ofHom φB) ≫ reciprocalChartMap R ∧
      (∀ r : R, φA (algebraMap R (CoordinateRing R) r) =
        algebraMap S (CoordinateRing S) (algebraMap R S r)) ∧
      (∀ r : R, φB (algebraMap R (ReciprocalRing R) r) =
        algebraMap S (ReciprocalRing S) (algebraMap R S r)) ∧
      φA (xCoordinate R) = xCoordinate S ∧
      φA (yCoordinate R) = yCoordinate S ∧
      φB (zCoordinate R) = zCoordinate S ∧
      φB (wCoordinate R) = wCoordinate S := by
  refine ⟨MazurTransfer.Order13ActualCurveBaseChange.wholeCurveBaseChangeIso R S,
    MazurTransfer.Order13CoordinateBaseChange.ordinaryRingMap R S,
    MazurTransfer.Order13CoordinateBaseChange.reciprocalRingMap R S,
    MazurTransfer.Order13ActualCurveBaseChange.wholeCurveBaseChangeIso_inv_fst R S,
    ?_, ?_, MazurTransfer.Order13CoordinateBaseChange.ordinaryRingMap_algebraMap R S,
    MazurTransfer.Order13CoordinateBaseChange.reciprocalRingMap_algebraMap R S,
    MazurTransfer.Order13CoordinateBaseChange.ordinaryRingMap_x R S,
    MazurTransfer.Order13CoordinateBaseChange.ordinaryRingMap_y R S,
    MazurTransfer.Order13CoordinateBaseChange.reciprocalRingMap_z R S,
    MazurTransfer.Order13CoordinateBaseChange.reciprocalRingMap_w R S⟩
  · rw [MazurTransfer.Order13ActualCurveBaseChange.wholeCurveBaseChangeIso_inv_snd,
      MazurTransfer.Order13ActualCurveBaseChange.ordinaryChartMap_curveMap]
  · rw [MazurTransfer.Order13ActualCurveBaseChange.wholeCurveBaseChangeIso_inv_snd,
      MazurTransfer.Order13ActualCurveBaseChange.reciprocalChartMap_curveMap]

#print axioms solution
