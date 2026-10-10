-- Prove2me | solution 1 for MazurTransfer.order13_actual_coordinate_base_change_and_reciprocal_transition
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-10T01:35:15.642988+00:00
-- url     : https://prove2.me/submissions/b1b1d553-3ca3-4095-81c9-befb69d6ed63

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: actual coordinate algebra base-change isomorphisms and
both whole-ring reciprocal transition diagrams. Named downstream consumer:
identification of the glued integral curve's rational and finite-field fibres.
No glued scheme isomorphism, properness or Picard family is assumed here.
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

open Polynomial Algebra TensorProduct
open MazurTorsion.XOneThirteenAffineCurve
open MazurTorsion.XOneThirteenProjectiveCurve

theorem solution.{u,v}
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S] :
    ∃ (eA : S ⊗[R] CoordinateRing R ≃ₐ[S] CoordinateRing S)
      (eB : S ⊗[R] ReciprocalRing R ≃ₐ[S] ReciprocalRing S)
      (φA : OrdinaryOverlapRing R →+* OrdinaryOverlapRing S)
      (φB : ReciprocalOverlapRing R →+* ReciprocalOverlapRing S),
      eA (1 ⊗ₜ[R] xCoordinate R) = xCoordinate S ∧
      eA (1 ⊗ₜ[R] yCoordinate R) = yCoordinate S ∧
      eB (1 ⊗ₜ[R] zCoordinate R) = zCoordinate S ∧
      eB (1 ⊗ₜ[R] wCoordinate R) = wCoordinate S ∧
      (∀ a : CoordinateRing R,
        φA (algebraMap (CoordinateRing R) (OrdinaryOverlapRing R) a) =
          algebraMap (CoordinateRing S) (OrdinaryOverlapRing S) (eA (1 ⊗ₜ[R] a))) ∧
      (∀ b : ReciprocalRing R,
        φB (algebraMap (ReciprocalRing R) (ReciprocalOverlapRing R) b) =
          algebraMap (ReciprocalRing S) (ReciprocalOverlapRing S) (eB (1 ⊗ₜ[R] b))) ∧
      φB.comp (ordinaryToReciprocal R).toRingHom =
        (ordinaryToReciprocal S).toRingHom.comp φA ∧
      φA.comp (reciprocalToOrdinary R).toRingHom =
        (reciprocalToOrdinary S).toRingHom.comp φB := by
  refine ⟨MazurTransfer.Order13CoordinateBaseChange.ordinaryCoordinateRingEquiv R S,
    MazurTransfer.Order13CoordinateBaseChange.reciprocalCoordinateRingEquiv R S,
    MazurTransfer.Order13CoordinateBaseChange.ordinaryOverlapRingMap R S,
    MazurTransfer.Order13CoordinateBaseChange.reciprocalOverlapRingMap R S,
    MazurTransfer.Order13CoordinateBaseChange.ordinaryCoordinateRingEquiv_x R S,
    MazurTransfer.Order13CoordinateBaseChange.ordinaryCoordinateRingEquiv_y R S,
    MazurTransfer.Order13CoordinateBaseChange.reciprocalCoordinateRingEquiv_z R S,
    MazurTransfer.Order13CoordinateBaseChange.reciprocalCoordinateRingEquiv_w R S,
    ?_, ?_, MazurTransfer.Order13CoordinateBaseChange.ordinaryTransition_natural R S,
    MazurTransfer.Order13CoordinateBaseChange.reciprocalTransition_natural R S⟩
  · intro a
    exact MazurTransfer.Order13CoordinateBaseChange.ordinaryOverlapRingMap_algebraMap R S a
  · intro b
    exact MazurTransfer.Order13CoordinateBaseChange.reciprocalOverlapRingMap_algebraMap R S b

#print axioms solution
