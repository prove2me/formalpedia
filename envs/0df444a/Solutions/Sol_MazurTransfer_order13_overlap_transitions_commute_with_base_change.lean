-- Prove2me | solution 1 for MazurTransfer.order13_overlap_transitions_commute_with_base_change
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T03:13:40.708172+00:00
-- url     : https://prove2.me/submissions/35aac7aa-951c-4210-8928-7f2c2c56b7de

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the literal reciprocal transition commutes with the actual
chart and localization change-of-base ring maps on the entire overlap rings.
Named downstream consumer: identification of the glued integral curve's
base-changed scheme with the literal order-thirteen curve over the new base.
This does not yet construct a glued scheme isomorphism or a Picard family.
-/
import Definitions.Def_MazurTransfer_Order13CoordinateBaseChangeMaps



noncomputable section
universe u v
namespace MazurTransfer.Order13CoordinateBaseChange
open Polynomial Algebra TensorProduct

variable (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
open MazurTorsion.XOneThirteenAffineCurve
open MazurTorsion.XOneThirteenProjectiveCurve

private theorem ordinaryOverlapRingMap_scalar (r : R) :
    ordinaryOverlapRingMap R S (algebraMap R (OrdinaryOverlapRing R) r) =
      algebraMap S (OrdinaryOverlapRing S) (algebraMap R S r) := by
  rw [IsScalarTower.algebraMap_apply R (CoordinateRing R) (OrdinaryOverlapRing R),
    ordinaryOverlapRingMap_algebraMap, ordinaryRingMap_algebraMap,
    ← IsScalarTower.algebraMap_apply S (CoordinateRing S) (OrdinaryOverlapRing S)]

private theorem reciprocalOverlapRingMap_scalar (r : R) :
    reciprocalOverlapRingMap R S (algebraMap R (ReciprocalOverlapRing R) r) =
      algebraMap S (ReciprocalOverlapRing S) (algebraMap R S r) := by
  rw [IsScalarTower.algebraMap_apply R (ReciprocalRing R) (ReciprocalOverlapRing R),
    reciprocalOverlapRingMap_algebraMap, reciprocalRingMap_algebraMap,
    ← IsScalarTower.algebraMap_apply S (ReciprocalRing S) (ReciprocalOverlapRing S)]

private theorem ordinaryTransition_x :
    ordinaryToReciprocal R
      (algebraMap (CoordinateRing R) (OrdinaryOverlapRing R) (xCoordinate R)) =
      IsLocalization.Away.invSelf (zCoordinate R) := by
  rw [ordinaryToReciprocal_algebraMap]
  exact ordinaryToReciprocalBase_x R

private theorem ordinaryTransition_y :
    ordinaryToReciprocal R
      (algebraMap (CoordinateRing R) (OrdinaryOverlapRing R) (yCoordinate R)) =
      algebraMap (ReciprocalRing R) (ReciprocalOverlapRing R) (wCoordinate R) *
        IsLocalization.Away.invSelf (zCoordinate R) ^ 3 := by
  rw [ordinaryToReciprocal_algebraMap]
  exact ordinaryToReciprocalBase_y R

private theorem ordinaryTransition_natural :
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

private theorem ordinaryTransition_left_inverse (a : OrdinaryOverlapRing R) :
    reciprocalToOrdinary R (ordinaryToReciprocal R a) = a := by
  simpa only [AlgHom.comp_apply, AlgHom.id_apply] using
    DFunLike.congr_fun (reciprocalToOrdinary_comp_ordinaryToReciprocal R) a

private theorem ordinaryTransition_right_inverse (a : ReciprocalOverlapRing R) :
    ordinaryToReciprocal R (reciprocalToOrdinary R a) = a := by
  simpa only [AlgHom.comp_apply, AlgHom.id_apply] using
    DFunLike.congr_fun (ordinaryToReciprocal_comp_reciprocalToOrdinary R) a

private theorem reciprocalTransition_natural :
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

open MazurTransfer.Order13CoordinateBaseChange
open MazurTorsion.XOneThirteenAffineCurve MazurTorsion.XOneThirteenProjectiveCurve

theorem solution (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S] :
    (reciprocalOverlapRingMap R S).comp (ordinaryToReciprocal R).toRingHom =
      (ordinaryToReciprocal S).toRingHom.comp (ordinaryOverlapRingMap R S) ∧
    (ordinaryOverlapRingMap R S).comp (reciprocalToOrdinary R).toRingHom =
      (reciprocalToOrdinary S).toRingHom.comp (reciprocalOverlapRingMap R S) := by
  exact ⟨ordinaryTransition_natural R S, reciprocalTransition_natural R S⟩
#print axioms solution
