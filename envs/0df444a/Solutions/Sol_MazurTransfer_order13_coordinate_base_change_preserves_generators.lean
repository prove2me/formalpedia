-- Prove2me | solution 1 for MazurTransfer.order13_coordinate_base_change_preserves_generators
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T03:03:54.273992+00:00
-- url     : https://prove2.me/submissions/a83f7853-e866-41be-90b3-bcb614ca0719

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual quadratic chart base-change isomorphisms preserve
the abscissa and ordinate generators. Named downstream consumer: checking
compatibility with the literal reciprocal localization transition when
identifying the glued integral curve's rational and finite-field fibres.
-/
import Definitions.Def_MazurTransfer_Order13CoordinateAlgebraBaseChange


noncomputable section
universe u v
namespace MazurTransfer.Order13CoordinateBaseChange
open Polynomial Algebra TensorProduct

variable (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]

private theorem quadraticCoordinateRingEquiv_root (f : Polynomial R) :
    quadraticCoordinateRingEquiv R S f (1 ⊗ₜ[R] AdjoinRoot.root (X ^ 2 - C f)) =
      AdjoinRoot.root (X ^ 2 - C (f.map (algebraMap R S))) := by
  unfold quadraticCoordinateRingEquiv
  rw [AlgEquiv.trans_apply, AdjoinRoot.tensorAlgEquiv_root]
  rw [AdjoinRoot.coe_mapAlgEquiv, AdjoinRoot.map_root]

private theorem quadraticCoordinateRingEquiv_of (f p : Polynomial R) :
    quadraticCoordinateRingEquiv R S f (1 ⊗ₜ[R] AdjoinRoot.of (X ^ 2 - C f) p) =
      AdjoinRoot.of (X ^ 2 - C (f.map (algebraMap R S))) (p.map (algebraMap R S)) := by
  unfold quadraticCoordinateRingEquiv
  rw [AlgEquiv.trans_apply, AdjoinRoot.tensorAlgEquiv_of]
  rw [AdjoinRoot.coe_mapAlgEquiv, AdjoinRoot.map_of]
  change AdjoinRoot.of (X ^ 2 - C (f.map (algebraMap R S)))
    ((polyEquivTensor R S).symm (1 ⊗ₜ[R] p)) = _
  apply congrArg (AdjoinRoot.of (X ^ 2 - C (f.map (algebraMap R S))))
  exact (polyEquivTensor_symm_apply_tmul_eq_smul R S 1 p).trans (one_smul S _)

private theorem quadraticEquationEquiv_of (p q : Polynomial (Polynomial S))
    (h : p = q) (s : Polynomial S) :
    AdjoinRoot.algEquivOfEq S p q h (AdjoinRoot.of p s) = AdjoinRoot.of q s := by
  cases h
  simp [AdjoinRoot.algEquivOfEq, AdjoinRoot.algEquivOfAssociated,
    AdjoinRoot.mapAlgEquiv, AdjoinRoot.mapAlgHom, AdjoinRoot.map]

private theorem ordinaryCoordinateRingEquiv_y :
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

private theorem ordinaryCoordinateRingEquiv_x :
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

private theorem reciprocalCoordinateRingEquiv_w :
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

private theorem reciprocalCoordinateRingEquiv_z :
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

open MazurTransfer.Order13CoordinateBaseChange
open Algebra TensorProduct
open MazurTorsion.XOneThirteenAffineCurve MazurTorsion.XOneThirteenProjectiveCurve

theorem solution (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S] :
    ordinaryCoordinateRingEquiv R S (1 ⊗ₜ[R] xCoordinate R) = xCoordinate S ∧
    ordinaryCoordinateRingEquiv R S (1 ⊗ₜ[R] yCoordinate R) = yCoordinate S ∧
    reciprocalCoordinateRingEquiv R S (1 ⊗ₜ[R] zCoordinate R) = zCoordinate S ∧
    reciprocalCoordinateRingEquiv R S (1 ⊗ₜ[R] wCoordinate R) = wCoordinate S := by
  exact ⟨ordinaryCoordinateRingEquiv_x R S, ordinaryCoordinateRingEquiv_y R S,
    reciprocalCoordinateRingEquiv_z R S, reciprocalCoordinateRingEquiv_w R S⟩
#print axioms solution
