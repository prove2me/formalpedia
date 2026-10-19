-- Prove2me | solution 1 for MazurTransfer.Order13ActualCurveBaseChange.chartMapToOriginal_compatible
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T03:23:11.790515+00:00
-- url     : https://prove2.me/submissions/04b17368-8315-47db-8807-1e57871ce32b

/- Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: actual chart base-change maps satisfy the original overlap
gluing compatibility. Named downstream consumer: construction of the actual
whole-curve base-change morphism. Original proof bodies are preserved. -/
import Definitions.Def_MazurTransfer_Order13BaseChangeChartMorphisms
import Theorems.Thm_MazurTransfer_order13_overlap_transitions_commute_with_base_change
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









private theorem ordinaryTransition_natural :
    (reciprocalOverlapRingMap R S).comp (ordinaryToReciprocal R).toRingHom =
      (ordinaryToReciprocal S).toRingHom.comp (ordinaryOverlapRingMap R S)  := by exact (_root_.MazurTransfer.order13_overlap_transitions_commute_with_base_change R S).1





private theorem reciprocalTransition_natural :
    (ordinaryOverlapRingMap R S).comp (reciprocalToOrdinary R).toRingHom =
      (reciprocalToOrdinary S).toRingHom.comp (reciprocalOverlapRingMap R S)  := by exact (_root_.MazurTransfer.order13_overlap_transitions_commute_with_base_change R S).2

end MazurTransfer.Order13CoordinateBaseChange




end

namespace ChartCompatibilityPublicProof20261017
open _root_.MazurTransfer.Order13ActualCurveBaseChange
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











end MazurTransfer.Order13ActualCurveBaseChange






end
end ChartCompatibilityPublicProof20261017

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MazurTorsion.XOneThirteenAffineCurve MazurTorsion.XOneThirteenProjectiveCurve
open _root_.MazurTransfer.Order13CoordinateBaseChange
open _root_.MazurTransfer.Order13ActualCurveBaseChange
open ChartCompatibilityPublicProof20261017.MazurTransfer.Order13ActualCurveBaseChange
universe u
theorem solution (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (i j : Chart.{u}) (h : i ≠ j) :
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
#print axioms solution
