-- Prove2me | solution 1 for MazurTransfer.Order13ActualCurveBaseChange.wholeCurve_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T03:37:21.662443+00:00
-- url     : https://prove2.me/submissions/88f1a27d-e7ea-42f7-b5cb-00a370eab8b7

/- Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual glued curve map, with its specified coordinate
maps, gives the Cartesian base-change square. Named downstream consumers:
the literal curve point injection and the integral Picard fibre dictionary.
The already Proved public whole-curve isomorphism is reused through its full
scalar and coordinate-preservation contract. Original official Anthropic FLT
APIs retain Apache-2.0 and pin 6e837e75355538c7f80bab5b956861e86c4eacc2. -/
import Definitions.Def_MazurTransfer_Order13ActualCurveBaseChangeMap
import Theorems.Thm_MazurTransfer_order13_actual_whole_curve_base_change_isomorphism
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MazurTorsion.XOneThirteenAffineCurve MazurTorsion.XOneThirteenProjectiveCurve
open MazurTransfer.Order13CoordinateBaseChange MazurTransfer.Order13ActualCurveBaseChange
universe u

theorem solution (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] :
    IsPullback (curveMap R S) (curveToBase S) (curveToBase R)
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  obtain ⟨e,φA,φB,hfst,hA,hB,hcoefA,hcoefB,hx,hy,hz,hw⟩ :=
    MazurTransfer.order13_actual_whole_curve_base_change_isomorphism R S
  have hφA : φA = ordinaryRingMap R S := by
    apply AdjoinRoot.ringHom_ext
    · apply Polynomial.ringHom_ext
      · intro r
        change φA (algebraMap R (CoordinateRing R) r) =
          ordinaryRingMap R S (algebraMap R (CoordinateRing R) r)
        rw [hcoefA r, ordinaryRingMap_algebraMap]
      · change φA (xCoordinate R) = ordinaryRingMap R S (xCoordinate R)
        rw [hx, ordinaryRingMap_x]
    · change φA (yCoordinate R) = ordinaryRingMap R S (yCoordinate R)
      rw [hy, ordinaryRingMap_y]
  have hφB : φB = reciprocalRingMap R S := by
    apply AdjoinRoot.ringHom_ext
    · apply Polynomial.ringHom_ext
      · intro r
        change φB (algebraMap R (ReciprocalRing R) r) =
          reciprocalRingMap R S (algebraMap R (ReciprocalRing R) r)
        rw [hcoefB r, reciprocalRingMap_algebraMap]
      · change φB (zCoordinate R) = reciprocalRingMap R S (zCoordinate R)
        rw [hz, reciprocalRingMap_z]
    · change φB (wCoordinate R) = reciprocalRingMap R S (wCoordinate R)
      rw [hw, reciprocalRingMap_w]
  have hsnd : e.inv ≫ pullback.snd _ _ = curveMap R S := by
    letI := Scheme.GlueData.instHasMulticoequalizerDiagram (glueData S)
    apply (glueData S).openCover.hom_ext
    intro i
    cases i
    · change ordinaryChartMap S ≫ (e.inv ≫ pullback.snd _ _) =
        ordinaryChartMap S ≫ curveMap R S
      rw [ordinaryChartMap_curveMap]
      simpa only [Category.assoc, hφA] using hA
    · change reciprocalChartMap S ≫ (e.inv ≫ pullback.snd _ _) =
        reciprocalChartMap S ≫ curveMap R S
      rw [reciprocalChartMap_curveMap]
      simpa only [Category.assoc, hφB] using hB
  have comm : CommSq (curveToBase S) (curveMap R S)
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) (curveToBase R) := by
    refine ⟨?_⟩
    calc
      _ = (e.inv ≫ pullback.fst _ _) ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)) := by rw [hfst]
      _ = e.inv ≫ (pullback.fst _ _ ≫ Spec.map (CommRingCat.ofHom (algebraMap R S))) := Category.assoc _ _ _
      _ = e.inv ≫ (pullback.snd _ _ ≫ curveToBase R) :=
        congrArg (fun f => e.inv ≫ f) (pullback.condition)
      _ = (e.inv ≫ pullback.snd _ _) ≫ curveToBase R := (Category.assoc _ _ _).symm
      _ = _ := by rw [hsnd]
  exact (IsPullback.of_iso_pullback comm e.symm hfst hsnd).flip
#print axioms solution
