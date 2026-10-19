-- Prove2me | solution 1 for MazurTransfer.Order13IntegralSections.infinityMorphism_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T04:07:20.287609+00:00
-- url     : https://prove2.me/submissions/460940a4-9566-4101-8e8a-88fd64342593

/- Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual infinity morphisms commute with scalar extension
and the specified actual curve map. Named downstream consumers: the integral
Abel-Jacobi dictionary and the literal Picard fibre section compatibility.
Original naturality proof bodies are preserved. -/
import Definitions.Def_MazurTransfer_Order13IntegralInfinitySections
import Definitions.Def_MazurTransfer_Order13InverseParameterChartComparison
import Definitions.Def_MazurTransfer_Order13ActualCurveBaseChangeMap
namespace InfinityBaseChangePublicProof20261017
open _root_.MazurTransfer.Order13IntegralSections
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual infinity sections commute with arbitrary
scalar extension and the previously proved whole-curve base-change map.
Named downstream consumer: compatible section inputs for the integral
Picard family and its rational and finite-field fibres.
-/


noncomputable section
universe u
namespace MazurTransfer.Order13IntegralSections
open CategoryTheory AlgebraicGeometry Polynomial
open MazurTorsion.XOneThirteenProjectiveCurve
open MazurTransfer.Order13CoordinateBaseChange
open MazurTransfer.Order13ActualCurveBaseChange
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
private theorem reciprocalInfinityEvaluation_z (a : R) (ha : a ^ 2 = 1) :
    reciprocalInfinityEvaluation R a ha (zCoordinate R) = 0 := by
  simpa only [MazurTransfer.Order13IntegralSections.reciprocalInfinityEvaluation] using
    InverseParameterChartComparisonLibrary.MazurTransfer.Order13IntegralSections.reciprocalInfinityEvaluation_z R a ha
private theorem reciprocalInfinityEvaluation_w (a : R) (ha : a ^ 2 = 1) :
    reciprocalInfinityEvaluation R a ha (wCoordinate R) = a := by
  simpa only [MazurTransfer.Order13IntegralSections.reciprocalInfinityEvaluation] using
    InverseParameterChartComparisonLibrary.MazurTransfer.Order13IntegralSections.reciprocalInfinityEvaluation_w R a ha


theorem reciprocalInfinityEvaluation_baseChange (a : R) (ha : a ^ 2 = 1) :
    (reciprocalInfinityEvaluation S (algebraMap R S a)
      (by rw [← map_pow, ha, map_one])).comp (reciprocalRingMap R S) =
    (algebraMap R S).comp (reciprocalInfinityEvaluation R a ha) := by
  apply AdjoinRoot.ringHom_ext
  · ext r
    · change reciprocalInfinityEvaluation S (algebraMap R S a)
        (by rw [← map_pow, ha, map_one])
        (reciprocalRingMap R S (algebraMap R (ReciprocalRing R) r)) = _
      rw [reciprocalRingMap_algebraMap]
      have hS := RingHom.congr_fun
        (reciprocalInfinityEvaluation_comp_algebraMap S (algebraMap R S a)
          (by rw [← map_pow, ha, map_one])) (algebraMap R S r)
      have hR := RingHom.congr_fun
        (reciprocalInfinityEvaluation_comp_algebraMap R a ha) r
      simpa only [RingHom.comp_apply, RingHom.id_apply, AdjoinRoot.algebraMap_eq', Polynomial.algebraMap_eq] using
        hS.trans (congrArg (algebraMap R S) hR).symm
    · change reciprocalInfinityEvaluation S (algebraMap R S a)
        (by rw [← map_pow, ha, map_one])
        (reciprocalRingMap R S (zCoordinate R)) =
        algebraMap R S (reciprocalInfinityEvaluation R a ha (zCoordinate R))
      rw [reciprocalRingMap_z, reciprocalInfinityEvaluation_z,
        reciprocalInfinityEvaluation_z, map_zero]
  · change reciprocalInfinityEvaluation S (algebraMap R S a)
        (by rw [← map_pow, ha, map_one])
        (reciprocalRingMap R S (wCoordinate R)) =
        algebraMap R S (reciprocalInfinityEvaluation R a ha (wCoordinate R))
    rw [reciprocalRingMap_w, reciprocalInfinityEvaluation_w,
      reciprocalInfinityEvaluation_w]



end MazurTransfer.Order13IntegralSections



end
end InfinityBaseChangePublicProof20261017
open CategoryTheory AlgebraicGeometry Polynomial
open MazurTorsion.XOneThirteenProjectiveCurve
open MazurTransfer.Order13IntegralSections MazurTransfer.Order13CoordinateBaseChange
open MazurTransfer.Order13ActualCurveBaseChange
open InfinityBaseChangePublicProof20261017.MazurTransfer.Order13IntegralSections
universe u
theorem solution (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (a : R) (ha : a ^ 2 = 1) :
    infinityMorphism S (algebraMap R S a)
      (by rw [← map_pow, ha, map_one]) ≫ curveMap R S =
    Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫ infinityMorphism R a ha := by
  unfold infinityMorphism
  rw [Category.assoc, reciprocalChartMap_curveMap]
  rw [← Category.assoc, ← Category.assoc]
  congr 1
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext
    (reciprocalInfinityEvaluation_baseChange R S a ha))
#print axioms solution
