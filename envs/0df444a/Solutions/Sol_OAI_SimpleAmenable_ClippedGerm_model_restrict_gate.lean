-- Prove2me | solution 1 for OAI.SimpleAmenable.ClippedGerm.model_restrict_gate
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T03:52:36.550518+00:00
-- url     : https://prove2.me/submissions/bfdecbc4-fa0a-4d93-9831-bf19d3dedb07

import Mathlib
import Definitions.Def_OAIQ65Sa010
import Definitions.Def_OAIQ65Sa011

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_LocalArrangementAssignments
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement

section LocalBooleanAssignments
variable {a : ℕ} {ι κ : Type*}

theorem polygonFormalMask_mem (U : κ → polygonAlgebra a) (V : polygonAlgebra a)
    (hV : ResolvedBy (fun i => (U i).val) V.val) (p : GenericSquare a) :
    polygonAssignment U p ∈ polygonFormalMask U V ↔ p ∈ V.val := by
  constructor
  · rintro ⟨q,hq,hqV⟩
    exact (hV q p ((polygonAssignment_eq_iff U q p).mp hq)).mp hqV
  · intro hp; exact ⟨p,rfl,hp⟩

end LocalBooleanAssignments

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_ChartQuadrants
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section ChartQuadrants

theorem coordinateRectangle_lift {a : ℕ} (u v : Fin 2 → CutRing)
    (huv : ∀ j, ordinary (u j) ≤ ordinary (v j))
    (hlen : ∀ j, ordinary (v j)-ordinary (u j) < 1)
    (p : GenericSquare a) (hp : p ∈ (coordinateRectangle a u v).val) :
    ∃ t : ℝ × ℝ, p.val = (Int.fract t.1,Int.fract t.2) ∧
      (ordinary (u 0) ≤ t.1 ∧ t.1 < ordinary (v 0)) ∧
      (ordinary (u 1) ≤ t.2 ∧ t.2 < ordinary (v 1)) := by
  change p ∈ coordinateBetween a 0 (u 0) (v 0) ∧
    p ∈ coordinateBetween a 1 (u 1) (v 1) at hp
  obtain ⟨k,hk⟩ := (mem_coordinateBetween_iff 0 (u 0) (v 0) (huv 0) (hlen 0) p).mp hp.1
  obtain ⟨l,hl⟩ := (mem_coordinateBetween_iff 1 (u 1) (v 1) (huv 1) (hlen 1) p).mp hp.2
  refine ⟨(coordinate 0 p+(k:ℝ),coordinate 1 p+(l:ℝ)),?_,hk,hl⟩
  simp only [Int.fract_add_intCast,Int.fract_eq_self.mpr (coordinate_bounds 0 p),
    Int.fract_eq_self.mpr (coordinate_bounds 1 p)]
  rfl

end ChartQuadrants

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_SpatialChartGeometry
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement

section ChartTransforms

theorem spatialTranslate_coordinateInterval {a : ℕ} (z : CutRing × CutRing)
    (j : Fin 2) (u v : CutRing) :
    spatialTranslate z (coordinateInterval a j u v) =
      coordinateInterval a j (u+(if j=0 then z.1 else z.2))
        (v+(if j=0 then z.1 else z.2)) := by
  apply Subtype.ext
  ext p
  have hfract (x y : ℝ) : Int.fract (Int.fract x+y) = Int.fract (x+y) := by
    change Int.fract (x-(⌊x⌋:ℝ)+y) = _
    rw [sub_add_eq_add_sub,Int.fract_sub_intCast]
  have hsub (x y : CutRing) : v+x-(u+y) = v-u+(x-y) := by ring
  fin_cases j <;>
    simp [spatialTranslate,coordinateInterval,coordinateBetween,coordinateArc,
      coordinate,coordinateShift,translate_val,hfract,hsub,sub_eq_add_neg,add_assoc]

theorem spatialTranslate_coordinateRectangle {a : ℕ} (z : CutRing × CutRing)
    (u v : Fin 2 → CutRing) :
    spatialTranslate z (coordinateRectangle a u v) =
      coordinateRectangle a (fun j => u j+(if j=0 then z.1 else z.2))
        (fun j => v j+(if j=0 then z.1 else z.2)) := by
  simp [coordinateRectangle,spatialTranslate_coordinateInterval]

end ChartTransforms

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_ClosedChartOverlap
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section ClosedChartOverlap

theorem planar_lift_avoidsCuts {a : ℕ} (p : GenericSquare a) (t : ℝ × ℝ)
    (ht : p.val = (Int.fract t.1,Int.fract t.2)) : AvoidsCuts a t := by
  have h := avoidsCuts_translate p.property.2.2
    ((⌊t.1⌋ : CutRing),(⌊t.2⌋ : CutRing))
  have he : p.val+(ordinary (⌊t.1⌋ : CutRing),ordinary (⌊t.2⌋ : CutRing)) = t := by
    rw [ht]
    apply Prod.ext
    · change Int.fract t.1+ordinary (⌊t.1⌋ : CutRing) = t.1
      rw [map_intCast]
      exact sub_add_cancel _ _
    · change Int.fract t.2+ordinary (⌊t.2⌋ : CutRing) = t.2
      rw [map_intCast]
      exact sub_add_cancel _ _
  rwa [he] at h

theorem coordinateRectangle_strict_lift {a : ℕ} (l h : Fin 2 → CutRing)
    (hlh : ∀ j, ordinary (l j) ≤ ordinary (h j))
    (hlen : ∀ j, ordinary (h j)-ordinary (l j) < 1)
    (p : GenericSquare a) (hp : p ∈ (coordinateRectangle a l h).val) :
    ∃ t : ℝ × ℝ, p.val = (Int.fract t.1,Int.fract t.2) ∧
      (ordinary (l 0) < t.1 ∧ t.1 < ordinary (h 0)) ∧
      (ordinary (l 1) < t.2 ∧ t.2 < ordinary (h 1)) := by
  obtain ⟨t,ht,hx,hy⟩ := coordinateRectangle_lift l h hlh hlen p hp
  have hx' := planar_lift_avoidsCuts p t ht 0 (l 0)
  have hy' := planar_lift_avoidsCuts p t ht 1 (l 1)
  simp only [cutForm,Matrix.cons_val_zero,Matrix.cons_val_one] at hx' hy'
  exact ⟨t,ht,⟨lt_of_le_of_ne hx.1 (Ne.symm hx'),hx.2⟩,
    ⟨lt_of_le_of_ne hy.1 (Ne.symm hy'),hy.2⟩⟩

end ClosedChartOverlap

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_LocalChartDecisions
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section LocalChartDecisions

theorem fract_fract_add_eq (x y : ℝ) :
    Int.fract (Int.fract x+y)=Int.fract (x+y) := by
  change Int.fract (x-(⌊x⌋:ℝ)+y)=_
  rw [sub_add_eq_add_sub,Int.fract_sub_intCast]

theorem translate_planar_lift {a : ℕ} (p : GenericSquare a) (z : ℝ × ℝ)
    (hz : p.val=(Int.fract z.1,Int.fract z.2)) (u : CutRing × CutRing) :
    (translate a u p).val=(Int.fract (z.1+ordinary u.1),Int.fract (z.2+ordinary u.2)) := by
  simp only [translate_val,hz,fract_fract_add_eq]

theorem translated_clippedSlope_planar {a : ℕ} (r : CutRing) (j : Fin 4)
    (hr : 0<ordinary r ∧ ordinary r<1/2) (u : CutRing × CutRing)
    (p : GenericSquare a) (z : ℝ × ℝ)
    (hz : p.val=(Int.fract z.1,Int.fract z.2))
    (hnear : |z.1-ordinary u.1|<ordinary r ∧ |z.2-ordinary u.2|<ordinary r) :
    p ∈ (spatialTranslate u (clippedSlopePrimitive a r j)).val ↔
      ordinary (integralCutForm a j u) ≤ cutForm a j z := by
  change translate a (-u) p ∈ (clippedSlopePrimitive a r j).val ↔ _
  have hp := translate_planar_lift p z hz (-u)
  simp only [Prod.fst_neg,Prod.snd_neg,map_neg,← sub_eq_add_neg] at hp
  rw [mem_clippedSlope_lift r j hr _ (z-(ordinary u.1,ordinary u.2))
    ⟨abs_lt.mp hnear.1,abs_lt.mp hnear.2⟩ hp,cutForm_sub,cutForm_ordinary]
  exact sub_nonneg

theorem fract_coordinate_sign (x : ℝ)
    (hl : -(2-Real.goldenRatio)<x) (hu : x<Real.goldenRatio-1) :
    Int.fract x<Real.goldenRatio-1 ↔ 0≤x := by
  have hτ := Real.one_lt_goldenRatio
  have hτ' := Real.goldenRatio_lt_two
  by_cases hx : 0≤x
  · rw [Int.fract_eq_self.mpr ⟨hx,by linarith⟩]
    exact iff_of_true hu hx
  · have hxf : Int.fract x=x+1 := by
      rw [← Int.fract_add_one x,Int.fract_eq_self.mpr ⟨by linarith,by linarith⟩]
    rw [hxf]
    exact iff_of_false (by linarith) hx

theorem translated_coordinate_planar {a : ℕ} (j : Fin 2) (u : CutRing × CutRing)
    (p : GenericSquare a) (z : ℝ × ℝ)
    (hz : p.val=(Int.fract z.1,Int.fract z.2))
    (hl : -(2-Real.goldenRatio) < realCoordinate z j-ordinary (pointCoordinate u j))
    (hu : realCoordinate z j-ordinary (pointCoordinate u j)<Real.goldenRatio-1) :
    p ∈ (spatialTranslate u (coordinatePrimitive a j)).val ↔
      ordinary (pointCoordinate u j) ≤ realCoordinate z j := by
  have ht := translate_planar_lift p z hz (-u)
  simp only [Prod.fst_neg,Prod.snd_neg,map_neg,← sub_eq_add_neg] at ht
  have hc : coordinate j (translate a (-u) p)=
      Int.fract (realCoordinate z j-ordinary (pointCoordinate u j)) := by
    fin_cases j
    · exact congrArg Prod.fst ht
    · exact congrArg Prod.snd ht
  have hmem : p ∈ (spatialTranslate u (coordinatePrimitive a j)).val ↔
      coordinate j (translate a (-u) p)<Real.goldenRatio-1 := by
    change (cutForm a (Fin.castLE (by omega) j) (translate a (-u) p).val<ordinary (cutTau-1) ∧
      ¬cutForm a (Fin.castLE (by omega) j) (translate a (-u) p).val<ordinary 0) ↔ _
    have hform : cutForm a (Fin.castLE (by omega) j) (translate a (-u) p).val=
        coordinate j (translate a (-u) p) := by fin_cases j <;> rfl
    simp only [hform,map_sub,ordinary_cutTau,map_one,map_zero,not_lt,
      (coordinate_bounds j (translate a (-u) p)).1,and_true]
  rw [hmem,hc,fract_coordinate_sign _ hl hu]
  exact sub_nonneg

end LocalChartDecisions

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_VertexMargins
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section VertexMargins

namespace VertexMargin
variable {z : ℝ × ℝ} {ε : ℝ} (V : VertexMargin z ε)

theorem width (_hε : 0<ε) (j : Fin 2) :
    ordinary (V.lower j)<ordinary (V.upper j) ∧
    ordinary (V.upper j)-ordinary (V.lower j)<4*ε := by
  have h₁ := V.lower_inner j
  have h₂ := V.upper_inner j
  have h₃ := V.lower_outer j
  have h₄ := V.upper_outer j
  constructor <;> linarith

end VertexMargin

end VertexMargins

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_SupportedCellPatching
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement

section ConcurrentAxisDecisions

namespace ConcurrentGeometry
variable {a : ℕ} {r : CutRing} (C : ConcurrentGeometry a r)

theorem axis_on_margin (j : Fin 2) (u b : CutRing × CutRing)
    (t : VertexType (commonVertexDenominator a))
    (hnear : ∀ z : ℝ × ℝ,
      (∀ k, ordinary ((C.margins t).lower k+pointCoordinate u k) ≤ realCoordinate z k ∧
        realCoordinate z k≤ordinary ((C.margins t).upper k+pointCoordinate u k)) →
      ∀ k, |realCoordinate z k-ordinary (pointCoordinate b k)|<3*C.epsilon)
    (p : GenericSquare a) (z : ℝ × ℝ) (hz : p.val=(Int.fract z.1,Int.fract z.2))
    (hcell : ∀ k, ordinary ((C.margins t).lower k+pointCoordinate u k) ≤ realCoordinate z k ∧
      realCoordinate z k≤ordinary ((C.margins t).upper k+pointCoordinate u k)) :
    p ∈ (spatialTranslate b (coordinatePrimitive a j)).val ↔
      ordinary (pointCoordinate b j) ≤ realCoordinate z j := by
  have hh := abs_lt.mp (hnear z hcell j)
  apply translated_coordinate_planar j b p z hz
  · have hg := C.second_gap
    have hp := C.positive
    linarith
  · have hg := C.first_gap
    have hp := C.positive
    linarith

end ConcurrentGeometry
end ConcurrentAxisDecisions

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_InwardPlanarGerms
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section InwardPlanarGerms

theorem finite_arrangement_germ_inward {ι : Type*} [Finite ι] (a : ℕ)
    (j : ι → Fin 4) (c : ι → ℝ) (z y : ℝ × ℝ) (σ : ι → Bool)
    (hz₁ : z.1 ∈ Set.Icc (0:ℝ) 1) (hz₂ : z.2 ∈ Set.Icc (0:ℝ) 1)
    (hzero : ∀ k, realCoordinate z k=0 → 0 < realCoordinate y k)
    (hone : ∀ k, realCoordinate z k=1 → realCoordinate y k<1)
    (hactive : ∀ i, cutForm a (j i) z=c i →
      if σ i then cutForm a (j i) y < c i else c i < cutForm a (j i) y)
    (hinactive : ∀ i, cutForm a (j i) z≠c i →
      if σ i then cutForm a (j i) z < c i else c i < cutForm a (j i) z)
    (N : Set (ℝ × ℝ)) (hN : IsOpen N) (hz : z ∈ N) :
    ∃ p : GenericSquare a, p.val ∈ N ∧ p.val ∈ strictLineCell a j c σ := by
  classical
  let J : Sum ι (Fin 2 × Bool) → Fin 4 := Sum.elim j (fun d => Fin.castLE (by omega) d.1)
  let C : Sum ι (Fin 2 × Bool) → ℝ := Sum.elim c (fun d => if d.2 then 1 else 0)
  let S : Sum ι (Fin 2 × Bool) → Bool := Sum.elim σ Prod.snd
  have ha : ∀ i, cutForm a (J i) z=C i →
      if S i then cutForm a (J i) y < C i else C i < cutForm a (J i) y := by
    intro i hi
    cases i with
    | inl i => exact hactive i hi
    | inr d =>
      rcases d with ⟨d,b⟩
      fin_cases d <;> cases b
      · exact hzero 0 hi
      · exact hone 0 hi
      · exact hzero 1 hi
      · exact hone 1 hi
  have hn : ∀ i, cutForm a (J i) z≠C i →
      if S i then cutForm a (J i) z < C i else C i < cutForm a (J i) z := by
    intro i hi
    cases i with
    | inl i => exact hinactive i hi
    | inr d =>
      rcases d with ⟨d,b⟩
      fin_cases d <;> cases b <;>
        simp [J,C,S,cutForm] at hi ⊢
      · exact lt_of_le_of_ne hz₁.1 (Ne.symm hi)
      · exact lt_of_le_of_ne hz₁.2 hi
      · exact lt_of_le_of_ne hz₂.1 (Ne.symm hi)
      · exact lt_of_le_of_ne hz₂.2 hi
  obtain ⟨p,hp,hcell,hgeneric⟩ := finite_arrangement_germ a J C z y S ha hn N hN hz
  have hp₁ : p.1 ∈ Set.Ioo (0:ℝ) 1 := ⟨hcell (.inr (0,false)),hcell (.inr (0,true))⟩
  have hp₂ : p.2 ∈ Set.Ioo (0:ℝ) 1 := ⟨hcell (.inr (1,false)),hcell (.inr (1,true))⟩
  exact ⟨⟨p,⟨hp₁.1.le,hp₁.2⟩,⟨hp₂.1.le,hp₂.2⟩,hgeneric⟩,hp,fun i => hcell (.inl i)⟩

end InwardPlanarGerms

section ConcurrentPositiveDecisions
namespace ConcurrentGeometry
variable {a : ℕ} {r : CutRing} (C : ConcurrentGeometry a r)

theorem positiveDecision_planar (hr : 0<ordinary r ∧ ordinary r<1/2)
    (t : VertexType (commonVertexDenominator a)) (u : CutRing × CutRing) (j : Fin 4)
    (hnear : ∀ z : ℝ × ℝ,
      (∀ k, ordinary ((C.margins t).lower k+pointCoordinate u k) ≤ realCoordinate z k ∧
        realCoordinate z k≤ordinary ((C.margins t).upper k+pointCoordinate u k)) →
      ∀ k, |realCoordinate z k-ordinary (pointCoordinate (u+C.anchors t j) k)|<3*C.epsilon)
    (p : GenericSquare a) (y : ℝ × ℝ) (hy : p.val=(Int.fract y.1,Int.fract y.2))
    (hcell : ∀ k, ordinary ((C.margins t).lower k+pointCoordinate u k) ≤ realCoordinate y k ∧
      realCoordinate y k≤ordinary ((C.margins t).upper k+pointCoordinate u k)) :
    p ∈ (C.positiveDecision t u j).val ↔
      ordinary (integralCutForm a j (u+C.anchors t j)) ≤ cutForm a j y := by
  have hs : |y.1-ordinary (u+C.anchors t j).1|<ordinary r ∧
      |y.2-ordinary (u+C.anchors t j).2|<ordinary r := by
    have h₀ := hnear y hcell 0
    have h₁ := hnear y hcell 1
    have hr' := C.radius
    have hε := C.positive
    change |y.1-ordinary (u+C.anchors t j).1|<3*C.epsilon at h₀
    change |y.2-ordinary (u+C.anchors t j).2|<3*C.epsilon at h₁
    constructor <;> linarith
  fin_cases j
  · exact C.axis_on_margin 0 u (u+C.anchors t 0) t hnear p y hy hcell
  · exact C.axis_on_margin 1 u (u+C.anchors t 1) t hnear p y hy hcell
  · exact translated_clippedSlope_planar r 2 hr (u+C.anchors t 2) p y hy hs
  · exact translated_clippedSlope_planar r 3 hr (u+C.anchors t 3) p y hy hs

theorem marginPolygon_lift (hr : ordinary r<1/2)
    (t : VertexType (commonVertexDenominator a)) (u : CutRing × CutRing)
    (p : GenericSquare a) (hp : p ∈ (C.marginPolygon t u).val) :
    ∃ y : ℝ × ℝ, p.val=(Int.fract y.1,Int.fract y.2) ∧ AvoidsCuts a y ∧
      ∀ k, ordinary ((C.margins t).lower k+pointCoordinate u k) < realCoordinate y k ∧
        realCoordinate y k<ordinary ((C.margins t).upper k+pointCoordinate u k) := by
  have hw (k) := (C.margins t).width C.positive k
  have hrad := C.radius
  have hlen (k) : ordinary ((C.margins t).upper k+pointCoordinate u k)-
      ordinary ((C.margins t).lower k+pointCoordinate u k)<1 := by
    simp only [map_add]
    linarith [hw k]
  have hle (k) : ordinary ((C.margins t).lower k+pointCoordinate u k) ≤
      ordinary ((C.margins t).upper k+pointCoordinate u k) := by
    simp only [map_add]
    linarith [hw k,C.positive]
  have hp' : p ∈ (coordinateRectangle a
      (fun k => (C.margins t).lower k+pointCoordinate u k)
      (fun k => (C.margins t).upper k+pointCoordinate u k)).val := by
    simpa only [marginPolygon,spatialTranslate_coordinateRectangle,pointCoordinate] using hp
  obtain ⟨y,hy,hy₀,hy₁⟩ := coordinateRectangle_strict_lift _ _ hle hlen p hp'
  refine ⟨y,hy,planar_lift_avoidsCuts p y hy,?_⟩
  intro k
  fin_cases k
  · exact hy₀
  · exact hy₁

end ConcurrentGeometry
end ConcurrentPositiveDecisions

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_ConcurrentInwardModel
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section ConcurrentInwardModel
namespace ConcurrentGeometry
variable {a : ℕ} {r : CutRing} (C : ConcurrentGeometry a r)

theorem localDecision_assignment_realized {ι : Type*} [Finite ι]
    (hr : 0<ordinary r ∧ ordinary r<1/2)
    (t : VertexType (commonVertexDenominator a)) (u : CutRing × CutRing)
    (j : ι → Fin 4) (c : ι → CutRing) (z : ℝ × ℝ)
    (hz₁ : z.1 ∈ Set.Icc (0:ℝ) 1) (hz₂ : z.2 ∈ Set.Icc (0:ℝ) 1)
    (hline : ∀ i, cutForm a (j i) z=ordinary (c i) →
      integralCutForm a (j i) (u+C.anchors t (j i))=c i)
    (hboundary : ∀ k, realCoordinate z k=0 ∨ realCoordinate z k=1 →
      ordinary (pointCoordinate (u+C.anchors t (axisDirection k)) k)=realCoordinate z k)
    (hnear : ∀ i, cutForm a (j i) z=ordinary (c i) → ∀ y : ℝ × ℝ,
      (∀ k, ordinary ((C.margins t).lower k+pointCoordinate u k) ≤ realCoordinate y k ∧
        realCoordinate y k≤ordinary ((C.margins t).upper k+pointCoordinate u k)) →
      ∀ k, |realCoordinate y k-ordinary (pointCoordinate (u+C.anchors t (j i)) k)|<3*C.epsilon)
    (hnearB : ∀ d, realCoordinate z d=0 ∨ realCoordinate z d=1 → ∀ y : ℝ × ℝ,
      (∀ k, ordinary ((C.margins t).lower k+pointCoordinate u k) ≤ realCoordinate y k ∧
        realCoordinate y k≤ordinary ((C.margins t).upper k+pointCoordinate u k)) →
      ∀ k, |realCoordinate y k-ordinary (pointCoordinate (u+C.anchors t (axisDirection d)) k)|<3*C.epsilon)
    (p : GenericSquare a) (hp : p ∈ (C.inwardMargin t u z).val)
    (N : Set (ℝ × ℝ)) (hN : IsOpen N) (hz : z ∈ N) :
    ∃ q : GenericSquare a, q.val ∈ N ∧
      polygonAssignment (fun i => cutPolygon a (j i) (c i)) q=
        polygonAssignment (fun i => C.localDecision t u z (j i) (c i)) p := by
  classical
  have hpM : p ∈ (C.marginPolygon t u).val := hp.1.1
  have hpG (k : Fin 2) : p ∈ (C.inwardGate t u z k).val := by
    fin_cases k
    · exact hp.1.2
    · exact hp.2
  obtain ⟨y,hy,ha,hcell⟩ := C.marginPolygon_lift hr.2 t u p hpM
  have hzero : ∀ k, realCoordinate z k=0 → 0 < realCoordinate y k := by
    intro k hk
    have h := hpG k
    simp only [inwardGate,hk,ite_eq_left] at h
    have hd := (C.positiveDecision_planar hr t u (axisDirection k) (hnearB k (Or.inl hk)) p y hy
      (fun k => ⟨(hcell k).1.le,(hcell k).2.le⟩)).mp h
    rw [integralCutForm_axis,hboundary k (Or.inl hk),hk] at hd
    have haxis : cutForm a (axisDirection k) y=realCoordinate y k := by fin_cases k <;> rfl
    rw [haxis] at hd
    apply lt_of_le_of_ne hd
    intro he
    have hn := ha (axisDirection k) 0
    simp only [map_zero,haxis] at hn
    exact hn he.symm
  have hone : ∀ k, realCoordinate z k=1 → realCoordinate y k<1 := by
    intro k hk
    have h := hpG k
    have hn : realCoordinate z k≠0 := by rw [hk]; norm_num
    simp only [inwardGate,ite_eq_right hn,ite_eq_left hk] at h
    have hd := (not_congr (C.positiveDecision_planar hr t u (axisDirection k) (hnearB k (Or.inr hk)) p y hy
      (fun k => ⟨(hcell k).1.le,(hcell k).2.le⟩))).mp h
    rw [integralCutForm_axis,hboundary k (Or.inr hk),hk] at hd
    have haxis : cutForm a (axisDirection k) y=realCoordinate y k := by fin_cases k <;> rfl
    rw [haxis] at hd
    exact lt_of_not_ge hd
  let σ := polygonAssignment (fun i => C.localDecision t u z (j i) (c i)) p
  have hactive : ∀ i, cutForm a (j i) z=ordinary (c i) →
      if σ i then cutForm a (j i) y<ordinary (c i)
      else ordinary (c i) < cutForm a (j i) y := by
    intro i hi
    have hd := C.positiveDecision_planar hr t u (j i) (hnear i hi) p y hy
      (fun k => ⟨(hcell k).1.le,(hcell k).2.le⟩)
    rw [hline i hi] at hd
    have hσ : σ i=decide (¬ordinary (c i) ≤ cutForm a (j i) y) := by
      apply decide_eq_decide.mpr
      change (p ∈ (C.localDecision t u z (j i) (c i)).val) ↔ _
      simp only [localDecision,ite_eq_left hi]
      exact not_congr hd
    rw [hσ]
    split_ifs with h
    · exact lt_of_not_ge (of_decide_eq_true h)
    · have hh := of_decide_eq_false (Bool.eq_false_iff.mpr h)
      exact lt_of_le_of_ne (not_not.mp hh) (ha (j i) (c i)).symm
  have hinactive : ∀ i, cutForm a (j i) z≠ordinary (c i) →
      if σ i then cutForm a (j i) z<ordinary (c i)
      else ordinary (c i) < cutForm a (j i) z := by
    intro i hi
    by_cases hlt : cutForm a (j i) z<ordinary (c i)
    · simp [σ,polygonAssignment,localDecision,hi,hlt]
    · simp only [σ,polygonAssignment,localDecision,ite_eq_right hi,ite_eq_right hlt]
      simpa using lt_of_le_of_ne (le_of_not_gt hlt) hi.symm
  obtain ⟨q,hq,hassign⟩ := finite_arrangement_germ_inward a j (fun i => ordinary (c i))
    z y σ hz₁ hz₂ hzero hone hactive hinactive N hN hz
  refine ⟨q,hq,?_⟩
  funext i
  change decide (cutForm a (j i) q.val<ordinary (c i))=σ i
  have hi := hassign i
  cases he : σ i
  · simp only [he,Bool.false_eq_true,↓reduceIte] at hi
    exact decide_eq_false (not_lt_of_gt hi)
  · simp only [he,↓reduceIte] at hi
    exact decide_eq_true hi

end ConcurrentGeometry
end ConcurrentInwardModel

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_InactiveNeighborhoodActions
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement

namespace ConcurrentGeometry
variable {a : ℕ} {r : CutRing} (C : ConcurrentGeometry a r) {ι : Type*}

namespace InwardChart
variable {C} {j : ι → Fin 4} {c : ι → CutRing} {z : ℝ × ℝ} (T : C.InwardChart j c z)
theorem active_anchor : C.InwardChartAnchor T.vertex T.offset j c z := T.property.2.1
theorem active_bound : C.InwardChartBound T.vertex T.offset j c z := T.property.2.2.1
theorem boundary_anchor : C.InwardChartBoundaryAnchor T.vertex T.offset z := T.property.2.2.2.1
theorem boundary_bound : C.InwardChartBoundaryBound T.vertex T.offset z := T.property.2.2.2.2
end InwardChart

namespace InwardChart
variable {C} {j : ι → Fin 4} {c : ι → CutRing} {z : ℝ × ℝ} (T : C.InwardChart j c z)

theorem assignment_realized [Finite ι] (hr : 0<ordinary r ∧ ordinary r<1/2)
    (hz₁ : z.1 ∈ Set.Icc (0:ℝ) 1) (hz₂ : z.2 ∈ Set.Icc (0:ℝ) 1)
    (p : GenericSquare a) (hp : p ∈ (C.inwardMargin T.vertex T.offset z).val)
    (N : Set (ℝ × ℝ)) (hN : IsOpen N) (hz : z ∈ N) :
    ∃ q : GenericSquare a, q.val ∈ N ∧
      polygonAssignment (fun i => cutPolygon a (j i) (c i)) q=
        polygonAssignment (fun i => C.localDecision T.vertex T.offset z (j i) (c i)) p :=
  C.localDecision_assignment_realized hr T.vertex T.offset j c z hz₁ hz₂
    T.active_anchor T.boundary_anchor T.active_bound T.boundary_bound p hp N hN hz

end InwardChart
end ConcurrentGeometry

end SimpleAmenable

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_ClippedGerms
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
section ClippedGerms

namespace ClippedGerm
variable {a : ℕ} {r : CutRing} {slope : Fin 4} {u : CutRing × CutRing} {z : ℝ × ℝ}
    (G : ClippedGerm a r slope u z)

theorem model_formula {ι : Type*} [Finite ι] {C : ConcurrentGeometry a r}
    {j : ι → Fin 4} {c : ι → CutRing}
    (T : C.InwardChart j c z) (hr : 0<ordinary r ∧ ordinary r<1/2)
    (hz₁ : z.1 ∈ Set.Icc (0:ℝ) 1) (hz₂ : z.2 ∈ Set.Icc (0:ℝ) 1)
    (lo hi : Fin 2 → ι) (s : ι)
    (hlo : ∀ d, j (lo d)=axisDirection d ∧ c (lo d)=pointCoordinate G.offset d-r)
    (hhi : ∀ d, j (hi d)=axisDirection d ∧ c (hi d)=pointCoordinate G.offset d+r)
    (hs : j s=slope ∧ c s=integralCutForm a slope G.offset)
    (hR : ResolvedBy (fun i => halfPlane a (j i) (c i))
      (spatialTranslate u (clippedSlopePrimitive a r slope)).val)
    (p : GenericSquare a) (hp : p ∈ (C.inwardMargin T.vertex T.offset z).val) :
    p ∈ (T.polygons (fun _ : Unit => spatialTranslate u (clippedSlopePrimitive a r slope)) ()).val ↔
      (∀ d, p ∉ (C.localDecision T.vertex T.offset z (j (lo d)) (c (lo d))).val ∧
        p ∈ (C.localDecision T.vertex T.offset z (j (hi d)) (c (hi d))).val) ∧
      p ∉ (C.localDecision T.vertex T.offset z (j s) (c s)).val := by
  obtain ⟨q,hq,he⟩ := T.assignment_realized hr hz₁ hz₂ p hp
    (Metric.ball z G.radius) Metric.isOpen_ball (Metric.mem_ball_self G.radius_pos)
  have hd (i : ι) : q ∈ (cutPolygon a (j i) (c i)).val ↔
      p ∈ (C.localDecision T.vertex T.offset z (j i) (c i)).val := by
    simpa only [polygonAssignment,decide_eq_true_eq] using Bool.eq_iff_iff.mp (congrFun he i)
  have hmodel : p ∈ (T.polygons (fun _ : Unit => spatialTranslate u (clippedSlopePrimitive a r slope)) ()).val ↔
      q ∈ (spatialTranslate u (clippedSlopePrimitive a r slope)).val := by
    change polygonAssignment (fun i => C.localDecision T.vertex T.offset z (j i) (c i)) p ∈
      polygonFormalMask (fun i => cutPolygon a (j i) (c i)) _ ↔ _
    rw [← he]
    exact polygonFormalMask_mem _ _ hR q
  rw [hmodel,G.valid q hq]
  apply and_congr
  · apply forall_congr'
    intro d
    apply and_congr
    · simpa only [cutPolygon,halfPlane,Set.mem_ofPred_eq,(hlo d).1,(hlo d).2,cutForm_axis,not_lt,offset]
        using not_congr (hd (lo d))
    · simpa only [cutPolygon,halfPlane,Set.mem_ofPred_eq,(hhi d).1,(hhi d).2,cutForm_axis,offset]
        using hd (hi d)
  · simpa only [cutPolygon,halfPlane,Set.mem_ofPred_eq,hs.1,hs.2,not_lt,offset] using not_congr (hd s)

end ClippedGerm
end ClippedGerms

namespace ClippedGerm
variable {a : ℕ} {r : CutRing} {slope : Fin 4} {u : CutRing × CutRing} {z : ℝ × ℝ}
    (G : ClippedGerm a r slope u z)

theorem model_restrict_gate_oai {ι : Type*} [Finite ι] {C : ConcurrentGeometry a r}
    {j : ι → Fin 4} {c : ι → CutRing}
    (T : C.InwardChart j c z) (hr : 0<ordinary r ∧ ordinary r<1/2)
    (hz₁ : z.1 ∈ Set.Icc (0:ℝ) 1) (hz₂ : z.2 ∈ Set.Icc (0:ℝ) 1)
    (lo hi : Fin 2 → ι) (s : ι)
    (hlo : ∀ d, j (lo d)=axisDirection d ∧ c (lo d)=pointCoordinate G.offset d-r)
    (hhi : ∀ d, j (hi d)=axisDirection d ∧ c (hi d)=pointCoordinate G.offset d+r)
    (hs : j s=slope ∧ c s=integralCutForm a slope G.offset)
    (hR : ResolvedBy (fun i => halfPlane a (j i) (c i))
      (spatialTranslate u (clippedSlopePrimitive a r slope)).val)
    (σ : Fin 2 × Bool → Bool) :
    T.polygons (fun _ : Unit => spatialTranslate u (clippedSlopePrimitive a r slope)) () ⊓
      C.coordinateGate T.vertex T.offset z Prod.fst G.axialCut σ =
    (if ∀ d, σ (d,false)=false ∧ σ (d,true)=true then
      (C.localDecision T.vertex T.offset z (j s) (c s))ᶜ else ⊥) ⊓
      C.coordinateGate T.vertex T.offset z Prod.fst G.axialCut σ := by
  classical
  apply Subtype.ext
  ext p
  by_cases hgate : p ∈ (C.coordinateGate T.vertex T.offset z Prod.fst G.axialCut σ).val
  · have hmargin := hgate.1
    have hassign := hgate.2
    have hlo' (d : Fin 2) : p ∉ (C.localDecision T.vertex T.offset z (j (lo d)) (c (lo d))).val ↔
        σ (d,false)=false := by
      have he := congrFun hassign (d,false)
      simpa only [polygonAssignment,axialCut,Bool.false_eq_true,↓reduceIte,Prod.fst,
        (hlo d).1,(hlo d).2,decide_eq_false_iff_not] using (congrArg (fun b => b=false) he).to_iff
    have hhi' (d : Fin 2) : p ∈ (C.localDecision T.vertex T.offset z (j (hi d)) (c (hi d))).val ↔
        σ (d,true)=true := by
      have he := congrFun hassign (d,true)
      simpa only [polygonAssignment,axialCut,↓reduceIte,Prod.fst,
        (hhi d).1,(hhi d).2,decide_eq_true_eq] using (congrArg (fun b => b=true) he).to_iff
    have he := G.model_formula T hr hz₁ hz₂ lo hi s hlo hhi hs hR p hmargin
    have hc : (∀ d, p ∉ (C.localDecision T.vertex T.offset z (j (lo d)) (c (lo d))).val ∧
        p ∈ (C.localDecision T.vertex T.offset z (j (hi d)) (c (hi d))).val) ↔
        ∀ d, σ (d,false)=false ∧ σ (d,true)=true :=
      forall_congr' (fun d => and_congr (hlo' d) (hhi' d))
    change (_ ∧ _) ↔ (_ ∧ _)
    simp only [hgate,and_true]
    rw [he,hc]
    split_ifs with HH <;> simp only [HH,forall_const,true_and,false_and] <;> rfl
  · change (_ ∧ _) ↔ (_ ∧ _)
    simp only [hgate,and_false]

end ClippedGerm

end SimpleAmenable

end OAI
end

theorem solution.{u_1} : type_of% @OAI.SimpleAmenable.ClippedGerm.model_restrict_gate_oai.{u_1} := @OAI.SimpleAmenable.ClippedGerm.model_restrict_gate_oai.{u_1}
