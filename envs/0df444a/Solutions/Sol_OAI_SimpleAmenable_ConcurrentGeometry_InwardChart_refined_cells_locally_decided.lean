-- Prove2me | solution 1 for OAI.SimpleAmenable.ConcurrentGeometry.InwardChart.refined_cells_locally_decided
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T04:41:47.38198+00:00
-- url     : https://prove2.me/submissions/049994ee-413a-4444-9a21-8ae801ac9874

import Mathlib
import Definitions.Def_OAIQ65Sa014

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_LocalArrangementAssignments
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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

theorem localCutFamily_locally_eq [Finite κ]
    (j : κ → Fin 4) (c : κ → CutRing) (z : ℝ × ℝ) :
    ∃ N : Set (ℝ × ℝ), IsOpen N ∧ z ∈ N ∧
      ∀ p : GenericSquare a, p.val ∈ N →
        polygonAssignment (localCutFamily j c z) p=
          polygonAssignment (fun k => cutPolygon a (j k) (c k)) p := by
  classical
  let N : Set (ℝ × ℝ) := ⋂ k,
    if cutForm a (j k) z=ordinary (c k) then Set.univ
    else if cutForm a (j k) z<ordinary (c k)
    then {p | cutForm a (j k) p<ordinary (c k)}
    else {p | ordinary (c k) < cutForm a (j k) p}
  refine ⟨N,?_,?_,?_⟩
  · apply isOpen_iInter_of_finite
    intro k
    split_ifs
    · exact isOpen_univ
    · exact isOpen_lt (cutForm_continuous a (j k)) continuous_const
    · exact isOpen_lt continuous_const (cutForm_continuous a (j k))
  · apply Set.mem_iInter.mpr
    intro k
    by_cases he : cutForm a (j k) z=ordinary (c k)
    · rw [ite_eq_left he]; trivial
    · rw [ite_eq_right he]
      by_cases hl : cutForm a (j k) z<ordinary (c k)
      · rw [ite_eq_left hl]; exact hl
      · rw [ite_eq_right hl]; exact lt_of_le_of_ne (le_of_not_gt hl) (Ne.symm he)
  · intro p hp
    funext k
    have hk := Set.mem_iInter.mp hp k
    by_cases he : cutForm a (j k) z=ordinary (c k)
    · simp [polygonAssignment,localCutFamily,he]
    · by_cases hl : cutForm a (j k) z<ordinary (c k)
      · simp only [ite_eq_right he,ite_eq_left hl,Set.mem_ofPred_eq] at hk
        simp [polygonAssignment,localCutFamily,he,hl,cutPolygon,halfPlane,hk]
      · simp only [ite_eq_right he,ite_eq_right hl,Set.mem_ofPred_eq] at hk
        simp [polygonAssignment,localCutFamily,he,hl,cutPolygon,halfPlane,not_lt_of_gt hk]

end LocalBooleanAssignments

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_SpatialChartGeometry
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_FiniteRefiningGrid
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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

section RefinementPartition

theorem coordinateInterval_mem_preferred {a : ℕ} (j : Fin 2) (u v : CutRing)
    (hlo : 0≤ordinary u) (huv : ordinary u≤ordinary v) (hup : ordinary v≤1)
    (hlen : ordinary v-ordinary u<1) (p : GenericSquare a) :
    p ∈ (coordinateInterval a j u v).val ↔
      ordinary u ≤ coordinate j p ∧ coordinate j p<ordinary v := by
  change p ∈ coordinateBetween a j u v ↔ _
  rw [mem_coordinateBetween_iff j u v huv hlen p]
  constructor
  · rintro ⟨k,hk,hk'⟩
    have hp := coordinate_bounds j p
    have hk₁ : (-1:ℝ)<k := by linarith [hp.2]
    have hk₂ : (k:ℝ)<1 := by linarith [hp.1]
    have hk₁' : (-1:ℤ)<k := by exact_mod_cast hk₁
    have hk₂' : k<(1:ℤ) := by exact_mod_cast hk₂
    have hk0 : k=0 := by omega
    simpa only [hk0,Int.cast_zero,add_zero] using And.intro hk hk'
  · exact fun h => ⟨0,by simpa using h.1,by simpa using h.2⟩

theorem refinedGridRectangle_mem {a N : ℕ} (e : Fin (N+1) → CutRing)
    (he : StrictMono (fun i => ordinary (e i))) (hzero : e 0=0) (hlast : e (Fin.last N)=1)
    (hmesh : ∀ i : Fin N, ordinary (e i.succ)-ordinary (e i.castSucc)<1)
    (cell : Fin 2 → Fin N) (p : GenericSquare a) :
    p ∈ (refinedGridRectangle a N e cell).val ↔ ∀ j : Fin 2,
      ordinary (e (cell j).castSucc) ≤ coordinate j p ∧ coordinate j p<ordinary (e (cell j).succ) := by
  have h (j : Fin 2) := coordinateInterval_mem_preferred j (e (cell j).castSucc) (e (cell j).succ)
    (by have hh := he.monotone (Fin.zero_le (cell j).castSucc); simpa only [hzero,map_zero] using hh)
    (he (Fin.castSucc_lt_succ (i := cell j))).le
    (by have hh := he.monotone (Fin.le_last (cell j).succ); simpa only [hlast,map_one] using hh)
    (hmesh (cell j)) p
  change (p ∈ (coordinateInterval a 0 _ _).val ∧ p ∈ (coordinateInterval a 1 _ _).val) ↔ _
  rw [h 0,h 1,Fin.forall_fin_two]

end RefinementPartition

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_LocalChartDecisions
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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

end ConcurrentGeometry
end ConcurrentPositiveDecisions

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_InwardMargins
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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
section InwardMargins
namespace ConcurrentGeometry
variable {a : ℕ} {r : CutRing} (C : ConcurrentGeometry a r)

theorem mem_marginPolygon_of_planar (hr : ordinary r<1/2)
    (t : VertexType (commonVertexDenominator a)) (u : CutRing × CutRing)
    (p : GenericSquare a) (y : ℝ × ℝ) (hy : p.val=(Int.fract y.1,Int.fract y.2))
    (hcell : ∀ k, ordinary ((C.margins t).lower k+pointCoordinate u k) ≤ realCoordinate y k ∧
      realCoordinate y k<ordinary ((C.margins t).upper k+pointCoordinate u k)) :
    p ∈ (C.marginPolygon t u).val := by
  have hw (k) := (C.margins t).width C.positive k
  have hlen (k) : ordinary ((C.margins t).upper k+pointCoordinate u k)-
      ordinary ((C.margins t).lower k+pointCoordinate u k)<1 := by
    simp only [map_add]
    linarith [hw k,C.radius]
  have hle (k) : ordinary ((C.margins t).lower k+pointCoordinate u k) ≤
      ordinary ((C.margins t).upper k+pointCoordinate u k) := by
    simp only [map_add]
    linarith [hw k]
  have hh (k) : p ∈ coordinateBetween a k
      ((C.margins t).lower k+pointCoordinate u k)
      ((C.margins t).upper k+pointCoordinate u k) := by
    rw [mem_coordinateBetween_iff k _ _ (hle k) (hlen k)]
    refine ⟨⌊realCoordinate y k⌋,?_⟩
    have he : coordinate k p+(⌊realCoordinate y k⌋:ℤ)=realCoordinate y k := by
      have h := congrArg (fun q : ℝ × ℝ => realCoordinate q k) hy
      have hh : coordinate k p=Int.fract (realCoordinate y k) := by fin_cases k <;> exact h
      rw [hh]
      exact sub_add_cancel _ _
    rw [he]
    exact hcell k
  change p ∈ (spatialTranslate u (coordinateRectangle a (C.margins t).lower (C.margins t).upper)).val
  rw [spatialTranslate_coordinateRectangle]
  exact ⟨hh 0,hh 1⟩

theorem mem_inwardMargin_of_planar (hr : 0<ordinary r ∧ ordinary r<1/2)
    (t : VertexType (commonVertexDenominator a)) (u : CutRing × CutRing)
    (z : ℝ × ℝ)
    (hboundary : ∀ k, realCoordinate z k=0 ∨ realCoordinate z k=1 →
      ordinary (pointCoordinate (u+C.anchors t (axisDirection k)) k)=realCoordinate z k)
    (hnearB : ∀ d, realCoordinate z d=0 ∨ realCoordinate z d=1 → ∀ y : ℝ × ℝ,
      (∀ k, ordinary ((C.margins t).lower k+pointCoordinate u k) ≤ realCoordinate y k ∧
        realCoordinate y k≤ordinary ((C.margins t).upper k+pointCoordinate u k)) →
      ∀ k, |realCoordinate y k-ordinary (pointCoordinate (u+C.anchors t (axisDirection d)) k)|<3*C.epsilon)
    (p : GenericSquare a)
    (hcell : ∀ k, ordinary ((C.margins t).lower k+pointCoordinate u k) ≤ realCoordinate p.val k ∧
      realCoordinate p.val k<ordinary ((C.margins t).upper k+pointCoordinate u k)) :
    p ∈ (C.inwardMargin t u z).val := by
  have hy : p.val=(Int.fract p.val.1,Int.fract p.val.2) := by
    rw [Int.fract_eq_self.mpr p.property.1,Int.fract_eq_self.mpr p.property.2.1]
  have hpM := C.mem_marginPolygon_of_planar hr.2 t u p p.val hy hcell
  have hgate k : p ∈ (C.inwardGate t u z k).val := by
    by_cases hzero : realCoordinate z k=0
    · simp only [inwardGate,ite_eq_left hzero]
      have hd := C.positiveDecision_planar hr t u (axisDirection k)
        (hnearB k (Or.inl hzero)) p p.val hy (fun k => ⟨(hcell k).1,(hcell k).2.le⟩)
      rw [integralCutForm_axis,hboundary k (Or.inl hzero),hzero] at hd
      apply hd.mpr
      have haxis : cutForm a (axisDirection k) p.val=coordinate k p := by fin_cases k <;> rfl
      rw [haxis]
      exact (coordinate_bounds k p).1
    · by_cases hone : realCoordinate z k=1
      · simp only [inwardGate,ite_eq_right hzero,ite_eq_left hone]
        have hd := C.positiveDecision_planar hr t u (axisDirection k)
          (hnearB k (Or.inr hone)) p p.val hy (fun k => ⟨(hcell k).1,(hcell k).2.le⟩)
        rw [integralCutForm_axis,hboundary k (Or.inr hone),hone] at hd
        apply (not_congr hd).mpr
        have haxis : cutForm a (axisDirection k) p.val=coordinate k p := by fin_cases k <;> rfl
        rw [haxis]
        exact not_le_of_gt (coordinate_bounds k p).2
      · simp [inwardGate,hzero,hone,wholePolygon]
  exact ⟨⟨hpM,hgate 0⟩,hgate 1⟩

end ConcurrentGeometry
end InwardMargins

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_InactiveNeighborhoodActions
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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
theorem neighborhood : C.InwardChartNeighborhood T.vertex T.offset z := T.property.1
theorem active_anchor : C.InwardChartAnchor T.vertex T.offset j c z := T.property.2.1
theorem active_bound : C.InwardChartBound T.vertex T.offset j c z := T.property.2.2.1
theorem boundary_anchor : C.InwardChartBoundaryAnchor T.vertex T.offset z := T.property.2.2.2.1
theorem boundary_bound : C.InwardChartBoundaryBound T.vertex T.offset z := T.property.2.2.2.2
end InwardChart

namespace InwardChart
variable {C} {j : ι → Fin 4} {c : ι → CutRing} {z : ℝ × ℝ} (T : C.InwardChart j c z)

theorem canonical_mem (hr : 0<ordinary r ∧ ordinary r<1/2)
    (p : GenericSquare a) (hp : dist p.val z<C.epsilon/2) :
    p ∈ (C.inwardMargin T.vertex T.offset z).val :=
  C.mem_inwardMargin_of_planar hr T.vertex T.offset z T.boundary_anchor T.boundary_bound p
    (fun k => ⟨(T.neighborhood p.val hp k).1.le,(T.neighborhood p.val hp k).2⟩)

theorem local_decisions_eq (hr : 0<ordinary r ∧ ordinary r<1/2)
    (p : GenericSquare a) (hp : dist p.val z<C.epsilon/2) :
    polygonAssignment (fun i => C.localDecision T.vertex T.offset z (j i) (c i)) p=
      polygonAssignment (localCutFamily j c z) p := by
  classical
  have hy : p.val=(Int.fract p.val.1,Int.fract p.val.2) := by
    rw [Int.fract_eq_self.mpr p.property.1,Int.fract_eq_self.mpr p.property.2.1]
  have hcell k := (T.neighborhood p.val hp k).imp le_of_lt le_of_lt
  funext i
  apply decide_eq_decide.mpr
  by_cases hi : cutForm a (j i) z=ordinary (c i)
  · have hd := C.positiveDecision_planar hr T.vertex T.offset (j i) (T.active_bound i hi) p p.val hy hcell
    rw [T.active_anchor i hi] at hd
    simp only [localDecision,localCutFamily,ite_eq_left hi]
    change (p ∉ (C.positiveDecision T.vertex T.offset (j i)).val) ↔ cutForm a (j i) p.val<ordinary (c i)
    exact (not_congr hd).trans not_le
  · simp only [localDecision,localCutFamily,ite_eq_right hi]

end InwardChart
end ConcurrentGeometry

end SimpleAmenable

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_LocalClippedBoxFormula
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement

namespace ConcurrentGeometry.InwardChart
variable {a : ℕ} {r : CutRing} {C : ConcurrentGeometry a r} {ι : Type*} [Finite ι]
    {j : ι → Fin 4} {c : ι → CutRing} {z : ℝ × ℝ} (T : C.InwardChart j c z)

theorem decisions_locally_eq (hr : 0<ordinary r ∧ ordinary r<1/2) :
    ∃ O : Set (ℝ × ℝ), IsOpen O ∧ z ∈ O ∧ ∀ p : GenericSquare a, p.val ∈ O →
      p ∈ (C.inwardMargin T.vertex T.offset z).val ∧
      ∀ i, p ∈ (C.localDecision T.vertex T.offset z (j i) (c i)).val ↔
        p ∈ (cutPolygon a (j i) (c i)).val := by
  obtain ⟨N,hN,hz,hlocal⟩ := localCutFamily_locally_eq j c z
  refine ⟨N ∩ Metric.ball z (C.epsilon/2),hN.inter Metric.isOpen_ball,
    ⟨hz,Metric.mem_ball_self (by linarith [C.positive])⟩,?_⟩
  intro p hp
  refine ⟨T.canonical_mem hr p hp.2,fun i => ?_⟩
  have he := (T.local_decisions_eq hr p hp.2).trans (hlocal p hp.1)
  simpa only [polygonAssignment,decide_eq_true_eq] using Bool.eq_iff_iff.mp (congrFun he i)

end ConcurrentGeometry.InwardChart

end SimpleAmenable

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_RefinedLocalDecisions
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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
section RefinedLocalDecisions

theorem refinedGridRectangle_point_near {a N : ℕ} (e : Fin (N+1) → CutRing)
    (he : StrictMono (fun i => ordinary (e i))) (hzero : e 0=0) (hlast : e (Fin.last N)=1)
    (hmesh : ∀ i : Fin N, ordinary (e i.succ)-ordinary (e i.castSucc)<1)
    (cell : Fin 2 → Fin N) (z : ℝ × ℝ) (δ : ℝ)
    (hnear : ∀ k, |ordinary (e (cell k).castSucc)-realCoordinate z k|<δ ∧
      |ordinary (e (cell k).succ)-realCoordinate z k|<δ)
    (p : GenericSquare a) (hp : p ∈ (refinedGridRectangle a N e cell).val) : dist p.val z<δ := by
  have hb := (refinedGridRectangle_mem e he hzero hlast hmesh cell p).mp hp
  have hd (k : Fin 2) : |realCoordinate p.val k-realCoordinate z k|<δ := by
    have hl := (abs_lt.mp (hnear k).1).1
    have hr := (abs_lt.mp (hnear k).2).2
    have hk := hb k
    change ordinary (e (cell k).castSucc) ≤ realCoordinate p.val k ∧
      realCoordinate p.val k<ordinary (e (cell k).succ) at hk
    rw [abs_lt]
    constructor <;> linarith [hk.1,hk.2]
  rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq,max_lt_iff]
  exact ⟨hd 0,hd 1⟩

namespace ConcurrentGeometry.InwardChart
variable {a : ℕ} {r : CutRing} {C : ConcurrentGeometry a r} {ι : Type*} [Finite ι]
    {j : ι → Fin 4} {c : ι → CutRing} {z : ℝ × ℝ} (T : C.InwardChart j c z)

theorem refined_cells_locally_decided_oai (hr : 0<ordinary r ∧ ordinary r<1/2) :
    ∃ δ : ℝ, 0<δ ∧ ∀ (N : ℕ) (e : Fin (N+1) → CutRing),
    StrictMono (fun i => ordinary (e i)) → e 0=0 → e (Fin.last N)=1 →
    (∀ i : Fin N, ordinary (e i.succ)-ordinary (e i.castSucc)<1) →
    ∀ cell : Fin 2 → Fin N,
    (∀ k, |ordinary (e (cell k).castSucc)-realCoordinate z k|<δ ∧
      |ordinary (e (cell k).succ)-realCoordinate z k|<δ) →
    ∀ p : GenericSquare a, p ∈ (refinedGridRectangle a N e cell).val →
      p ∈ (C.inwardMargin T.vertex T.offset z).val ∧
      ∀ i, p ∈ (C.localDecision T.vertex T.offset z (j i) (c i)).val ↔
        p ∈ (cutPolygon a (j i) (c i)).val := by
  obtain ⟨O,hO,hz,hlocal⟩ := T.decisions_locally_eq hr
  obtain ⟨δ,hδ,hball⟩ := Metric.isOpen_iff.mp hO z hz
  refine ⟨δ,hδ,?_⟩
  intro N e he hzero hlast hmesh cell hnear p hp
  exact hlocal p (hball (refinedGridRectangle_point_near e he hzero hlast hmesh cell z δ hnear p hp))

end ConcurrentGeometry.InwardChart
end RefinedLocalDecisions

end SimpleAmenable
end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.SimpleAmenable.ConcurrentGeometry.InwardChart.refined_cells_locally_decided_oai.{u_1} := @OAI.SimpleAmenable.ConcurrentGeometry.InwardChart.refined_cells_locally_decided_oai.{u_1}
