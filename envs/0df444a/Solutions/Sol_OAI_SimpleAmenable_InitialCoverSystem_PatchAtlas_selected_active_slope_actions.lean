-- Prove2me | solution 1 for OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.selected_active_slope_actions
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T05:01:12.812489+00:00
-- url     : https://prove2.me/submissions/a6b435be-f5c0-4833-87bb-107b39d4323d

import Mathlib
import Definitions.Def_OAIQ65Sa015
import Theorems.Thm_OAI_SimpleAmenable_InitialCoverSystem_RectangularAtlas_slope_line_action

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_InactiveNeighborhoodActions
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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
end InwardChart

end ConcurrentGeometry

end SimpleAmenable

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_SelectedInwardActions
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.BankEmbedding.instCoeFunForallPointTrackPoint _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonPlacement.Configuration.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.PolygonPlacement.instCoeFunForallGenericSquareTrackPoint _root_.OAI.SimpleAmenable.PolygonPlacement.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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
section SelectedInwardActions
namespace InitialCoverSystem.PatchAtlas
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    {B : InitialCoverSystem a r m hm M}
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (A : B.PatchAtlas) {ι : Type*}

theorem selected_active_slope_actions_oai
    (hlarge : 20 ≤ m+1) (hr : 0<ordinary r ∧ ordinary r<1/2)
    {j : ι → Fin 4} {c : ι → CutRing} {z : ℝ × ℝ}
    (T : A.geometry.InwardChart j c z) (i : ι)
    (hi : cutForm a (j i) z=ordinary (c i))
    (d : Fin 2) (hd : j i=slopeDirection d) (v : CutRing × CutRing)
    (hv : integralCutForm a (slopeDirection d) v=c i)
    (L V : Fin 2 → CutRing)
    (hLV : ∀ k, ordinary (L k)≤ordinary (V k))
    (hclip : ∀ k, -ordinary r≤ordinary (L k)-ordinary (pointCoordinate v k) ∧
      ordinary (V k)-ordinary (pointCoordinate v k)≤ordinary r)
    (hnear : ∀ k, |ordinary (L k)-realCoordinate z k|<A.geometry.epsilon/2 ∧
      |ordinary (V k)-realCoordinate z k|<A.geometry.epsilon/2)
    (n : ℕ) (q : Fin 2 → ℤ)
    (hW : ResolvedBy (fun e => (primitiveTests (a := a) (r := r)
      (coordinateWindowPrimitives n q) e).val) (coordinateRectangle a L V).val)
    (f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm))
    (hf : B.AlignedSmallSupported f)
    (hc : SmallControlled B.c f (B.windowSector (by omega) n (A.rectangles.rectangles n) q
      (coordinateRectangle a L V)))
    (I : ControlAlphabet (Fin (m+1))) (s : UniversalExtension (alternatingGroup I.val))
    (b : BoundedRelationCover M (alternatingGenerator a r m hm)) (hb : b ∈ f.range) :
      A.rectangles.slope (by omega) d v (universalMap (subtypeAlternatingHom I.val) s)*b*
        (A.rectangles.slope (by omega) d v (universalMap (subtypeAlternatingHom I.val) s))⁻¹ =
      A.rectangles.slope (by omega) d (T.offset+A.geometry.anchors T.vertex (j i))
          (universalMap (subtypeAlternatingHom I.val) s)*b*
        (A.rectangles.slope (by omega) d (T.offset+A.geometry.anchors T.vertex (j i))
          (universalMap (subtypeAlternatingHom I.val) s))⁻¹ := by
  have hLdist : dist (ordinary (L 0),ordinary (L 1)) z < A.geometry.epsilon/2 := by
    rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq,max_lt_iff]
    exact ⟨(hnear 0).1,(hnear 1).1⟩
  have hVdist : dist (ordinary (V 0),ordinary (V 1)) z < A.geometry.epsilon/2 := by
    rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq,max_lt_iff]
    exact ⟨(hnear 0).2,(hnear 1).2⟩
  have hclip' : ∀ k, -ordinary r ≤ ordinary (L k)-ordinary (pointCoordinate (T.offset+A.geometry.anchors T.vertex (j i)) k) ∧
      ordinary (V k)-ordinary (pointCoordinate (T.offset+A.geometry.anchors T.vertex (j i)) k) ≤ ordinary r := by
    intro k
    have hL := (T.active_bound i hi) (ordinary (L 0),ordinary (L 1))
      (fun l => (T.neighborhood _ hLdist l).imp le_of_lt le_of_lt) k
    have hV := (T.active_bound i hi) (ordinary (V 0),ordinary (V 1))
      (fun l => (T.neighborhood _ hVdist l).imp le_of_lt le_of_lt) k
    have heL : realCoordinate (ordinary (L 0),ordinary (L 1)) k=ordinary (L k) := by fin_cases k <;> rfl
    have heV : realCoordinate (ordinary (V 0),ordinary (V 1)) k=ordinary (V k) := by fin_cases k <;> rfl
    rw [heL] at hL
    rw [heV] at hV
    have hL' := (abs_lt.mp hL).1
    have hV' := (abs_lt.mp hV).2
    have hrad := A.geometry.radius
    have hpos := A.geometry.positive
    constructor <;> linarith
  have hline : integralCutForm a (slopeDirection d) v=
      integralCutForm a (slopeDirection d) (T.offset+A.geometry.anchors T.vertex (j i)) := by
    rw [hv,← hd,(T.active_anchor i hi)]
  have hz : cutForm a (slopeDirection d) z=ordinary (integralCutForm a (slopeDirection d) v) := by
    rw [hv,← hd]; exact hi
  have hnear' : ∀ k, |ordinary (L k)-realCoordinate z k| ≤ ordinary r/4 ∧
      |ordinary (V k)-realCoordinate z k| ≤ ordinary r/4 := by
    intro k
    have hh := hnear k
    have hrad := A.geometry.radius
    have hpos := A.geometry.positive
    constructor <;> linarith
  exact A.rectangles.slope_line_action hlarge hr d v (T.offset+A.geometry.anchors T.vertex (j i)) hline L V hLV
    hclip hclip' z hz hnear' n q hW f hf hc I s b hb

end InitialCoverSystem.PatchAtlas
end SelectedInwardActions

end SimpleAmenable
end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.selected_active_slope_actions_oai.{u_1} := @OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.selected_active_slope_actions_oai.{u_1}
