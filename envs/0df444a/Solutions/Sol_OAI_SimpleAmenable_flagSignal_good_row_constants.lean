-- Prove2me | solution 1 for OAI.SimpleAmenable.flagSignal_good_row_constants
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T04:48:44.951221+00:00
-- url     : https://prove2.me/submissions/3e6c0f5b-b8e8-4619-af24-78451fc5216a

import Mathlib
import Definitions.Def_OAIQ65Sa014
import Theorems.Thm_OAI_SimpleAmenable_flagAveragingMatrix_good_row_error

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_WindowRectangles
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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

section CellLineIntersections

theorem linear_form_dist_bound (A B : ℝ) (x y : ℝ × ℝ) :
    |(A*x.1+B*x.2)-(A*y.1+B*y.2)| ≤ (|A|+|B|)*dist x y := by
  have hx : |x.1-y.1| ≤ dist x y := by
    rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq]
    exact le_max_left _ _
  have hy : |x.2-y.2| ≤ dist x y := by
    rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq]
    exact le_max_right _ _
  calc
    _ = |A*(x.1-y.1)+B*(x.2-y.2)| := by congr 1; ring
    _ ≤ |A*(x.1-y.1)|+|B*(x.2-y.2)| := abs_add_le _ _
    _ ≤ |A| *dist x y+|B| *dist x y := by
      rw [abs_mul,abs_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left hx (abs_nonneg _))
        (mul_le_mul_of_nonneg_left hy (abs_nonneg _))
    _ = _ := by ring

end CellLineIntersections

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_FinePatchAtlas
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

section FarGridActions

theorem cutForm_dist_bound (a : ℕ) (j : Fin 4) (x y : ℝ × ℝ) :
    |cutForm a j x-cutForm a j y| ≤ (1+|ordinary (cutTau^a)|)*dist x y := by
  have hc : 0 ≤ |ordinary (cutTau^a)| *dist x y := mul_nonneg (abs_nonneg _) dist_nonneg
  have hslope : ordinary (cutTau^a)=Real.goldenRatio^a := by simp
  fin_cases j
  · have h := linear_form_dist_bound 1 0 x y
    simp only [one_mul,zero_mul,add_zero,abs_one,abs_zero] at h
    change |x.1-y.1| ≤ _
    nlinarith
  · have h := linear_form_dist_bound 0 1 x y
    simp only [one_mul,zero_mul,zero_add,abs_one,abs_zero] at h
    change |x.2-y.2| ≤ _
    nlinarith
  · have h := linear_form_dist_bound (-Real.goldenRatio^a) 1 x y
    change |(x.2-Real.goldenRatio^a*x.1)-(y.2-Real.goldenRatio^a*y.1)| ≤ _
    simpa only [one_mul,neg_mul,sub_eq_add_neg,abs_neg,abs_one,hslope,add_comm] using h
  · have h := linear_form_dist_bound 1 (-Real.goldenRatio^a) x y
    change |(x.1-Real.goldenRatio^a*x.2)-(y.1-Real.goldenRatio^a*y.2)| ≤ _
    simpa only [one_mul,neg_mul,sub_eq_add_neg,abs_neg,abs_one,hslope] using h

end FarGridActions

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_FlagGerms
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.TranslationFiltered.regular_filtered
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
section FlagGerms
open Classical

theorem flagMem_halfPlane {a : ℕ} {v : ℝ×ℝ} (j : Fin 4) (c : CutRing)
    (z : SquareFlag a v) :
    flagMem ⟨halfPlane a j c,halfPlane_mem a j c⟩ z ↔
      (if cutForm a j z.val=ordinary c then cutForm a j v<0
        else cutForm a j z.val<ordinary c) := by
  let U : polygonAlgebra a := ⟨halfPlane a j c,halfPlane_mem a j c⟩
  have hg : flagValue (fun p => decide (p∈U.val))
      (polygon_hasSquareArrangement U.property) z =
      decide (if cutForm a j z.val=ordinary c then cutForm a j v<0
        else cutForm a j z.val<ordinary c) := by
    apply flagValue_eq
    refine ⟨arrangementNeighborhood a {(j,c)} z.val,
      arrangementNeighborhood_open a {(j,c)} z.val,
      self_mem_arrangementNeighborhood a {(j,c)} z.val, fun p hp hpv => ?_⟩
    exact planeSign_neighborhood (p:=⟨p.val,p.property.2.2⟩) hp hpv (Finset.mem_singleton_self _)
  change flagValue _ _ z=true ↔ _
  rw [hg]
  simp

end FlagGerms

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_FlagSites
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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
section FlagSites
open Classical

theorem scaledOrdinary_injective {D : ℕ} (hD : 0<D) :
    Function.Injective (scaledOrdinary D) := by
  intro u w h
  have hD' : (D:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hD
  apply Prod.ext
  · exact ordinary_injective ((div_left_inj' hD').mp (congrArg Prod.fst h))
  · exact ordinary_injective ((div_left_inj' hD').mp (congrArg Prod.snd h))

theorem flagSiteNumerator_action {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) (z : FlagSite a m D v) :
    flagSiteNumerator (flagSiteAction hD g z)=flagShiftNumerator D (flagSiteNumerator z)
      (flagChart g z.val).shift (flagShiftPeriod (flagChart g z.val).shift z.val.2) := by
  apply scaledOrdinary_injective hD
  rw [flagSiteNumerator_spec,scaledOrdinary_shift hD,flagSiteNumerator_spec]
  change (flagTranslate _ z.val.2).val=_
  simp only [flagTranslate_val,flagFract_eq,flagShiftPeriod]
  rfl

theorem flagSiteConjugate_action {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) (z : FlagSite a m D v) :
    flagSiteConjugate (flagSiteAction hD g z)=flagSiteConjugate z+
      (conjugate (flagChart g z.val).shift.1,conjugate (flagChart g z.val).shift.2)-
      (((flagShiftPeriod (flagChart g z.val).shift z.val.2).1:ℝ),
       ((flagShiftPeriod (flagChart g z.val).shift z.val.2).2:ℝ)) := by
  have hD' : (D:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hD
  unfold flagSiteConjugate
  rw [flagSiteNumerator_action hD]
  apply Prod.ext <;>
    simp only [scaledConjugate,flagShiftNumerator,Prod.fst_sub,Prod.snd_sub,
      Prod.fst_add,Prod.snd_add,map_sub,map_add,map_mul,map_natCast,map_intCast] <;>
    field_simp

end FlagSites

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_FlagSeparatingLevels
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.TranslationFiltered.regular_filtered
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
section FlagSeparatingLevels
open Classical

theorem flagSeparates_ordinary_bound {a : ℕ} {v : ℝ×ℝ} {j : Fin 4} {c : CutRing}
    {z w : SquareFlag a v} (h : FlagSeparates j c z w) :
    ordinary c ∈ Set.Icc (min (cutForm a j z.val) (cutForm a j w.val))
      (max (cutForm a j z.val) (cutForm a j w.val)) := by
  unfold FlagSeparates at h
  simp only [flagMem_halfPlane] at h
  constructor
  · by_contra hn
    have hz : ordinary c < cutForm a j z.val := lt_of_lt_of_le (lt_of_not_ge hn) (min_le_left _ _)
    have hw : ordinary c < cutForm a j w.val := lt_of_lt_of_le (lt_of_not_ge hn) (min_le_right _ _)
    simp [ne_of_gt hz,ne_of_gt hw,not_lt_of_ge hz.le,not_lt_of_ge hw.le] at h
  · by_contra hn
    have hz : cutForm a j z.val < ordinary c := lt_of_le_of_lt (le_max_left _ _) (lt_of_not_ge hn)
    have hw : cutForm a j w.val < ordinary c := lt_of_le_of_lt (le_max_right _ _) (lt_of_not_ge hn)
    simp [ne_of_lt hz,ne_of_lt hw,hz,hw] at h

theorem flagSeparates_bounded_finite {a : ℕ} {v : ℝ×ℝ} (j : Fin 4)
    (z w : SquareFlag a v) (R : ℝ) :
    {c : CutRing | FlagSeparates j c z w ∧ |conjugate c| ≤ R}.Finite := by
  let b := |R|+1
  have hb : 0 < b := by dsimp [b]; positivity
  let x := min (cutForm a j z.val) (cutForm a j w.val)
  let y := max (cutForm a j z.val) (cutForm a j w.val)
  apply (cutRectangle_finite x (-b) (y-x) (2*b) (by positivity)).subset
  intro c hc
  have ho := flagSeparates_ordinary_bound hc.1
  have ht := abs_le.mp hc.2
  change _ ∧ _
  constructor
  · simpa [x,y] using ho
  · constructor <;> dsimp [b] <;> linarith [le_abs_self R]

theorem flagSeparates_exists_min {a : ℕ} {v : ℝ×ℝ} (j : Fin 4)
    (z w : SquareFlag a v) (h : ∃ c,FlagSeparates j c z w) :
    ∃ c,FlagSeparates j c z w ∧ ∀ d,FlagSeparates j d z w →
      |conjugate c| ≤ |conjugate d| := by
  obtain ⟨c,hc⟩ := h
  let S : Set CutRing := {d : CutRing | FlagSeparates j d z w ∧ |conjugate d| ≤ |conjugate c|}
  have hS : S.Finite := flagSeparates_bounded_finite j z w _
  have hn : S.Nonempty := ⟨c,hc,le_rfl⟩
  obtain ⟨d,hd,hmin⟩ := Set.exists_min_image S (fun e => |conjugate e|) hS hn
  refine ⟨d,hd.1,fun e he => ?_⟩
  by_cases hec : |conjugate e| ≤ |conjugate c|
  · exact hmin e ⟨he,hec⟩
  · exact hd.2.trans (le_of_not_ge hec)

end FlagSeparatingLevels

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_TentMatrixPositivity
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.TranslationFiltered.regular_filtered
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

section FlagSeparatorMatrices
open Classical MeasureTheory

theorem flagChamber_eq_iff {a : ℕ} {v : ℝ×ℝ} (t : Fin 4 → ℝ)
    (z w : SquareFlag a v) : flagChamber t z=flagChamber t w ↔
    ∀j c,|conjugate c|≤t j →
      (flagMem ⟨halfPlane a j c,halfPlane_mem a j c⟩ z ↔
       flagMem ⟨halfPlane a j c,halfPlane_mem a j c⟩ w) := by
  constructor
  · intro he j c hc
    have h := congrFun he (j,c)
    simpa only [flagChamber,hc,ite_true,decide_eq_decide] using h
  · intro h
    funext l
    simp only [flagChamber]
    split_ifs with hl
    · exact propext (h l.1 l.2 hl) ▸ rfl
    · rfl

theorem measurableSet_flagChamber_eq {a : ℕ} {v : ℝ×ℝ} (z w : SquareFlag a v) :
    MeasurableSet {t : Fin 4 → ℝ | flagChamber t z=flagChamber t w} := by
  have he : {t : Fin 4 → ℝ | flagChamber t z=flagChamber t w}=
      ⋂l : Fin 4 × CutRing, {t | flagChamber t z l=flagChamber t w l} := by
    ext t
    simp only [Set.mem_ofPred_eq,Set.mem_iInter]
    exact funext_iff
  rw [he]
  apply MeasurableSet.iInter
  intro l
  by_cases hz : flagMem ⟨halfPlane a l.1 l.2,halfPlane_mem a l.1 l.2⟩ z <;>
    by_cases hw : flagMem ⟨halfPlane a l.1 l.2,halfPlane_mem a l.1 l.2⟩ w
  · simp only [flagChamber,hz,hw,decide_true,Set.ofPred_true]
    exact MeasurableSet.univ
  · simpa [flagChamber,hz,hw] using
      (measurableSet_lt (measurable_pi_apply l.1) (measurable_const (a := |conjugate l.2|)) :
        MeasurableSet {t : Fin 4 → ℝ | t l.1 < |conjugate l.2|})
  · simpa [flagChamber,hz,hw] using
      (measurableSet_lt (measurable_pi_apply l.1) (measurable_const (a := |conjugate l.2|)) :
        MeasurableSet {t : Fin 4 → ℝ | t l.1 < |conjugate l.2|})
  · simp only [flagChamber,hz,hw,decide_false,ite_self,Set.ofPred_true]
    exact MeasurableSet.univ

theorem separatorMatrix_eq_measure {a : ℕ} {v : ℝ×ℝ}
    (μ : Measure (Fin 4 → ℝ)) (z w : SquareFlag a v) :
    separatorMatrix μ z w=μ.real {t|flagChamber t z=flagChamber t w} :=
  integral_indicator_one (measurableSet_flagChamber_eq z w)

end FlagSeparatorMatrices

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_UniformThresholdCDF
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.TranslationFiltered.regular_filtered
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
section UniformThresholdCDF
open Classical MeasureTheory ProbabilityTheory

theorem uniformInterval_Iio {lo hi : ℝ} (h : lo < hi) (d : ℝ) :
    (cond volume (Set.Icc lo hi)).real (Set.Iio d)=intervalCDF lo hi d := by
  rw [measureReal_def,cond_apply measurableSet_Icc,ENNReal.toReal_mul,
    ENNReal.toReal_inv,Real.volume_Icc,ENNReal.toReal_ofReal (sub_nonneg.mpr h.le)]
  by_cases hd : d ≤ hi
  · have he : Set.Icc lo hi ∩ Set.Iio d = Set.Ico lo d := by
      ext x
      exact ⟨fun hx => ⟨hx.1.1,hx.2⟩,fun hx => ⟨⟨hx.1,hx.2.le.trans hd⟩,hx.2⟩⟩
    rw [he,Real.volume_Ico,ENNReal.toReal_ofReal']
    simp [intervalCDF,min_eq_right hd,div_eq_mul_inv,mul_comm]
  · have he : Set.Icc lo hi ∩ Set.Iio d = Set.Icc lo hi := by
      ext x
      exact ⟨fun hx => hx.1,fun hx => ⟨hx,lt_of_le_of_lt hx.2 (lt_of_not_ge hd)⟩⟩
    rw [he,Real.volume_Icc,ENNReal.toReal_ofReal']
    simp [intervalCDF,min_eq_left (le_of_not_ge hd),div_eq_mul_inv,mul_comm]

end UniformThresholdCDF

section SeparatorCovariance
open Classical MeasureTheory ProbabilityTheory

theorem directionNoCut_of_min {a : ℕ} {v : ℝ×ℝ} (j : Fin 4)
    (z w : SquareFlag a v) (c : CutRing) (hc : FlagSeparates j c z w)
    (hmin : ∀ d,FlagSeparates j d z w → |conjugate c| ≤ |conjugate d|) :
    directionNoCut j z w = Set.Iio |conjugate c| := by
  ext t
  constructor
  · intro ht
    exact lt_of_not_ge (fun hle => ht c hle hc)
  · intro ht d hd hsep
    exact not_le_of_gt ht ((hmin d hsep).trans hd)

theorem uniformInterval_isProbability {lo hi : ℝ} (h : lo < hi) :
    IsProbabilityMeasure (cond volume (Set.Icc lo hi)) :=
  cond_isProbabilityMeasure_of_finite
    (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_zero_iff.mpr (sub_pos.mpr h))
    (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)

theorem separatorMatrix_product {a : ℕ} {v : ℝ×ℝ}
    {s κ : ℝ} (hs : 0 < s) (hκ : 0 < κ) (z w : SquareFlag a v) :
    separatorMatrix (thresholdLaw s κ) z w = ∏j,directionNoCutProbability s κ j z w := by
  have h : κ/s < 2*κ/s := (div_lt_div_iff_of_pos_right hs).mpr (by linarith)
  have := uniformInterval_isProbability h
  have he : {t : Fin 4 → ℝ | flagChamber t z=flagChamber t w}=
      Set.univ.pi (fun j => directionNoCut j z w) := by
    ext t
    rw [Set.mem_ofPred_eq,flagChamber_eq_iff]
    simp only [Set.mem_pi,Set.mem_univ,forall_true_left,directionNoCut,Set.mem_ofPred_eq,
      FlagSeparates,not_not]
  rw [separatorMatrix_eq_measure,measureReal_def,he]
  change (Measure.pi (fun _ : Fin 4 => cond volume (Set.Icc (κ/s) (2*κ/s)))
    (Set.univ.pi (fun j => directionNoCut j z w))).toReal = _
  rw [Measure.pi_pi,ENNReal.toReal_prod]
  rfl

end SeparatorCovariance

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_FlagArrangementControl
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
section FlagArrangementControl
open Classical MeasureTheory

theorem flagValue_arrangement {a : ℕ} {v : ℝ×ℝ} {K : Type*}
    (f : GenericSquare a → K) (S : Finset PlaneCut)
    (hS : ∀p q,(∀l∈S,squareSign l p=squareSign l q) → f p=f q)
    (z w : SquareFlag a v)
    (hs : ∀l∈S,¬ FlagSeparates l.1 l.2 z w) :
    flagValue f ⟨S,hS⟩ z=flagValue f ⟨S,hS⟩ w := by
  obtain ⟨N,hN,hz,hf⟩ := flagValue_spec f ⟨S,hS⟩ z
  obtain ⟨M,hM,hw,hg⟩ := flagValue_spec f ⟨S,hS⟩ w
  obtain ⟨p,hp,hpv⟩ := squareSector_generic z (hN.inter (arrangementNeighborhood_open a S z.val))
    ⟨hz,self_mem_arrangementNeighborhood a S z.val⟩
  obtain ⟨q,hq,hqv⟩ := squareSector_generic w (hM.inter (arrangementNeighborhood_open a S w.val))
    ⟨hw,self_mem_arrangementNeighborhood a S w.val⟩
  rw [← hf p hp.1 hpv,← hg q hq.1 hqv]
  apply hS p q
  intro l hl
  have h₁ := planeSign_neighborhood (p:=⟨p.val,p.property.2.2⟩) hp.2 hpv hl
  have h₂ := planeSign_neighborhood (p:=⟨q.val,q.property.2.2⟩) hq.2 hqv hl
  change squareSign l p=_ at h₁
  change squareSign l q=_ at h₂
  rw [h₁,h₂]
  apply decide_eq_decide.mpr
  have h := not_not.mp (hs l hl)
  simpa only [flagMem_halfPlane] using h

theorem separatorMatrix_zero_of_cut {a : ℕ} {v : ℝ×ℝ}
    {s κ : ℝ} (hs : 0 < s) (hκ : 0 < κ) (z w : SquareFlag a v)
    (j : Fin 4) (c : CutRing) (hc : FlagSeparates j c z w)
    (hcut : |conjugate c| ≤ κ/s) :
    separatorMatrix (thresholdLaw s κ) z w=0 := by
  obtain ⟨d,hd,hdmin⟩ := flagSeparates_exists_min j z w ⟨c,hc⟩
  have h : κ/s < 2*κ/s := (div_lt_div_iff_of_pos_right hs).mpr (by linarith)
  have hd' : |conjugate d| ≤ κ/s := (hdmin c hc).trans hcut
  have hp : directionNoCutProbability s κ j z w=0 := by
    rw [directionNoCutProbability,directionNoCut_of_min j z w d hd hdmin,
      uniformInterval_Iio h,intervalCDF]
    rw [max_eq_right (by linarith [min_le_right (2*κ/s) |conjugate d|]),zero_div]
  rw [separatorMatrix_product hs hκ]
  exact Finset.prod_eq_zero (Finset.mem_univ j) hp

theorem separatorMatrix_ne_zero_signs {a : ℕ} {v : ℝ×ℝ}
    {s κ : ℝ} (hs : 0 < s) (hκ : 0 < κ) (S : Finset PlaneCut)
    (hS : ∀l∈S,|conjugate l.2| ≤ κ/s) (z w : SquareFlag a v)
    (hp : separatorMatrix (thresholdLaw s κ) z w ≠ 0) :
    ∀l∈S,¬ FlagSeparates l.1 l.2 z w := by
  intro l hl hsep
  exact hp (separatorMatrix_zero_of_cut hs hκ z w l.1 l.2 hsep (hS l hl))

theorem separatorMatrix_controls_step {a : ℕ} {v : ℝ×ℝ} {K : Type*}
    (f : GenericSquare a → K) (hf : HasSquareArrangement f) :
    ∃R : ℝ, 0 ≤ R ∧ ∀(s κ : ℝ),0 < s → 0 < κ → R ≤ κ/s →
      ∀z w : SquareFlag a v,separatorMatrix (thresholdLaw s κ) z w ≠ 0 →
        flagValue f hf z=flagValue f hf w := by
  obtain ⟨S,hS⟩ := hf
  let R := ∑l∈S,|conjugate l.2|
  have hR : 0 ≤ R := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  refine ⟨R,hR,fun s κ hs hκ hRs z w hp => ?_⟩
  apply flagValue_arrangement f S hS z w
  apply separatorMatrix_ne_zero_signs hs hκ S _ z w hp
  intro l hl
  exact (Finset.single_le_sum (fun _ _ => abs_nonneg _) hl).trans hRs

end FlagArrangementControl

section SquareAffineCharts
open Classical

theorem squareTranslationPeriod_germ {a : ℕ} {v : ℝ×ℝ}
    (u : CutRing×CutRing) (z : SquareFlag a v) :
    IsSquareGerm (squareTranslationPeriod u) z (flagShiftPeriod u z) := by
  let k := flagShiftPeriod u z
  let t := u-SquareStep.intPair k
  let b : ℝ×ℝ := (ordinary t.1,ordinary t.2)
  have hbase : (flagTranslate u z).val=z.val+b := by
    apply Prod.ext <;> simp only [flagTranslate_val,flagFract_eq,b,t,k,flagShiftPeriod,SquareStep.intPair,
      Prod.fst_sub,Prod.snd_sub,Prod.fst_add,Prod.snd_add,map_sub,map_intCast] <;> ring
  let M : Set (ℝ×ℝ) := (fun p => p+b) ⁻¹' arrangementNeighborhood a SquareStep.squareEdgeCuts (flagTranslate u z).val
  refine ⟨M,(arrangementNeighborhood_open _ _ _).preimage (continuous_id.add continuous_const),?_,fun p hp hpv => ?_⟩
  · change z.val+b ∈ arrangementNeighborhood a SquareStep.squareEdgeCuts (flagTranslate u z).val
    rw [← hbase]
    exact self_mem_arrangementNeighborhood _ _ _
  · let q : GenericPlane a := GenericPlane.shift t ⟨p.val,p.property.2.2⟩
    have hqv : q.val ∈ planeSector a (flagTranslate u z).val v := by
      rw [hbase]
      exact (planeSector_add_iff z.val v b p.val).mpr hpv
    have hpq : q.val ∈ arrangementNeighborhood a SquareStep.squareEdgeCuts (flagTranslate u z).val := hp
    have hqs := sector_enters_square (flagTranslate u z).property.2 hpq hqv
    have hx : 0 ≤ p.val.1+ordinary u.1-(k.1:ℝ) ∧ p.val.1+ordinary u.1-(k.1:ℝ) < 1 := by
      simpa only [q,GenericPlane.shift,t,SquareStep.intPair,Prod.fst_add,Prod.fst_sub,map_sub,map_intCast,← add_sub_assoc,Set.mem_Ico] using hqs.1
    have hy : 0 ≤ p.val.2+ordinary u.2-(k.2:ℝ) ∧ p.val.2+ordinary u.2-(k.2:ℝ) < 1 := by
      simpa only [q,GenericPlane.shift,t,SquareStep.intPair,Prod.snd_add,Prod.snd_sub,map_sub,map_intCast,← add_sub_assoc,Set.mem_Ico] using hqs.2
    apply Prod.ext
    · exact Int.floor_eq_iff.mpr ⟨by linarith [hx.1],by linarith [hx.2]⟩
    · exact Int.floor_eq_iff.mpr ⟨by linarith [hy.1],by linarith [hy.2]⟩

end SquareAffineCharts

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_GoodRowSeparators
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
section GoodRowSeparators
open Classical MeasureTheory ProbabilityTheory

theorem flagSeparates_near_row {a : ℕ} {v : ℝ×ℝ} {j : Fin 4} {c : CutRing}
    {z w : SquareFlag a v} (h : FlagSeparates j c z w) :
    |cutForm a j z.val-ordinary c| ≤ (1+|ordinary (cutTau^a)|)*dist z.val w.val := by
  have hc := flagSeparates_ordinary_bound h
  have hb := abs_le.mp (cutForm_dist_bound a j z.val w.val)
  rcases le_total (cutForm a j z.val) (cutForm a j w.val) with hh|hh
  · rw [min_eq_left hh,max_eq_right hh] at hc
    exact abs_le.mpr ⟨by linarith [hc.1,hc.2],by linarith [hc.1,hc.2]⟩
  · rw [min_eq_right hh,max_eq_left hh] at hc
    exact abs_le.mpr ⟨by linarith [hc.1,hc.2],by linarith [hc.1,hc.2]⟩

theorem directionNoCutProbability_eq_one {a : ℕ} {v : ℝ×ℝ} {s κ : ℝ}
    (hs : 0 < s) (hκ : 0 < κ) (j : Fin 4) (z w : SquareFlag a v)
    (h : ∀c, |conjugate c| ≤ 2*κ/s → ¬ FlagSeparates j c z w) :
    directionNoCutProbability s κ j z w=1 := by
  have hi : κ/s < 2*κ/s := (div_lt_div_iff_of_pos_right hs).mpr (by linarith)
  have hinter : Set.Icc (κ/s) (2*κ/s) ∩ directionNoCut j z w = Set.Icc (κ/s) (2*κ/s) := by
    apply Set.inter_eq_left.mpr
    intro t ht c hc
    exact h c (hc.trans ht.2)
  have he : cond volume (Set.Icc (κ/s) (2*κ/s)) (directionNoCut j z w)=1 := by
    calc
      _ = cond volume (Set.Icc (κ/s) (2*κ/s)) (Set.Icc (κ/s) (2*κ/s)) := by
        rw [cond_apply measurableSet_Icc,cond_apply measurableSet_Icc,hinter,Set.inter_self]
      _ = 1 := cond_apply_self
        (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_zero_iff.mpr (sub_pos.mpr hi))
        (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  exact congrArg ENNReal.toReal he

theorem separatorMatrix_eq_one_on_good_row {a : ℕ} {v : ℝ×ℝ} {s κ : ℝ}
    (hs : 0 < s) (hκ : 0 < κ) (z w : SquareFlag a v) (hw : dist z.val w.val ≤ s)
    (hz : ∀j c, |conjugate c| ≤ 2*κ/s →
      (1+|ordinary (cutTau^a)|)*s < |cutForm a j z.val-ordinary c|) :
    separatorMatrix (thresholdLaw s κ) z w=1 := by
  rw [separatorMatrix_product hs hκ]
  suffices ∀j,directionNoCutProbability s κ j z w=1 by simp [this]
  intro j
  apply directionNoCutProbability_eq_one hs hκ
  intro c hc hsep
  have hb := (flagSeparates_near_row hsep).trans
    (mul_le_mul_of_nonneg_left hw (by positivity))
  exact (not_le_of_gt (hz j c hc)) hb

end GoodRowSeparators

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_FlagAveragingMatrices
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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

section AveragingRowBounds
open Classical MeasureTheory

theorem tentFactor_ne_zero {s d : ℝ} (hs : 0 < s) :
    max (1-|d/s|) 0 ≠ 0 ↔ |d| < s := by
  rw [ne_eq,max_eq_right_iff,not_le,abs_div,abs_of_pos hs]
  have he : 0 < 1-|d|/s ↔ |d|/s < 1 := by constructor <;> intro h <;> linarith
  rw [he,div_lt_iff₀ hs,one_mul]

theorem planeTent_ne_zero {s : ℝ} (hs : 0 < s) (x y : ℝ×ℝ) :
    planeTent s x y ≠ 0 ↔ |x.1-y.1| < s ∧ |x.2-y.2| < s := by
  rw [planeTent,mul_ne_zero_iff,tentFactor_ne_zero hs,tentFactor_ne_zero hs]

end AveragingRowBounds

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_FlagTentMass
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
section FlagTentMass
open Classical

@[simp] theorem flagSiteFromNumerator_numerator {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (hv : TransverseDirection a v) (k : Fin m) (u : CutRing×CutRing)
    (hu : SquareBoundary v (scaledOrdinary D u)) :
    flagSiteNumerator (flagSiteFromNumerator hv k u hu)=u :=
  scaledOrdinary_injective hD (flagSiteNumerator_spec _)

end FlagTentMass

section FiniteDifference

theorem finiteDifference_lipschitz {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (θ : E → ℝ) (hθ : Differentiable ℝ θ) {L : NNReal}
    (hL : LipschitzWith L (fderiv ℝ θ)) (δ x y : E) :
    |(θ (x+δ)-θ x)-(θ (y+δ)-θ y)| ≤ (L:ℝ)*‖δ‖*‖x-y‖ := by
  let F : E → ℝ := fun x => θ (x+δ)-θ x
  have hf (x : E) : HasFDerivAt F (fderiv ℝ θ (x+δ)-fderiv ℝ θ x) x := by
    have hh := (hasFDerivAt_comp_add_right δ).mpr (hθ (x+δ)).hasFDerivAt
    exact hh.sub (hθ x).hasFDerivAt
  have hb (z : E) : ‖fderiv ℝ F z‖ ≤ (L:ℝ)*‖δ‖ := by
    rw [(hf z).fderiv]
    simpa only [add_sub_cancel_left] using hL.norm_sub_le (z+δ) z
  have hh := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜:=ℝ)
    (f:=F) (s:=Set.univ) (fun z _ => (hf z).differentiableAt) (fun z _ => hb z)
    convex_univ (Set.mem_univ y) (Set.mem_univ x)
  simpa only [F,Real.norm_eq_abs] using hh

theorem compactSignal_uniform_constants {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ψ : E → ℝ) (hψ : ContDiff ℝ 2 ψ) (hs : HasCompactSupport ψ) :
    ∃L₀ L₁ : NNReal,LipschitzWith L₀ ψ ∧ ∀δ x y : E,
      |(ψ (x+δ)-ψ x)-(ψ (y+δ)-ψ y)| ≤ (L₁:ℝ)*‖δ‖*‖x-y‖ := by
  obtain ⟨L₀,hL₀⟩ := hψ.lipschitzWith_of_hasCompactSupport hs (by norm_num)
  have hd : ContDiff ℝ 1 (fderiv ℝ ψ) := hψ.fderiv_right (by norm_num)
  obtain ⟨L₁,hL₁⟩ := hd.lipschitzWith_of_hasCompactSupport (hs.fderiv ℝ) (by norm_num)
  exact ⟨L₀,L₁,hL₀,finiteDifference_lipschitz ψ (hψ.differentiable (by norm_num)) hL₁⟩

end FiniteDifference

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_FullGroupAffineData
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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
section FullGroupAffineData
open Classical

theorem flagAffineData_chart {a m : ℕ} {v : ℝ×ℝ} (g : polygonFullGroup a m)
    (i : Fin m) (z : SquareFlag a v) (c : TableChart a m) (hc : c.Holds g.val)
    (hi : i=c.source) (hz : flagMem c.domain z) :
    flagAffineData g i z=(c.target,c.shift-SquareStep.intPair (flagShiftPeriod c.shift z)) := by
  obtain ⟨N,hN,hzN,hf⟩ := flagMem_iff c.domain z
  obtain ⟨M,hM,hzM,hp⟩ := squareTranslationPeriod_germ c.shift z
  apply flagValue_eq
  refine ⟨N∩M,hN.inter hM,⟨hzN,hzM⟩,fun p hpm hpv => ?_⟩
  rw [fullGroupAffineData_chart g i p c hc hi ((hf p hpm.1 hpv).mpr hz),hp p hpm.2 hpv]

theorem flagAffineData_selected {a m : ℕ} {v : ℝ×ℝ} (g : polygonFullGroup a m)
    (z : FlagTrackPoint a m v) :
    flagAffineData g z.1 z.2=((flagChart g z).target,
      (flagChart g z).shift-SquareStep.intPair (flagShiftPeriod (flagChart g z).shift z.2)) :=
  flagAffineData_chart g z.1 z.2 (flagChart g z) (flagChart_spec g z).1
    (flagChart_spec g z).2.1 (flagChart_spec g z).2.2

theorem flagAffineData_conjugate {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) (z : FlagSite a m D v) :
    flagSiteConjugate (flagSiteAction hD g z)=flagSiteConjugate z+
      (conjugate (flagAffineData g z.val.1 z.val.2).2.1,
       conjugate (flagAffineData g z.val.1 z.val.2).2.2) := by
  rw [flagAffineData_selected,flagSiteConjugate_action hD]
  apply Prod.ext <;>
    simp only [SquareStep.intPair,Prod.fst_sub,Prod.snd_sub,Prod.fst_add,Prod.snd_add,
      map_sub,map_intCast] <;> ring

end FullGroupAffineData

section FlagAffineControl
open Classical

theorem squareArrangement_finite_range {a : ℕ} {K : Type*} (f : GenericSquare a → K)
    (hf : HasSquareArrangement f) : (Set.range f).Finite := by
  obtain ⟨S,hS⟩ := hf
  let p (k : Set.range f) : GenericSquare a := k.property.choose
  have hp (k : Set.range f) : f (p k)=k.val := k.property.choose_spec
  let q (k : Set.range f) : S → Bool := fun l => squareSign l.val (p k)
  have hq : Function.Injective q := by
    intro k j h
    apply Subtype.ext
    rw [← hp k,← hp j]
    exact hS (p k) (p j) (fun l hl => congrFun h ⟨l,hl⟩)
  have : Finite (Set.range f) := Finite.of_injective q hq
  exact Set.toFinite _

theorem flagValue_mem_range {a : ℕ} {v : ℝ×ℝ} {K : Type*} (f : GenericSquare a → K)
    (hf : HasSquareArrangement f) (z : SquareFlag a v) : flagValue f hf z∈Set.range f := by
  obtain ⟨N,hN,hz,hf'⟩ := flagValue_spec f hf z
  obtain ⟨p,hp,hpv⟩ := squareSector_generic z hN hz
  exact ⟨p,hf' p hp hpv⟩

theorem flagValue_finite_range {a : ℕ} {v : ℝ×ℝ} {K : Type*} (f : GenericSquare a → K)
    (hf : HasSquareArrangement f) : (Set.range (flagValue (v:=v) f hf)).Finite :=
  (squareArrangement_finite_range f hf).subset (by rintro _ ⟨z,rfl⟩; exact flagValue_mem_range f hf z)

theorem flagAffineData_finite_range {a m : ℕ} {v : ℝ×ℝ} (g : polygonFullGroup a m) :
    (Set.range (fun z : FlagTrackPoint a m v => flagAffineData g z.1 z.2)).Finite := by
  have h (i : Fin m) : (Set.range (flagAffineData (v:=v) g i)).Finite :=
    flagValue_finite_range (fullGroupAffineData g i) (fullGroupAffineData_arrangement g i)
  apply (Set.finite_iUnion h).subset
  rintro _ ⟨z,rfl⟩
  exact Set.mem_iUnion.mpr ⟨z.1,⟨z.2,rfl⟩⟩

theorem flagAffineData_bounded {a m : ℕ} {v : ℝ×ℝ} (g : polygonFullGroup a m)
    (f : (CutRing×CutRing) → ℝ) :
    ∃C : ℝ,0 ≤ C ∧ ∀z : FlagTrackPoint a m v,|f (flagAffineData g z.1 z.2).2| ≤ C := by
  let S := (flagAffineData_finite_range (v:=v) g).toFinset
  refine ⟨∑d∈S,|f d.2|,Finset.sum_nonneg (fun _ _ => abs_nonneg _),fun z => ?_⟩
  apply Finset.single_le_sum (f:=fun d : Fin m × (CutRing×CutRing) => |f d.2|) (fun _ _ => abs_nonneg _)
  change flagAffineData g z.1 z.2∈(flagAffineData_finite_range (v:=v) g).toFinset
  exact (Set.Finite.mem_toFinset _).mpr ⟨z,rfl⟩

theorem flagAffineData_separator_control {a m : ℕ} {v : ℝ×ℝ} (g : polygonFullGroup a m) :
    ∃R : ℝ,0 ≤ R ∧ ∀(s κ : ℝ),0 < s → 0 < κ → R ≤ κ/s →
      ∀(i : Fin m) (z w : SquareFlag a v),separatorMatrix (thresholdLaw s κ) z w ≠ 0 →
        flagAffineData g i z=flagAffineData g i w := by
  choose R hR hcontrol using fun i : Fin m => separatorMatrix_controls_step (v:=v)
    (fullGroupAffineData g i) (fullGroupAffineData_arrangement g i)
  refine ⟨∑i,R i,Finset.sum_nonneg (fun i _ => hR i),fun s κ hs hκ hbound i z w hp => ?_⟩
  exact hcontrol i s κ hs hκ ((Finset.single_le_sum
    (fun j _ => hR j) (Finset.mem_univ i)).trans hbound) z w hp

end FlagAffineControl

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_FlagSignalEnergy
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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
section FlagSignalEnergy
open Classical

theorem flagSignalDifference_chart {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) (θ : (ℝ×ℝ) → ℝ) (N : ℝ) (z : FlagSite a m D v) :
    flagSignalDifference hD g θ N z=
      θ ((flagSiteConjugate z).1/N+conjugate (flagAffineData g⁻¹ z.val.1 z.val.2).2.1/N,
         (flagSiteConjugate z).2/N+conjugate (flagAffineData g⁻¹ z.val.1 z.val.2).2.2/N)-
      θ (scaledSiteConjugate N z) := by
  simp only [flagSignalDifference,flagMeanSignal,scaledSiteConjugate,
    flagAffineData_conjugate hD,Prod.fst_add,Prod.snd_add,add_div]

theorem flagSiteAction_displacement {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) :
    ∃Q : ℝ,0≤Q ∧ ∀z : FlagSite a m D v,
      |(flagSiteConjugate (flagSiteAction hD g z)).1-(flagSiteConjugate z).1|+
      |(flagSiteConjugate (flagSiteAction hD g z)).2-(flagSiteConjugate z).2| ≤ Q := by
  obtain ⟨Q,hQ,hb⟩ := flagAffineData_bounded (v:=v) g
    (fun u => |conjugate u.1|+|conjugate u.2|)
  refine ⟨Q,hQ,fun z => ?_⟩
  have hh := hb z.val
  rw [abs_of_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _))] at hh
  simpa only [flagAffineData_conjugate hD,Prod.fst_add,Prod.snd_add,add_sub_cancel_left] using hh

theorem flagSignalDifference_amplitude {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) (θ : (ℝ×ℝ) → ℝ) {L : ℝ} (hL : 0≤L)
    (hLip : ∀x y,|θ x-θ y| ≤ L*(|x.1-y.1|+|x.2-y.2|)) :
    ∃ C : ℝ,0≤C ∧ ∀N : ℝ,0<N → ∀z : FlagSite a m D v,
      |flagSignalDifference hD g θ N z| ≤ C/N := by
  obtain ⟨Q,hQ,hdisp⟩ := flagSiteAction_displacement (v:=v) hD g⁻¹
  refine ⟨L*Q,mul_nonneg hL hQ,fun N hN z => ?_⟩
  have h := hLip (scaledSiteConjugate N (flagSiteAction hD g⁻¹ z)) (scaledSiteConjugate N z)
  simp only [scaledSiteConjugate,← sub_div,abs_div,abs_of_pos hN,← add_div] at h
  change |flagSignalDifference hD g θ N z| ≤ _ at h
  calc
    _ ≤ _ := h
    _ ≤ L*(Q/N) := mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right (hdisp z) hN.le) hL
    _ = _ := (mul_div_assoc _ _ _).symm

end FlagSignalEnergy

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_WeightedAveragingError
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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

section SignalChartVariation
open Classical

theorem flagSignalDifference_add_constant {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) (ψ : (ℝ×ℝ) → ℝ) (q N : ℝ) (z : FlagSite a m D v) :
    flagSignalDifference hD g (fun x => q+ψ x) N z=flagSignalDifference hD g ψ N z := by
  unfold flagSignalDifference flagMeanSignal
  ring

theorem flagSignalDifference_vector_chart {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) (θ : (ℝ×ℝ) → ℝ) (N : ℝ) (z : FlagSite a m D v) :
    flagSignalDifference hD g θ N z=
      θ (scaledSiteConjugate N z+N⁻¹ •
        (conjugate (flagAffineData g⁻¹ z.val.1 z.val.2).2.1,
         conjugate (flagAffineData g⁻¹ z.val.1 z.val.2).2.2))-θ (scaledSiteConjugate N z) := by
  rw [flagSignalDifference_chart hD]
  congr 2
  simp [scaledSiteConjugate,div_eq_mul_inv,mul_comm]

theorem flagSignalDifference_chart_variation {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) (ψ : (ℝ×ℝ) → ℝ)
    (hψ : ContDiff ℝ 2 ψ) (hs : HasCompactSupport ψ) (q : ℝ) :
    ∃C : ℝ,0 ≤ C ∧ ∀(N η : ℝ),0<N → 0 ≤ η → ∀z w : FlagSite a m D v,
      flagAffineData g⁻¹ z.val.1 z.val.2=flagAffineData g⁻¹ w.val.1 w.val.2 →
      ‖scaledSiteConjugate N z-scaledSiteConjugate N w‖ ≤ η →
      |flagSignalDifference hD g (fun x => q+ψ x) N z-
        flagSignalDifference hD g (fun x => q+ψ x) N w| ≤ C*η/N := by
  obtain ⟨L₀,L₁,hL₀,hL₁⟩ := compactSignal_uniform_constants ψ hψ hs
  obtain ⟨Q,hQ,hbound⟩ := flagAffineData_bounded (v:=v) g⁻¹
    (fun u => ‖(conjugate u.1,conjugate u.2)‖)
  refine ⟨(L₁:ℝ)*Q,mul_nonneg L₁.coe_nonneg hQ,fun N η hN hη z w hchart hnear => ?_⟩
  rw [flagSignalDifference_add_constant,flagSignalDifference_add_constant,
    flagSignalDifference_vector_chart hD,flagSignalDifference_vector_chart hD,← hchart]
  let u := (conjugate (flagAffineData g⁻¹ z.val.1 z.val.2).2.1,
    conjugate (flagAffineData g⁻¹ z.val.1 z.val.2).2.2)
  have hu : ‖u‖ ≤ Q := by simpa only [abs_of_nonneg (norm_nonneg _)] using hbound z.val
  have hd : ‖N⁻¹ • u‖ ≤ Q/N := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hN),div_eq_mul_inv]
    exact (mul_le_mul_of_nonneg_left hu (inv_pos.mpr hN).le).trans_eq (mul_comm _ _)
  calc
    _ ≤ (L₁:ℝ)*‖N⁻¹ • u‖*‖scaledSiteConjugate N z-scaledSiteConjugate N w‖ := hL₁ _ _ _
    _ ≤ (L₁:ℝ)*(Q/N)*η := by gcongr
    _ = _ := by ring

theorem planeTent_scaled_near {a m D : ℕ} {v : ℝ×ℝ} {N η : ℝ} (hN : 0<N)
    (hη : 0<η) (z w : FlagSite a m D v)
    (h : planeTent (N*η) (flagSiteConjugate z) (flagSiteConjugate w)≠0) :
    ‖scaledSiteConjugate N z-scaledSiteConjugate N w‖ ≤ η := by
  have hh := (planeTent_ne_zero (mul_pos hN hη) _ _).mp h
  rw [Prod.norm_def]
  apply max_le <;> simp only [scaledSiteConjugate,Prod.fst_sub,Prod.snd_sub,Real.norm_eq_abs,
    ← sub_div,abs_div,abs_of_pos hN]
  · exact (div_le_iff₀ hN).mpr (by nlinarith [hh.1.le])
  · exact (div_le_iff₀ hN).mpr (by nlinarith [hh.2.le])

end SignalChartVariation

section GoodRowAveraging
open Classical

theorem flagRowTent_ne_zero_iff {a m D : ℕ} {v : ℝ×ℝ} (s t : ℝ) (z w : FlagSite a m D v) :
    flagRowTent s t z w≠0 ↔ z.val.1=w.val.1 ∧
      planeTent s (flagSiteOrdinary z) (flagSiteOrdinary w)≠0 ∧
      planeTent t (flagSiteConjugate z) (flagSiteConjugate w)≠0 := by
  by_cases ht : z.val.1=w.val.1 <;> simp [flagRowTent,ht]

theorem flagRowTent_separator_one {a m D : ℕ} {v : ℝ×ℝ} {s κ : ℝ} (hs : 0 < s)
    (hκ : 0<κ) (t : ℝ) (z w : FlagSite a m D v)
    (hz : flagGoodRow s κ z) (hw : flagRowTent s t z w≠0) :
    separatorMatrix (thresholdLaw s κ) z.val.2 w.val.2=1 := by
  apply separatorMatrix_eq_one_on_good_row hs hκ _ _ _ hz
  have hh := (planeTent_ne_zero hs _ _).mp ((flagRowTent_ne_zero_iff s t z w).mp hw).2.1
  rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq]
  exact max_le hh.1.le hh.2.le

end GoodRowAveraging

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_SignalCutoff
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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
section SignalCutoff
open Classical

theorem scaledSiteConjugate_displacement {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) :
    ∃Q : ℝ,0 ≤ Q ∧ ∀N : ℝ,0<N → ∀z : FlagSite a m D v,
      ‖scaledSiteConjugate N (flagSiteAction hD g z)-scaledSiteConjugate N z‖ ≤ Q/N := by
  obtain ⟨Q,hQ,hb⟩ := flagSiteAction_displacement (v:=v) hD g
  refine ⟨Q,hQ,fun N hN z => ?_⟩
  rw [Prod.norm_def]
  apply max_le <;> simp only [scaledSiteConjugate,Prod.fst_sub,Prod.snd_sub,Real.norm_eq_abs,
    ← sub_div,abs_div,abs_of_pos hN]
  · apply div_le_div_of_nonneg_right _ hN.le
    exact (le_add_of_nonneg_right (abs_nonneg _)).trans (hb z)
  · apply div_le_div_of_nonneg_right _ hN.le
    exact (le_add_of_nonneg_left (abs_nonneg _)).trans (hb z)

theorem flagSignalDifference_ne_zero_near {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) (ψ : (ℝ×ℝ) → ℝ) {K Q N : ℝ} (q : ℝ)
    (hcompact : ∀x,K ≤ ‖x‖ → ψ x=0)
    (hQ : 0 ≤ Q) (hN : 0<N)
    (hdisp : ∀z : FlagSite a m D v,
      ‖scaledSiteConjugate N (flagSiteAction hD g⁻¹ z)-scaledSiteConjugate N z‖ ≤ Q/N)
    (z : FlagSite a m D v) (hz : flagSignalDifference hD g (fun x => q+ψ x) N z≠0) :
    ‖scaledSiteConjugate N z‖ < K+Q/N := by
  rw [flagSignalDifference_add_constant] at hz
  by_cases hh : ψ (scaledSiteConjugate N z)=0
  · have hi : ψ (scaledSiteConjugate N (flagSiteAction hD g⁻¹ z))≠0 := by
      intro he
      exact hz (by simp [flagSignalDifference,flagMeanSignal,he,hh])
    have hn : ‖scaledSiteConjugate N (flagSiteAction hD g⁻¹ z)‖<K :=
      lt_of_not_ge (fun he => hi (hcompact _ he))
    have ht := norm_le_norm_add_norm_sub (scaledSiteConjugate N (flagSiteAction hD g⁻¹ z))
      (scaledSiteConjugate N z)
    linarith [hdisp z]
  · have hn : ‖scaledSiteConjugate N z‖<K := lt_of_not_ge (fun he => hh (hcompact _ he))
    exact hn.trans_le (le_add_of_nonneg_right (div_nonneg hQ hN.le))

theorem flagSignalDifference_cutoff {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) (ψ χ : (ℝ×ℝ) → ℝ) {K : ℝ} (q : ℝ)
    (hcompact : ∀x,K ≤ ‖x‖ → ψ x=0)
    (hχ : ∀x,‖x‖ ≤ K+2 → χ x=1) :
    ∃Q : ℝ,0 ≤ Q ∧ ∀(N r η : ℝ),0<N → Q ≤ N → 0<η → η ≤ 1 →
      ∀z w : FlagSite a m D v,flagRowTent (r/N) (N*η) z w≠0 →
        flagSignalDifference hD g (fun x => q+ψ x) N w≠0 →
        χ (scaledSiteConjugate N z)=1 ∧ χ (scaledSiteConjugate N w)=1 := by
  obtain ⟨Q,hQ,hdisp⟩ := scaledSiteConjugate_displacement (v:=v) hD g⁻¹
  refine ⟨Q,hQ,fun N r η hN hQN hη hη₁ z w hkw hw => ?_⟩
  have hwn := flagSignalDifference_ne_zero_near hD g ψ q hcompact hQ hN (hdisp N hN) w hw
  have hQN' : Q/N ≤ 1 := (div_le_one hN).mpr hQN
  have hn := planeTent_scaled_near hN hη z w
    ((flagRowTent_ne_zero_iff _ _ _ _).mp hkw).2.2
  have hz := norm_le_norm_add_norm_sub (scaledSiteConjugate N w) (scaledSiteConjugate N z)
  rw [norm_sub_rev] at hz
  exact ⟨hχ _ (by linarith),hχ _ (by linarith)⟩

theorem compactSignal_amplitude {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) (ψ : (ℝ×ℝ) → ℝ)
    (hψ : ContDiff ℝ 2 ψ) (hs : HasCompactSupport ψ) (q : ℝ) :
    ∃C : ℝ,0 ≤ C ∧ ∀N : ℝ,0<N → ∀z : FlagSite a m D v,
      |flagSignalDifference hD g (fun x => q+ψ x) N z| ≤ C/N := by
  obtain ⟨L₀,L₁,hL₀,hL₁⟩ := compactSignal_uniform_constants ψ hψ hs
  obtain ⟨C,hC,hamp⟩ := flagSignalDifference_amplitude (v:=v) hD g ψ L₀.coe_nonneg (by
    intro x y
    have hh := hL₀.dist_le_mul x y
    rw [Real.dist_eq,dist_eq_norm,Prod.norm_def] at hh
    refine hh.trans (mul_le_mul_of_nonneg_left ?_ L₀.coe_nonneg)
    simp only [Prod.fst_sub,Prod.snd_sub,Real.norm_eq_abs]
    exact max_le (le_add_of_nonneg_right (abs_nonneg _)) (le_add_of_nonneg_left (abs_nonneg _)))
  refine ⟨C,hC,fun N hN z => ?_⟩
  rw [flagSignalDifference_add_constant]
  exact hamp N hN z

end SignalCutoff

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_SignalGoodRows
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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
section SignalGoodRows
open Classical

theorem finset_sum_eq_of_zero_outside {ι : Type*} (f : ι → ℝ) (S T : Finset ι)
    (hS : ∀i,i∉S → f i=0) (hT : ∀i,i∉T → f i=0) :
    (∑i∈S,f i)=∑i∈T,f i := by
  calc
    _ = ∑i∈S∪T,f i := Finset.sum_subset Finset.subset_union_left (fun i _ hi => hS i hi)
    _ = _ := (Finset.sum_subset Finset.subset_union_right (fun i _ hi => hT i hi)).symm

theorem flagSignal_good_row_constants_oai {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) (ψ χ : (ℝ×ℝ) → ℝ)
    (hψ : ContDiff ℝ 2 ψ) (hsψ : HasCompactSupport ψ) (q K : ℝ)
    (hcompact : ∀x,K ≤ ‖x‖ → ψ x=0)
    (hχ : ∀x,‖x‖ ≤ K+2 → χ x=1) :
    ∃R Q Cv Ca : ℝ,0 ≤ R ∧ 0 ≤ Q ∧ 0 ≤ Cv ∧ 0 ≤ Ca ∧
      (∀N : ℝ,0<N → ∀z : FlagSite a m D v,
        |flagSignalDifference hD g (fun x => q+ψ x) N z| ≤ Ca/N) ∧
      ∀(N r η κ : ℝ),0<N → Q ≤ N → 0 < r → 0<η → η ≤ 1 → 0<κ →
        36 ≤ r*η → 1 ≤ 2*κ/(r/N) → R ≤ κ/(r/N) →
        ∀(z : FlagSite a m D v) (J : Finset (FlagSite a m D v)),flagGoodRow (r/N) κ z →
        (∀w,w∉J → flagAveragingMatrix χ ((D:ℝ)^4/5) N r η κ z w*
          flagSignalDifference hD g (fun x => q+ψ x) N w=0) →
        |(∑w∈J,flagAveragingMatrix χ ((D:ℝ)^4/5) N r η κ z w*
          flagSignalDifference hD g (fun x => q+ψ x) N w)-
          flagSignalDifference hD g (fun x => q+ψ x) N z| ≤
          (Cv*η/N)*(1+38880/((D:ℝ)*Real.sqrt (r*η)))+
          (Ca/N)*(38880/((D:ℝ)*Real.sqrt (r*η))) := by
  obtain ⟨R,hR,hcharts⟩ := flagAffineData_separator_control (v:=v) g⁻¹
  obtain ⟨Q,hQ,hcutoff⟩ := flagSignalDifference_cutoff (v:=v) hD g ψ χ q hcompact hχ
  obtain ⟨Cv,hCv,hvar⟩ := flagSignalDifference_chart_variation (v:=v) hD g ψ hψ hsψ q
  obtain ⟨Ca,hCa,hamp⟩ := compactSignal_amplitude (v:=v) hD g ψ hψ hsψ q
  refine ⟨R,Q,Cv,Ca,hR,hQ,hCv,hCa,hamp,fun N r η κ hN hQN hr hη hη₁ hκ hscale hline hRf z J hz hJ => ?_⟩
  let h := flagSignalDifference (v:=v) hD g (fun x => q+ψ x) N
  obtain ⟨T,hT,herror⟩ := flagAveragingMatrix_good_row_error hD χ h hN hr hη hκ hscale hline
    (show 0 ≤ Cv*η/N by positivity) z hz (hamp N hN z) (hcutoff N r η hN hQN hη hη₁ z) (by
      intro w hw
      obtain ⟨ht,hord,hconj⟩ := (flagRowTent_ne_zero_iff _ _ _ _).mp hw
      have hsep := flagRowTent_separator_one (div_pos hr hN) hκ (N*η) z w hz hw
      have hchart : flagAffineData g⁻¹ z.val.1 z.val.2=flagAffineData g⁻¹ w.val.1 w.val.2 := by
        rw [← ht]
        exact hcharts (r/N) κ (div_pos hr hN) hκ hRf z.val.1 z.val.2 w.val.2 (by rw [hsep]; norm_num)
      have hv := hvar N η hN hη.le z w hchart (planeTent_scaled_near hN hη z w hconj)
      simpa only [abs_sub_comm] using hv)
  have he := finset_sum_eq_of_zero_outside
    (fun w => flagAveragingMatrix χ ((D:ℝ)^4/5) N r η κ z w*h w) J T hJ hT
  change |(∑w∈J,flagAveragingMatrix χ ((D:ℝ)^4/5) N r η κ z w*h w)-h z| ≤ _
  rw [he]
  exact herror

end SignalGoodRows

end SimpleAmenable
end
end

end OAI
end

theorem solution : type_of% @OAI.SimpleAmenable.flagSignal_good_row_constants_oai := @OAI.SimpleAmenable.flagSignal_good_row_constants_oai
