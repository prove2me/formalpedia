-- Prove2me | solution 1 for OAI.SimpleAmenable.polygon_signal_approx_identity
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T04:51:01.724726+00:00
-- url     : https://prove2.me/submissions/234feff4-4b21-4901-a982-b12a7bfefafd

import Mathlib
import Definitions.Def_OAIQ65Sa014
import Theorems.Thm_OAI_SimpleAmenable_flagSignal_good_row_constants

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Arithmetic_QuadraticRectangleCounts
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.SimpleAmenable.instCountableCutRing _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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
section QuadraticRectangleCounts
open Classical

theorem cutRectangle_card_floor (S : Finset CutRing) (x y a b : ℝ) (hb : 0<b)
    (hS : ∀u∈S,u∈cutRectangle x y a b) :
    S.card≤(⌊b*(x+a)⌋+1-⌊b*x⌋).toNat := by
  have hinj : Set.InjOn (fun u : CutRing => ⌊b*ordinary u⌋) (↑S) := by
    intro u hu w hw he
    exact conjugateStrip_floor_inj y b hb (hS u hu).2 (hS w hw).2 he
  rw [← Int.card_Icc,← Finset.card_image_of_injOn hinj]
  apply Finset.card_le_card
  intro t ht
  obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp ht
  exact Finset.mem_Icc.mpr
    ⟨Int.floor_mono (mul_le_mul_of_nonneg_left (hS u hu).1.1 hb.le),
      Int.floor_mono (mul_le_mul_of_nonneg_left (hS u hu).1.2 hb.le)⟩

theorem cutRectangle_card_bound (S : Finset CutRing) (x y a b : ℝ)
    (ha : 0≤a) (hb : 0<b) (hS : ∀u∈S,u∈cutRectangle x y a b) :
    (S.card:ℝ)<a*b+2 := by
  have hc := cutRectangle_card_floor S x y a b hb hS
  have hle : ⌊b*x⌋≤⌊b*(x+a)⌋ := Int.floor_mono (by nlinarith)
  have hnon : 0≤⌊b*(x+a)⌋+1-⌊b*x⌋ := by omega
  have hc' : (S.card:ℤ)≤⌊b*(x+a)⌋+1-⌊b*x⌋ := by
    rw [← Int.toNat_of_nonneg hnon]
    exact_mod_cast hc
  have hc'' : (S.card:ℝ)≤(⌊b*(x+a)⌋:ℝ)+1-(⌊b*x⌋:ℝ) := by exact_mod_cast hc'
  have h₁ := Int.floor_le (b*(x+a))
  have h₂ := Int.lt_floor_add_one (b*x)
  nlinarith

end QuadraticRectangleCounts

end SimpleAmenable
end
end

end OAI
end

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
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_FlagSiteCounts
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
section FlagSiteCounts
open Classical

theorem flagSiteBox_card_bound {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    {R : ℝ} (hR : 0<R) (S : Finset (FlagSite a m D v))
    (hS : ∀z∈S,z∈flagSiteBox R) :
    (S.card:ℝ) ≤ m *(2*(D:ℝ)^2*R+2)^2 := by
  have hd : (0:ℝ)<D := by exact_mod_cast hD
  let T := (cutRectangle_finite 0 (-(D:ℝ)*R) D (2*D*R) (by positivity)).toFinset
  have ht (u : CutRing) : u∈T ↔ u∈cutRectangle 0 (-(D:ℝ)*R) D (2*D*R) :=
    Set.Finite.mem_toFinset _
  have hc : T.card < (2*(D:ℝ)^2*R+2) := by
    have hh := cutRectangle_card_bound T 0 (-(D:ℝ)*R) D (2*D*R) hd.le (by positivity)
      (fun u hu => (ht u).mp hu)
    nlinarith
  have hn : S.card ≤ m *T.card^2 := by
    rw [← Finset.card_image_of_injective _ flagSite_key_injective]
    have hi : S.image (fun z => (z.val.1,flagSiteNumerator z)) ⊆
        (Finset.univ : Finset (Fin m)) ×ˢ (T ×ˢ T) := by
      intro x hx
      obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hx
      have hh := flagSiteNumerator_box hD z (hS z hz)
      simp only [Finset.mem_product,Finset.mem_univ,true_and]
      exact ⟨(ht _).mpr hh.1,(ht _).mpr hh.2⟩
    simpa [Finset.card_product,pow_two] using Finset.card_le_card hi
  have hn' : (S.card:ℝ) ≤ m *(T.card:ℝ)^2 := by exact_mod_cast hn
  have hh : (T.card:ℝ)^2≤(2*(D:ℝ)^2*R+2)^2 := by
    nlinarith [Nat.cast_nonneg (α:=ℝ) T.card]
  exact hn'.trans (mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg _))

end FlagSiteCounts

section FlagWindowCounts
open Classical

theorem flagWindow_numerators {a m D : ℕ} {v : ℝ×ℝ} (hD : 0 < D)
    {x y : ℝ×ℝ} {B C : ℝ} (z : FlagSite a m D v) (hz : z∈flagWindow x y B C) :
    (flagSiteNumerator z).1∈cutRectangle (D*x.1) (D*y.1) (D*B) (D*C) ∧
    (flagSiteNumerator z).2∈cutRectangle (D*x.2) (D*y.2) (D*B) (D*C) := by
  have hd : (0:ℝ)<D := by exact_mod_cast hD
  have he₁ := congrArg Prod.fst (flagSiteNumerator_spec z)
  have he₂ := congrArg Prod.snd (flagSiteNumerator_spec z)
  change ordinary (flagSiteNumerator z).1/(D:ℝ)=z.val.2.val.1 at he₁
  change ordinary (flagSiteNumerator z).2/(D:ℝ)=z.val.2.val.2 at he₂
  have ho₁ := hz.1
  have ho₂ := hz.2.1
  rw [← he₁] at ho₁
  rw [← he₂] at ho₂
  have hc₁ : y.1 ≤ conjugate (flagSiteNumerator z).1/(D:ℝ) ∧
      conjugate (flagSiteNumerator z).1/(D:ℝ)≤y.1+C := hz.2.2.1
  have hc₂ : y.2 ≤ conjugate (flagSiteNumerator z).2/(D:ℝ) ∧
      conjugate (flagSiteNumerator z).2/(D:ℝ)≤y.2+C := hz.2.2.2
  simp only [Set.mem_Icc,le_div_iff₀ hd,div_le_iff₀ hd] at ho₁ ho₂ hc₁ hc₂
  constructor <;> constructor <;> constructor <;> nlinarith

theorem flagWindow_card_bound {a m D : ℕ} {v : ℝ×ℝ} (hD : 0 < D)
    (t : Fin m) {x y : ℝ×ℝ} {B C : ℝ} (hB : 0 ≤ B) (hC : 0 < C)
    (S : Finset (FlagSite a m D v)) (hT : ∀z∈S,z.val.1=t)
    (hS : ∀z∈S,z∈flagWindow x y B C) :
    (S.card:ℝ) ≤ ((D:ℝ)^2*B*C+2)^2 := by
  have hd : (0:ℝ)<D := by exact_mod_cast hD
  let T₁ := (cutRectangle_finite (D*x.1) (D*y.1) (D*B) (D*C) (mul_pos hd hC)).toFinset
  let T₂ := (cutRectangle_finite (D*x.2) (D*y.2) (D*B) (D*C) (mul_pos hd hC)).toFinset
  have hc₁ : (T₁.card:ℝ)<(D:ℝ)^2*B*C+2 := by
    have hh := cutRectangle_card_bound T₁ (D*x.1) (D*y.1) (D*B) (D*C)
      (mul_nonneg hd.le hB) (mul_pos hd hC) (fun u hu => (Set.Finite.mem_toFinset _).mp hu)
    nlinarith
  have hc₂ : (T₂.card:ℝ)<(D:ℝ)^2*B*C+2 := by
    have hh := cutRectangle_card_bound T₂ (D*x.2) (D*y.2) (D*B) (D*C)
      (mul_nonneg hd.le hB) (mul_pos hd hC) (fun u hu => (Set.Finite.mem_toFinset _).mp hu)
    nlinarith
  have hi : Set.InjOn (flagSiteNumerator (a:=a) (m:=m) (D:=D) (v:=v)) (↑S : Set (FlagSite a m D v)) := by
    intro z hz w hw hn
    apply flagSite_key_injective
    exact Prod.ext ((hT z hz).trans (hT w hw).symm) hn
  have hn : S.card ≤ T₁.card*T₂.card := by
    rw [← Finset.card_image_of_injOn hi,← Finset.card_product]
    apply Finset.card_le_card
    intro n hn
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hn
    have hh := flagWindow_numerators hD z (hS z hz)
    simpa only [Finset.mem_product,T₁,T₂,Set.Finite.mem_toFinset] using hh
  have hn' : (S.card:ℝ) ≤ (T₁.card:ℝ)*(T₂.card:ℝ) := by exact_mod_cast hn
  calc
    (S.card:ℝ) ≤ (T₁.card:ℝ)*(T₂.card:ℝ) := hn'
    _ ≤ ((D:ℝ)^2*B*C+2)*((D:ℝ)^2*B*C+2) :=
      mul_le_mul hc₁.le hc₂.le (Nat.cast_nonneg _) (by positivity)
    _ = _ := (pow_two _).symm

end FlagWindowCounts

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_DirectionStripCounts
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
section DirectionStripCounts
open Classical

theorem cutCoordinates_conjugate_bound (a : ℕ) (j : Fin 4) (p : CutRing×CutRing)
    {R : ℝ} (hR : 0 ≤ R) (hx : |conjugate p.1| ≤ R) (hy : |conjugate p.2| ≤ R) :
    |conjugate (cutCoordinates a j p).1| ≤ (1+|conjugate (cutTau^a)|)*R := by
  have hmulx := mul_le_mul_of_nonneg_left hx (abs_nonneg (conjugate (cutTau^a)))
  have hmuly := mul_le_mul_of_nonneg_left hy (abs_nonneg (conjugate (cutTau^a)))
  have hn : 0 ≤ |conjugate (cutTau^a)| * R := mul_nonneg (abs_nonneg _) hR
  fin_cases j
  · change |conjugate p.1| ≤ (1+|conjugate (cutTau^a)|)*R
    nlinarith
  · change |conjugate p.2| ≤ (1+|conjugate (cutTau^a)|)*R
    nlinarith
  · change |conjugate (p.2-cutTau^a*p.1)| ≤ (1+|conjugate (cutTau^a)|)*R
    rw [map_sub,map_mul]
    calc
      |conjugate p.2-conjugate (cutTau^a)*conjugate p.1| ≤
          |conjugate p.2| + |conjugate (cutTau^a)| * |conjugate p.1| := by
        simpa only [abs_mul] using abs_sub (conjugate p.2) (conjugate (cutTau^a)*conjugate p.1)
      _ ≤ _ := by nlinarith
  · change |conjugate (p.1-cutTau^a*p.2)| ≤ (1+|conjugate (cutTau^a)|)*R
    rw [map_sub,map_mul]
    calc
      |conjugate p.1-conjugate (cutTau^a)*conjugate p.2| ≤
          |conjugate p.1| + |conjugate (cutTau^a)| * |conjugate p.2| := by
        simpa only [abs_mul] using abs_sub (conjugate p.1) (conjugate (cutTau^a)*conjugate p.2)
      _ ≤ _ := by nlinarith

theorem flagDirectionStrip_numerators {a m D : ℕ} {v : ℝ×ℝ} (hD : 0 < D)
    (j : Fin 4) {c ε R : ℝ} (hR : 0 ≤ R) (z : FlagSite a m D v)
    (hz : z∈flagDirectionStrip j c ε R) :
    (cutCoordinates a j (flagSiteNumerator z)).1∈
      cutRectangle (D*(c-ε)) (-(D:ℝ)*(1+|conjugate (cutTau^a)|)*R)
        (2*D*ε) (2*D*(1+|conjugate (cutTau^a)|)*R) ∧
    (cutCoordinates a j (flagSiteNumerator z)).2∈
      cutRectangle 0 (-(D:ℝ)*R) D (2*D*R) := by
  have hd : (0:ℝ) < D := by exact_mod_cast hD
  have hb := flagSiteNumerator_box hD z hz.1
  have hx : |conjugate (flagSiteNumerator z).1| ≤ (D:ℝ)*R := by
    exact abs_le.mpr ⟨by linarith [hb.1.2.1],by linarith [hb.1.2.2]⟩
  have hy : |conjugate (flagSiteNumerator z).2| ≤ (D:ℝ)*R := by
    exact abs_le.mpr ⟨by linarith [hb.2.2.1],by linarith [hb.2.2.2]⟩
  have hc := abs_le.mp (cutCoordinates_conjugate_bound a j (flagSiteNumerator z)
    (mul_nonneg hd.le hR) hx hy)
  have he : ordinary (cutCoordinates a j (flagSiteNumerator z)).1 =
      (D:ℝ)*cutForm a j z.val.2.val := by
    rw [cutCoordinates_fst,← cutForm_ordinary,← cutForm_smul]
    congr 1
    have hh := flagSiteNumerator_spec z
    apply Prod.ext
    · have hh₁ := congrArg Prod.fst hh
      change ordinary (flagSiteNumerator z).1/(D:ℝ)=z.val.2.val.1 at hh₁
      simpa [smul_eq_mul,mul_comm] using (div_eq_iff hd.ne').mp hh₁
    · have hh₂ := congrArg Prod.snd hh
      change ordinary (flagSiteNumerator z).2/(D:ℝ)=z.val.2.val.2 at hh₂
      simpa [smul_eq_mul,mul_comm] using (div_eq_iff hd.ne').mp hh₂
  constructor
  · have hs := abs_le.mp hz.2
    constructor <;> constructor <;> nlinarith [hs.1,hs.2,hc.1,hc.2]
  · fin_cases j <;> first | simpa [cutCoordinates] using hb.1 | simpa [cutCoordinates] using hb.2

theorem flagDirectionStrip_card_bound {a m D : ℕ} {v : ℝ×ℝ} (hD : 0 < D)
    (j : Fin 4) {c ε R : ℝ} (hε : 0 ≤ ε) (hR : 0 < R)
    (S : Finset (FlagSite a m D v)) (hS : ∀z∈S,z∈flagDirectionStrip j c ε R) :
    (S.card:ℝ) ≤ m*(4*(D:ℝ)^2*(1+|conjugate (cutTau^a)|)*ε*R+2)*(2*(D:ℝ)^2*R+2) := by
  have hd : (0:ℝ) < D := by exact_mod_cast hD
  have hl : 0 < 1+|conjugate (cutTau^a)| := by positivity
  let T₁ := (cutRectangle_finite (D*(c-ε)) (-(D:ℝ)*(1+|conjugate (cutTau^a)|)*R)
    (2*D*ε) (2*D*(1+|conjugate (cutTau^a)|)*R) (by positivity)).toFinset
  let T₂ := (cutRectangle_finite 0 (-(D:ℝ)*R) D (2*D*R) (by positivity)).toFinset
  have hc₁ : (T₁.card:ℝ) < 4*(D:ℝ)^2*(1+|conjugate (cutTau^a)|)*ε*R+2 := by
    have hh := cutRectangle_card_bound T₁ _ _ _ _ (by positivity) (by positivity)
      (fun u hu => (Set.Finite.mem_toFinset _).mp hu)
    dsimp [T₁] at hh ⊢
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hc₂ : (T₂.card:ℝ) < 2*(D:ℝ)^2*R+2 := by
    have hh := cutRectangle_card_bound T₂ 0 (-(D:ℝ)*R) D (2*D*R) hd.le (by positivity)
      (fun u hu => (Set.Finite.mem_toFinset _).mp hu)
    nlinarith
  let key := fun z : FlagSite a m D v => (z.val.1,cutCoordinates a j (flagSiteNumerator z))
  have hi : Function.Injective key := by
    intro z w h
    have ht : z.val.1=w.val.1 := congrArg (fun x : Fin m × (CutRing×CutRing) => x.1) h
    have hn : cutCoordinates a j (flagSiteNumerator z)=cutCoordinates a j (flagSiteNumerator w) :=
      congrArg (fun x : Fin m × (CutRing×CutRing) => x.2) h
    exact flagSite_key_injective (Prod.ext ht ((cutCoordinates a j).injective hn))
  have hn : S.card ≤ m*T₁.card*T₂.card := by
    rw [← Finset.card_image_of_injective _ hi]
    have hh : S.image key ⊆ (Finset.univ : Finset (Fin m)) ×ˢ (T₁ ×ˢ T₂) := by
      intro x hx
      obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hx
      have hz' := flagDirectionStrip_numerators hD j hR.le z (hS z hz)
      simpa only [Finset.mem_product,Finset.mem_univ,true_and,key,T₁,T₂,
        Set.Finite.mem_toFinset] using hz'
    simpa only [Finset.card_product,Finset.card_univ,Fintype.card_fin,mul_assoc]
      using Finset.card_le_card hh
  have hn' : (S.card:ℝ) ≤ m*(T₁.card:ℝ)*(T₂.card:ℝ) := by exact_mod_cast hn
  exact hn'.trans (mul_le_mul
    (mul_le_mul_of_nonneg_left hc₁.le (Nat.cast_nonneg _)) hc₂.le
    (Nat.cast_nonneg _) (by positivity))

end DirectionStripCounts

section ExceptionalRowCounts
open Classical

theorem flagDirectionStrip_union_card_bound {a m D : ℕ} {v : ℝ×ℝ} (hD : 0 < D)
    (j : Fin 4) (T : Finset CutRing) {ε R : ℝ} (hε : 0 ≤ ε) (hR : 0 < R)
    (S : Finset (FlagSite a m D v))
    (hS : ∀z∈S,∃c∈T,z∈flagDirectionStrip j (ordinary c) ε R) :
    (S.card:ℝ) ≤ T.card*(m*(4*(D:ℝ)^2*(1+|conjugate (cutTau^a)|)*ε*R+2)*
      (2*(D:ℝ)^2*R+2)) := by
  let rows := fun c => S.filter (fun z => z∈flagDirectionStrip j (ordinary c) ε R)
  have hh : S ⊆ T.biUnion rows := by
    intro z hz
    obtain ⟨c,hc,hzc⟩ := hS z hz
    exact Finset.mem_biUnion.mpr ⟨c,hc,Finset.mem_filter.mpr ⟨hz,hzc⟩⟩
  have hn : S.card ≤ ∑c∈T,(rows c).card :=
    (Finset.card_le_card hh).trans (Finset.card_biUnion_le)
  have hn' : (S.card:ℝ) ≤ ∑c∈T,((rows c).card:ℝ) := by exact_mod_cast hn
  calc
    (S.card:ℝ) ≤ ∑c∈T,((rows c).card:ℝ) := hn'
    _ ≤ ∑c∈T,(m*(4*(D:ℝ)^2*(1+|conjugate (cutTau^a)|)*ε*R+2)*
        (2*(D:ℝ)^2*R+2)) := by
      apply Finset.sum_le_sum
      intro c hc
      exact flagDirectionStrip_card_bound hD j hε hR (rows c)
        (fun z hz => (Finset.mem_filter.mp hz).2)
    _ = _ := by simp [nsmul_eq_mul]

theorem boundedCutLevels_eq (A B : ℝ) :
    boundedCutLevels A B = cutRectangle (-A) (-B) (2*A) (2*B) := by
  ext c
  simp only [boundedCutLevels,cutRectangle,Set.mem_ofPred_eq,Set.mem_Icc,abs_le]
  constructor <;> rintro ⟨⟨h₁,h₂⟩,⟨h₃,h₄⟩⟩ <;> constructor <;> constructor <;> linarith

theorem boundedCutLevels_finite (A : ℝ) {B : ℝ} (hB : 0 < B) :
    (boundedCutLevels A B).Finite := by
  rw [boundedCutLevels_eq]
  exact cutRectangle_finite _ _ _ _ (by positivity)

theorem boundedCutLevels_card_bound {A B : ℝ} (hA : 0 ≤ A) (hB : 0 < B)
    (T : Finset CutRing) (hT : ∀c∈T,c∈boundedCutLevels A B) :
    (T.card:ℝ) < 4*A*B+2 := by
  have hh := cutRectangle_card_bound T (-A) (-B) (2*A) (2*B) (by positivity)
    (by positivity) (fun c hc => by rw [← boundedCutLevels_eq]; exact hT c hc)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ring

theorem exceptional_direction_rows {a m D : ℕ} {v : ℝ×ℝ} (hD : 0 < D)
    (j : Fin 4) {A C Q κ s N : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) (hQ : 0 < Q)
    (hκ : 0 < κ) (hs : 0 < s) (hN : 1 ≤ N) (hscale : 1 ≤ s*N)
    (S : Finset (FlagSite a m D v))
    (hS : ∀z∈S,∃c : CutRing, |ordinary c| ≤ A ∧ |conjugate c| ≤ 2*κ/s ∧
      z∈flagDirectionStrip j (ordinary c) (C*s) (Q*N)) :
    (S.card:ℝ) ≤
      (m*(4*(D:ℝ)^2*(1+|conjugate (cutTau^a)|)*C*Q+2)*(2*(D:ℝ)^2*Q+2)*(8*A+2))*
        (κ+s)*N^2 := by
  have hd : (0:ℝ) < D := by exact_mod_cast hD
  have hN' : 0 < N := lt_of_lt_of_le zero_lt_one hN
  let T := (boundedCutLevels_finite A (show 0 < 2*κ/s by positivity)).toFinset
  have hTc : (T.card:ℝ) ≤ 8*A*κ/s+2 := by
    have hh := boundedCutLevels_card_bound hA (show 0 < 2*κ/s by positivity) T
      (fun c hc => (Set.Finite.mem_toFinset _).mp hc)
    have he : 4*A*(2*κ/s)+2=8*A*κ/s+2 := by ring
    rw [he] at hh
    exact hh.le
  have hTu := flagDirectionStrip_union_card_bound hD j T
    (mul_nonneg hC hs.le) (mul_pos hQ hN') S (by
      intro z hz
      obtain ⟨c,hc₁,hc₂,hzc⟩ := hS z hz
      exact ⟨c,(Set.Finite.mem_toFinset _).mpr ⟨hc₁,hc₂⟩,hzc⟩)
  let U := 4*(D:ℝ)^2*(1+|conjugate (cutTau^a)|)*C*Q
  let V := 2*(D:ℝ)^2*Q
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have he₁ : 4*(D:ℝ)^2*(1+|conjugate (cutTau^a)|)*(C*s)*(Q*N)+2 ≤ (U+2)*(s*N) := by
    dsimp [U]
    nlinarith
  have he₂ : 2*(D:ℝ)^2*(Q*N)+2 ≤ (V+2)*N := by
    dsimp [V]
    nlinarith
  have hf : 8*A*κ+2*s ≤ (8*A+2)*(κ+s) := by
    nlinarith [mul_nonneg hA hs.le]
  calc
    (S.card:ℝ) ≤ T.card*(m*(4*(D:ℝ)^2*(1+|conjugate (cutTau^a)|)*(C*s)*(Q*N)+2)*
        (2*(D:ℝ)^2*(Q*N)+2)) := hTu
    _ ≤ (8*A*κ/s+2)*(m*((U+2)*(s*N))*((V+2)*N)) := by
      apply mul_le_mul hTc
      · exact mul_le_mul (mul_le_mul_of_nonneg_left he₁ (Nat.cast_nonneg _)) he₂
          (by positivity) (by positivity)
      · positivity
      · positivity
    _ = (m*(U+2)*(V+2))*(8*A*κ+2*s)*N^2 := by field_simp
    _ ≤ (m*(U+2)*(V+2))*((8*A+2)*(κ+s))*N^2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hf (by positivity)) (sq_nonneg N)
    _ = _ := by dsimp [U,V]; ring

end ExceptionalRowCounts

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

theorem thresholdLaw_isProbability {s κ : ℝ} (hs : 0 < s) (hκ : 0<κ) :
    IsProbabilityMeasure (thresholdLaw s κ) := by
  have hlt : κ/s<2*κ/s := by exact (div_lt_div_iff_of_pos_right hs).mpr (by linarith)
  have : IsProbabilityMeasure (ProbabilityTheory.cond volume (Set.Icc (κ/s) (2*κ/s))) :=
    ProbabilityTheory.cond_isProbabilityMeasure_of_finite
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_zero_iff.mpr (sub_pos.mpr hlt))
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  unfold thresholdLaw
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

theorem separatorMatrix_bounds {a : ℕ} {v : ℝ×ℝ}
    (μ : Measure (Fin 4 → ℝ)) [IsProbabilityMeasure μ] (z w : SquareFlag a v) :
    0 ≤ separatorMatrix μ z w ∧ separatorMatrix μ z w≤1 := by
  rw [separatorMatrix_eq_measure]
  exact ⟨ENNReal.toReal_nonneg,measureReal_le_one⟩

end FlagSeparatorMatrices

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

theorem squareFlag_cutForm_bound {a : ℕ} {v : ℝ×ℝ} (j : Fin 4) (z : SquareFlag a v) :
    |cutForm a j z.val| ≤ 1+|ordinary (cutTau^a)| := by
  have hn : ‖z.val‖ ≤ (1:ℝ) := by
    rw [Prod.norm_def]
    apply max_le
    · rw [Real.norm_eq_abs,abs_of_nonneg z.property.2.1.1]
      exact z.property.2.1.2
    · rw [Real.norm_eq_abs,abs_of_nonneg z.property.2.2.1.1]
      exact z.property.2.2.1.2
  have hz : cutForm a j 0=0 := by fin_cases j <;> simp [cutForm]
  have hh := cutForm_dist_bound a j z.val 0
  rw [hz,sub_zero,dist_zero_right] at hh
  exact hh.trans (by nlinarith [abs_nonneg (ordinary (cutTau^a))])

theorem flagBadSeparatorRow_card_bound {a m D : ℕ} {v : ℝ×ℝ} (hD : 0 < D)
    {Q κ s N : ℝ} (hQ : 0 < Q) (hκ : 0 < κ) (hs : 0 < s)
    (hs₁ : s ≤ 1) (hN : 1 ≤ N) (hscale : 1 ≤ s*N)
    (S : Finset (FlagSite a m D v)) (hS : ∀z∈S,z∈flagBadSeparatorRow s κ (Q*N)) :
    (S.card:ℝ) ≤ 4*(m*(4*(D:ℝ)^2*(1+|conjugate (cutTau^a)|)*(1+|ordinary (cutTau^a)|)*Q+2)*
      (2*(D:ℝ)^2*Q+2)*(16*(1+|ordinary (cutTau^a)|)+2))*(κ+s)*N^2 := by
  let L : ℝ := 1+|ordinary (cutTau^a)|
  have hL : 0 ≤ L := by dsimp [L]; positivity
  let row := fun j : Fin 4 => S.filter (fun z => ∃c : CutRing, |conjugate c| ≤ 2*κ/s ∧
    |cutForm a j z.val.2.val-ordinary c| ≤ L*s)
  have hh : S ⊆ Finset.univ.biUnion row := by
    intro z hz
    obtain ⟨j,c,hc,hd⟩ := (hS z hz).2
    exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,Finset.mem_filter.mpr ⟨hz,c,hc,hd⟩⟩
  have hc j := exceptional_direction_rows hD j (show 0 ≤ 2*L by positivity) hL hQ hκ hs hN hscale
    (row j) (by
      intro z hz
      obtain ⟨hzS,c,hc,hd⟩ := Finset.mem_filter.mp hz
      refine ⟨c,?_,hc,(hS z hzS).1,hd⟩
      have hb := squareFlag_cutForm_bound j z.val.2
      have htri := abs_sub_le (ordinary c) (cutForm a j z.val.2.val) 0
      rw [sub_zero,sub_zero,abs_sub_comm (ordinary c)] at htri
      change |cutForm a j z.val.2.val| ≤ L at hb
      exact htri.trans (by nlinarith))
  have hn : S.card ≤ ∑j : Fin 4,(row j).card :=
    (Finset.card_le_card hh).trans Finset.card_biUnion_le
  have hn' : (S.card:ℝ) ≤ ∑j : Fin 4,((row j).card:ℝ) := by exact_mod_cast hn
  refine hn'.trans ((Finset.sum_le_sum (fun j _ => hc j)).trans_eq ?_)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  dsimp [L]
  ring

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
section FlagAveragingMatrices
open Classical MeasureTheory

theorem planeTent_nonneg (s : ℝ) (x y : ℝ×ℝ) : 0 ≤ planeTent s x y :=
  mul_nonneg (le_max_right _ _) (le_max_right _ _)

theorem planeTent_le_one (s : ℝ) (x y : ℝ×ℝ) : planeTent s x y ≤ 1 := by
  have h₁ : max (1-|(x.1-y.1)/s|) 0 ≤ 1 := max_le (by linarith [abs_nonneg ((x.1-y.1)/s)]) zero_le_one
  have h₂ : max (1-|(x.2-y.2)/s|) 0 ≤ 1 := max_le (by linarith [abs_nonneg ((x.2-y.2)/s)]) zero_le_one
  exact (mul_le_mul h₁ h₂ (le_max_right _ _) zero_le_one).trans_eq (one_mul 1)

theorem flagAveragingMatrix_cutoff_left {a m D : ℕ} {v : ℝ×ℝ}
    (χ : (ℝ×ℝ) → ℝ) (ρ N r η κ : ℝ) (z w : FlagSite a m D v)
    (hz : χ (scaledSiteConjugate N z)=0) : flagAveragingMatrix χ ρ N r η κ z w=0 := by
  simp [flagAveragingMatrix,hz]

theorem flagAveragingMatrix_cutoff_right {a m D : ℕ} {v : ℝ×ℝ}
    (χ : (ℝ×ℝ) → ℝ) (ρ N r η κ : ℝ) (z w : FlagSite a m D v)
    (hw : χ (scaledSiteConjugate N w)=0) : flagAveragingMatrix χ ρ N r η κ z w=0 := by
  simp [flagAveragingMatrix,hw]

end FlagAveragingMatrices

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

theorem flagAveragingMatrix_localization {a m D : ℕ} {v : ℝ×ℝ}
    (χ : (ℝ×ℝ) → ℝ) (ρ κ : ℝ) {N r η : ℝ} (hN : 0 < N) (hr : 0 < r)
    (hη : 0 < η) (z w : FlagSite a m D v)
    (hw : flagAveragingMatrix χ ρ N r η κ z w ≠ 0) :
    w.val.1=z.val.1 ∧ w∈flagWindow
      (z.val.2.val.1-r/N,z.val.2.val.2-r/N)
      ((flagSiteConjugate z).1-N*η,(flagSiteConjugate z).2-N*η) (2*(r/N)) (2*(N*η)) := by
  have ht : z.val.1=w.val.1 := by
    by_contra hh
    simp [flagAveragingMatrix,hh] at hw
  have hk₁ : planeTent (r/N) (flagSiteOrdinary z) (flagSiteOrdinary w) ≠ 0 := by
    intro he
    simp [flagAveragingMatrix,he] at hw
  have hk₂ : planeTent (N*η) (flagSiteConjugate z) (flagSiteConjugate w) ≠ 0 := by
    intro he
    simp [flagAveragingMatrix,he] at hw
  have hx := (planeTent_ne_zero (div_pos hr hN) _ _).mp hk₁
  have hy := (planeTent_ne_zero (mul_pos hN hη) _ _).mp hk₂
  have hx₁ := abs_lt.mp hx.1
  have hx₂ := abs_lt.mp hx.2
  have hy₁ := abs_lt.mp hy.1
  have hy₂ := abs_lt.mp hy.2
  refine ⟨ht.symm,?_,?_,?_,?_⟩ <;>
    simp only [flagSiteOrdinary] at hx₁ hx₂ <;> constructor <;> linarith

theorem flagAveragingMatrix_row_card {a m D : ℕ} {v : ℝ×ℝ} (hD : 0 < D)
    (χ : (ℝ×ℝ) → ℝ) (ρ κ : ℝ) {N r η : ℝ} (hN : 0 < N) (hr : 0 < r)
    (hη : 0 < η) (z : FlagSite a m D v) (S : Finset (FlagSite a m D v))
    (hS : ∀w∈S,flagAveragingMatrix χ ρ N r η κ z w ≠ 0) :
    (S.card:ℝ) ≤ (4*(D:ℝ)^2*r*η+2)^2 := by
  have hloc := fun w hw => flagAveragingMatrix_localization χ ρ κ hN hr hη z w (hS w hw)
  have hc := flagWindow_card_bound hD z.val.1
    (show 0 ≤ 2*(r/N) by positivity) (show 0 < 2*(N*η) by positivity) S
    (fun w hw => (hloc w hw).1) (fun w hw => (hloc w hw).2)
  have he : (D:ℝ)^2*(2*(r/N))*(2*(N*η))+2=4*(D:ℝ)^2*r*η+2 := by
    field_simp
    ring
  rwa [he] at hc

theorem flagAveragingMatrix_entry_bounds {a m D : ℕ} {v : ℝ×ℝ}
    (χ : (ℝ×ℝ) → ℝ) (hχ : ∀x,χ x∈Set.Icc (0:ℝ) 1)
    {ρ N r η κ : ℝ} (hρ : 0 < ρ) (hN : 0 < N) (hr : 0 < r)
    (hη : 0 < η) (hκ : 0 < κ) (z w : FlagSite a m D v) :
    0 ≤ flagAveragingMatrix χ ρ N r η κ z w ∧
    flagAveragingMatrix χ ρ N r η κ z w ≤ (ρ*(r*η)^2)⁻¹ := by
  have : IsProbabilityMeasure (thresholdLaw (r/N) κ) := thresholdLaw_isProbability (div_pos hr hN) hκ
  have hp := separatorMatrix_bounds (thresholdLaw (r/N) κ) z.val.2 w.val.2
  have hk₁ := planeTent_nonneg (r/N) (flagSiteOrdinary z) (flagSiteOrdinary w)
  have hk₂ := planeTent_nonneg (N*η) (flagSiteConjugate z) (flagSiteConjugate w)
  have hk₁' := planeTent_le_one (r/N) (flagSiteOrdinary z) (flagSiteOrdinary w)
  have hk₂' := planeTent_le_one (N*η) (flagSiteConjugate z) (flagSiteConjugate w)
  have hχz := hχ (scaledSiteConjugate N z)
  have hχw := hχ (scaledSiteConjugate N w)
  have hd : 0 < ρ*(r*η)^2 := mul_pos hρ (sq_pos_of_pos (mul_pos hr hη))
  unfold flagAveragingMatrix
  split_ifs
  · constructor
    · exact mul_nonneg (mul_nonneg (mul_nonneg
        (div_nonneg (mul_nonneg hχz.1 hχw.1) hd.le) hk₁) hk₂) hp.1
    · have hc : χ (scaledSiteConjugate N z)*χ (scaledSiteConjugate N w) ≤ 1 :=
        (mul_le_mul hχz.2 hχw.2 hχw.1 zero_le_one).trans_eq (one_mul 1)
      calc
        _ ≤ (1/(ρ*(r*η)^2))*1*1*1 := by gcongr <;> first | exact hp.1 | exact hp.2
        _ = _ := by ring
  · exact ⟨le_rfl,inv_nonneg.mpr hd.le⟩

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

theorem flagMeanSignal_outside {a m D : ℕ} {v : ℝ×ℝ}
    (θ : (ℝ×ℝ) → ℝ) {q K N : ℝ} (hN : 0<N)
    (hcompact : ∀x,K ≤ ‖x‖ → θ x=q) (z : FlagSite a m D v)
    (hz : z∉flagSiteBox (N*K)) : flagMeanSignal θ N z=q := by
  apply hcompact
  by_contra hh
  have hh' : ‖scaledSiteConjugate N z‖<K := lt_of_not_ge hh
  have h₁ := norm_fst_le (scaledSiteConjugate N z)
  have h₂ := norm_snd_le (scaledSiteConjugate N z)
  simp only [scaledSiteConjugate,Real.norm_eq_abs,abs_div,abs_of_pos hN] at h₁ h₂
  apply hz
  constructor
  · have h := (div_lt_iff₀ hN).mp (h₁.trans_lt hh'); nlinarith
  · have h := (div_lt_iff₀ hN).mp (h₂.trans_lt hh'); nlinarith

end FlagSignalEnergy

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_WeightedAveragingError
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
section WeightedAveragingError
open Classical

theorem squared_error_good_bad {ι : Type*} (T B : Finset ι) (e : ι → ℝ)
    {E H : ℝ} (hE : 0≤E) (hH : 0≤H)
    (hgood : ∀i∈T,i∉B → |e i|≤E) (hbad : ∀i∈T,|e i|≤H) :
    ∑i∈T,(e i)^2 ≤ (T.card:ℝ)*E^2+(B.card:ℝ)*H^2 := by
  have hh : ∀i∈T,(e i)^2 ≤ E^2 + (if i∈B then H^2 else 0) := by
    intro i hi
    by_cases hb : i∈B
    · rw [ite_eq_left hb]
      have he := (sq_le_sq₀ (abs_nonneg _) hH).mpr (hbad i hi)
      rw [sq_abs] at he
      linarith [sq_nonneg E]
    · rw [ite_eq_right hb,add_zero]
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hE).mpr (hgood i hi hb)
  calc
    _ ≤ ∑i∈T,(E^2+(if i∈B then H^2 else 0)) := Finset.sum_le_sum hh
    _ = (T.card:ℝ)*E^2+((T.filter (·∈B)).card:ℝ)*H^2 := by
      rw [Finset.sum_add_distrib,← Finset.sum_filter]
      simp only [Finset.sum_const,nsmul_eq_mul]
    _ ≤ _ := by
      have hc : ((T.filter (·∈B)).card:ℝ) ≤ (B.card:ℝ) := by
        exact_mod_cast Finset.card_le_card (show T.filter (·∈B) ⊆ B from fun i hi => (Finset.mem_filter.mp hi).2)
      linarith [mul_le_mul_of_nonneg_right hc (sq_nonneg H)]

end WeightedAveragingError

section SignalChartVariation
open Classical

theorem flagSignalDifference_add_constant {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) (ψ : (ℝ×ℝ) → ℝ) (q N : ℝ) (z : FlagSite a m D v) :
    flagSignalDifference hD g (fun x => q+ψ x) N z=flagSignalDifference hD g ψ N z := by
  unfold flagSignalDifference flagMeanSignal
  ring

end SignalChartVariation

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

end SignalCutoff

section AveragingL1Rows
open Classical

theorem flagAveragingMatrix_row_sum {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (χ : (ℝ×ℝ) → ℝ) (hχ : ∀x,χ x∈Set.Icc (0:ℝ) 1)
    {ρ N r η κ : ℝ} (hρ : 0<ρ) (hN : 0<N) (hr : 0 < r) (hη : 0<η) (hκ : 0<κ)
    (z : FlagSite a m D v) (S : Finset (FlagSite a m D v)) :
    ∑w∈S,flagAveragingMatrix χ ρ N r η κ z w ≤
      (4*(D:ℝ)^2*r*η+2)^2/(ρ*(r*η)^2) := by
  let T := S.filter (fun w => flagAveragingMatrix χ ρ N r η κ z w≠0)
  have he : (∑w∈S,flagAveragingMatrix χ ρ N r η κ z w)=
      ∑w∈T,flagAveragingMatrix χ ρ N r η κ z w := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro w hw hwt
    simpa [T,hw] using hwt
  rw [he]
  have hc := flagAveragingMatrix_row_card hD χ ρ κ hN hr hη z T
    (fun w hw => (Finset.mem_filter.mp hw).2)
  calc
    _ ≤ ∑_w∈T,(ρ*(r*η)^2)⁻¹ := Finset.sum_le_sum
      (fun w _ => (flagAveragingMatrix_entry_bounds χ hχ hρ hN hr hη hκ z w).2)
    _ = (T.card:ℝ)*(ρ*(r*η)^2)⁻¹ := by simp
    _ ≤ (4*(D:ℝ)^2*r*η+2)^2*(ρ*(r*η)^2)⁻¹ := mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by rw [div_eq_mul_inv]

theorem flagAveragingMatrix_row_sum_uniform {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (χ : (ℝ×ℝ) → ℝ) (hχ : ∀x,χ x∈Set.Icc (0:ℝ) 1)
    {ρ N r η κ : ℝ} (hρ : 0<ρ) (hN : 0<N) (hr : 0 < r) (hη : 0<η) (hκ : 0<κ)
    (hscale : 1 ≤ r*η) (z : FlagSite a m D v) (S : Finset (FlagSite a m D v)) :
    ∑w∈S,flagAveragingMatrix χ ρ N r η κ z w ≤ (4*(D:ℝ)^2+2)^2/ρ := by
  have hh := flagAveragingMatrix_row_sum hD χ hχ hρ hN hr hη hκ z S
  refine hh.trans ?_
  have hle : 4*(D:ℝ)^2*r*η+2 ≤ (4*(D:ℝ)^2+2)*(r*η) := by nlinarith
  have hb := pow_le_pow_left₀ (show 0 ≤ 4*(D:ℝ)^2*r*η+2 by positivity) hle 2
  calc
    _ ≤ ((4*(D:ℝ)^2+2)*(r*η))^2/(ρ*(r*η)^2) := div_le_div_of_nonneg_right hb (by positivity)
    _ = _ := by field_simp

theorem flagAveragingMatrix_crude_error {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (χ : (ℝ×ℝ) → ℝ) (hχ : ∀x,χ x∈Set.Icc (0:ℝ) 1)
    (h : FlagSite a m D v → ℝ) {ρ N r η κ H : ℝ}
    (hρ : 0<ρ) (hN : 0<N) (hr : 0 < r) (hη : 0<η) (hκ : 0<κ)
    (hscale : 1 ≤ r*η) (hH : 0 ≤ H) (hamp : ∀z,|h z| ≤ H)
    (z : FlagSite a m D v) (S : Finset (FlagSite a m D v)) :
    |(∑w∈S,flagAveragingMatrix χ ρ N r η κ z w*h w)-h z| ≤
      ((4*(D:ℝ)^2+2)^2/ρ+1)*H := by
  have hsum : |∑w∈S,flagAveragingMatrix χ ρ N r η κ z w*h w| ≤
      ((4*(D:ℝ)^2+2)^2/ρ)*H := by
    calc
      _ ≤ ∑w∈S,|flagAveragingMatrix χ ρ N r η κ z w*h w| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑w∈S,flagAveragingMatrix χ ρ N r η κ z w*H := by
        apply Finset.sum_le_sum
        intro w hw
        have hm := (flagAveragingMatrix_entry_bounds χ hχ hρ hN hr hη hκ z w).1
        rw [abs_mul,abs_of_nonneg hm]
        exact mul_le_mul_of_nonneg_left (hamp w) hm
      _ = (∑w∈S,flagAveragingMatrix χ ρ N r η κ z w)*H := (Finset.sum_mul _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (flagAveragingMatrix_row_sum_uniform hD χ hχ hρ hN hr hη hκ hscale z S) hH
  have ht := abs_sub (∑w∈S,flagAveragingMatrix χ ρ N r η κ z w*h w) (h z)
  nlinarith [hamp z]

end AveragingL1Rows

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

section SignalActiveBox
open Classical

theorem flagAveragingMatrix_box_support {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (χ : (ℝ×ℝ) → ℝ) {L N : ℝ} (hL : 0<L) (hN : 0<N)
    (hχc : ∀x,L ≤ ‖x‖ → χ x=0) (ρ r η κ : ℝ) (z w : FlagSite a m D v)
    (hz : z∉flagBoxFinset hD (mul_pos hN hL) ∨ w∉flagBoxFinset hD (mul_pos hN hL)) :
    flagAveragingMatrix χ ρ N r η κ z w=0 := by
  rcases hz with hz | hw
  · exact flagAveragingMatrix_cutoff_left χ ρ N r η κ z w
      (flagMeanSignal_outside χ hN hχc z (by simpa only [mem_flagBoxFinset] using hz))
  · exact flagAveragingMatrix_cutoff_right χ ρ N r η κ z w
      (flagMeanSignal_outside χ hN hχc w (by simpa only [mem_flagBoxFinset] using hw))

theorem flagSignal_box_support {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) (ψ : (ℝ×ℝ) → ℝ) (q : ℝ) {K L : ℝ}
    (hL : 0<L) (hKL : K+1 ≤ L) (hcompact : ∀x,K ≤ ‖x‖ → ψ x=0) :
    ∃Q : ℝ,0 ≤ Q ∧ ∀(N : ℝ) (hN : 0<N),Q ≤ N → ∀z : FlagSite a m D v,
      z∉flagBoxFinset hD (mul_pos hN hL) →
        flagSignalDifference hD g (fun x => q+ψ x) N z=0 := by
  obtain ⟨Q,hQ,hdisp⟩ := scaledSiteConjugate_displacement (v:=v) hD g⁻¹
  refine ⟨Q,hQ,fun N hN hQN z hz => ?_⟩
  by_contra hh
  have hn := flagSignalDifference_ne_zero_near hD g ψ q hcompact hQ hN (hdisp N hN) z hh
  simp only [scaledSiteConjugate] at hn
  have hqn : Q/N ≤ 1 := (div_le_one hN).mpr hQN
  have hx := norm_fst_le (scaledSiteConjugate N z)
  have hy := norm_snd_le (scaledSiteConjugate N z)
  simp only [scaledSiteConjugate,Real.norm_eq_abs,abs_div,abs_of_pos hN] at hx hy
  apply hz
  rw [mem_flagBoxFinset]
  have hxL : |(flagSiteConjugate z).1|/N ≤ L := by linarith
  have hyL : |(flagSiteConjugate z).2|/N ≤ L := by linarith
  exact ⟨by simpa only [mul_comm L N] using (div_le_iff₀ hN).mp hxL,
    by simpa only [mul_comm L N] using (div_le_iff₀ hN).mp hyL⟩

end SignalActiveBox

section ApproximationEnergy
open Classical

theorem flag_good_bad_energy {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    {Q κ s N E H : ℝ} (hQ : 0<Q) (hκ : 0<κ) (hs : 0 < s) (hs₁ : s ≤ 1)
    (hN : 1 ≤ N) (hscale : 1 ≤ s*N) (hE : 0 ≤ E) (hH : 0 ≤ H)
    (T : Finset (FlagSite a m D v)) (hT : ∀z∈T,z∈flagSiteBox (Q*N))
    (e : FlagSite a m D v → ℝ)
    (hgood : ∀z∈T,flagGoodRow s κ z → |e z| ≤ E/N)
    (hbad : ∀z∈T,|e z| ≤ H/N) :
    ∑z∈T,(e z)^2 ≤ flagVolumeConstant m D Q*E^2+
      flagExceptionalConstant a m D Q*(κ+s)*H^2 := by
  have hN' : 0<N := lt_of_lt_of_le zero_lt_one hN
  let B := T.filter (fun z => ¬flagGoodRow s κ z)
  have hb : (B.card:ℝ) ≤ flagExceptionalConstant a m D Q*(κ+s)*N^2 := by
    apply flagBadSeparatorRow_card_bound hD hQ hκ hs hs₁ hN hscale B
    intro z hz
    obtain ⟨hzt,hzb⟩ := Finset.mem_filter.mp hz
    refine ⟨hT z hzt,?_⟩
    simp only [flagGoodRow,not_forall,not_lt] at hzb
    obtain ⟨j,c,hc,he⟩ := hzb
    exact ⟨j,c,hc,he⟩
  have ht : (T.card:ℝ) ≤ flagVolumeConstant m D Q*N^2 := by
    have hh := flagSiteBox_card_bound hD (mul_pos hQ hN') T hT
    have he : 2*(D:ℝ)^2*(Q*N)+2 ≤ (2*(D:ℝ)^2*Q+2)*N := by nlinarith
    refine hh.trans ?_
    calc
      _ ≤ m*((2*(D:ℝ)^2*Q+2)*N)^2 := by gcongr
      _ = _ := by dsimp [flagVolumeConstant]; ring
  have hh := squared_error_good_bad T B e (div_nonneg hE hN'.le) (div_nonneg hH hN'.le)
    (by
      intro z hz hzb
      apply hgood z hz
      by_contra he
      exact hzb (Finset.mem_filter.mpr ⟨hz,he⟩)) hbad
  refine hh.trans ?_
  calc
    _ ≤ (flagVolumeConstant m D Q*N^2)*(E/N)^2+
        (flagExceptionalConstant a m D Q*(κ+s)*N^2)*(H/N)^2 := by
      gcongr
    _ = _ := by field_simp

end ApproximationEnergy

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_PolygonApproxIdentity
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
section PolygonApproxIdentity
open Classical

theorem polygon_signal_approx_identity_oai {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) (ψ χ : (ℝ×ℝ) → ℝ)
    (hψ : ContDiff ℝ 2 ψ) (hsψ : HasCompactSupport ψ) (q K L : ℝ)
    (hL : 0<L) (hKL : K+2 ≤ L)
    (hcompact : ∀x,K ≤ ‖x‖ → ψ x=0)
    (hχ : ∀x,χ x∈Set.Icc (0:ℝ) 1)
    (hχ₁ : ∀x,‖x‖ ≤ K+2 → χ x=1)
    (hχc : ∀x,L ≤ ‖x‖ → χ x=0) :
    ∃R Q Cv Ca : ℝ,0 ≤ R ∧ 0 ≤ Q ∧ 0 ≤ Cv ∧ 0 ≤ Ca ∧
      ∀(N r η κ : ℝ) (hN : 1 ≤ N),Q ≤ N → 1 ≤ r → r ≤ N →
        0<η → η ≤ 1 → 0<κ → 36 ≤ r*η → 1 ≤ 2*κ/(r/N) → R ≤ κ/(r/N) →
        let J := flagBoxFinset (a:=a) (m:=m) (v:=v) hD
          (mul_pos (lt_of_lt_of_le zero_lt_one hN) hL)
        let h := flagSignalDifference (v:=v) hD g (fun x => q+ψ x) N
        let e := fun z => (∑w∈J,flagAveragingMatrix χ ((D:ℝ)^4/5) N r η κ z w*h w)-h z
        let δ := 38880/((D:ℝ)*Real.sqrt (r*η))
        (∀z,z∉J → e z=0) ∧
        ∑z∈J,(e z)^2 ≤ flagVolumeConstant m D L*(Cv*η*(1+δ)+Ca*δ)^2+
          flagExceptionalConstant a m D L*(κ+r/N)*(flagRowSumConstant D*Ca)^2 := by
  obtain ⟨R,Q₁,Cv,Ca,hR,hQ₁,hCv,hCa,hamp,hgood⟩ :=
    flagSignal_good_row_constants (v:=v) hD g ψ χ hψ hsψ q K hcompact hχ₁
  obtain ⟨Q₂,hQ₂,hsupp⟩ := flagSignal_box_support (v:=v) hD g ψ q hL (by linarith) hcompact
  refine ⟨R,max Q₁ Q₂,Cv,Ca,hR,(hQ₁.trans (le_max_left _ _)),hCv,hCa,
    fun N r η κ hN hQN hr hrN hη hη₁ hκ hscale hline hRf => ?_⟩
  have hN' : 0<N := lt_of_lt_of_le zero_lt_one hN
  have hr' : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hd : (0:ℝ)<D := by exact_mod_cast hD
  have hρ : 0<(D:ℝ)^4/5 := by positivity
  let J := flagBoxFinset (a:=a) (m:=m) (v:=v) hD (mul_pos hN' hL)
  let h := flagSignalDifference (v:=v) hD g (fun x => q+ψ x) N
  let e := fun z => (∑w∈J,flagAveragingMatrix χ ((D:ℝ)^4/5) N r η κ z w*h w)-h z
  let δ := 38880/((D:ℝ)*Real.sqrt (r*η))
  change (∀z,z∉J → e z=0) ∧ _
  have hprod (z w : FlagSite a m D v) (hw : w∉J) :
      flagAveragingMatrix χ ((D:ℝ)^4/5) N r η κ z w*h w=0 := by
    rw [flagAveragingMatrix_box_support hD χ hL hN' hχc _ _ _ _ z w (Or.inr hw),zero_mul]
  refine ⟨?_,?_⟩
  · intro z hz
    have hh := hsupp N hN' ((le_max_right _ _).trans hQN) z hz
    dsimp [e,h]
    rw [hh,sub_zero]
    apply Finset.sum_eq_zero
    intro w hw
    rw [flagAveragingMatrix_box_support hD χ hL hN' hχc _ _ _ _ z w (Or.inl hz),zero_mul]
  · apply flag_good_bad_energy hD hL hκ (div_pos hr' hN') ((div_le_one hN').mpr hrN) hN
        (by rwa [div_mul_cancel₀ _ hN'.ne'])
        (show 0 ≤ Cv*η*(1+δ)+Ca*δ by dsimp [δ]; positivity)
        (show 0 ≤ flagRowSumConstant D*Ca by dsimp [flagRowSumConstant]; positivity) J
        (fun z hz => by simpa only [mul_comm N L] using (mem_flagBoxFinset _ _ _).mp hz) e
    · intro z hz hzg
      have hh := hgood N r η κ hN' ((le_max_left _ _).trans hQN) hr' hη hη₁ hκ
        hscale hline hRf z J hzg (hprod z)
      convert hh using 1
      all_goals try with_reducible_and_instances rfl
      dsimp [e,h,δ]
      ring
    · intro z hz
      have hh := flagAveragingMatrix_crude_error hD χ hχ h hρ hN' hr' hη hκ
        (show 1 ≤ r*η by linarith) (div_nonneg hCa hN'.le) (hamp N hN') z J
      convert hh using 1
      all_goals try with_reducible_and_instances rfl
      dsimp [e,flagRowSumConstant]
      ring

end PolygonApproxIdentity

end SimpleAmenable
end
end

end OAI
end

theorem solution : type_of% @OAI.SimpleAmenable.polygon_signal_approx_identity_oai := @OAI.SimpleAmenable.polygon_signal_approx_identity_oai
