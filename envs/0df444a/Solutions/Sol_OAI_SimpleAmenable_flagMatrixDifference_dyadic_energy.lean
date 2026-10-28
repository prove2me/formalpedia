-- Prove2me | solution 1 for OAI.SimpleAmenable.flagMatrixDifference_dyadic_energy
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T04:48:21.674704+00:00
-- url     : https://prove2.me/submissions/377cb937-e708-42d9-9de9-7019b94ccb37

import Mathlib
import Definitions.Def_OAIQ65Sa014

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

theorem flagMem_halfPlane_local_translation {a : ℕ} {v : ℝ×ℝ}
    (u : CutRing×CutRing) (j : Fin 4) (c : CutRing) (z z' : SquareFlag a v)
    (hz : z'.val=z.val+(ordinary u.1,ordinary u.2)) :
    flagMem ⟨halfPlane a j (c+integralCutForm a j u),halfPlane_mem _ _ _⟩ z' ↔
      flagMem ⟨halfPlane a j c,halfPlane_mem _ _ _⟩ z := by
  rw [flagMem_halfPlane,flagMem_halfPlane,hz,cutForm_add,cutForm_ordinary,map_add]
  simp only [add_left_inj,add_lt_add_iff_right]

theorem flagSeparates_local_translation {a : ℕ} {v : ℝ×ℝ}
    (u : CutRing×CutRing) (j : Fin 4) (c : CutRing) (z w z' w' : SquareFlag a v)
    (hz : z'.val=z.val+(ordinary u.1,ordinary u.2))
    (hw : w'.val=w.val+(ordinary u.1,ordinary u.2)) :
    FlagSeparates j (c+integralCutForm a j u) z' w' ↔ FlagSeparates j c z w := by
  unfold FlagSeparates
  rw [flagMem_halfPlane_local_translation u j c z z' hz,
    flagMem_halfPlane_local_translation u j c w w' hw]

theorem separating_min_translation_bound {a : ℕ} {v : ℝ×ℝ}
    (u : CutRing×CutRing) (j : Fin 4) (z w z' w' : SquareFlag a v)
    (hz : z'.val=z.val+(ordinary u.1,ordinary u.2))
    (hw : w'.val=w.val+(ordinary u.1,ordinary u.2))
    (c d : CutRing) (hc : FlagSeparates j c z w) (hd : FlagSeparates j d z' w')
    (hcmin : ∀ e,FlagSeparates j e z w → |conjugate c| ≤ |conjugate e|)
    (hdmin : ∀ e,FlagSeparates j e z' w' → |conjugate d| ≤ |conjugate e|) :
    abs (|conjugate c|-|conjugate d|) ≤ |conjugate (integralCutForm a j u)| := by
  have hd' := hdmin (c+integralCutForm a j u)
    ((flagSeparates_local_translation u j c z w z' w' hz hw).mpr hc)
  have hc' := hcmin (d-integralCutForm a j u) (by
    apply (flagSeparates_local_translation u j (d-integralCutForm a j u) z w z' w' hz hw).mp
    simpa only [sub_add_cancel] using hd)
  have h₁ := abs_add_le (conjugate c) (conjugate (integralCutForm a j u))
  have h₂ : |conjugate d-conjugate (integralCutForm a j u)| ≤ |conjugate d|+|conjugate (integralCutForm a j u)| := by
    simpa only [sub_zero,zero_sub,abs_neg] using abs_sub_le (conjugate d) 0 (conjugate (integralCutForm a j u))
  simp only [map_add,map_sub] at hd' hc'
  apply abs_le.mpr
  constructor <;> linarith

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

theorem intervalCDF_lipschitz {lo hi : ℝ} (h : lo < hi) (d e : ℝ) :
    |intervalCDF lo hi d-intervalCDF lo hi e| ≤ |d-e|/(hi-lo) := by
  have hh := sub_pos.mpr h
  simp only [intervalCDF,← sub_div,abs_div,abs_of_pos hh]
  apply (div_le_div_iff_of_pos_right hh).mpr
  have h₁ := abs_max_sub_max_le_abs (min hi d-lo) (min hi e-lo) 0
  have h₂ := abs_min_sub_min_le_max hi d hi e
  calc
    _ ≤ |(min hi d-lo)-(min hi e-lo)| := h₁
    _ = |min hi d-min hi e| := by congr 1; ring
    _ ≤ |d-e| := by simpa only [sub_self,abs_zero,max_eq_right (abs_nonneg (d-e))] using h₂

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

theorem unit_product_sub_bound {ι : Type*} (S : Finset ι) (f g : ι → ℝ)
    (hf : ∀i∈S,0 ≤ f i ∧ f i ≤ 1) (hg : ∀i∈S,0 ≤ g i ∧ g i ≤ 1) :
    |(∏i∈S,f i)-(∏i∈S,g i)| ≤ ∑i∈S,|f i-g i| := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    have hfS (j) (hj : j∈S) := hf j (Finset.mem_insert_of_mem hj)
    have hgS (j) (hj : j∈S) := hg j (Finset.mem_insert_of_mem hj)
    have hfi := hf i (Finset.mem_insert_self _ _)
    have hgi := hg i (Finset.mem_insert_self _ _)
    have hp₀ : 0 ≤ ∏j∈S,g j := Finset.prod_nonneg (fun j hj => (hgS j hj).1)
    have hp₁ : (∏j∈S,g j) ≤ 1 := Finset.prod_le_one (fun j hj => (hgS j hj).1) (fun j hj => (hgS j hj).2)
    simp only [Finset.prod_insert hi,Finset.sum_insert hi]
    calc
      _ = |f i*((∏j∈S,f j)-(∏j∈S,g j))+(f i-g i)*(∏j∈S,g j)| := by congr 1; ring
      _ ≤ |f i*((∏j∈S,f j)-(∏j∈S,g j))|+|(f i-g i)*(∏j∈S,g j)| := abs_add_le _ _
      _ ≤ |(∏j∈S,f j)-(∏j∈S,g j)|+|f i-g i| := by
        rw [abs_mul,abs_mul,abs_of_nonneg hfi.1,abs_of_nonneg hp₀]
        exact add_le_add (mul_le_of_le_one_left (abs_nonneg _) hfi.2)
          (mul_le_of_le_one_right (abs_nonneg _) hp₁)
      _ ≤ _ := by linarith [ih hfS hgS]

end UniformThresholdCDF

section SeparatorCovariance
open Classical MeasureTheory ProbabilityTheory

theorem directionNoCut_of_none {a : ℕ} {v : ℝ×ℝ} (j : Fin 4)
    (z w : SquareFlag a v) (h : ¬ ∃c,FlagSeparates j c z w) :
    directionNoCut j z w = Set.univ := by
  ext t
  simp only [directionNoCut,Set.mem_ofPred_eq,Set.mem_univ,iff_true]
  exact fun c _ hc => h ⟨c,hc⟩

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

theorem directionNoCutProbability_bounds {a : ℕ} {v : ℝ×ℝ}
    {s κ : ℝ} (hs : 0 < s) (hκ : 0 < κ) (j : Fin 4) (z w : SquareFlag a v) :
    0 ≤ directionNoCutProbability s κ j z w ∧ directionNoCutProbability s κ j z w ≤ 1 := by
  have h : κ/s < 2*κ/s := (div_lt_div_iff_of_pos_right hs).mpr (by linarith)
  have := uniformInterval_isProbability h
  exact ⟨ENNReal.toReal_nonneg,measureReal_le_one⟩

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

theorem directionNoCutProbability_translation_bound {a : ℕ} {v : ℝ×ℝ}
    {s κ : ℝ} (hs : 0 < s) (hκ : 0 < κ)
    (u : CutRing×CutRing) (j : Fin 4) (z w z' w' : SquareFlag a v)
    (hz : z'.val=z.val+(ordinary u.1,ordinary u.2))
    (hw : w'.val=w.val+(ordinary u.1,ordinary u.2)) :
    |directionNoCutProbability s κ j z w-directionNoCutProbability s κ j z' w'| ≤
      |conjugate (integralCutForm a j u)| *s/κ := by
  have he : (∃c,FlagSeparates j c z w) ↔ ∃c,FlagSeparates j c z' w' := by
    constructor
    · rintro ⟨c,hc⟩
      exact ⟨c+integralCutForm a j u,
        (flagSeparates_local_translation u j c z w z' w' hz hw).mpr hc⟩
    · rintro ⟨c,hc⟩
      refine ⟨c-integralCutForm a j u,?_⟩
      apply (flagSeparates_local_translation u j (c-integralCutForm a j u) z w z' w' hz hw).mp
      simpa only [sub_add_cancel] using hc
  by_cases hc : ∃c,FlagSeparates j c z w
  · obtain ⟨c,hc,hcmin⟩ := flagSeparates_exists_min j z w hc
    obtain ⟨d,hd,hdmin⟩ := flagSeparates_exists_min j z' w' (he.mp ⟨c,hc⟩)
    have h : κ/s < 2*κ/s := (div_lt_div_iff_of_pos_right hs).mpr (by linarith)
    simp only [directionNoCutProbability,directionNoCut_of_min j z w c hc hcmin,
      directionNoCut_of_min j z' w' d hd hdmin,uniformInterval_Iio h]
    have hmin := separating_min_translation_bound u j z w z' w' hz hw c d hc hd hcmin hdmin
    calc
      _ ≤ abs (|conjugate c|-|conjugate d|)/(2*κ/s-κ/s) := intervalCDF_lipschitz h _ _
      _ ≤ |conjugate (integralCutForm a j u)|/(2*κ/s-κ/s) :=
        (div_le_div_iff_of_pos_right (sub_pos.mpr h)).mpr hmin
      _ = _ := by field_simp; ring
  · have hc' := he.not.mp hc
    simp only [directionNoCutProbability,directionNoCut_of_none j z w hc,
      directionNoCut_of_none j z' w' hc',sub_self,abs_zero]
    positivity

theorem separatorMatrix_translation_bound {a : ℕ} {v : ℝ×ℝ}
    {s κ : ℝ} (hs : 0 < s) (hκ : 0 < κ)
    (u : CutRing×CutRing) (z w z' w' : SquareFlag a v)
    (hz : z'.val=z.val+(ordinary u.1,ordinary u.2))
    (hw : w'.val=w.val+(ordinary u.1,ordinary u.2)) :
    |separatorMatrix (thresholdLaw s κ) z w-separatorMatrix (thresholdLaw s κ) z' w'| ≤
      (∑j : Fin 4,|conjugate (integralCutForm a j u)|)*s/κ := by
  rw [separatorMatrix_product hs hκ,separatorMatrix_product hs hκ]
  calc
    _ ≤ ∑j : Fin 4,|directionNoCutProbability s κ j z w-directionNoCutProbability s κ j z' w'| :=
      unit_product_sub_bound Finset.univ _ _
        (fun j _ => directionNoCutProbability_bounds hs hκ j z w)
        (fun j _ => directionNoCutProbability_bounds hs hκ j z' w')
    _ ≤ ∑j : Fin 4,|conjugate (integralCutForm a j u)| *s/κ :=
      Finset.sum_le_sum (fun j _ => directionNoCutProbability_translation_bound hs hκ u j z w z' w' hz hw)
    _ = _ := by rw [← Finset.sum_div,← Finset.sum_mul]

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

theorem flagAffineData_action {a m : ℕ} {v : ℝ×ℝ} (g : polygonFullGroup a m)
    (z : FlagTrackPoint a m v) :
    (flagAction g z).1=(flagAffineData g z.1 z.2).1 ∧
    (flagAction g z).2.val=z.2.val+
      (ordinary (flagAffineData g z.1 z.2).2.1,ordinary (flagAffineData g z.1 z.2).2.2) := by
  rw [flagAffineData_selected]
  refine ⟨rfl,?_⟩
  apply Prod.ext <;>
    simp only [flagAction,flagTranslate_val,flagFract_eq,flagShiftPeriod,SquareStep.intPair,
      Prod.fst_sub,Prod.snd_sub,Prod.fst_add,Prod.snd_add,map_sub,map_intCast] <;> ring

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

theorem flagAffineData_inverse {a m : ℕ} {v : ℝ×ℝ} (g : polygonFullGroup a m)
    (z : FlagTrackPoint a m v) :
    flagAffineData g⁻¹ (flagAction g z).1 (flagAction g z).2=(z.1,-(flagAffineData g z.1 z.2).2) := by
  have he : flagAction g⁻¹ (flagAction g z)=z := by rw [← flagAction_mul,inv_mul_cancel,flagAction_one]
  have hf := flagAffineData_action g z
  have hb := flagAffineData_action g⁻¹ (flagAction g z)
  rw [he] at hb
  apply Prod.ext
  · exact hb.1.symm
  · rw [hf.2] at hb
    apply Prod.ext
    · apply ordinary_injective
      have hh := congrArg Prod.fst hb.2
      simp only [Prod.fst_add] at hh
      simp only [Prod.fst_neg,map_neg]
      linarith
    · apply ordinary_injective
      have hh := congrArg Prod.snd hb.2
      simp only [Prod.snd_add] at hh
      simp only [Prod.snd_neg,map_neg]
      linarith

end FlagAffineControl

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

end AveragingRowBounds

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_AveragingAffinePairs
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
section AveragingAffinePairs
open Classical MeasureTheory

theorem sameAffineBranch_inverse_iff {a m : ℕ} {v : ℝ×ℝ} (g : polygonFullGroup a m)
    (z w : FlagTrackPoint a m v) :
    SameAffineBranch g⁻¹ (flagAction g z) (flagAction g w) ↔ SameAffineBranch g z w := by
  simp only [SameAffineBranch,flagAffineData_inverse,Prod.mk.injEq,neg_inj]
  rw [(flagAffineData_action g z).1,(flagAffineData_action g w).1]
  constructor
  · rintro ⟨ht,hzw,hu⟩
    exact ⟨hzw,Prod.ext ht hu⟩
  · rintro ⟨hzw,he⟩
    exact ⟨congrArg Prod.fst he,hzw,congrArg Prod.snd he⟩

theorem flagAveragingMatrix_nezero_separator {a m D : ℕ} {v : ℝ×ℝ}
    (χ : (ℝ×ℝ) → ℝ) (ρ N r η κ : ℝ) (z w : FlagSite a m D v)
    (h : flagAveragingMatrix χ ρ N r η κ z w ≠ 0) :
    z.val.1=w.val.1 ∧ separatorMatrix (thresholdLaw (r/N) κ) z.val.2 w.val.2 ≠ 0 := by
  have ht : z.val.1=w.val.1 := by
    by_contra ht
    exact h (by simp [flagAveragingMatrix,ht])
  refine ⟨ht,fun hp => h ?_⟩
  simp [flagAveragingMatrix,hp]

theorem flagAveragingMatrix_common_branch {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) :
    ∃R : ℝ,0 ≤ R ∧ ∀(χ : (ℝ×ℝ) → ℝ) (ρ N r η κ : ℝ),
      0 < N → 0 < r → 0 < κ → R ≤ κ/(r/N) →
      ∀z w : FlagSite a m D v,
      (flagAveragingMatrix χ ρ N r η κ z w ≠ 0 ∨
       flagAveragingMatrix χ ρ N r η κ (flagSiteAction hD g z) (flagSiteAction hD g w) ≠ 0) →
        SameAffineBranch g z.val w.val := by
  obtain ⟨R,hR,hcontrol⟩ := flagAffineData_separator_control (v:=v) g
  obtain ⟨T,hT,hcontrol'⟩ := flagAffineData_separator_control (v:=v) g⁻¹
  refine ⟨max R T,le_max_of_le_left hR,fun χ ρ N r η κ hN hr hκ hbound z w hm => ?_⟩
  rcases hm with hm|hm
  · obtain ⟨ht,hp⟩ := flagAveragingMatrix_nezero_separator χ ρ N r η κ z w hm
    refine ⟨ht,?_⟩
    rw [← ht]
    exact hcontrol (r/N) κ (div_pos hr hN) hκ ((le_max_left _ _).trans hbound) z.val.1 _ _ hp
  · obtain ⟨ht,hp⟩ := flagAveragingMatrix_nezero_separator χ ρ N r η κ
      (flagSiteAction hD g z) (flagSiteAction hD g w) hm
    apply (sameAffineBranch_inverse_iff g z.val w.val).mp
    refine ⟨ht,?_⟩
    change (flagAction g z.val).1=(flagAction g w.val).1 at ht
    rw [← ht]
    exact hcontrol' (r/N) κ (div_pos hr hN) hκ ((le_max_right _ _).trans hbound)
      (flagAction g z.val).1 _ _ hp

theorem planeTent_common_translation (s : ℝ) (x y b : ℝ×ℝ) :
    planeTent s (x+b) (y+b)=planeTent s x y := by
  simp only [planeTent,Prod.fst_add,Prod.snd_add,add_sub_add_right_eq_sub]

theorem sameAffineBranch_kernels {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) (z w : FlagSite a m D v) (hf : SameAffineBranch g z.val w.val)
    (s t : ℝ) :
    planeTent s (flagSiteOrdinary (flagSiteAction hD g z)) (flagSiteOrdinary (flagSiteAction hD g w))=
      planeTent s (flagSiteOrdinary z) (flagSiteOrdinary w) ∧
    planeTent t (flagSiteConjugate (flagSiteAction hD g z)) (flagSiteConjugate (flagSiteAction hD g w))=
      planeTent t (flagSiteConjugate z) (flagSiteConjugate w) := by
  constructor
  · change planeTent s (flagAction g z.val).2.val (flagAction g w.val).2.val=_
    rw [(flagAffineData_action g z.val).2,(flagAffineData_action g w.val).2,← hf.2]
    exact planeTent_common_translation _ _ _ _
  · rw [flagAffineData_conjugate hD,flagAffineData_conjugate hD,← hf.2]
    exact planeTent_common_translation _ _ _ _

theorem flagAffineData_cost_bound {a m : ℕ} {v : ℝ×ℝ} (g : polygonFullGroup a m) :
    ∃C : ℝ,0 ≤ C ∧ ∀z : FlagTrackPoint a m v,affineConjugateCost a (flagAffineData g z.1 z.2).2 ≤ C := by
  obtain ⟨C,hC,h⟩ := flagAffineData_bounded (v:=v) g (affineConjugateCost a)
  exact ⟨C,hC,fun z => (abs_le.mp (h z)).2⟩

end AveragingAffinePairs

section AveragingEntryCovariance
open Classical MeasureTheory

theorem unit_pair_sub_bound {a b c d : ℝ}
    (hb : b∈Set.Icc (0:ℝ) 1) (hc : c∈Set.Icc (0:ℝ) 1) :
    |a*b-c*d| ≤ |a-c|+|b-d| := by
  calc
    _ = |(a-c)*b+c*(b-d)| := by congr 1; ring
    _ ≤ |(a-c)*b|+|c*(b-d)| := abs_add_le _ _
    _ = |a-c| *b+c*|b-d| := by rw [abs_mul,abs_mul,abs_of_nonneg hb.1,abs_of_nonneg hc.1]
    _ ≤ _ := by nlinarith [abs_nonneg (a-c),abs_nonneg (b-d),hb.2,hc.2]

theorem unit_triple_sub_bound {a b c d e f : ℝ}
    (_ha : a∈Set.Icc (0:ℝ) 1) (hb : b∈Set.Icc (0:ℝ) 1)
    (hc : c∈Set.Icc (0:ℝ) 1) (hd : d∈Set.Icc (0:ℝ) 1)
    (he : e∈Set.Icc (0:ℝ) 1) :
    |a*b*c-d*e*f| ≤ |a-d|+|b-e|+|c-f| := by
  have hde : d*e∈Set.Icc (0:ℝ) 1 := ⟨mul_nonneg hd.1 he.1,
    (mul_le_mul hd.2 he.2 he.1 zero_le_one).trans_eq (one_mul 1)⟩
  have h₁ : |a*b*c-d*e*f| ≤ |a*b-d*e|+|c-f| := unit_pair_sub_bound hc hde
  have h₂ : |a*b-d*e| ≤ |a-d|+|b-e| := unit_pair_sub_bound hb hd
  linarith

theorem scaledSiteConjugate_action_diff {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) (z : FlagSite a m D v) (N : ℝ) :
    (scaledSiteConjugate N (flagSiteAction hD g z)).1-(scaledSiteConjugate N z).1=
      conjugate (flagAffineData g z.val.1 z.val.2).2.1/N ∧
    (scaledSiteConjugate N (flagSiteAction hD g z)).2-(scaledSiteConjugate N z).2=
      conjugate (flagAffineData g z.val.1 z.val.2).2.2/N := by
  simp only [scaledSiteConjugate,flagAffineData_conjugate hD,Prod.fst_add,Prod.snd_add,add_div,add_sub_cancel_left]
  exact ⟨trivial,trivial⟩

theorem cutoff_action_bound {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) (z : FlagSite a m D v) {N L : ℝ} (hN : 0<N)
    (χ : (ℝ×ℝ) → ℝ)
    (hχ : ∀x y,|χ x-χ y| ≤ L*(|x.1-y.1|+|x.2-y.2|)) :
    |χ (scaledSiteConjugate N z)-χ (scaledSiteConjugate N (flagSiteAction hD g z))| ≤
      L*(|conjugate (flagAffineData g z.val.1 z.val.2).2.1|+
         |conjugate (flagAffineData g z.val.1 z.val.2).2.2|)/N := by
  rw [abs_sub_comm]
  have h := hχ (scaledSiteConjugate N (flagSiteAction hD g z)) (scaledSiteConjugate N z)
  rw [(scaledSiteConjugate_action_diff hD g z N).1,(scaledSiteConjugate_action_diff hD g z N).2,
    abs_div,abs_div,abs_of_pos hN,← add_div,← mul_div_assoc] at h
  exact h

theorem flagAveragingMatrix_chart_difference {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) (z w : FlagSite a m D v) (hf : SameAffineBranch g z.val w.val)
    (χ : (ℝ×ℝ) → ℝ) (hχ : ∀x,χ x∈Set.Icc (0:ℝ) 1)
    {L ρ N r η κ : ℝ} (hL : 0 ≤ L) (hρ : 0<ρ) (hN : 0<N) (hr : 0 < r) (hη : 0<η) (hκ : 0<κ)
    (hLip : ∀x y,|χ x-χ y| ≤ L*(|x.1-y.1|+|x.2-y.2|)) :
    |flagAveragingMatrix χ ρ N r η κ z w-
      flagAveragingMatrix χ ρ N r η κ (flagSiteAction hD g z) (flagSiteAction hD g w)| ≤
      affineConjugateCost a (flagAffineData g z.val.1 z.val.2).2 * (2*L+r/κ)/(N*(ρ*(r*η)^2)) := by
  have : IsProbabilityMeasure (thresholdLaw (r/N) κ) := thresholdLaw_isProbability (div_pos hr hN) hκ
  let u := (flagAffineData g z.val.1 z.val.2).2
  let d := ρ*(r*η)^2
  have hd : 0<d := mul_pos hρ (sq_pos_of_pos (mul_pos hr hη))
  let A := |conjugate u.1|+|conjugate u.2|
  let B := ∑j : Fin 4,|conjugate (integralCutForm a j u)|
  have hA : 0 ≤ A := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hz := cutoff_action_bound hD g z hN χ hLip
  have hw := cutoff_action_bound hD g w hN χ hLip
  rw [← hf.2] at hw
  have hp := separatorMatrix_translation_bound (div_pos hr hN) hκ u z.val.2 w.val.2
    (flagAction g z.val).2 (flagAction g w.val).2
    (flagAffineData_action g z.val).2 (by rw [(flagAffineData_action g w.val).2,← hf.2])
  have ht : (flagSiteAction hD g z).val.1=(flagSiteAction hD g w).val.1 := by
    change (flagAction g z.val).1=(flagAction g w.val).1
    rw [(flagAffineData_action g z.val).1,(flagAffineData_action g w.val).1,hf.2]
  have hk := sameAffineBranch_kernels hD g z w hf (r/N) (N*η)
  let T := planeTent (r/N) (flagSiteOrdinary z) (flagSiteOrdinary w)*
    planeTent (N*η) (flagSiteConjugate z) (flagSiteConjugate w)
  have hT₀ : 0 ≤ T := mul_nonneg (planeTent_nonneg _ _ _) (planeTent_nonneg _ _ _)
  have hT₁ : T ≤ 1 := (mul_le_mul (planeTent_le_one _ _ _) (planeTent_le_one _ _ _)
    (planeTent_nonneg _ _ _) zero_le_one).trans_eq (one_mul 1)
  have he : (flagAveragingMatrix χ ρ N r η κ z w-
      flagAveragingMatrix χ ρ N r η κ (flagSiteAction hD g z) (flagSiteAction hD g w))=
    (χ (scaledSiteConjugate N z)*χ (scaledSiteConjugate N w)*
      separatorMatrix (thresholdLaw (r/N) κ) z.val.2 w.val.2-
     χ (scaledSiteConjugate N (flagSiteAction hD g z))*χ (scaledSiteConjugate N (flagSiteAction hD g w))*
      separatorMatrix (thresholdLaw (r/N) κ) (flagAction g z.val).2 (flagAction g w.val).2)*T/d := by
    rw [flagAveragingMatrix,flagAveragingMatrix,ite_eq_left hf.1,ite_eq_left ht,hk.1,hk.2]
    change _=(_-_*separatorMatrix (thresholdLaw (r/N) κ) (flagSiteAction hD g z).val.2
      (flagSiteAction hD g w).val.2)*T/d
    dsimp only [T,d]
    ring
  rw [he,abs_div,abs_mul,abs_of_pos hd,abs_of_nonneg hT₀]
  have htrip := unit_triple_sub_bound (f:=separatorMatrix (thresholdLaw (r/N) κ) (flagAction g z.val).2 (flagAction g w.val).2) (hχ (scaledSiteConjugate N z)) (hχ (scaledSiteConjugate N w))
    (separatorMatrix_bounds (thresholdLaw (r/N) κ) z.val.2 w.val.2)
    (hχ (scaledSiteConjugate N (flagSiteAction hD g z)))
    (hχ (scaledSiteConjugate N (flagSiteAction hD g w)))
  have hh := add_le_add (add_le_add hz hw) hp
  have hmain := htrip.trans hh
  change _ ≤ L*A/N+L*A/N+B*(r/N)/κ at hmain
  calc
    _ ≤ (L*A/N+L*A/N+B*(r/N)/κ)/d := by
      apply (div_le_div_iff_of_pos_right hd).mpr
      exact (mul_le_mul_of_nonneg_left hT₁ (abs_nonneg _)).trans (by simpa only [mul_one] using hmain)
    _ = (2*L*A+B*(r/κ))/(N*d) := by field_simp; ring
    _ ≤ (A+B)*(2*L+r/κ)/(N*d) := by
      apply (div_le_div_iff_of_pos_right (mul_pos hN hd)).mpr
      nlinarith [mul_nonneg hA (div_nonneg hr.le hκ.le),mul_nonneg hB hL]
    _ = _ := rfl

end AveragingEntryCovariance

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_AveragingUniformCovariance
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
section AveragingUniformCovariance
open Classical

theorem flagAveragingMatrix_uniform_difference {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) :
    ∃R C : ℝ,0 ≤ R ∧ 0 ≤ C ∧
      ∀(χ : (ℝ×ℝ) → ℝ), (∀x,χ x∈Set.Icc (0:ℝ) 1) →
      ∀(L ρ N r η κ : ℝ),0 ≤ L → 0<ρ → 0<N → 1 ≤ r → 0<η → 0<κ → R ≤ κ/(r/N) →
      (∀x y,|χ x-χ y| ≤ L*(|x.1-y.1|+|x.2-y.2|)) →
      ∀z w : FlagSite a m D v,
      |flagAveragingMatrix χ ρ N r η κ z w-
        flagAveragingMatrix χ ρ N r η κ (flagSiteAction hD g z) (flagSiteAction hD g w)| ≤
        (C*(2*L+1/κ)/(ρ*η^2))/(N*r) := by
  obtain ⟨R,hR,hbranch⟩ := flagAveragingMatrix_common_branch (v:=v) hD g
  obtain ⟨C,hC,hcost⟩ := flagAffineData_cost_bound (v:=v) g
  refine ⟨R,C,hR,hC,fun χ hχ L ρ N r η κ hL hρ hN hr hη hκ hbound hLip z w => ?_⟩
  have hr₀ : 0 < r := lt_of_lt_of_le zero_lt_one hr
  by_cases hm : flagAveragingMatrix χ ρ N r η κ z w ≠ 0 ∨
      flagAveragingMatrix χ ρ N r η κ (flagSiteAction hD g z) (flagSiteAction hD g w) ≠ 0
  · have hf := hbranch χ ρ N r η κ hN hr₀ hκ hbound z w hm
    have he := flagAveragingMatrix_chart_difference hD g z w hf χ hχ hL hρ hN hr₀ hη hκ hLip
    have hnum : 0 ≤ 2*L+r/κ := by positivity
    have hden : 0<N*(ρ*(r*η)^2) := by positivity
    have hn : 2*L+r/κ ≤ r*(2*L+1/κ) := by
      have hh := mul_nonneg hL (sub_nonneg.mpr hr)
      simp only [div_eq_mul_inv,one_mul]
      nlinarith
    calc
      _ ≤ affineConjugateCost a (flagAffineData g z.val.1 z.val.2).2*(2*L+r/κ)/(N*(ρ*(r*η)^2)) := he
      _ ≤ C*(2*L+r/κ)/(N*(ρ*(r*η)^2)) := by gcongr; exact hcost z.val
      _ ≤ C*(r*(2*L+1/κ))/(N*(ρ*(r*η)^2)) := by gcongr
      _ = _ := by field_simp
  · have hz : flagAveragingMatrix χ ρ N r η κ z w=0 := not_not.mp (fun h => hm (Or.inl h))
    have hw : flagAveragingMatrix χ ρ N r η κ (flagSiteAction hD g z) (flagSiteAction hD g w)=0 :=
      not_not.mp (fun h => hm (Or.inr h))
    rw [hz,hw,sub_self,abs_zero]
    positivity

end AveragingUniformCovariance

section AveragingSupportCounts
open Classical

theorem pair_card_of_row_bound {α β : Type*} (T : Finset (α×β)) {B : ℝ}
    (hB : ∀x∈T.image Prod.fst, ((T.filter (fun p => p.1=x)).image Prod.snd).card ≤ B) :
    (T.card:ℝ) ≤ (T.image Prod.fst).card*B := by
  have hrow (x : α) : ((T.filter (fun p => p.1=x)).image Prod.snd).card=
      (T.filter (fun p => p.1=x)).card := by
    apply Finset.card_image_of_injOn
    intro p hp q hq he
    exact Prod.ext ((Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm) he
  rw [Finset.card_eq_sum_card_image Prod.fst T,Nat.cast_sum]
  calc
    _ ≤ ∑x∈T.image Prod.fst,B := Finset.sum_le_sum (fun x hx => by rw [← hrow x]; exact hB x hx)
    _ = _ := by simp

theorem flagAveragingMatrix_support_card {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (χ : (ℝ×ℝ) → ℝ) {K : ℝ} (hK : 0<K) (hχ : ∀x,K ≤ ‖x‖ → χ x=0)
    (ρ κ : ℝ) {N r η : ℝ} (hN : 0<N) (hr : 0 < r) (hη : 0<η)
    (T : Finset (FlagSite a m D v × FlagSite a m D v))
    (hT : ∀p∈T,flagAveragingMatrix χ ρ N r η κ p.1 p.2 ≠ 0) :
    (T.card:ℝ) ≤ (m*(2*(D:ℝ)^2*(N*K)+2)^2)*(4*(D:ℝ)^2*r*η+2)^2 := by
  have hrows : ((T.image Prod.fst).card:ℝ) ≤ m*(2*(D:ℝ)^2*(N*K)+2)^2 := by
    apply flagSiteBox_card_bound hD (mul_pos hN hK)
    intro z hz
    obtain ⟨⟨z,w⟩,hp,rfl⟩ := Finset.mem_image.mp hz
    have hcz : χ (scaledSiteConjugate N z)≠0 := fun h => hT (z,w) hp
      (flagAveragingMatrix_cutoff_left χ ρ N r η κ z w h)
    have hn : ‖scaledSiteConjugate N z‖ < K := lt_of_not_ge (fun he => hcz (hχ _ he))
    have hx := (norm_fst_le (scaledSiteConjugate N z)).trans_lt hn
    have hy := (norm_snd_le (scaledSiteConjugate N z)).trans_lt hn
    simp only [scaledSiteConjugate,Real.norm_eq_abs,abs_div,abs_of_pos hN] at hx hy
    exact ⟨by nlinarith [(div_lt_iff₀ hN).mp hx],by nlinarith [(div_lt_iff₀ hN).mp hy]⟩
  have hc := pair_card_of_row_bound T (B:=(4*(D:ℝ)^2*r*η+2)^2) (fun z _ => ?_)
  · exact hc.trans (mul_le_mul_of_nonneg_right hrows (sq_nonneg _))
  · apply flagAveragingMatrix_row_card hD χ ρ κ hN hr hη z
    intro w hw
    obtain ⟨⟨z',w⟩,hp,rfl⟩ := Finset.mem_image.mp hw
    have he : z'=z := (Finset.mem_filter.mp hp).2
    subst z'
    exact hT (z,w) (Finset.mem_filter.mp hp).1

theorem flagAveragingMatrix_support_quadratic {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (χ : (ℝ×ℝ) → ℝ) {K : ℝ} (hK : 0<K) (hχ : ∀x,K ≤ ‖x‖ → χ x=0)
    (ρ κ : ℝ) {N r η : ℝ} (hN : 1≤N) (hr : 1 ≤ r) (hη : 0<η)
    (T : Finset (FlagSite a m D v × FlagSite a m D v))
    (hT : ∀p∈T,flagAveragingMatrix χ ρ N r η κ p.1 p.2 ≠ 0) :
    (T.card:ℝ) ≤ (m*(2*(D:ℝ)^2*K+2)^2*(4*(D:ℝ)^2*η+2)^2)*N^2*r^2 := by
  have hx : 2*(D:ℝ)^2*(N*K)+2 ≤ (2*(D:ℝ)^2*K+2)*N := by nlinarith
  have hy : 4*(D:ℝ)^2*r*η+2 ≤ (4*(D:ℝ)^2*η+2)*r := by nlinarith
  have hx₀ : 0 ≤ 2*(D:ℝ)^2*(N*K)+2 := by positivity
  have hy₀ : 0 ≤ 4*(D:ℝ)^2*r*η+2 := by positivity
  calc
    _ ≤ (m*(2*(D:ℝ)^2*(N*K)+2)^2)*(4*(D:ℝ)^2*r*η+2)^2 :=
      flagAveragingMatrix_support_card hD χ hK hχ ρ κ (lt_of_lt_of_le zero_lt_one hN)
        (lt_of_lt_of_le zero_lt_one hr) hη T hT
    _ ≤ (m*((2*(D:ℝ)^2*K+2)*N)^2)*((4*(D:ℝ)^2*η+2)*r)^2 := by gcongr
    _ = _ := by ring

theorem flagAveragingMatrix_difference_support {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) (χ : (ℝ×ℝ) → ℝ) {K : ℝ} (hK : 0<K)
    (hχ : ∀x,K ≤ ‖x‖ → χ x=0) (ρ κ : ℝ) {N r η : ℝ}
    (hN : 1≤N) (hr : 1 ≤ r) (hη : 0<η)
    (T : Finset (FlagSite a m D v × FlagSite a m D v))
    (hT : ∀p∈T,flagAveragingMatrix χ ρ N r η κ p.1 p.2-
      flagAveragingMatrix χ ρ N r η κ (flagSiteAction hD g p.1) (flagSiteAction hD g p.2) ≠ 0) :
    (T.card:ℝ) ≤ (2*m*(2*(D:ℝ)^2*K+2)^2*(4*(D:ℝ)^2*η+2)^2)*N^2*r^2 := by
  let U := T.filter (fun p => flagAveragingMatrix χ ρ N r η κ p.1 p.2 ≠ 0)
  let V := T.filter (fun p => flagAveragingMatrix χ ρ N r η κ (flagSiteAction hD g p.1) (flagSiteAction hD g p.2) ≠ 0)
  have he : T ⊆ U∪V := by
    intro p hp
    by_cases h : flagAveragingMatrix χ ρ N r η κ p.1 p.2 ≠ 0
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp,h⟩)
    · apply Finset.mem_union_right
      apply Finset.mem_filter.mpr
      refine ⟨hp,fun h' => hT p hp ?_⟩
      rw [not_not.mp h,h',sub_self]
  have hu := flagAveragingMatrix_support_quadratic hD χ hK hχ ρ κ hN hr hη U
    (fun p hp => (Finset.mem_filter.mp hp).2)
  let e := (flagSitePermutation (v:=v) hD g).prodCongr (flagSitePermutation (v:=v) hD g)
  have hv := flagAveragingMatrix_support_quadratic hD χ hK hχ ρ κ hN hr hη (V.image e)
    (by intro p hp; obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp; exact (Finset.mem_filter.mp hq).2)
  rw [Finset.card_image_of_injective V e.injective] at hv
  have hn : (T.card:ℝ) ≤ U.card+V.card := by
    exact_mod_cast (Finset.card_le_card he).trans (Finset.card_union_le _ _)
  nlinarith

end AveragingSupportCounts

section FiniteCovarianceEnergy
open Classical

theorem finite_correlation_bound {α : Type*} (T : Finset α) (f g : α → ℝ)
    {A B H : ℝ} (hA : 0≤A) (hB : 0≤B)
    (hf : ∀x∈T,|f x|≤A) (hg : ∀x∈T,|g x|≤B)
    (hc : ∀S⊆T,(∀x∈S,f x≠0) → (S.card:ℝ)≤H) :
    |∑x∈T,f x*g x| ≤ H*A*B := by
  let S := T.filter (fun x => f x≠0)
  have he : (∑x∈T,f x*g x)=∑x∈S,f x*g x := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro x hx hxS
    have hh : f x=0 := by simpa [S,hx] using hxS
    simp [hh]
  rw [he]
  calc
    _ ≤ ∑x∈S,|f x*g x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑_x∈S,A*B := Finset.sum_le_sum (fun x hx => by
      rw [abs_mul]
      exact mul_le_mul (hf x (Finset.mem_filter.mp hx).1)
        (hg x (Finset.mem_filter.mp hx).1) (abs_nonneg _) hA)
    _ = (S.card:ℝ)*A*B := by simp; ring
    _ ≤ H*A*B := by
      have hh := hc S (Finset.filter_subset _ _) (fun x hx => (Finset.mem_filter.mp hx).2)
      gcongr

theorem finite_half_geometric_sum (I : Finset ℕ) :
    ∑i∈I,(1/2:ℝ)^i ≤ 2 := by
  have hi : I ⊆ Finset.range (I.sup id+1) := by
    intro i hi
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f:=id) hi))
  calc
    _ ≤ ∑i∈Finset.range (I.sup id+1),(1/2:ℝ)^i :=
      Finset.sum_le_sum_of_subset_of_nonneg hi (fun _ _ _ => by positivity)
    _ ≤ 2 := by
      have h := geom_sum_Ico_le_of_lt_one (m:=0) (n:=I.sup id+1)
        (show (0:ℝ) ≤ 1/2 by norm_num) (show (1/2:ℝ)<1 by norm_num)
      norm_num at h ⊢
      exact h

theorem finite_dyadic_row (I : Finset ℕ) (i : ℕ) :
    ∑j∈I,(1/2:ℝ)^(Nat.dist i j) ≤ 4 := by
  let J := I.filter (fun j => j ≤ i)
  let K := I.filter (fun j => ¬j ≤ i)
  have hJ : Set.InjOn (Nat.dist i) J := by
    intro j hj k hk he
    have hj' := (Finset.mem_filter.mp hj).2
    have hk' := (Finset.mem_filter.mp hk).2
    rw [Nat.dist_eq_sub_of_le_right hj',Nat.dist_eq_sub_of_le_right hk'] at he
    omega
  have hK : Set.InjOn (Nat.dist i) K := by
    intro j hj k hk he
    have hj' : i ≤ j := by have := (Finset.mem_filter.mp hj).2; omega
    have hk' : i ≤ k := by have := (Finset.mem_filter.mp hk).2; omega
    rw [Nat.dist_eq_sub_of_le hj',Nat.dist_eq_sub_of_le hk'] at he
    omega
  have hj : ∑j∈J,(1/2:ℝ)^(Nat.dist i j) ≤ 2 := by
    rw [← Finset.sum_image hJ]
    exact finite_half_geometric_sum _
  have hk : ∑j∈K,(1/2:ℝ)^(Nat.dist i j) ≤ 2 := by
    rw [← Finset.sum_image hK]
    exact finite_half_geometric_sum _
  have he := Finset.sum_filter_add_sum_filter_not I (fun j => j ≤ i) (fun j => (1/2:ℝ)^(Nat.dist i j))
  change (∑j∈J,_) + (∑j∈K,_) = _ at he
  linarith

theorem finite_dyadic_energy {α : Type*} (T : Finset α) (I : Finset ℕ)
    (d : ℕ → α → ℝ) {C : ℝ} (hC : 0≤C)
    (hc : ∀i∈I,∀j∈I,i ≤ j → |∑x∈T,d i x*d j x| ≤ C*((2:ℝ)^i/(2:ℝ)^j))
    (w : ℝ) :
    ∑x∈T,(w*∑i∈I,d i x)^2 ≤ 4*C*(I.card:ℝ)*w^2 := by
  have he (i j : ℕ) (hi : i∈I) (hj : j∈I) :
      ∑x∈T,d i x*d j x ≤ C*(1/2:ℝ)^(Nat.dist i j) := by
    have aux (i j : ℕ) (hij : i ≤ j) : (2:ℝ)^i/(2:ℝ)^j=(1/2:ℝ)^(Nat.dist i j) := by
      rw [Nat.dist_eq_sub_of_le hij,div_pow,one_pow]
      have hh : (2:ℝ)^j=(2:ℝ)^i*(2:ℝ)^(j-i) := by
        rw [← pow_add,Nat.add_sub_of_le hij]
      rw [hh]
      field_simp
    by_cases hij : i ≤ j
    · exact (le_abs_self _).trans ((hc i hi j hj hij).trans_eq (by rw [aux i j hij]))
    · have hji : j ≤ i := by omega
      have h := (le_abs_self _).trans (hc j hj i hi hji)
      simpa only [mul_comm, Nat.dist_comm,aux j i hji] using h
  have hsum : ∑i∈I,∑j∈I,∑x∈T,d i x*d j x ≤ 4*C*(I.card:ℝ) := by
    calc
      _ ≤ ∑i∈I,∑j∈I,C*(1/2:ℝ)^(Nat.dist i j) :=
        Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun j hj => he i j hi hj))
      _ = ∑i∈I,C*(∑j∈I,(1/2:ℝ)^(Nat.dist i j)) := by simp_rw [Finset.mul_sum]
      _ ≤ ∑_i∈I,C*4 := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (finite_dyadic_row I i) hC)
      _ = _ := by simp; ring
  have hid : (∑x∈T,(w*∑i∈I,d i x)^2)=w^2*(∑i∈I,∑j∈I,∑x∈T,d i x*d j x) := by
    simp_rw [mul_pow,pow_two,Finset.sum_mul_sum]
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_comm]
  rw [hid]
  nlinarith [mul_le_mul_of_nonneg_left hsum (sq_nonneg w)]

end FiniteCovarianceEnergy

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_PolygonCovarianceEnergy
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
section PolygonCovarianceEnergy
open Classical

theorem flagMatrixDifference_correlation {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) (χ : (ℝ×ℝ) → ℝ)
    (hχ : ∀x,χ x∈Set.Icc (0:ℝ) 1) {K L ρ η κ : ℝ}
    (hK : 0<K) (hcompact : ∀x,K ≤ ‖x‖ → χ x=0)
    (hL : 0≤L) (hρ : 0<ρ) (hη : 0<η) (hκ : 0<κ)
    (hLip : ∀x y,|χ x-χ y| ≤ L*(|x.1-y.1|+|x.2-y.2|)) :
    ∃R C : ℝ,0≤R ∧ 0≤C ∧ ∀N r r' : ℝ,1≤N → 1 ≤ r → 1 ≤ r' →
      R ≤ κ/(r/N) → R ≤ κ/(r'/N) →
      ∀T : Finset (FlagSite a m D v × FlagSite a m D v),
      |∑p∈T,flagMatrixDifference hD g χ ρ N r η κ p*
        flagMatrixDifference hD g χ ρ N r' η κ p| ≤ C*(r/r') := by
  obtain ⟨R,A,hR,hA,he⟩ := flagAveragingMatrix_uniform_difference (v:=v) hD g
  let B := A*(2*L+1/κ)/(ρ*η^2)
  let H := 2*(m:ℝ)*(2*(D:ℝ)^2*K+2)^2*(4*(D:ℝ)^2*η+2)^2
  have hB : 0≤B := by dsimp [B]; positivity
  have hH : 0≤H := by dsimp [H]; positivity
  refine ⟨R,H*B^2,hR,mul_nonneg hH (sq_nonneg _),?_⟩
  intro N r r' hN hr hr' hfine hfine' T
  have hN₀ : 0<N := lt_of_lt_of_le zero_lt_one hN
  have hr₀ : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hr'₀ : 0 < r' := lt_of_lt_of_le zero_lt_one hr'
  have hb (r : ℝ) (hr : 1 ≤ r) (hh : R ≤ κ/(r/N)) (p : FlagSite a m D v × FlagSite a m D v) :
      |flagMatrixDifference hD g χ ρ N r η κ p| ≤ B/(N*r) :=
    he χ hχ L ρ N r η κ hL hρ hN₀ hr hη hκ hh hLip p.1 p.2
  have hs (S : Finset (FlagSite a m D v × FlagSite a m D v))
      (hh : ∀p∈S,flagMatrixDifference hD g χ ρ N r η κ p≠0) : (S.card:ℝ) ≤ H*N^2*r^2 :=
    flagAveragingMatrix_difference_support hD g χ hK hcompact ρ κ hN hr hη S hh
  calc
    _ ≤ (H*N^2*r^2)*(B/(N*r))*(B/(N*r')) :=
      finite_correlation_bound T _ _ (by positivity) (by positivity)
        (fun p _ => hb r hr hfine p) (fun p _ => hb r' hr' hfine' p) (fun S _ hh => hs S hh)
    _ = _ := by field_simp

theorem flagMatrixDifference_dyadic_energy_oai {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) (χ : (ℝ×ℝ) → ℝ)
    (hχ : ∀x,χ x∈Set.Icc (0:ℝ) 1) {K L ρ η κ : ℝ}
    (hK : 0<K) (hcompact : ∀x,K ≤ ‖x‖ → χ x=0)
    (hL : 0≤L) (hρ : 0<ρ) (hη : 0<η) (hκ : 0<κ)
    (hLip : ∀x y,|χ x-χ y| ≤ L*(|x.1-y.1|+|x.2-y.2|)) :
    ∃R C : ℝ,0≤R ∧ 0≤C ∧ ∀N : ℝ,1≤N → ∀I : Finset ℕ,
      (∀i∈I,R ≤ κ/((2:ℝ)^i/N)) → ∀w : ℝ,
      ∀T : Finset (FlagSite a m D v × FlagSite a m D v),
      ∑p∈T,(w*∑i∈I,flagMatrixDifference hD g χ ρ N ((2:ℝ)^i) η κ p)^2 ≤
        4*C*(I.card:ℝ)*w^2 := by
  obtain ⟨R,C,hR,hC,hcorr⟩ := flagMatrixDifference_correlation (v:=v) hD g χ hχ
    hK hcompact hL hρ hη hκ hLip
  refine ⟨R,C,hR,hC,fun N hN I hfine w T => ?_⟩
  apply finite_dyadic_energy T I _ hC
  intro i hi j hj _
  exact hcorr N ((2:ℝ)^i) ((2:ℝ)^j) hN (one_le_pow₀ (by norm_num))
    (one_le_pow₀ (by norm_num)) (hfine i hi) (hfine j hj) T

end PolygonCovarianceEnergy

end SimpleAmenable
end
end

end OAI
end

theorem solution : type_of% @OAI.SimpleAmenable.flagMatrixDifference_dyadic_energy_oai := @OAI.SimpleAmenable.flagMatrixDifference_dyadic_energy_oai
