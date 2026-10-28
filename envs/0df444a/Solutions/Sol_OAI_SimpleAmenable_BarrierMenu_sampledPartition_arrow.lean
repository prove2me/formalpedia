-- Prove2me | solution 1 for OAI.SimpleAmenable.BarrierMenu.sampledPartition_arrow
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T04:41:01.269935+00:00
-- url     : https://prove2.me/submissions/85423bc9-1f2d-4f81-b98a-49942de0e729

import Mathlib
import Definitions.Def_OAIQ65Sa014
import Theorems.Thm_OAI_SimpleAmenable_BarrierSignalSystem_chart_line_transport

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Amenability_BarrierCells
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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

section BarrierPartitions
open Classical Set

theorem mem_finiteBarrierPartition {ι : Type*} [Fintype ι] {a : ℕ}
    {j : ι → Fin 4} {c : ι → CutRing} {B : Set (ℝ×ℝ)}
    (hB : SupportedBarriers a j c B) (C : polygonAlgebra a) :
    C∈(finiteBarrierPartition hB).cells ↔ ∃p : GenericSquare a,
      C.val=barrierComponentCell B p.val := by
  change C∈(barrierPolygonAt_finite_range hB).toFinset ↔ _
  rw [Set.Finite.mem_toFinset]
  constructor
  · rintro ⟨p,rfl⟩
    exact ⟨p,rfl⟩
  · rintro ⟨p,hp⟩
    exact ⟨p,Subtype.ext hp.symm⟩

end BarrierPartitions

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Amenability_BarrierLineGeometry
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
section BarrierLineGeometry
open Classical Set

theorem barrierLineParameter_point (a : ℕ) (j : Fin 4) (c : CutRing) (t : ℝ) :
    barrierLineParameter j (barrierLinePoint a j c t)=t := by
  fin_cases j <;> simp [barrierLineParameter,barrierLinePoint]

end BarrierLineGeometry

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Amenability_BarrierAlgorithm
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
section BarrierAlgorithm
open Classical Set

theorem flagSite_eq_of_track_point {a m D : ℕ} {v : ℝ×ℝ}
    {z w : FlagSite a m D v} (ht : z.val.1=w.val.1)
    (hp : barrierSitePoint z=barrierSitePoint w) : z=w := by
  apply Subtype.ext
  exact Prod.ext ht (Subtype.ext hp)

theorem barrierActivation_at_site {a m : ℕ} (ha : 0<a) (i : Fin m)
    (j : Fin 4) (c : CutRing)
    (b : FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j) → Bool)
    (s : ℝ) (z : FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j))
    (ht : z.val.1=i) (hp : barrierSitePoint z=barrierLinePoint a j c s) :
    barrierActivation ha i j c b s=b z := by
  apply Bool.eq_iff_iff.mpr
  simp only [barrierActivation,decide_eq_true_eq]
  constructor
  · rintro ⟨w,hw,hwp,hb⟩
    have he : w=z := flagSite_eq_of_track_point (hw.trans ht.symm) (hwp.trans hp.symm)
    simpa [he] using hb
  · intro hb
    exact ⟨z,ht,hp,hb⟩

theorem mem_barrierSubdivision_bounds {a m : ℕ} (ha : 0<a) (i : Fin m)
    {j : Fin 4} {N : ℝ} {c : CutRing} (hc : c∈barrierCandidate a j N)
    (M : Finset (FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j)))
    {s : ℝ} (hs : s∈barrierSubdivision ha i j c M) :
    s∈Icc (barrierLineLower a j c) (barrierLineUpper a j c) := by
  have hgap := (barrierLineLower_lt_upper hc).le
  simp only [barrierSubdivision,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hs
  rcases hs with (rfl | rfl) | hs
  · exact ⟨le_rfl,hgap⟩
  · exact ⟨hgap,le_rfl⟩
  · obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨_,hzt,hzp,hzc⟩ := Finset.mem_filter.mp hz
    have hp : barrierLinePoint a j c (barrierLineParameter j (barrierSitePoint z))∈squareInterior := by
      rwa [barrierLinePoint_parameter hzc]
    exact ⟨((barrierLinePoint_interior_iff hc _).mp hp).1.le,
      ((barrierLinePoint_interior_iff hc _).mp hp).2.le⟩

theorem barrierSubdivision_start_site {a m : ℕ} (ha : 0<a) (i : Fin m)
    {j : Fin 4} {N : ℝ} {c : CutRing} (hc : c∈barrierCandidate a j N)
    (M : Finset (FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j)))
    {s t : ℝ} (h : ConsecutiveSubdivision (barrierSubdivision ha i j c M) s t) :
    ∃z : FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j),
      z.val.1=i ∧ barrierSitePoint z=barrierLinePoint a j c s ∧
      (s=barrierLineLower a j c ∨ z∈M) := by
  have hs := h.1
  have ht := mem_barrierSubdivision_bounds ha i hc M h.2.1
  simp only [barrierSubdivision,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hs
  rcases hs with (rfl | rfl) | hs
  · exact ⟨barrierIncomingSite ha i hc,rfl,rfl,Or.inl rfl⟩
  · exact False.elim (not_lt_of_ge ht.2 h.2.2.1)
  · obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨hzM,hzt,hzp,hzc⟩ := Finset.mem_filter.mp hz
    exact ⟨z,hzt,(barrierLinePoint_parameter hzc).symm,Or.inr hzM⟩

end BarrierAlgorithm

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Amenability_BarrierSignals
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
section BarrierSignals
open Classical Set
open scoped ContDiff

theorem conjugateLineForm_integral (a : ℕ) (j : Fin 4) (u : CutRing×CutRing) :
    conjugateLineForm a j (conjugate u.1,conjugate u.2)=conjugate (integralCutForm a j u) := by
  fin_cases j <;> simp [conjugateLineForm,lineNormal,integralCutForm] <;> ring

end BarrierSignals

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_OrderedSubdivision
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
section OrderedSubdivision
open Classical Set

theorem exists_consecutiveSubdivision (E : Finset ℝ) {L U x : ℝ}
    (hL : L∈E) (hU : U∈E) (hx : x∈Ico L U) :
    ∃s t,ConsecutiveSubdivision E s t ∧ x∈Icc s t := by
  let E₀ := E.filter (fun s => s≤x)
  have h₀ : E₀.Nonempty := ⟨L,Finset.mem_filter.mpr ⟨hL,hx.1⟩⟩
  let s := E₀.max' h₀
  have hs₀ : s∈E₀ := Finset.max'_mem E₀ h₀
  have hs := Finset.mem_filter.mp hs₀
  let E₁ := E.filter (fun t => s<t)
  have h₁ : E₁.Nonempty := ⟨U,Finset.mem_filter.mpr ⟨hU,lt_of_le_of_lt hs.2 hx.2⟩⟩
  let t := E₁.min' h₁
  have ht₁ : t∈E₁ := Finset.min'_mem E₁ h₁
  have ht := Finset.mem_filter.mp ht₁
  refine ⟨s,t,⟨hs.1,ht.1,ht.2,?_⟩,hs.2,?_⟩
  · intro r hr hsr
    exact Finset.min'_le E₁ r (Finset.mem_filter.mpr ⟨hr,hsr⟩)
  · by_contra h
    have htx : t≤x := le_of_lt (lt_of_not_ge h)
    have hts : t ≤ s := Finset.le_max' E₀ t (Finset.mem_filter.mpr ⟨ht.1,htx⟩)
    exact not_lt_of_ge hts ht.2

theorem sampledBarriers_contains_line {a m : ℕ} (ha : 0<a) (i : Fin m) {N : ℝ}
    (M : ∀j,Finset (FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j)))
    (b : ∀j,FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j) → Bool)
    {j : Fin 4} {c : CutRing} (hc : c∈barrierCandidate a j N)
    (hact : ∀z : FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j),
      z.val.1=i → cutForm a j (barrierSitePoint z)=ordinary c →
      (barrierSitePoint z=barrierIncoming a j c ∨ z∈M j) → b j z=true) :
    ∀p∈squareInterior,cutForm a j p=ordinary c → p∈sampledBarriers ha i N M b := by
  intro p hp hpc
  let x := barrierLineParameter j p
  have hpx : barrierLinePoint a j c x=p := barrierLinePoint_parameter hpc
  have hxin : x∈Ioo (barrierLineLower a j c) (barrierLineUpper a j c) := by
    apply (barrierLinePoint_interior_iff hc x).mp
    rwa [hpx]
  let E := barrierSubdivision ha i j c (M j)
  have hL : barrierLineLower a j c∈E := by simp [E,barrierSubdivision]
  have hU : barrierLineUpper a j c∈E := by simp [E,barrierSubdivision]
  obtain ⟨s,t,hst,hx⟩ := exists_consecutiveSubdivision E hL hU ⟨hxin.1.le,hxin.2⟩
  obtain ⟨z,hzt,hzp,hzm⟩ := barrierSubdivision_start_site ha i hc (M j) hst
  have hzline : cutForm a j (barrierSitePoint z)=ordinary c := by
    rw [hzp]; exact cutForm_barrierLinePoint a j c s
  have hzb : b j z=true := hact z hzt hzline (hzm.imp (fun hs => by rw [hzp,hs]; rfl) id)
  have hactivation : barrierActivation ha i j c (b j) s=true := by
    rw [barrierActivation_at_site ha i j c (b j) s z hzt hzp,hzb]
  refine ⟨⟨j,⟨c,hc⟩⟩,(s,t),?_,x,hx,hpx⟩
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_product.mpr ⟨hst.1,hst.2.1⟩,hst,hactivation⟩

theorem barrierActiveIntervals_empty {a m : ℕ} (ha : 0<a) (i : Fin m)
    {j : Fin 4} {N : ℝ} {c : CutRing} (hc : c∈barrierCandidate a j N)
    (M : Finset (FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j)))
    (b : FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j) → Bool)
    (hb : ∀z,z.val.1=i → cutForm a j (barrierSitePoint z)=ordinary c → b z=false) :
    barrierActiveIntervals ha i j c M b=∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro st hst
  have hh := (Finset.mem_filter.mp hst).2
  obtain ⟨z,hzt,hzp,_⟩ := barrierSubdivision_start_site ha i hc M hh.1
  have hzline : cutForm a j (barrierSitePoint z)=ordinary c := by
    rw [hzp]; exact cutForm_barrierLinePoint a j c st.1
  rw [barrierActivation_at_site ha i j c b st.1 z hzt hzp,hb z hzt hzline] at hh
  exact Bool.false_ne_true hh.2

end OrderedSubdivision

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Amenability_BarrierCore
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
section BarrierCore
open Classical

theorem conjugateLineForm_site {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (z : FlagSite a m D v) (j : Fin 4) (c : CutRing)
    (hc : cutForm a j (barrierSitePoint z)=ordinary c) :
    conjugateLineForm a j (flagSiteConjugate z)=conjugate c := by
  have hD' : (D:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hD
  have hpoint : (ordinary (flagSiteNumerator z).1,ordinary (flagSiteNumerator z).2)=
      (D:ℝ) • barrierSitePoint z := by
    rw [show barrierSitePoint z=scaledOrdinary D (flagSiteNumerator z) from (flagSiteNumerator_spec z).symm]
    apply Prod.ext <;> simp [scaledOrdinary,mul_div_cancel₀ _ hD']
  have hlevel : integralCutForm a j (flagSiteNumerator z)=(D:CutRing)*c := by
    apply ordinary_injective
    rw [←cutForm_ordinary,hpoint,cutForm_smul,hc,map_mul,map_natCast]
  have hconj : flagSiteConjugate z=(D:ℝ)⁻¹ •
      (conjugate (flagSiteNumerator z).1,conjugate (flagSiteNumerator z).2) := by
    apply Prod.ext <;> simp [flagSiteConjugate,scaledConjugate,div_eq_mul_inv,mul_comm]
  rw [hconj,map_smul,conjugateLineForm_integral,hlevel,map_mul,map_natCast]
  simp [hD']

end BarrierCore

section BarrierSignalGeometry
open Classical Set

theorem scaledSiteConjugate_eq_smul {a m D : ℕ} {v : ℝ×ℝ} (N : ℝ)
    (z : FlagSite a m D v) : scaledSiteConjugate N z=N⁻¹ • flagSiteConjugate z := by
  apply Prod.ext <;> simp [scaledSiteConjugate,div_eq_mul_inv,mul_comm]

theorem norm_scaledSiteConjugate {a m D : ℕ} {v : ℝ×ℝ} {N : ℝ} (hN : 0<N)
    (z : FlagSite a m D v) : ‖scaledSiteConjugate N z‖=‖flagSiteConjugate z‖/N := by
  rw [scaledSiteConjugate_eq_smul,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hN]
  ring

theorem conjugateLineForm_scaledSite {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (z : FlagSite a m D v) (j : Fin 4) (c : CutRing) (N : ℝ)
    (hc : cutForm a j (barrierSitePoint z)=ordinary c) :
    conjugateLineForm a j (scaledSiteConjugate N z)=conjugate c/N := by
  rw [scaledSiteConjugate_eq_smul,map_smul,conjugateLineForm_site hD z j c hc]
  simp [div_eq_mul_inv,mul_comm]

theorem firstSignal_true_norm {a m D : ℕ} {v : ℝ×ℝ} {N R : ℝ}
    (θ : (ℝ×ℝ) → ℝ) (b : FlagSite a m D v → Bool)
    (hθ : ∀x,R≤‖x‖ → θ x=-3) (hs : signalSuccess (flagMeanSignal θ N) b)
    (z : FlagSite a m D v) (hz : b z=true) : ‖scaledSiteConjugate N z‖<R := by
  by_contra h
  have hh := (hs z).2 (show flagMeanSignal θ N z≤-2 by
    rw [flagMeanSignal,hθ _ (le_of_not_gt h)]; norm_num)
  rw [hz] at hh
  cases hh

theorem firstSignal_true_in_box {a m D : ℕ} {v : ℝ×ℝ} {N R : ℝ} (hN : 0<N)
    (θ : (ℝ×ℝ) → ℝ) (b : FlagSite a m D v → Bool)
    (hθ : ∀x,R≤‖x‖ → θ x=-3) (hs : signalSuccess (flagMeanSignal θ N) b)
    (z : FlagSite a m D v) (hz : b z=true) : z∈flagSiteBox (N*R) := by
  have hh := firstSignal_true_norm θ b hθ hs z hz
  rw [norm_scaledSiteConjugate hN,div_lt_iff₀ hN] at hh
  change |(flagSiteConjugate z).1|≤N*R ∧ |(flagSiteConjugate z).2|≤N*R
  rw [Prod.norm_def,max_lt_iff,Real.norm_eq_abs,Real.norm_eq_abs] at hh
  constructor <;> linarith [hh.1,hh.2]

theorem mem_finiteFirstMarks_iff {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    {N R : ℝ} (hN : 0<N) (hR : 0<R) (θ : (ℝ×ℝ) → ℝ) (b : FlagSite a m D v → Bool)
    (hθ : ∀x,R≤‖x‖ → θ x=-3) (hs : signalSuccess (flagMeanSignal θ N) b)
    (z : FlagSite a m D v) : z∈finiteFirstMarks hD hN hR b ↔ b z=true := by
  simp only [finiteFirstMarks,Finset.mem_filter,mem_flagBoxFinset]
  exact ⟨And.right,fun hz => ⟨firstSignal_true_in_box hN θ b hθ hs z hz,hz⟩⟩

theorem secondSignal_negative_empty {a m : ℕ} (ha : 0<a) (i : Fin m)
    {j : Fin 4} {N : ℝ} (hN : 0<N) {c : CutRing} (hc : c∈barrierCandidate a j N)
    (M : Finset (FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j)))
    (θ : (ℝ×ℝ) → ℝ)
    (b : FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j) → Bool)
    (hθ : ∀x,3 ≤ |conjugateLineForm a j x| → θ x=-3)
    (hs : signalSuccess (flagMeanSignal θ N) b) (hcneg : 3*N ≤ |conjugate c|) :
    barrierActiveIntervals ha i j c M b=∅ := by
  apply barrierActiveIntervals_empty ha i hc M b
  intro z _ hz
  apply (hs z).2
  rw [flagMeanSignal,hθ]
  · norm_num
  · rw [conjugateLineForm_scaledSite (commonVertexDenominator_pos ha) z j c N hz,
      abs_div,abs_of_pos hN]
    exact (le_div_iff₀ hN).mpr hcneg

end BarrierSignalGeometry

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Amenability_BarrierSignalSystem
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
section BarrierSignalSystem
open Classical Set

namespace BarrierSignalSystem
variable {a : ℕ} {ha : 0 < a} {Q B : ℝ} (S : BarrierSignalSystem a ha Q B)

theorem incoming_first_true {m : ℕ} (i : Fin m) {N : ℝ} (hN : 1 ≤ N) {j : Fin 4}
    {c : CutRing} (hc : c ∈ barrierCandidate a j N)
    (b : FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j) → Bool)
    (hs : signalSuccess (flagMeanSignal S.first.signal N) b) : b (barrierIncomingSite ha i hc)=true := by
  apply (hs _).1
  rw [flagMeanSignal,S.first_pos]
  · norm_num
  · rw [norm_scaledSiteConjugate (by linarith : 0 < N),div_le_iff₀ (by linarith : 0 < N)]
    exact S.incoming_core m i N hN j c hc

theorem mem_marks_iff {m : ℕ} {N : ℝ} (hN : 0 < N) (j : Fin 4)
    (b : FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j) → Bool)
    (hs : signalSuccess (flagMeanSignal S.first.signal N) b) (z) :
    z ∈ S.marks hN j b ↔ b z=true :=
  mem_finiteFirstMarks_iff (commonVertexDenominator_pos ha) hN S.R₁_pos S.first.signal b S.first_neg hs z

theorem central_line_barrier {m : ℕ} (i : Fin m) {N : ℝ} (hN : 1 ≤ N)
    (b₁ b₂ : ∀j,FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j) → Bool)
    (hs₁ : ∀j,signalSuccess (flagMeanSignal S.first.signal N) (b₁ j))
    (hs₂ : ∀j,signalSuccess (flagMeanSignal (S.second j).signal N) (b₂ j))
    {j : Fin 4} {c : CutRing} (hc : c ∈ barrierCandidate a j N) (hband : |conjugate c| ≤ N) :
    ∀p ∈ squareInterior,cutForm a j p=ordinary c →
      p ∈ sampledBarriers ha i N (fun j => S.marks (N:=N) (lt_of_lt_of_le zero_lt_one hN) j (b₁ j)) b₂ := by
  have hN₀ : 0 < N := by linarith
  apply sampledBarriers_contains_line ha i _ b₂ hc
  intro z hzt hzline hzstart
  have hzfirst : b₁ j z=true := by
    rcases hzstart with hz | hz
    · have he : z=barrierIncomingSite ha i hc :=
        flagSite_eq_of_track_point hzt hz
      rw [he]
      exact S.incoming_first_true i hN hc (b₁ j) (hs₁ j)
    · exact (S.mem_marks_iff hN₀ j (b₁ j) (hs₁ j) z).mp hz
  apply (hs₂ j z).1
  rw [flagMeanSignal,S.second_pos]
  · norm_num
  · exact (firstSignal_true_norm S.first.signal (b₁ j) S.first_neg (hs₁ j) z hzfirst).le
  · rw [conjugateLineForm_scaledSite (commonVertexDenominator_pos ha) z j c N hzline,
      abs_div,abs_of_pos hN₀,div_le_one hN₀]
    exact hband

end BarrierSignalSystem
end BarrierSignalSystem

section SubdivisionCovariance
open Classical Set

theorem mem_barrierActiveIntervals_image_iff {a m : ℕ} (ha : 0 < a) (i : Fin m)
    (j : Fin 4) (c : CutRing)
    (M : Finset (FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j)))
    (b : FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j) → Bool) (x : ℝ) :
    (∃st ∈ barrierActiveIntervals ha i j c M b,x ∈ Icc st.1 st.2) ↔
      x ∈ subdivisionBarrier (barrierSubdivision ha i j c M) (barrierActivation ha i j c b) := by
  constructor
  · rintro ⟨⟨s,t⟩,hst,hx⟩
    have hh := (Finset.mem_filter.mp hst).2
    exact ⟨s,t,hh.1,hh.2,hx⟩
  · rintro ⟨s,t,hst,hb,hx⟩
    exact ⟨(s,t),Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hst.1,hst.2.1⟩,hst,hb⟩,hx⟩

end SubdivisionCovariance

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Amenability_BarrierChartRefinement
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

section BarrierCrossings
open Classical Set

theorem barrierLineParameter_add (j : Fin 4) (p q : ℝ×ℝ) :
    barrierLineParameter j (p+q)=barrierLineParameter j p+barrierLineParameter j q := by
  fin_cases j  <;> simp [barrierLineParameter]

end BarrierCrossings

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Amenability_BarrierStartGerm
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
section BarrierStartGerm
open Classical Set

theorem continuous_nonzero_sign {X : Type*} [TopologicalSpace X] {C : Set X}
    (hC : IsPreconnected C) {f : X → ℝ} (hf : ContinuousOn f C)
    (hn : ∀x ∈ C,f x ≠ 0) {x y : X} (hx : x ∈ C) (hy : y ∈ C) :
    f x < 0 ↔ f y < 0 := by
  have h (u v : X) (hu : u ∈ C) (hv : v ∈ C) (hu' : f u < 0) : f v < 0 := by
    by_contra hh
    obtain ⟨z,hz,hz0⟩ := hC.intermediate_value hu hv hf ⟨hu'.le,le_of_not_gt hh⟩
    exact hn z hz hz0
  exact ⟨h x y hx hy,h y x hy hx⟩

end BarrierStartGerm

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_OpenAffineCharts
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
section OpenAffineCharts
open Classical Set

theorem openSquareChart_open {a : ℕ} (T : Finset PlaneCut) (p : GenericSquare a) :
    IsOpen (openSquareChart T p) := by
  apply ((isOpen_Ioo : IsOpen (Ioo (0:ℝ) 1)).prod isOpen_Ioo).inter
  have he : strictLineCell a (fun l : T => l.val.1) (fun l => ordinary l.val.2)
      (fun l => squareSign l.val p)=⋂l : T,{x | if squareSign l.val p then
      cutForm a l.val.1 x < ordinary l.val.2 else ordinary l.val.2 < cutForm a l.val.1 x} := by
    ext x
    simp [strictLineCell]
  rw [he]
  apply isOpen_iInter_of_finite
  intro l
  split_ifs
  · exact isOpen_lt (cutForm_continuous a l.val.1) continuous_const
  · exact isOpen_lt continuous_const (cutForm_continuous a l.val.1)

theorem openSquareChart_signs {a : ℕ} {T : Finset PlaneCut} {p : GenericSquare a}
    {x : ℝ×ℝ} (hx : x ∈ openSquareChart T p) {l : PlaneCut} (hl : l ∈ T) :
    cutForm a l.1 x ≠ ordinary l.2 ∧
      (cutForm a l.1 x < ordinary l.2 ↔ cutForm a l.1 p.val < ordinary l.2) := by
  have hh := hx.2 ⟨l,hl⟩
  by_cases h : cutForm a l.1 p.val < ordinary l.2
  · have ht : cutForm a l.1 x < ordinary l.2 := by simpa [squareSign,h] using hh
    exact ⟨ne_of_lt ht,iff_of_true ht h⟩
  · have ht : ordinary l.2 < cutForm a l.1 x := by simpa [squareSign,h] using hh
    exact ⟨ne_of_gt ht,iff_of_false (not_lt_of_gt ht) h⟩

theorem squareArrangement_on_openChart {a : ℕ} {K : Type*}
    (f : GenericSquare a → K) (T : Finset PlaneCut)
    (hT : ∀p q,(∀l ∈ T,squareSign l p=squareSign l q) → f p=f q)
    (p q : GenericSquare a) (hq : q.val ∈ openSquareChart T p) : f q=f p :=
  hT q p (fun _ hl => decide_eq_decide.mpr (openSquareChart_signs hq hl).2)

theorem open_subset_closed_of_dense {X : Type*} [TopologicalSpace X]
    {D C A : Set X} (hD : Dense D) (hC : IsOpen C) (hA : IsClosed A)
    (h : C ∩ D ⊆ A) : C ⊆ A := by
  intro x hx
  by_contra hn
  have hne : (C ∩ Aᶜ).Nonempty := ⟨x,hx,hn⟩
  obtain ⟨y,hy,hyD⟩ := hD.inter_open_nonempty (C ∩ Aᶜ) (hC.inter hA.isOpen_compl) hne
  exact hy.2 (h ⟨hy.1,hyD⟩)

theorem open_translation_square {a : ℕ} {C : Set (ℝ×ℝ)} (hC : IsOpen C)
    (hCs : C ⊆ squareInterior) (u : CutRing×CutRing)
    (hgen : ∀p : GenericSquare a,p.val ∈ C → p.val+(ordinary u.1,ordinary u.2) ∈ squareInterior) :
    (fun x => x+(ordinary u.1,ordinary u.2)) '' C ⊆ squareInterior := by
  let v := (ordinary u.1,ordinary u.2)
  let W := (fun x => x+v) '' C
  have hW : IsOpen W := (Homeomorph.addRight v).isOpenMap C hC
  have hWclosed : W ⊆ Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1 := by
    apply open_subset_closed_of_dense (avoidsCuts_dense a) hW (isClosed_Icc.prod isClosed_Icc)
    rintro y ⟨⟨x,hx,rfl⟩,hy⟩
    have hg : AvoidsCuts a x := by
      have hh := avoidsCuts_translate hy (-u)
      simpa [v,map_neg,←Prod.neg_mk] using hh
    have hp : x.1 ∈ Ico (0:ℝ) 1 ∧ x.2 ∈ Ico (0:ℝ) 1 ∧ AvoidsCuts a x :=
      ⟨⟨(hCs hx).1.1.le,(hCs hx).1.2⟩,⟨(hCs hx).2.1.le,(hCs hx).2.2⟩,hg⟩
    have hi := hgen ⟨x,hp⟩ hx
    exact ⟨⟨hi.1.1.le,hi.1.2.le⟩,⟨hi.2.1.le,hi.2.2.le⟩⟩
  have hh := hW.subset_interior_iff.mpr hWclosed
  simpa only [interior_prod_eq,interior_Icc,squareInterior] using hh

theorem fullGroupAffineChart_square {a m : ℕ} (g : polygonFullGroup a m) (i : Fin m)
    (T : Finset PlaneCut)
    (hT : ∀p q,(∀l ∈ T,squareSign l p=squareSign l q) →
      fullGroupAffineData g i p=fullGroupAffineData g i q) (p : GenericSquare a) :
    (fun x => x+(ordinary (fullGroupAffineData g i p).2.1,
      ordinary (fullGroupAffineData g i p).2.2)) '' openSquareChart T p ⊆ squareInterior := by
  apply open_translation_square (openSquareChart_open T p) (fun _ h => h.1)
  intro q hq
  have hf := squareArrangement_on_openChart (fullGroupAffineData g i) T hT p q hq
  have hg := fullGroupSquareShift_spec g i q
  change (g.val (i,q)).2.val=q.val+(ordinary (fullGroupAffineData g i q).2.1,
      ordinary (fullGroupAffineData g i q).2.2) at hg
  rw [hf] at hg
  rw [←hg]
  exact generic_mem_squareInterior _

end OpenAffineCharts

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Amenability_BarrierFiniteMenu
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
section BarrierFiniteMenu
open Classical Set

theorem barrierChartCuts_spec {a m : ℕ} (g : polygonFullGroup a m) (i : Fin m) :
    ∀p q,(∀l ∈ barrierChartCuts g i,squareSign l p=squareSign l q) →
      fullGroupAffineData g i p=fullGroupAffineData g i q :=
  (fullGroupAffineData_arrangement g i).choose_spec

end BarrierFiniteMenu

section EightBarrierFields
open Classical MeasureTheory Filter Set
open scoped Topology

theorem castFlagBits_success {a m D : ℕ} {v w : ℝ×ℝ} (e : v=w)
    (b : FlagSite a m D v → Bool) (f : (ℝ×ℝ) → ℝ) (N : ℝ)
    (h : signalSuccess (flagMeanSignal f N) b) :
    signalSuccess (flagMeanSignal f N) (castFlagBits e b) := by cases e; exact h

theorem castFlagBits_transport {a m D : ℕ} {v w : ℝ×ℝ} (e : v=w) (hD : 0 < D)
    (b : FlagSite a m D v → Bool) (g : polygonFullGroup a m) (z : FlagSite a m D w) :
    castFlagBits e (bitReindex (flagSitePermutation hD g) b) (flagSiteAction hD g z)=castFlagBits e b z := by
  cases e
  exact congrArg b ((flagSitePermutation hD g).symm_apply_apply z)

namespace BarrierSignalSystem
variable {a : ℕ} {ha : 0 < a} {Q B : ℝ} (S : BarrierSignalSystem a ha Q B)

theorem eight_success {m n : ℕ} {b : BarrierBits a m ha}
    (h : jointFieldSuccess (barrierEightDirections ha) S.eight n b) :
    (∀j,signalSuccess (flagMeanSignal S.first.signal (sourceDyadicN n)) (barrierFirstBits b j)) ∧
    (∀j,signalSuccess (flagMeanSignal (S.second j).signal (sourceDyadicN n)) (barrierSecondBits b j)) := by
  constructor
  · intro j
    apply castFlagBits_success
    simpa only [eight,Fin.addCases_left] using h (j.castAdd 4)
  · intro j
    apply castFlagBits_success
    simpa only [eight,Fin.addCases_right] using h (j.natAdd 4)

end BarrierSignalSystem

theorem barrierBitsTransport_first {a m : ℕ} {ha : 0 < a} (g : polygonFullGroup a m)
    (b : BarrierBits a m ha) (j : Fin 4) (z) :
    barrierFirstBits (barrierBitsTransport g b) j
      (flagSiteAction (commonVertexDenominator_pos ha) g z)=barrierFirstBits b j z := by
  exact castFlagBits_transport (Fin.addCases_left j) (commonVertexDenominator_pos ha)
    (b (j.castAdd 4)) g z

theorem barrierBitsTransport_second {a m : ℕ} {ha : 0 < a} (g : polygonFullGroup a m)
    (b : BarrierBits a m ha) (j : Fin 4) (z) :
    barrierSecondBits (barrierBitsTransport g b) j
      (flagSiteAction (commonVertexDenominator_pos ha) g z)=barrierSecondBits b j z := by
  exact castFlagBits_transport (Fin.addCases_right j) (commonVertexDenominator_pos ha)
    (b (j.natAdd 4)) g z

end EightBarrierFields

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Amenability_ChartLineTransport
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

section ChartBarrierTransport
open Classical Set

theorem mem_sampledBarriers_iff {a m : ℕ} (ha : 0 < a) (i : Fin m) (N : ℝ)
    (M : ∀j,Finset (FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j)))
    (b : ∀j,FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j) → Bool)
    (p : ℝ×ℝ) : p ∈ sampledBarriers ha i N M b ↔
      ∃j c,c ∈ barrierCandidate a j N ∧ cutForm a j p=ordinary c ∧
        barrierLineParameter j p ∈ subdivisionBarrier (barrierSubdivision ha i j c (M j))
          (barrierActivation ha i j c (b j)) := by
  constructor
  · rintro ⟨⟨j,c,hc⟩,st,hst,x,hx,rfl⟩
    refine ⟨j,c,hc,cutForm_barrierLinePoint a j c x,?_⟩
    rw [barrierLineParameter_point]
    exact (mem_barrierActiveIntervals_image_iff ha i j c (M j) (b j) x).mp ⟨st,hst,hx⟩
  · rintro ⟨j,c,hc,hpc,hp⟩
    obtain ⟨st,hst,hx⟩ := (mem_barrierActiveIntervals_image_iff ha i j c (M j) (b j) _).mpr hp
    exact ⟨⟨j,⟨c,hc⟩⟩,st,hst,barrierLineParameter j p,hx,barrierLinePoint_parameter hpc⟩

namespace BarrierSignalSystem
variable {a : ℕ} {ha : 0 < a} {Q B : ℝ} (S : BarrierSignalSystem a ha Q B)

theorem active_line_small {m : ℕ} (i : Fin m) {N : ℝ} (hN : 0 < N) (j : Fin 4)
    (c : CutRing) (hc : c ∈ barrierCandidate a j N)
    (M : Finset (FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j)))
    (b : FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j) → Bool)
    (hs : signalSuccess (flagMeanSignal (S.second j).signal N) b)
    {x : ℝ} (hx : x ∈ subdivisionBarrier (barrierSubdivision ha i j c M) (barrierActivation ha i j c b)) :
    |conjugate c| < 3*N := by
  by_contra hn
  have he := secondSignal_negative_empty ha i hN hc M (S.second j).signal b
    (S.second_neg j) hs (le_of_not_gt hn)
  obtain ⟨st,hst,_⟩ := (mem_barrierActiveIntervals_image_iff ha i j c M b x).mpr hx
  rw [he] at hst
  exact Finset.notMem_empty st hst

theorem chart_barrier_transport {m : ℕ} (g : polygonFullGroup a m) (i k : Fin m)
    (T : Finset PlaneCut)
    (hT : ∀p q,(∀l ∈ T,squareSign l p=squareSign l q) →
      fullGroupAffineData g i p=fullGroupAffineData g i q) (p : GenericSquare a)
    (u : CutRing×CutRing) (hdata : fullGroupAffineData g i p=(k,u))
    (hQ : 0 ≤ Q) (huQ : ∀j,|conjugate (integralCutForm a j u)| ≤ Q)
    (hB : ∀l ∈ T ∪ squareBoundaryCuts,|conjugate l.2| ≤ B ∧
      |conjugate (l.2+integralCutForm a l.1 u)| ≤ B)
    {N : ℝ} (hN : 1 ≤ N) (hQN : Q < N)
    (b₁ b₂ b₁' b₂' : ∀j,FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j) → Bool)
    (hs : ∀j,signalSuccess (flagMeanSignal S.first.signal N) (b₁ j))
    (hs' : ∀j,signalSuccess (flagMeanSignal S.first.signal N) (b₁' j))
    (ht : ∀j,signalSuccess (flagMeanSignal (S.second j).signal N) (b₂ j))
    (ht' : ∀j,signalSuccess (flagMeanSignal (S.second j).signal N) (b₂' j))
    (hb₁ : ∀j z,b₁' j (flagSiteAction (commonVertexDenominator_pos ha) g z)=b₁ j z)
    (hb₂ : ∀j z,b₂' j (flagSiteAction (commonVertexDenominator_pos ha) g z)=b₂ j z)
    {x : ℝ×ℝ} (hx : x ∈ openSquareChart T p) :
    x ∈ sampledBarriers ha i N (fun j => S.marks (N:=N) (lt_of_lt_of_le zero_lt_one hN) j (b₁ j)) b₂ ↔
    x+(ordinary u.1,ordinary u.2) ∈ sampledBarriers ha k N
      (fun j => S.marks (N:=N) (lt_of_lt_of_le zero_lt_one hN) j (b₁' j)) b₂' := by
  have hN₀ : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hx' : x+(ordinary u.1,ordinary u.2) ∈ squareInterior := by
    have hh := fullGroupAffineChart_square g i T hT p
    rw [hdata] at hh
    exact hh ⟨x,hx,rfl⟩
  rw [mem_sampledBarriers_iff,mem_sampledBarriers_iff]
  constructor
  · rintro ⟨j,c,hc,hline,hactive⟩
    have hsmall := S.active_line_small i hN₀ j c hc _ (b₂ j) (ht j) hactive
    have hc' : c+integralCutForm a j u ∈ barrierCandidate a j N := by
      refine ⟨?_,x+(ordinary u.1,ordinary u.2),hx',?_⟩
      · rw [map_add]
        calc
          |conjugate c+conjugate (integralCutForm a j u)| ≤ |conjugate c|+|conjugate (integralCutForm a j u)| := abs_add_le _ _
          _ ≤ 4*N := by linarith [huQ j]
      · rw [cutForm_add,hline,cutForm_ordinary,map_add]
    have hxline : barrierLinePoint a j c (barrierLineParameter j x) ∈ openSquareChart T p := by
      rwa [barrierLinePoint_parameter hline]
    have htransport := S.chart_line_transport g i k T hT p u hdata hQ hB hN j c hc hc'
      (b₁ j) (b₂ j) (b₁' j) (b₂' j) (hs j) (hs' j) (hb₁ j) (hb₂ j) hxline
    refine ⟨j,c+integralCutForm a j u,hc',?_,?_⟩
    · rw [cutForm_add,hline,cutForm_ordinary,map_add]
    · rw [barrierLineParameter_add]
      exact htransport.mp hactive
  · rintro ⟨j,c',hc',hline',hactive'⟩
    let c := c'-integralCutForm a j u
    have hce : c+integralCutForm a j u=c' := sub_add_cancel _ _
    have hline : cutForm a j x=ordinary c := by
      rw [cutForm_add,cutForm_ordinary] at hline'
      dsimp [c]
      rw [map_sub]
      linarith
    have hsmall := S.active_line_small k hN₀ j c' hc' _ (b₂' j) (ht' j) hactive'
    have hc : c ∈ barrierCandidate a j N := by
      refine ⟨?_,x,hx.1,hline⟩
      change |conjugate (c'-integralCutForm a j u)| ≤ _
      rw [map_sub]
      calc
        |conjugate c'-conjugate (integralCutForm a j u)| ≤ |conjugate c'|+|conjugate (integralCutForm a j u)| := abs_sub _ _
        _ ≤ 4*N := by linarith [huQ j]
    have hxline : barrierLinePoint a j c (barrierLineParameter j x) ∈ openSquareChart T p := by
      rwa [barrierLinePoint_parameter hline]
    have htransport := S.chart_line_transport g i k T hT p u hdata hQ hB hN j c hc
      (hce.symm ▸ hc') (b₁ j) (b₂ j) (b₁' j) (b₂' j) (hs j) (hs' j) (hb₁ j) (hb₂ j) hxline
    rw [hce] at htransport
    refine ⟨j,c,hc,hline,htransport.mpr ?_⟩
    simpa only [barrierLineParameter_add] using hactive'

end BarrierSignalSystem
end ChartBarrierTransport

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Amenability_ComponentChartContainment
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
section ComponentChartContainment
open Classical Set

theorem barrier_component_cut_ordinary {a : ℕ} {B : Set (ℝ×ℝ)} {j : Fin 4} {c : CutRing}
    (hline : ∀x ∈ squareInterior,cutForm a j x=ordinary c → x ∈ B)
    {p x : ℝ×ℝ} (hp : p ∈ barrierRegion B)
    (hx : x ∈ connectedComponentIn (barrierRegion B) p) :
    cutForm a j x ≠ ordinary c ∧ (cutForm a j x < ordinary c ↔ cutForm a j p < ordinary c) := by
  have hn (y : ℝ×ℝ) (hy : y ∈ connectedComponentIn (barrierRegion B) p) : cutForm a j y ≠ ordinary c := by
    intro he
    have hr := connectedComponentIn_subset (barrierRegion B) p hy
    exact hr.2 (hline y hr.1 he)
  refine ⟨hn x hx,?_⟩
  have hh := continuous_nonzero_sign isPreconnected_connectedComponentIn
    ((cutForm_continuous a j).sub continuous_const).continuousOn
    (fun y hy => sub_ne_zero.mpr (hn y hy)) hx (mem_connectedComponentIn hp)
  simpa only [Pi.sub_apply,sub_lt_zero] using hh

theorem barrier_component_openChart {a : ℕ} {B : Set (ℝ×ℝ)}
    (T : Finset PlaneCut) (p : GenericSquare a)
    (hp : p.val ∈ barrierRegion B)
    (hline : ∀l ∈ T,∀x ∈ squareInterior,cutForm a l.1 x=ordinary l.2 → x ∈ B) :
    connectedComponentIn (barrierRegion B) p.val ⊆ openSquareChart T p := by
  intro x hx
  refine ⟨(connectedComponentIn_subset (barrierRegion B) p.val hx).1,?_⟩
  intro l
  obtain ⟨hne,hs⟩ := barrier_component_cut_ordinary (hline l.val l.property) hp hx
  by_cases hh : cutForm a l.val.1 p.val < ordinary l.val.2
  · simpa [squareSign,hh] using hs.mpr hh
  · simpa [squareSign,hh] using lt_of_le_of_ne (le_of_not_gt (fun h => hh (hs.mp h))) hne.symm

theorem barrier_component_translatedChart {a : ℕ} {B : Set (ℝ×ℝ)}
    (T : Finset PlaneCut) (p q : GenericSquare a) (u : CutRing×CutRing)
    (hqp : q.val=p.val+(ordinary u.1,ordinary u.2))
    (hq : q.val ∈ barrierRegion B)
    (hline : ∀l ∈ T ∪ squareBoundaryCuts,∀x ∈ squareInterior,
      cutForm a l.1 x=ordinary (l.2+integralCutForm a l.1 u) → x ∈ B) :
    ∀x ∈ connectedComponentIn (barrierRegion B) q.val,
      x-(ordinary u.1,ordinary u.2) ∈ openSquareChart T p := by
  intro x hx
  have hsign (l : PlaneCut) (hl : l ∈ T ∪ squareBoundaryCuts) :
      cutForm a l.1 (x-(ordinary u.1,ordinary u.2)) ≠ ordinary l.2 ∧
      (cutForm a l.1 (x-(ordinary u.1,ordinary u.2)) < ordinary l.2 ↔
        cutForm a l.1 p.val < ordinary l.2) := by
    obtain ⟨hne,hs⟩ := barrier_component_cut_ordinary (hline l hl) hq hx
    rw [hqp,cutForm_add,cutForm_ordinary,map_add] at hs
    rw [map_add] at hne
    rw [cutForm_sub,cutForm_ordinary]
    refine ⟨fun h => hne (by linarith),?_⟩
    constructor
    · intro h
      have hh := hs.mp (by linarith : cutForm a l.1 x < ordinary l.2+ordinary (integralCutForm a l.1 u))
      linarith
    · intro h
      have hh := hs.mpr (by linarith : cutForm a l.1 p.val+ordinary (integralCutForm a l.1 u) < ordinary l.2+ordinary (integralCutForm a l.1 u))
      linarith
  have hp := generic_mem_squareInterior p
  have hx₀ := hsign (0,0) (Finset.mem_union_right _ (by simp [squareBoundaryCuts]))
  have hx₁ := hsign (0,1) (Finset.mem_union_right _ (by simp [squareBoundaryCuts]))
  have hy₀ := hsign (1,0) (Finset.mem_union_right _ (by simp [squareBoundaryCuts]))
  have hy₁ := hsign (1,1) (Finset.mem_union_right _ (by simp [squareBoundaryCuts]))
  simp only [cutForm,Matrix.cons_val_zero,Matrix.cons_val_one,
    map_zero,map_one,Prod.fst_sub,Prod.snd_sub] at hx₀ hx₁ hy₀ hy₁
  refine ⟨⟨⟨?_,?_⟩,⟨?_,?_⟩⟩,?_⟩
  · exact lt_of_le_of_ne (le_of_not_gt (fun h => not_lt_of_gt hp.1.1 (hx₀.2.mp h))) hx₀.1.symm
  · exact hx₁.2.mpr hp.1.2
  · exact lt_of_le_of_ne (le_of_not_gt (fun h => not_lt_of_gt hp.2.1 (hy₀.2.mp h))) hy₀.1.symm
  · exact hy₁.2.mpr hp.2.2
  · intro l
    obtain ⟨hne,hs⟩ := hsign l.val (Finset.mem_union_left _ l.property)
    by_cases hh : cutForm a l.val.1 p.val < ordinary l.val.2
    · simpa [squareSign,hh] using hs.mpr hh
    · simpa [squareSign,hh] using lt_of_le_of_ne (le_of_not_gt (fun h => hh (hs.mp h))) hne.symm

end ComponentChartContainment

section ComponentTransport
open Classical Set
namespace BarrierSignalSystem
variable {a : ℕ} {ha : 0 < a} {Q B : ℝ} (S : BarrierSignalSystem a ha Q B)

theorem component_transport {m : ℕ} (g : polygonFullGroup a m) (i k : Fin m)
    (T : Finset PlaneCut)
    (hT : ∀p q,(∀l ∈ T,squareSign l p=squareSign l q) →
      fullGroupAffineData g i p=fullGroupAffineData g i q) (p q : GenericSquare a)
    (u : CutRing×CutRing) (hdata : fullGroupAffineData g i p=(k,u))
    (hqp : q.val=p.val+(ordinary u.1,ordinary u.2))
    (hQ : 0 ≤ Q) (huQ : ∀j,|conjugate (integralCutForm a j u)| ≤ Q)
    (hB : ∀l ∈ T ∪ squareBoundaryCuts,|conjugate l.2| ≤ B ∧
      |conjugate (l.2+integralCutForm a l.1 u)| ≤ B)
    {N : ℝ} (hN : 1 ≤ N) (hQN : Q < N) (hBN : B ≤ N)
    (b₁ b₂ b₁' b₂' : ∀j,FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j) → Bool)
    (hs : ∀j,signalSuccess (flagMeanSignal S.first.signal N) (b₁ j))
    (hs' : ∀j,signalSuccess (flagMeanSignal S.first.signal N) (b₁' j))
    (ht : ∀j,signalSuccess (flagMeanSignal (S.second j).signal N) (b₂ j))
    (ht' : ∀j,signalSuccess (flagMeanSignal (S.second j).signal N) (b₂' j))
    (hb₁ : ∀j z,b₁' j (flagSiteAction (commonVertexDenominator_pos ha) g z)=b₁ j z)
    (hb₂ : ∀j z,b₂' j (flagSiteAction (commonVertexDenominator_pos ha) g z)=b₂ j z) :
    (fun x => x+(ordinary u.1,ordinary u.2)) '' connectedComponentIn
      (barrierRegion (sampledBarriers ha i N
        (fun j => S.marks (N:=N) (lt_of_lt_of_le zero_lt_one hN) j (b₁ j)) b₂)) p.val =
    connectedComponentIn (barrierRegion (sampledBarriers ha k N
      (fun j => S.marks (N:=N) (lt_of_lt_of_le zero_lt_one hN) j (b₁' j)) b₂')) q.val := by
  let v := (ordinary u.1,ordinary u.2)
  let A₀ := sampledBarriers ha i N
    (fun j => S.marks (N:=N) (lt_of_lt_of_le zero_lt_one hN) j (b₁ j)) b₂
  let A₁ := sampledBarriers ha k N
    (fun j => S.marks (N:=N) (lt_of_lt_of_le zero_lt_one hN) j (b₁' j)) b₂'
  have hp : p.val ∈ barrierRegion A₀ := generic_mem_barrierRegion (sampledBarriers_supported ha i N _ b₂) p
  have hq : q.val ∈ barrierRegion A₁ := generic_mem_barrierRegion (sampledBarriers_supported ha k N _ b₂') q
  have hsource : connectedComponentIn (barrierRegion A₀) p.val ⊆ openSquareChart T p := by
    apply barrier_component_openChart T p hp
    intro l hl x hx hxc
    have hband := ((hB l (Finset.mem_union_left _ hl)).1).trans hBN
    exact S.central_line_barrier i hN b₁ b₂ hs ht
      ⟨by linarith, x,hx,hxc⟩ hband x hx hxc
  have htarget : ∀x ∈ connectedComponentIn (barrierRegion A₁) q.val,x-v ∈ openSquareChart T p := by
    apply barrier_component_translatedChart T p q u hqp hq
    intro l hl x hx hxc
    have hband := ((hB l hl).2).trans hBN
    exact S.central_line_barrier k hN b₁' b₂' hs' ht'
      ⟨by linarith,x,hx,hxc⟩ hband x hx hxc
  have hbar (x : ℝ×ℝ) (hx : x ∈ openSquareChart T p) : x ∈ A₀ ↔ x+v ∈ A₁ :=
    S.chart_barrier_transport g i k T hT p u hdata hQ huQ hB hN hQN
      b₁ b₂ b₁' b₂' hs hs' ht ht' hb₁ hb₂ hx
  have hforward : (fun x => x+v) '' connectedComponentIn (barrierRegion A₀) p.val ⊆
      connectedComponentIn (barrierRegion A₁) q.val := by
    apply (isPreconnected_connectedComponentIn.image _ (continuous_id.add continuous_const).continuousOn).subset_connectedComponentIn
    · exact ⟨p.val,mem_connectedComponentIn hp,hqp.symm⟩
    · rintro x ⟨y,hy,rfl⟩
      have hyC := hsource hy
      have hyreg := connectedComponentIn_subset (barrierRegion A₀) p.val hy
      refine ⟨?_,fun h => hyreg.2 ((hbar y hyC).mpr h)⟩
      have himage := fullGroupAffineChart_square g i T hT p
      rw [hdata] at himage
      exact himage ⟨y,hyC,rfl⟩
  have hbackward : (fun x => x-v) '' connectedComponentIn (barrierRegion A₁) q.val ⊆
      connectedComponentIn (barrierRegion A₀) p.val := by
    apply (isPreconnected_connectedComponentIn.image _ (continuous_id.sub continuous_const).continuousOn).subset_connectedComponentIn
    · refine ⟨q.val,mem_connectedComponentIn hq,?_⟩
      change q.val-v=p.val
      rw [hqp,add_sub_cancel_right]
    · rintro x ⟨y,hy,rfl⟩
      have hyC := htarget y hy
      have hyreg := connectedComponentIn_subset (barrierRegion A₁) q.val hy
      refine ⟨hyC.1,?_⟩
      intro h
      have hh := (hbar (y-v) hyC).mp h
      rw [sub_add_cancel] at hh
      exact hyreg.2 hh
  apply Subset.antisymm hforward
  intro y hy
  exact ⟨y-v,hbackward ⟨y,hy,rfl⟩,sub_add_cancel y v⟩

end BarrierSignalSystem
end ComponentTransport

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Amenability_FinitePartitionArrows
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

section SampledPartitionMotion
open Classical Set

theorem generic_component_image {a m : ℕ} (g : polygonFullGroup a m) (i k : Fin m)
    (u : CutRing×CutRing) (C D : Set (ℝ×ℝ)) (hC : C ⊆ squareInterior)
    (he : (fun x => x+(ordinary u.1,ordinary u.2)) '' C=D)
    (haff : ∀p : GenericSquare a,p.val∈C → fullGroupAffineData g i p=(k,u)) :
    g.val '' {x : TrackPoint a m | x.1=i ∧ x.2.val∈C}=
      {x : TrackPoint a m | x.1=k ∧ x.2.val∈D} := by
  apply Set.Subset.antisymm
  · rintro x ⟨⟨j,p⟩,⟨hji,hp⟩,rfl⟩
    dsimp at hji
    subst j
    have hd := haff p hp
    have ht := congrArg Prod.fst hd
    have hu := congrArg Prod.snd hd
    have hv := fullGroupSquareShift_spec g i p
    change fullGroupSquareShift g i p=u at hu
    rw [hu] at hv
    exact ⟨ht,by rw [hv,←he]; exact ⟨p.val,hp,rfl⟩⟩
  · rintro ⟨j,q⟩ ⟨hjk,hq⟩
    dsimp at hjk
    subst j
    obtain ⟨x,hx,hxq⟩ := (Set.mem_image _ _ _).mp (he.symm ▸ hq)
    have hxg : AvoidsCuts a x := by
      have hh := avoidsCuts_translate q.property.2.2 (-u)
      rw [←hxq] at hh
      simpa [map_neg,←Prod.neg_mk] using hh
    let p : GenericSquare a := ⟨x,⟨⟨(hC hx).1.1.le,(hC hx).1.2⟩,
      ⟨(hC hx).2.1.le,(hC hx).2.2⟩,hxg⟩⟩
    have hd := haff p hx
    have ht := congrArg Prod.fst hd
    have hu := congrArg Prod.snd hd
    have hv := fullGroupSquareShift_spec g i p
    change fullGroupSquareShift g i p=u at hu
    rw [hu] at hv
    refine ⟨(i,p),⟨rfl,hx⟩,?_⟩
    exact Prod.ext ht (Subtype.ext (hv.trans hxq))

namespace BarrierMenu
variable {a m : ℕ} {ha : 0 < a} {F : Finset (polygonFullGroup a m)} (M : BarrierMenu a m ha F)

theorem component_chart {n : ℕ} (hN : 1 ≤ sourceDyadicN n) (hB : M.B ≤ sourceDyadicN n)
    {b : BarrierBits a m ha} (hs : jointFieldSuccess (barrierEightDirections ha) M.signals.eight n b)
    (g : polygonFullGroup a m) (hg : g∈F) (i : Fin m) (p : GenericSquare a) :
    connectedComponentIn (barrierRegion (sampledBarriers ha i (sourceDyadicN n)
      (fun j => M.signals.marks (sourceDyadicN_pos n) j (barrierFirstBits b j))
      (barrierSecondBits b))) p.val ⊆ openSquareChart (barrierChartCuts g i) p := by
  obtain ⟨hs₁,hs₂⟩ := M.signals.eight_success hs
  apply barrier_component_openChart (barrierChartCuts g i) p
    (generic_mem_barrierRegion (sampledBarriers_supported ha i _ _ _) p)
  intro l hl x hx hxc
  have hb := ((M.chart_bound g hg i p l (Finset.mem_union_left _ hl)).1).trans hB
  exact M.signals.central_line_barrier i hN (barrierFirstBits b) (barrierSecondBits b) hs₁ hs₂
    ⟨by linarith,x,hx,hxc⟩ hb x hx hxc

theorem sampledPartition_arrow_oai {n : ℕ} (hN : 1 ≤ sourceDyadicN n)
    (hQ : M.Q < sourceDyadicN n) (hB : M.B ≤ sourceDyadicN n)
    (g : polygonFullGroup a m) (hg : g∈F) (b : BarrierBits a m ha)
    (hs : jointFieldSuccess (barrierEightDirections ha) M.signals.eight n b)
    (hs' : jointFieldSuccess (barrierEightDirections ha) M.signals.eight n (barrierBitsTransport g b)) :
    PartitionArrow (M.signals.sampledPartition n b)
      (M.signals.sampledPartition n (barrierBitsTransport g b)) g := by
  let := barrierLineIndexFintype a (sourceDyadicN_pos n)
  obtain ⟨hs₁,hs₂⟩ := M.signals.eight_success hs
  obtain ⟨hs₁',hs₂'⟩ := M.signals.eight_success hs'
  intro c
  have hc := c.2.property
  change c.2.val∈(sampledPolygonPartition ha c.1 (sourceDyadicN_pos n) _ _).cells at hc
  obtain ⟨p,hpc⟩ := (mem_finiteBarrierPartition _ c.2.val).mp hc
  let k := (g.val (c.1,p)).1
  let q := (g.val (c.1,p)).2
  let u := fullGroupSquareShift g c.1 p
  let B₀ := sampledBarriers ha c.1 (sourceDyadicN n)
    (fun j => M.signals.marks (sourceDyadicN_pos n) j (barrierFirstBits b j)) (barrierSecondBits b)
  let B₁ := sampledBarriers ha k (sourceDyadicN n)
    (fun j => M.signals.marks (sourceDyadicN_pos n) j (barrierFirstBits (barrierBitsTransport g b) j))
    (barrierSecondBits (barrierBitsTransport g b))
  let d₀ : polygonAlgebra a := ⟨barrierComponentCell B₁ q.val,
    barrierComponentCell_polygon (sampledBarriers_supported ha k _ _ _) q.val⟩
  have hd₀ : d₀∈(M.signals.sampledPartition n (barrierBitsTransport g b) k).cells :=
    (mem_finiteBarrierPartition _ d₀).mpr ⟨q,rfl⟩
  let d : PartitionCell (M.signals.sampledPartition n (barrierBitsTransport g b)) := ⟨k,⟨d₀,hd₀⟩⟩
  have hdata : fullGroupAffineData g c.1 p=(k,u) := rfl
  have haff (r : GenericSquare a) (hr : r.val∈connectedComponentIn (barrierRegion B₀) p.val) :
      fullGroupAffineData g c.1 r=(k,u) := by
    exact (squareArrangement_on_openChart (fullGroupAffineData g c.1) (barrierChartCuts g c.1)
      (barrierChartCuts_spec g c.1) p r (M.component_chart hN hB hs g hg c.1 p hr)).trans hdata
  have he := M.signals.component_transport g c.1 k (barrierChartCuts g c.1)
    (barrierChartCuts_spec g c.1) p q u hdata (fullGroupSquareShift_spec g c.1 p)
    M.Q_nonneg (M.shift_bound g hg c.1 p) (M.chart_bound g hg c.1 p)
    hN hQ hB (barrierFirstBits b) (barrierSecondBits b)
    (barrierFirstBits (barrierBitsTransport g b)) (barrierSecondBits (barrierBitsTransport g b))
    hs₁ hs₁' hs₂ hs₂' (barrierBitsTransport_first g b) (barrierBitsTransport_second g b)
  have hcs : partitionCellSet c={x : TrackPoint a m | x.1=c.1 ∧
      x.2.val∈connectedComponentIn (barrierRegion B₀) p.val} := by
    ext x
    change (x.1=c.1 ∧ x.2∈c.2.val.val) ↔ _
    rw [hpc]
    rfl
  refine ⟨d,?_,u,?_⟩
  · rw [hcs]
    exact generic_component_image g c.1 k u _ _
      (fun _ hx => (connectedComponentIn_subset (barrierRegion B₀) p.val hx).1) he haff
  · intro x hx
    rw [hcs] at hx
    have hi := hx.1
    have hd := congrArg Prod.snd (haff x.2 hx.2)
    have hv := fullGroupSquareShift_spec g c.1 x.2
    change fullGroupSquareShift g c.1 x.2=u at hd
    rw [hd] at hv
    have hxpair : x=(c.1,x.2) := Prod.ext hi rfl
    rw [hxpair]
    exact hv

end BarrierMenu
end SampledPartitionMotion

end SimpleAmenable
end
end

end OAI
end

theorem solution : type_of% @OAI.SimpleAmenable.BarrierMenu.sampledPartition_arrow_oai := @OAI.SimpleAmenable.BarrierMenu.sampledPartition_arrow_oai
