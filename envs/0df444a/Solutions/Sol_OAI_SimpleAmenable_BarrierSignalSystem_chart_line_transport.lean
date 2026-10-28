-- Prove2me | solution 1 for OAI.SimpleAmenable.BarrierSignalSystem.chart_line_transport
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T03:55:57.113821+00:00
-- url     : https://prove2.me/submissions/21b3eeb1-6053-4c83-af6e-1644764eba41

import Mathlib
import Definitions.Def_OAIQ65Sa009
import Definitions.Def_OAIQ65Sa010
import Definitions.Def_OAIQ65Sa011

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

section BarrierFlags
open Classical

theorem barrierLinePoint_sub (a : ℕ) (j : Fin 4) (c : CutRing) (s t : ℝ) :
    barrierLinePoint a j c s-barrierLinePoint a j c t=(s-t) • barrierTangent a j := by
  fin_cases j <;> apply Prod.ext <;> simp [barrierLinePoint,barrierTangent] <;> ring

theorem barrierTangent_cut (a : ℕ) (j : Fin 4) : cutForm a j (barrierTangent a j)=0 := by
  fin_cases j <;> simp [barrierTangent,cutForm]

end BarrierFlags

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

theorem barrierLinePoint_continuous (a : ℕ) (j : Fin 4) (c : CutRing) :
    Continuous (barrierLinePoint a j c) := by
  change Continuous (fun t => barrierLinePoint a j c t)
  fin_cases j <;> simp only [barrierLinePoint] <;> fun_prop

end BarrierAlgorithm

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

end FullGroupAffineData

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

theorem mem_marks_iff {m : ℕ} {N : ℝ} (hN : 0 < N) (j : Fin 4)
    (b : FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j) → Bool)
    (hs : signalSuccess (flagMeanSignal S.first.signal N) b) (z) :
    z ∈ S.marks hN j b ↔ b z=true :=
  mem_finiteFirstMarks_iff (commonVertexDenominator_pos ha) hN S.R₁_pos S.first.signal b S.first_neg hs z

theorem intersection_first_true {m : ℕ} {N : ℝ} (hN : 1 ≤ N) {i j : Fin 4} (hij : i ≠ j)
    {c d : CutRing} (hc : |conjugate c| ≤ 4*N+Q) (hd : |conjugate d| ≤ B)
    (z : FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha i))
    (hz : cutForm a i (barrierSitePoint z)=ordinary c)
    (hzd : cutForm a j (barrierSitePoint z)=ordinary d)
    (b : FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha i) → Bool)
    (hs : signalSuccess (flagMeanSignal S.first.signal N) b) : b z=true := by
  apply (hs z).1
  rw [flagMeanSignal,S.first_pos]
  · norm_num
  · rw [norm_scaledSiteConjugate (by linarith : 0 < N),div_le_iff₀ (by linarith : 0 < N)]
    exact S.intersection_core N hN i j hij c d hc hd _
      (conjugateLineForm_site (commonVertexDenominator_pos ha) z i c hz)
      (conjugateLineForm_site (commonVertexDenominator_pos ha) z j d hzd)

end BarrierSignalSystem
end BarrierSignalSystem

section SubdivisionCovariance
open Classical Set

theorem consecutiveSubdivision_local {E : Finset ℝ} {L U x s t : ℝ}
    (hL : L ∈ E) (hU : U ∈ E) (hx : x ∈ Ioo L U)
    (hst : ConsecutiveSubdivision E s t) (hxi : x ∈ Icc s t) : L ≤ s ∧ t ≤ U := by
  constructor
  · by_contra h
    have hh := hst.2.2.2 L hL (lt_of_not_ge h)
    have hlx := hx.1
    have hxt := hxi.2
    linarith
  · exact hst.2.2.2 U hU (lt_of_le_of_lt hxi.1 hx.2)

theorem consecutiveSubdivision_translate {E F : Finset ℝ} {L U s t d : ℝ}
    (hE : ∀r ∈ Icc L U,r ∈ E ↔ r+d ∈ F) (hs : L ≤ s) (ht : t ≤ U)
    (hst : ConsecutiveSubdivision E s t) : ConsecutiveSubdivision F (s+d) (t+d) := by
  have hsU : s ≤ U := hst.2.2.1.le.trans ht
  have hLt : L ≤ t := hs.trans hst.2.2.1.le
  refine ⟨(hE s ⟨hs,hsU⟩).mp hst.1,(hE t ⟨hLt,ht⟩).mp hst.2.1,
    by linarith [hst.2.2.1],?_⟩
  intro r hr hsr
  by_contra htr
  have hrU : r-d ≤ U := by linarith
  have hLr : L ≤ r-d := by linarith
  have hrE : r-d ∈ E := (hE (r-d) ⟨hLr,hrU⟩).mpr (by simpa using hr)
  have hh := hst.2.2.2 (r-d) hrE (by linarith)
  linarith

theorem subdivisionBarrier_translate_iff {E F : Finset ℝ} {b c : ℝ → Bool}
    {L U d : ℝ} (hL : L ∈ E) (hU : U ∈ E)
    (hFL : L+d ∈ F) (hFU : U+d ∈ F)
    (hE : ∀r ∈ Icc L U,r ∈ E ↔ r+d ∈ F)
    (hb : ∀r ∈ E,r ∈ Ico L U → b r=c (r+d)) {x : ℝ} (hx : x ∈ Ioo L U) :
    x ∈ subdivisionBarrier E b ↔ x+d ∈ subdivisionBarrier F c := by
  constructor
  · rintro ⟨s,t,hst,hbs,hxi⟩
    obtain ⟨hs,ht⟩ := consecutiveSubdivision_local hL hU hx hst hxi
    refine ⟨s+d,t+d,consecutiveSubdivision_translate hE hs ht hst,?_,?_⟩
    · rw [←hb s hst.1 ⟨hs,lt_of_lt_of_le hst.2.2.1 ht⟩]
      exact hbs
    · exact ⟨by linarith [hxi.1],by linarith [hxi.2]⟩
  · rintro ⟨s,t,hst,hcs,hxi⟩
    have hx' : x+d ∈ Ioo (L+d) (U+d) := ⟨by linarith [hx.1],by linarith [hx.2]⟩
    obtain ⟨hs,ht⟩ := consecutiveSubdivision_local hFL hFU hx' hst hxi
    have hFinv : ∀r ∈ Icc (L+d) (U+d),r ∈ F ↔ r+(-d) ∈ E := by
      intro r hr
      have hr' : r-d ∈ Icc L U := ⟨by linarith [hr.1],by linarith [hr.2]⟩
      simpa [sub_eq_add_neg,add_assoc] using (hE (r-d) hr').symm
    have hst' := consecutiveSubdivision_translate hFinv hs ht hst
    refine ⟨s+(-d),t+(-d),hst',?_,?_⟩
    · rw [hb _ hst'.1 ⟨by linarith,by linarith [hst.2.2.1]⟩]
      simpa using hcs
    · exact ⟨by linarith [hxi.1],by linarith [hxi.2]⟩

end SubdivisionCovariance

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Amenability_BarrierChartRefinement
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

section BarrierCrossings
open Classical Set

theorem barrierIntersection_lattice {a : ℕ} (ha : 0 < a) {i j : Fin 4} (hij : i ≠ j)
    {c d : CutRing} {p : ℝ×ℝ} (hi : cutForm a i p=ordinary c)
    (hj : cutForm a j p=ordinary d) : InFlagLattice (commonVertexDenominator a) p := by
  obtain ⟨u,v,hu,hv⟩ := all_intersections_common_denominator ha i j hij c d p hi hj
  have hD : (commonVertexDenominator a : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (commonVertexDenominator_pos ha)
  refine ⟨(u,v),?_⟩
  apply Prod.ext  <;> simp only [scaledOrdinary,hu,hv]  <;> field_simp

namespace BarrierSignalSystem
variable {a : ℕ} {ha : 0 < a} {Q B : ℝ} (S : BarrierSignalSystem a ha Q B)

theorem crossing_in_subdivision {m : ℕ} (i : Fin m) {N : ℝ} (hN : 1 ≤ N)
    {j k : Fin 4} (hjk : j ≠ k) {c d : CutRing} (hc : c ∈ barrierCandidate a j N)
    (hcQ : |conjugate c| ≤ 4*N+Q) (hd : |conjugate d| ≤ B)
    (b : FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j) → Bool)
    (hs : signalSuccess (flagMeanSignal S.first.signal N) b)
    {t : ℝ} (ht : t ∈ Icc (barrierLineLower a j c) (barrierLineUpper a j c))
    (hk : cutForm a k (barrierLinePoint a j c t)=ordinary d) :
    t ∈ barrierSubdivision ha i j c (S.marks (N:=N) (lt_of_lt_of_le zero_lt_one hN) j b) := by
  by_cases hL : t=barrierLineLower a j c
  · simp [barrierSubdivision,hL]
  by_cases hU : t=barrierLineUpper a j c
  · simp [barrierSubdivision,hU]
  have ht' : t ∈ Ioo (barrierLineLower a j c) (barrierLineUpper a j c) :=
    ⟨lt_of_le_of_ne ht.1 (Ne.symm hL),lt_of_le_of_ne ht.2 hU⟩
  have hp := (barrierLinePoint_interior_iff hc t).mpr ht'
  let z := barrierInteriorSite ha i j hp
    (barrierIntersection_lattice ha hjk (cutForm_barrierLinePoint a j c t) hk)
  have hzpoint : barrierSitePoint z=barrierLinePoint a j c t := rfl
  have hzt : z.val.1=i := rfl
  have hzline : cutForm a j (barrierSitePoint z)=ordinary c := cutForm_barrierLinePoint a j c t
  have hzbit := S.intersection_first_true hN hjk hcQ hd z hzline hk b hs
  have hzmem := (S.mem_marks_iff (lt_of_lt_of_le zero_lt_one hN) j b hs z).mpr hzbit
  apply Finset.mem_union_right
  apply Finset.mem_image.mpr
  refine ⟨z,Finset.mem_filter.mpr ⟨hzmem,hzt,hp,hzline⟩,?_⟩
  exact barrierLineParameter_point a j c t

end BarrierSignalSystem

theorem barrierLineParameter_add (j : Fin 4) (p q : ℝ×ℝ) :
    barrierLineParameter j (p+q)=barrierLineParameter j p+barrierLineParameter j q := by
  fin_cases j  <;> simp [barrierLineParameter]

theorem barrierLinePoint_translate (a : ℕ) (j : Fin 4) (c : CutRing)
    (u : CutRing×CutRing) (t : ℝ) :
    barrierLinePoint a j (c+integralCutForm a j u)
      (t+barrierLineParameter j (ordinary u.1,ordinary u.2))=
    barrierLinePoint a j c t+(ordinary u.1,ordinary u.2) := by
  have hp : cutForm a j (barrierLinePoint a j c t+(ordinary u.1,ordinary u.2)) =
      ordinary (c+integralCutForm a j u) := by
    rw [cutForm_add,cutForm_barrierLinePoint,cutForm_ordinary,map_add]
  have hparam : barrierLineParameter j
      (barrierLinePoint a j c t+(ordinary u.1,ordinary u.2)) =
      t+barrierLineParameter j (ordinary u.1,ordinary u.2) := by
    rw [barrierLineParameter_add,barrierLineParameter_point]
  rw [←hparam]
  exact barrierLinePoint_parameter hp

end BarrierCrossings

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Amenability_BarrierStartGerm
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

theorem barrier_cut_difference (a : ℕ) (j k : Fin 4) (c : CutRing) (s t : ℝ) :
    cutForm a k (barrierLinePoint a j c t)=cutForm a k (barrierLinePoint a j c s)+
      (t-s)*cutForm a k (barrierTangent a j) := by
  have hh := barrierLinePoint_sub a j c t s
  have hp : barrierLinePoint a j c t=barrierLinePoint a j c s+(t-s) • barrierTangent a j := by
    exact (sub_eq_iff_eq_add.mp hh).trans (add_comm _ _)
  rw [hp,cutForm_add,cutForm_smul]

theorem barrier_start_cut_sign {a : ℕ} (ha : 0 < a) (j k : Fin 4) (c d : CutRing)
    {L U s x : ℝ} (hs : s ∈ Ico L U) (hx : x ∈ Ioo L U)
    (hn : ∀r ∈ Ioo L U,cutForm a k (barrierLinePoint a j c r) ≠ ordinary d) :
    (if cutForm a k (barrierLinePoint a j c s)=ordinary d then
      cutForm a k (barrierFlagDirection ha j) < 0 else
      cutForm a k (barrierLinePoint a j c s) < ordinary d) ↔
      cutForm a k (barrierLinePoint a j c x) < ordinary d := by
  let t := (s+U)/2
  have hst : s < t := by dsimp [t]; linarith [hs.2]
  have ht : t ∈ Ioo L U := by dsimp [t]; constructor <;> linarith [hs.1,hs.2]
  let f := fun r => cutForm a k (barrierLinePoint a j c r)-ordinary d
  have hf : Continuous f := ((cutForm_continuous a k).comp (barrierLinePoint_continuous a j c)).sub continuous_const
  have hnon : ∀r ∈ Ioo L U,f r ≠ 0 := fun r hr => sub_ne_zero.mpr (hn r hr)
  have htx : f t < 0 ↔ f x < 0 := continuous_nonzero_sign isPreconnected_Ioo hf.continuousOn hnon ht hx
  have hdif := barrier_cut_difference a j k c s t
  by_cases he : cutForm a k (barrierLinePoint a j c s)=ordinary d
  · have hB : cutForm a k (barrierTangent a j) ≠ 0 := by
      intro hh
      apply hn t ht
      rw [he,hh,mul_zero,add_zero] at hdif
      exact hdif
    have hflag := (barrierFlagDirection_spec ha j).2.2.2 k
    rw [ite_eq_right hB] at hflag
    rw [ite_eq_left he,hflag]
    have heq : f t=(t-s)*cutForm a k (barrierTangent a j) := by dsimp [f]; linarith
    have hsign : f t < 0 ↔ cutForm a k (barrierTangent a j) < 0 := by
      rw [heq,mul_neg_iff]
      have hts : 0 < t-s := sub_pos.mpr hst
      simp [hts,not_lt_of_gt hts]
    exact (hsign.symm.trans htx).trans (sub_lt_zero (a:=cutForm a k (barrierLinePoint a j c x)) (b:=ordinary d))
  · rw [ite_eq_right he]
    have hseg : ∀r ∈ Icc s t,f r ≠ 0 := by
      intro r hr
      by_cases hrs : r=s
      · subst r
        exact sub_ne_zero.mpr he
      · exact hnon r ⟨lt_of_le_of_lt hs.1 (lt_of_le_of_ne hr.1 (Ne.symm hrs)),hr.2.trans_lt ht.2⟩
    have hsign := continuous_nonzero_sign isPreconnected_Icc hf.continuousOn hseg
      (left_mem_Icc.mpr hst.le) (right_mem_Icc.mpr hst.le)
    simpa only [f,sub_lt_zero] using hsign.trans htx

theorem flagValue_of_arrangement_signs {a : ℕ} {v : ℝ×ℝ} {K : Type*}
    (f : GenericSquare a → K) (T : Finset PlaneCut)
    (hT : ∀p q,(∀l ∈ T,squareSign l p=squareSign l q) → f p=f q)
    (z : SquareFlag a v) (p : GenericSquare a)
    (hs : ∀l ∈ T,(if cutForm a l.1 z.val=ordinary l.2 then cutForm a l.1 v < 0
      else cutForm a l.1 z.val < ordinary l.2) ↔ cutForm a l.1 p.val < ordinary l.2) :
    flagValue f ⟨T,hT⟩ z=f p := by
  apply flagValue_eq
  refine ⟨arrangementNeighborhood a T z.val,arrangementNeighborhood_open a T z.val,
    self_mem_arrangementNeighborhood a T z.val,?_⟩
  intro q hq hqv
  apply hT q p
  intro l hl
  have hh := planeSign_neighborhood (p:=⟨q.val,q.property.2.2⟩) hq hqv hl
  change squareSign l q=_ at hh
  rw [hh]
  exact decide_eq_decide.mpr (hs l hl)

theorem flagAffineData_barrier_chart {a m : ℕ} (ha : 0 < a) (g : polygonFullGroup a m)
    (i : Fin m) (j : Fin 4) (c : CutRing) (T : Finset PlaneCut)
    (hT : ∀p q,(∀l ∈ T,squareSign l p=squareSign l q) →
      fullGroupAffineData g i p=fullGroupAffineData g i q)
    (p : GenericSquare a) {L U s : ℝ} (hLU : L < U) (hs : s ∈ Ico L U)
    (hchart : ∀l ∈ T,∀r ∈ Ioo L U,
      cutForm a l.1 (barrierLinePoint a j c r) ≠ ordinary l.2 ∧
      (cutForm a l.1 (barrierLinePoint a j c r) < ordinary l.2 ↔
        cutForm a l.1 p.val < ordinary l.2))
    (z : SquareFlag a (barrierFlagDirection ha j)) (hz : z.val=barrierLinePoint a j c s) :
    flagAffineData g i z=fullGroupAffineData g i p := by
  let x := (L+U)/2
  have hx : x ∈ Ioo L U := by dsimp [x]; constructor <;> linarith
  apply flagValue_of_arrangement_signs (fullGroupAffineData g i) T hT z p
  intro l hl
  rw [hz]
  exact (barrier_start_cut_sign ha j l.1 c l.2 hs hx
    (fun r hr => (hchart l hl r hr).1)).trans (hchart l hl x hx).2

end BarrierStartGerm

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Amenability_LocalBarrierTransport
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
section LocalBarrierTransport
open Classical Set

theorem inFlagLattice_add {D : ℕ} (hD : 0 < D) {p : ℝ×ℝ}
    (hp : InFlagLattice D p) (u : CutRing×CutRing) :
    InFlagLattice D (p+(ordinary u.1,ordinary u.2)) := by
  obtain ⟨v,rfl⟩ := hp
  have hD' : (D : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hD
  refine ⟨(v.1+D*u.1,v.2+D*u.2),?_⟩
  apply Prod.ext <;> simp only [scaledOrdinary,map_add,map_mul,map_natCast,Prod.fst_add,Prod.snd_add] <;> field_simp

theorem mem_barrierSubdivision_interior {a m : ℕ} (ha : 0 < a) (i : Fin m)
    {j : Fin 4} {c : CutRing} {N : ℝ} (hc : c ∈ barrierCandidate a j N)
    (M : Finset (FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j)))
    {s : ℝ} (hp : barrierLinePoint a j c s ∈ squareInterior) :
    s ∈ barrierSubdivision ha i j c M ↔
      ∃z ∈ M,z.val.1=i ∧ barrierSitePoint z=barrierLinePoint a j c s := by
  have hs := (barrierLinePoint_interior_iff hc s).mp hp
  simp only [barrierSubdivision,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
  have hlo : s ≠ barrierLineLower a j c := ne_of_gt hs.1
  have hhi : s ≠ barrierLineUpper a j c := ne_of_lt hs.2
  simp only [hlo,hhi,false_or]
  constructor
  · intro h
    obtain ⟨z,hz,he⟩ := Finset.mem_image.mp h
    obtain ⟨hzM,hzi,hzp,hzc⟩ := Finset.mem_filter.mp hz
    refine ⟨z,hzM,hzi,?_⟩
    rw [←he,barrierLinePoint_parameter hzc]
  · rintro ⟨z,hz,hzi,hzp⟩
    apply Finset.mem_image.mpr
    refine ⟨z,Finset.mem_filter.mpr ⟨hz,hzi,?_,?_⟩,?_⟩
    · rwa [hzp]
    · rw [hzp,cutForm_barrierLinePoint]
    · rw [hzp,barrierLineParameter_point]

theorem barrierSubdivision_site_before_upper {a m : ℕ} (ha : 0 < a) (i : Fin m)
    {j : Fin 4} {c : CutRing} {N : ℝ} (hc : c ∈ barrierCandidate a j N)
    (M : Finset (FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j)))
    {s : ℝ} (hs : s ∈ barrierSubdivision ha i j c M)
    (hsU : s < barrierLineUpper a j c) :
    ∃z : FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j),
      z.val.1=i ∧ barrierSitePoint z=barrierLinePoint a j c s := by
  simp only [barrierSubdivision,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hs
  rcases hs with (rfl | rfl) | hs
  · exact ⟨barrierIncomingSite ha i hc,rfl,rfl⟩
  · exact False.elim (lt_irrefl _ hsU)
  · obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨_,hzi,_,hzline⟩ := Finset.mem_filter.mp hz
    exact ⟨z,hzi,(barrierLinePoint_parameter hzline).symm⟩

namespace BarrierSignalSystem
variable {a : ℕ} {ha : 0 < a} {Q B : ℝ} (S : BarrierSignalSystem a ha Q B)

theorem local_line_transport {m : ℕ} (g : polygonFullGroup a m) (i k : Fin m)
    {N : ℝ} (hN : 0 < N) (j : Fin 4) (c : CutRing) (u : CutRing×CutRing)
    (hc : c ∈ barrierCandidate a j N)
    (hc' : c+integralCutForm a j u ∈ barrierCandidate a j N)
    (b₁ b₂ b₁' b₂' : FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j) → Bool)
    (hs : signalSuccess (flagMeanSignal S.first.signal N) b₁)
    (hs' : signalSuccess (flagMeanSignal S.first.signal N) b₁')
    (hb₁ : ∀z,b₁' (flagSiteAction (commonVertexDenominator_pos ha) g z)=b₁ z)
    (hb₂ : ∀z,b₂' (flagSiteAction (commonVertexDenominator_pos ha) g z)=b₂ z)
    (L U : ℝ)
    (hinside : ∀r ∈ Ioo L U,barrierLinePoint a j c r ∈ squareInterior ∧
      barrierLinePoint a j (c+integralCutForm a j u)
        (r+barrierLineParameter j (ordinary u.1,ordinary u.2)) ∈ squareInterior)
    (hU : U ≤ barrierLineUpper a j c)
    (hL : L ∈ barrierSubdivision ha i j c (S.marks hN j b₁))
    (hT : U ∈ barrierSubdivision ha i j c (S.marks hN j b₁))
    (hL' : L+barrierLineParameter j (ordinary u.1,ordinary u.2) ∈
      barrierSubdivision ha k j (c+integralCutForm a j u) (S.marks hN j b₁'))
    (hT' : U+barrierLineParameter j (ordinary u.1,ordinary u.2) ∈
      barrierSubdivision ha k j (c+integralCutForm a j u) (S.marks hN j b₁'))
    (hchart : ∀(r : ℝ),r ∈ Ico L U →
      ∀z : FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j),
      z.val.1=i → barrierSitePoint z=barrierLinePoint a j c r →
      flagAffineData g i z.val.2=(k,u))
    {x : ℝ} (hx : x ∈ Ioo L U) :
    x ∈ subdivisionBarrier (barrierSubdivision ha i j c (S.marks hN j b₁))
        (barrierActivation ha i j c b₂) ↔
    x+barrierLineParameter j (ordinary u.1,ordinary u.2) ∈
      subdivisionBarrier (barrierSubdivision ha k j (c+integralCutForm a j u) (S.marks hN j b₁'))
        (barrierActivation ha k j (c+integralCutForm a j u) b₂') := by
  let d := barrierLineParameter j (ordinary u.1,ordinary u.2)
  have haction (r : ℝ) (hr : r ∈ Ico L U)
      (z : FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j))
      (hzi : z.val.1=i) (hzp : barrierSitePoint z=barrierLinePoint a j c r) :
      (flagSiteAction (commonVertexDenominator_pos ha) g z).val.1=k ∧
      barrierSitePoint (flagSiteAction (commonVertexDenominator_pos ha) g z)=
        barrierLinePoint a j (c+integralCutForm a j u) (r+d) := by
    have hh := flagAffineData_action g z.val
    rw [hzi,hchart r hr z hzi hzp] at hh
    refine ⟨hh.1,?_⟩
    change (flagAction g z.val).2.val=_
    rw [hh.2]
    change barrierSitePoint z+_= _
    rw [hzp,barrierLinePoint_translate]
  apply subdivisionBarrier_translate_iff hL hT hL' hT' _ _ hx
  · intro r hr
    by_cases heL : r=L
    · subst r
      exact iff_of_true hL hL'
    by_cases heU : r=U
    · subst r
      exact iff_of_true hT hT'
    have hr' : r ∈ Ioo L U := ⟨lt_of_le_of_ne hr.1 (Ne.symm heL),lt_of_le_of_ne hr.2 heU⟩
    obtain ⟨hp,hp'⟩ := hinside r hr'
    rw [mem_barrierSubdivision_interior ha i hc _ hp,
      mem_barrierSubdivision_interior ha k hc' _ hp']
    constructor
    · rintro ⟨z,hz,hzi,hzp⟩
      obtain ⟨hwi,hwp⟩ := haction r ⟨hr'.1.le,hr'.2⟩ z hzi hzp
      refine ⟨flagSiteAction (commonVertexDenominator_pos ha) g z,?_,hwi,hwp⟩
      rw [S.mem_marks_iff hN j b₁' hs',hb₁]
      exact (S.mem_marks_iff hN j b₁ hs z).mp hz
    · rintro ⟨w,hw,hwk,hwp⟩
      have hlat : InFlagLattice (commonVertexDenominator a) (barrierLinePoint a j c r) := by
        have hh := inFlagLattice_add (commonVertexDenominator_pos ha) w.property (-u)
        change InFlagLattice _ (barrierSitePoint w+_) at hh
        rw [hwp,barrierLinePoint_translate] at hh
        simpa only [Prod.fst_neg,Prod.snd_neg,map_neg,←Prod.neg_mk,add_neg_cancel_right] using hh
      let z := barrierInteriorSite ha i j hp hlat
      obtain ⟨hwi,hwp'⟩ := haction r ⟨hr'.1.le,hr'.2⟩ z rfl rfl
      have hew : flagSiteAction (commonVertexDenominator_pos ha) g z=w :=
        flagSite_eq_of_track_point (hwi.trans hwk.symm) (hwp'.trans hwp.symm)
      refine ⟨z,?_,rfl,rfl⟩
      rw [S.mem_marks_iff hN j b₁ hs,←hb₁,hew]
      exact (S.mem_marks_iff hN j b₁' hs' w).mp hw
  · intro r hr hrLU
    obtain ⟨z,hzi,hzp⟩ := barrierSubdivision_site_before_upper ha i hc _ hr (hrLU.2.trans_le hU)
    obtain ⟨hwi,hwp⟩ := haction r hrLU z hzi hzp
    rw [barrierActivation_at_site ha i j c b₂ r z hzi hzp,
      barrierActivation_at_site ha k j (c+integralCutForm a j u) b₂' _ _ hwi hwp,hb₂]

end BarrierSignalSystem
end LocalBarrierTransport

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

section ChartLineIntervals
open Classical Set

theorem chartCrossingParameter_spec (a : ℕ) (j : Fin 4) (c : CutRing) (l : PlaneCut)
    (hl : cutForm a l.1 (barrierTangent a j) ≠ 0) :
    cutForm a l.1 (barrierLinePoint a j c (chartCrossingParameter a j c l))=ordinary l.2 := by
  rw [barrier_cut_difference a j l.1 c 0]
  simp only [sub_zero,chartCrossingParameter,div_mul_cancel₀ _ hl]
  ring

theorem chartCrossingParameter_unique (a : ℕ) (j : Fin 4) (c : CutRing) (l : PlaneCut)
    (hl : cutForm a l.1 (barrierTangent a j) ≠ 0) {r : ℝ}
    (hr : cutForm a l.1 (barrierLinePoint a j c r)=ordinary l.2) :
    r=chartCrossingParameter a j c l := by
  have hd := barrier_cut_difference a j l.1 c 0 r
  dsimp [chartCrossingParameter]
  apply (eq_div_iff hl).mpr
  simpa only [sub_zero] using (eq_sub_iff_add_eq.mpr (by linarith :
    r*cutForm a l.1 (barrierTangent a j)+cutForm a l.1 (barrierLinePoint a j c 0)=ordinary l.2))

theorem openSquareChart_line_interval {a : ℕ} (T : Finset PlaneCut) (p : GenericSquare a)
    {j : Fin 4} {c : CutRing} {N x : ℝ} (hc : c ∈ barrierCandidate a j N)
    (hx : barrierLinePoint a j c x ∈ openSquareChart T p) :
    ∃L U : ℝ,x ∈ Ioo L U ∧
      L ∈ Icc (barrierLineLower a j c) (barrierLineUpper a j c) ∧
      U ∈ Icc (barrierLineLower a j c) (barrierLineUpper a j c) ∧
      (∀r ∈ Ioo L U,barrierLinePoint a j c r ∈ openSquareChart T p) ∧
      (∀r ∈ ({L,U} : Finset ℝ),r=barrierLineLower a j c ∨ r=barrierLineUpper a j c ∨
        ∃l ∈ T,j ≠ l.1 ∧ cutForm a l.1 (barrierLinePoint a j c r)=ordinary l.2) := by
  let lo := barrierLineLower a j c
  let hi := barrierLineUpper a j c
  let R := T.filter (fun l => cutForm a l.1 (barrierTangent a j) ≠ 0)
  let E := (({lo,hi} : Finset ℝ) ∪ R.image (chartCrossingParameter a j c)).filter (fun r => r ∈ Icc lo hi)
  have hxin : x ∈ Ioo lo hi := (barrierLinePoint_interior_iff hc x).mp hx.1
  have hgap : lo ≤ hi := hxin.1.le.trans hxin.2.le
  have hlo : lo ∈ E := by simp [E,hgap]
  have hhi : hi ∈ E := by simp [E,hgap]
  have hxE : x ∉ E := by
    intro he
    have hh := (Finset.mem_filter.mp he).1
    rcases Finset.mem_union.mp hh with hh | hh
    · simp only [Finset.mem_insert,Finset.mem_singleton] at hh
      rcases hh with hh | hh
      · exact (ne_of_gt hxin.1) hh
      · exact (ne_of_lt hxin.2) hh
    · obtain ⟨l,hl,he⟩ := Finset.mem_image.mp hh
      obtain ⟨hlT,hlne⟩ := Finset.mem_filter.mp hl
      exact (openSquareChart_signs hx hlT).1 (he ▸ chartCrossingParameter_spec a j c l hlne)
  obtain ⟨L,U,hLU,hxLU⟩ := exists_consecutiveSubdivision E hlo hhi ⟨hxin.1.le,hxin.2⟩
  have hxL : L < x := lt_of_le_of_ne hxLU.1 (fun h => hxE (h ▸ hLU.1))
  have hxU : x < U := lt_of_le_of_ne hxLU.2 (fun h => hxE (h.symm ▸ hLU.2.1))
  have hL := (Finset.mem_filter.mp hLU.1).2
  have hU := (Finset.mem_filter.mp hLU.2.1).2
  have hn (l : PlaneCut) (hl : l ∈ T) (r : ℝ) (hr : r ∈ Ioo L U) :
      cutForm a l.1 (barrierLinePoint a j c r) ≠ ordinary l.2 := by
    intro he
    by_cases hzero : cutForm a l.1 (barrierTangent a j)=0
    · have hh := barrier_cut_difference a j l.1 c r x
      rw [hzero,mul_zero,add_zero,he] at hh
      exact (openSquareChart_signs hx hl).1 hh
    · have hre : r ∈ E := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_union_right _ (Finset.mem_image.mpr ⟨l,Finset.mem_filter.mpr ⟨hl,hzero⟩,?_⟩),
          ⟨hL.1.trans hr.1.le,hr.2.le.trans hU.2⟩⟩
        exact (chartCrossingParameter_unique a j c l hzero he).symm
      exact not_le_of_gt hr.2 (hLU.2.2.2 r hre hr.1)
  refine ⟨L,U,⟨hxL,hxU⟩,hL,hU,?_,?_⟩
  · intro r hr
    refine ⟨(barrierLinePoint_interior_iff hc r).mpr ⟨hL.1.trans_lt hr.1,hr.2.trans_le hU.2⟩,?_⟩
    intro l
    have hs := continuous_nonzero_sign isPreconnected_Ioo
      (((cutForm_continuous a l.val.1).comp (barrierLinePoint_continuous a j c)).sub continuous_const).continuousOn
      (fun t ht => sub_ne_zero.mpr (hn l.val l.property t ht)) hr ⟨hxL,hxU⟩
    have hsg : (cutForm a l.val.1 (barrierLinePoint a j c r) < ordinary l.val.2 ↔
      cutForm a l.val.1 (barrierLinePoint a j c x) < ordinary l.val.2) := by simpa only [Pi.sub_apply,Function.comp_apply,sub_lt_zero] using hs
    have hh := hx.2 l
    by_cases hl : squareSign l.val p=true
    · simpa [hl] using hsg.mpr (by simpa [hl] using hh)
    · have hnot : ¬cutForm a l.val.1 (barrierLinePoint a j c r) < ordinary l.val.2 :=
        fun h => not_lt_of_gt (by simpa [hl] using hh) (hsg.mp h)
      simpa [hl] using lt_of_le_of_ne (le_of_not_gt hnot) (hn l.val l.property r hr).symm
  · intro r hr
    have hre : r ∈ E := by
      simp only [Finset.mem_insert,Finset.mem_singleton] at hr
      rcases hr with rfl|rfl
      · exact hLU.1
      · exact hLU.2.1
    rcases Finset.mem_union.mp (Finset.mem_filter.mp hre).1 with he | he
    · simp only [Finset.mem_insert,Finset.mem_singleton] at he
      exact he.elim Or.inl (fun h => Or.inr (Or.inl h))
    · obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp he
      obtain ⟨hlT,hlne⟩ := Finset.mem_filter.mp hl
      refine Or.inr (Or.inr ⟨l,hlT,?_,chartCrossingParameter_spec a j c l hlne⟩)
      intro he
      exact hlne (he ▸ barrierTangent_cut a j)

end ChartLineIntervals

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_ChartBoundaryEndpoints
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
section ChartBoundaryEndpoints
open Classical Set

theorem interval_endpoints_closed {X : Type*} [TopologicalSpace X] {f : ℝ → X}
    (hf : Continuous f) {A : Set X} (hA : IsClosed A) {L U : ℝ} (hLU : L < U)
    (h : ∀r ∈ Ioo L U,f r ∈ A) : f L ∈ A ∧ f U ∈ A := by
  have hs : closure (Ioo L U) ⊆ f ⁻¹' A := (hA.preimage hf).closure_subset_iff.mpr h
  rw [closure_Ioo hLU.ne] at hs
  exact ⟨hs (left_mem_Icc.mpr hLU.le),hs (right_mem_Icc.mpr hLU.le)⟩

theorem squareBoundaryCuts_of_closed_not_open {a : ℕ} {p : ℝ×ℝ}
    (hp : p ∈ Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1) (hn : p ∉ squareInterior) :
    ∃l ∈ squareBoundaryCuts,cutForm a l.1 p=ordinary l.2 := by
  by_cases hx₀ : p.1=0
  · exact ⟨(0,0),by simp [squareBoundaryCuts],by simp [cutForm,hx₀]⟩
  by_cases hx₁ : p.1=1
  · exact ⟨(0,1),by simp [squareBoundaryCuts],by simp [cutForm,hx₁]⟩
  by_cases hy₀ : p.2=0
  · exact ⟨(1,0),by simp [squareBoundaryCuts],by simp [cutForm,hy₀]⟩
  by_cases hy₁ : p.2=1
  · exact ⟨(1,1),by simp [squareBoundaryCuts],by simp [cutForm,hy₁]⟩
  exact False.elim (hn ⟨⟨lt_of_le_of_ne hp.1.1 (Ne.symm hx₀),lt_of_le_of_ne hp.1.2 hx₁⟩,
    ⟨lt_of_le_of_ne hp.2.1 (Ne.symm hy₀),lt_of_le_of_ne hp.2.2 hy₁⟩⟩)

theorem squareBoundaryCuts_nonzero_on_interior {a : ℕ} {p : ℝ×ℝ}
    (hp : p ∈ squareInterior) {l : PlaneCut} (hl : l ∈ squareBoundaryCuts) :
    cutForm a l.1 p ≠ ordinary l.2 := by
  simp only [squareBoundaryCuts,Finset.mem_insert,Finset.mem_singleton] at hl
  rcases hl with rfl|rfl|rfl|rfl
  · simpa [cutForm] using ne_of_gt hp.1.1
  · simpa [cutForm] using ne_of_lt hp.1.2
  · simpa [cutForm] using ne_of_gt hp.2.1
  · simpa [cutForm] using ne_of_lt hp.2.2

theorem barrier_geometric_endpoint_cut {a : ℕ} {j : Fin 4} {c : CutRing} {N r : ℝ}
    (hc : c ∈ barrierCandidate a j N)
    (hr : r=barrierLineLower a j c ∨ r=barrierLineUpper a j c) :
    ∃l ∈ squareBoundaryCuts,j ≠ l.1 ∧ cutForm a l.1 (barrierLinePoint a j c r)=ordinary l.2 := by
  have hgap := barrierLineLower_lt_upper hc
  have hh := interval_endpoints_closed (barrierLinePoint_continuous a j c)
    (isClosed_Icc.prod isClosed_Icc) hgap
    (fun t ht => let hp := (barrierLinePoint_interior_iff hc t).mpr ht
      show barrierLinePoint a j c t ∈ Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1 from
        ⟨⟨hp.1.1.le,hp.1.2.le⟩,⟨hp.2.1.le,hp.2.2.le⟩⟩)
  have hclosed : barrierLinePoint a j c r ∈ Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1 :=
    hr.elim (fun h => h ▸ hh.1) (fun h => h ▸ hh.2)
  have hn : barrierLinePoint a j c r ∉ squareInterior := by
    rw [barrierLinePoint_interior_iff hc r]
    rcases hr with rfl|rfl <;> simp
  obtain ⟨l,hl,hcut⟩ := squareBoundaryCuts_of_closed_not_open hclosed hn
  refine ⟨l,hl,?_,hcut⟩
  intro he
  obtain ⟨p,hp,hpc⟩ := hc.2
  have hjc := cutForm_barrierLinePoint a j c r
  rw [←he] at hcut
  have hp' := hpc.trans (hjc.symm.trans hcut)
  rw [he] at hp'
  exact squareBoundaryCuts_nonzero_on_interior hp hl hp'

theorem chart_line_endpoints_forced {a : ℕ} (T : Finset PlaneCut) (p : GenericSquare a)
    {j : Fin 4} {c : CutRing} {N x : ℝ} (hc : c ∈ barrierCandidate a j N)
    (hx : barrierLinePoint a j c x ∈ openSquareChart T p) :
    ∃L U : ℝ,x ∈ Ioo L U ∧
      L ∈ Icc (barrierLineLower a j c) (barrierLineUpper a j c) ∧
      U ∈ Icc (barrierLineLower a j c) (barrierLineUpper a j c) ∧
      (∀r ∈ Ioo L U,barrierLinePoint a j c r ∈ openSquareChart T p) ∧
      (∀r ∈ ({L,U} : Finset ℝ),∃l ∈ T ∪ squareBoundaryCuts,j ≠ l.1 ∧
        cutForm a l.1 (barrierLinePoint a j c r)=ordinary l.2) := by
  obtain ⟨L,U,hx,hL,hU,hchart,hend⟩ := openSquareChart_line_interval T p hc hx
  refine ⟨L,U,hx,hL,hU,hchart,?_⟩
  intro r hr
  rcases hend r hr with h | h | h
  · obtain ⟨l,hl,hj,hc⟩ := barrier_geometric_endpoint_cut hc (Or.inl h)
    exact ⟨l,Finset.mem_union_right _ hl,hj,hc⟩
  · obtain ⟨l,hl,hj,hc⟩ := barrier_geometric_endpoint_cut hc (Or.inr h)
    exact ⟨l,Finset.mem_union_right _ hl,hj,hc⟩
  · obtain ⟨l,hl,hj,hc⟩ := h
    exact ⟨l,Finset.mem_union_left _ hl,hj,hc⟩

end ChartBoundaryEndpoints

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
section ChartLineTransport
open Classical Set
namespace BarrierSignalSystem
variable {a : ℕ} {ha : 0 < a} {Q B : ℝ} (S : BarrierSignalSystem a ha Q B)

theorem chart_line_transport_oai {m : ℕ} (g : polygonFullGroup a m) (i k : Fin m)
    (T : Finset PlaneCut)
    (hT : ∀p q,(∀l ∈ T,squareSign l p=squareSign l q) →
      fullGroupAffineData g i p=fullGroupAffineData g i q) (p : GenericSquare a)
    (u : CutRing×CutRing) (hdata : fullGroupAffineData g i p=(k,u))
    (hQ : 0 ≤ Q)
    (hB : ∀l ∈ T ∪ squareBoundaryCuts,|conjugate l.2| ≤ B ∧
      |conjugate (l.2+integralCutForm a l.1 u)| ≤ B)
    {N : ℝ} (hN : 1 ≤ N) (j : Fin 4) (c : CutRing)
    (hc : c ∈ barrierCandidate a j N)
    (hc' : c+integralCutForm a j u ∈ barrierCandidate a j N)
    (b₁ b₂ b₁' b₂' : FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j) → Bool)
    (hs : signalSuccess (flagMeanSignal S.first.signal N) b₁)
    (hs' : signalSuccess (flagMeanSignal S.first.signal N) b₁')
    (hb₁ : ∀z,b₁' (flagSiteAction (commonVertexDenominator_pos ha) g z)=b₁ z)
    (hb₂ : ∀z,b₂' (flagSiteAction (commonVertexDenominator_pos ha) g z)=b₂ z)
    {x : ℝ} (hx : barrierLinePoint a j c x ∈ openSquareChart T p) :
    x ∈ subdivisionBarrier (barrierSubdivision ha i j c
        (S.marks (N:=N) (lt_of_lt_of_le zero_lt_one hN) j b₁)) (barrierActivation ha i j c b₂) ↔
    x+barrierLineParameter j (ordinary u.1,ordinary u.2) ∈
      subdivisionBarrier (barrierSubdivision ha k j (c+integralCutForm a j u)
        (S.marks (N:=N) (lt_of_lt_of_le zero_lt_one hN) j b₁'))
        (barrierActivation ha k j (c+integralCutForm a j u) b₂') := by
  let d := barrierLineParameter j (ordinary u.1,ordinary u.2)
  obtain ⟨L,U,hxLU,hL,hU,hchart,hend⟩ := chart_line_endpoints_forced T p hc hx
  have hLU : L < U := hxLU.1.trans hxLU.2
  have htrans : ∀r ∈ Ioo L U,barrierLinePoint a j (c+integralCutForm a j u) (r+d) ∈ squareInterior := by
    intro r hr
    rw [barrierLinePoint_translate]
    have hh := fullGroupAffineChart_square g i T hT p
    rw [hdata] at hh
    exact hh ⟨barrierLinePoint a j c r,hchart r hr,rfl⟩
  have hbounds := interval_endpoints_closed (continuous_id.add continuous_const)
    isClosed_Icc hLU (fun r hr => let hp := (barrierLinePoint_interior_iff hc' (r+d)).mp (htrans r hr)
      show r+d ∈ Icc (barrierLineLower a j (c+integralCutForm a j u))
        (barrierLineUpper a j (c+integralCutForm a j u)) from ⟨hp.1.le,hp.2.le⟩)
  have hsource (r : ℝ) (hr : r ∈ ({L,U} : Finset ℝ))
      (hrb : r ∈ Icc (barrierLineLower a j c) (barrierLineUpper a j c)) :
      r ∈ barrierSubdivision ha i j c (S.marks (N:=N) (lt_of_lt_of_le zero_lt_one hN) j b₁) := by
    obtain ⟨l,hl,hjl,hzero⟩ := hend r hr
    exact S.crossing_in_subdivision i hN hjl hc (by linarith [hc.1]) (hB l hl).1 b₁ hs hrb hzero
  have htarget (r : ℝ) (hr : r ∈ ({L,U} : Finset ℝ))
      (hrb : r+d ∈ Icc (barrierLineLower a j (c+integralCutForm a j u))
        (barrierLineUpper a j (c+integralCutForm a j u))) :
      r+d ∈ barrierSubdivision ha k j (c+integralCutForm a j u)
        (S.marks (N:=N) (lt_of_lt_of_le zero_lt_one hN) j b₁') := by
    obtain ⟨l,hl,hjl,hzero⟩ := hend r hr
    apply S.crossing_in_subdivision k hN hjl hc' (by linarith [hc'.1]) (hB l hl).2 b₁' hs' hrb
    rw [barrierLinePoint_translate,cutForm_add,hzero,cutForm_ordinary,map_add]
  apply S.local_line_transport g i k (lt_of_lt_of_le zero_lt_one hN) j c u hc hc' b₁ b₂ b₁' b₂'
    hs hs' hb₁ hb₂ L U (fun r hr => ⟨(hchart r hr).1,htrans r hr⟩) hU.2
    (hsource L (by simp) hL) (hsource U (by simp) hU)
    (htarget L (by simp) hbounds.1) (htarget U (by simp) hbounds.2) _ hxLU
  intro r hr z hzi hzp
  exact (flagAffineData_barrier_chart ha g i j c T hT p hLU hr
    (fun l hl r hr => openSquareChart_signs (hchart r hr) hl) z.val.2 hzp).trans hdata

end BarrierSignalSystem
end ChartLineTransport

end SimpleAmenable
end
end

end OAI
end

theorem solution : type_of% @OAI.SimpleAmenable.BarrierSignalSystem.chart_line_transport_oai := @OAI.SimpleAmenable.BarrierSignalSystem.chart_line_transport_oai
