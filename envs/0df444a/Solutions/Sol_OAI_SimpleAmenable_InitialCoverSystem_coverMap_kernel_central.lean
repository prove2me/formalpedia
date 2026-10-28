-- Prove2me | solution 1 for OAI.SimpleAmenable.InitialCoverSystem.coverMap_kernel_central
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T04:43:22.006579+00:00
-- url     : https://prove2.me/submissions/1a0191be-0a2e-4321-8d0f-56d1783adb05

import Mathlib
import Definitions.Def_OAIQ65Sa015

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_SectorControl
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
section ActualSectorControl

variable {E H Q Ω : Type*} [Group E] [Group H] [Group Q] [Group.IsPerfect E]

variable {a : ℕ} {ι : Type*}

namespace InitialCoverSystem
variable {m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M) [Finite ι]

theorem geometricSector_input (I : Finset (Fin (m+1)))
    [Group.IsPerfect (alternatingGroup I)]
    (b : Fin (m+1)) (hb : b ∉ I) (P : ι → Fin 5 × (CutRing × CutRing))
    (h : B.PrimitiveFamilyLaw I b hb P) (i : ι) :
    B.geometricSector I b hb P h (primitiveTests (a := a) (r := r) P i) =
      (B.primitiveCopy I b hb (P i)).comp (universalProjection (alternatingGroup I)) := by
  apply CentralOn.lift_unique (coverMap M (alternatingGenerator a r m hm))
    (copyFamilyEval (B.primitiveFamily I b hb P)).range h
  · rintro x ⟨s,rfl⟩
    exact B.geometricSector_mem I b hb P h _ s
  · rintro x ⟨s,rfl⟩
    rw [copyFamilyEval_range]
    exact (le_iSup (fun z => (B.primitiveFamily I b hb P z).range) (some i))
      ⟨universalProjection (alternatingGroup I) s,rfl⟩
  · rw [B.geometricSector_projection I b hb P h _ (resolved_test _ i)]
    rw [← MonoidHom.comp_assoc,B.primitiveCopy_projection]
    rfl

end InitialCoverSystem
end ActualSectorControl

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_GridPrimitiveInputs
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
section GridPrimitiveInputs
namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M) {ι κ : Type*} [Finite κ]
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem fullGeometricSector_small_input (hlarge : 15 < m+1)
    (P : κ → Fin 5 × (CutRing × CutRing))
    (h : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb P)
    (R : ι → Fin 5 × (CutRing × CutRing)) (k : κ) (i : ι) (he : P k=R i)
    (I : FiveAlphabet (Fin (m+1))) :
    (B.fullGeometricSector hlarge P h (primitiveTests (a := a) (r := r) R i)).comp
      (universalMap (subtypeAlternatingHom I.val)) =
      (B.smallPrimitiveInputs hlarge R I (some i)).comp (universalProjection (alternatingGroup I.val)) := by
  let b := smallAlphabetBalance hlarge I.val (by rw [I.property.2]; omega)
  have hb := smallAlphabetBalance_notMem hlarge I.val (by rw [I.property.2]; omega)
  have hR : primitiveTests (a := a) (r := r) R i=primitiveTests (a := a) (r := r) P k := by
    simp only [primitiveTests,primitiveFamilyTests,he]
  rw [hR,B.fullGeometricSector_inclusion hlarge P h I.val (by rw [I.property.2]) b hb
    (h I.val (by rw [I.property.2]; omega) b hb) _ (resolved_test _ k),B.geometricSector_input]
  change (B.primitiveCopy I.val b hb (P k)).comp _ = (B.primitiveCopy I.val b hb (R i)).comp _
  rw [he]

end InitialCoverSystem
end GridPrimitiveInputs

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_CanonicalSlotStars
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.BankEmbedding.instCoeFunForallPointTrackPoint _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonPlacement.Configuration.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.PolygonPlacement.instCoeFunForallGenericSquareTrackPoint _root_.OAI.SimpleAmenable.PolygonPlacement.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (hlarge : 15 < m+1) (h : B.AllPrimitiveLaws) (hr : 0<ordinary r ∧ ordinary r<1/2)

namespace SlotRouting
variable {B hlarge h hr}

theorem identity_star (V : polygonAlgebra a) (ι : Fin 5 ↪ Fin (m+1))
    (u : Fin (m+1) → CutRing × CutRing)
    (F : OffsetFrame a r m hm (orderedTrackAlphabet ι) u) :
    (identity (B := B) (hlarge := hlarge) (h := h) (hr := hr) V ι u F).star =
      B.distinctSlotStar hlarge h hr ι u F V := by
  ext s : 1
  change 1⁻¹*B.distinctSlotStar hlarge h hr ι u F V s*(1⁻¹)⁻¹ = _
  simp

end SlotRouting

variable (R : alternatingGroup (Fin (m+1)) →
      Multiplicative (FreeAbelianGroup (Fin m × Fin 2)) →*
      Multiplicative (FreeAbelianGroup (Fin m × Fin 2)))
    (hR : ∀ s k, B.c s * B.t k * (B.c s)⁻¹ = B.t (R s k))
    (hwide : 100 ≤ m+1)

include R hR

theorem slotStar_distinct (V : polygonAlgebra a) (ι : Fin 5 ↪ Fin (m+1))
    (u : Fin (m+1) → CutRing × CutRing)
    (F : OffsetFrame a r m hm (orderedTrackAlphabet ι) u)
    (hinj : Function.Injective (SlotMap a (m+1) V (fun j => (ι j,u (ι j))))) :
    B.slotStar hlarge h hr hwide V (fun j => ι j) (fun j => u (ι j)) hinj =
      B.distinctSlotStar hlarge h hr ι u F V := by
  rw [B.slotStar_eq_routing hlarge h hr R hR hwide V _ _ hinj (SlotRouting.identity V ι u F)]
  exact SlotRouting.identity_star V ι u F

theorem slotStar_aligned_transport (V : polygonAlgebra a)
    (i k : Fin 5 → Fin (m+1)) (u : Fin 5 → CutRing × CutRing)
    (hi : Function.Injective (SlotMap a (m+1) V (fun j => (i j,u j))))
    (hk : Function.Injective (SlotMap a (m+1) V (fun j => (k j,u j))))
    (J : Finset (Fin (m+1))) (hJ : J.card ≤ 5)
    (z : BoundedRelationCover M (alternatingGenerator a r m hm))
    (hz : z ∈ ⨆ W : polygonAlgebra a, (B.polygonStar hlarge h hr W).range)
    (hzJ : z ∈ sourceAlignedGroup a r m hm M B.t J)
    (htransport : ∀ (j : Fin 5) (x : V.val),
      (coverMap M (alternatingGenerator a r m hm) z).val.val (i j,translate a (u j) x.val) =
        (k j,translate a (u j) x.val)) :
    (MulAut.conj z).toMonoidHom.comp (B.slotStar hlarge h hr hwide V i u hi) =
      B.slotStar hlarge h hr hwide V k u hk :=
  SlotRouting.aligned_transport R hR _ _ J (by omega) z hz hzJ htransport

end InitialCoverSystem

end SimpleAmenable

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_GenerationUpstairs
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.BankEmbedding.instCoeFunForallPointTrackPoint _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonPlacement.Configuration.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.PolygonPlacement.instCoeFunForallGenericSquareTrackPoint _root_.OAI.SimpleAmenable.PolygonPlacement.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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
section GenerationUpstairs
namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)

theorem sourceAlignedGroup_univ_eq_top :
    sourceAlignedGroup a r m hm M B.t Finset.univ=⊤ := by
  classical
  let H := sourceAlignedGroup a r m hm M B.t Finset.univ
  have hx (b : SmallConditional m) : PresentedGroup.of (Sum.inl b) ∈ H :=
    alignedGroup_input B.t _ _ b (Finset.subset_univ _)
  have ht (u : Multiplicative (FreeAbelianGroup (Fin m × Fin 2))) :
      B.t u ∈ (Subgroup.normalizer (H : Set (BoundedRelationCover M (alternatingGenerator a r m hm)))) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · exact alignedGroup_conjugate B.t _ _ u
    · intro hy
      have hh := alignedGroup_conjugate B.t _ _ u⁻¹ hy
      have he : B.t u⁻¹*(B.t u*y*(B.t u)⁻¹)*(B.t u⁻¹)⁻¹=y := by
        rw [map_inv]; group
      rw [he] at hh
      exact hh
  have hn : (Subgroup.normalizer (H : Set (BoundedRelationCover M (alternatingGenerator a r m hm))))=⊤ := by
    apply top_unique
    intro z _
    apply PresentedGroup.generated_by _ (Subgroup.normalizer (H : Set (BoundedRelationCover M (alternatingGenerator a r m hm)))) _ z
    intro j
    cases j with
    | inl b => exact H.le_normalizer (hx b)
    | inr k =>
      have hh := ht (Multiplicative.ofAdd (FreeAbelianGroup.of k))
      rw [B.t_base] at hh
      exact hh
  let : H.Normal := Subgroup.normalizer_eq_top_iff.mp hn
  let q := QuotientGroup.mk' H
  let f := q.comp B.t
  have hgen (z : BoundedRelationCover M (alternatingGenerator a r m hm)) :
      q z ∈ f.range := by
    change z ∈ f.range.comap q
    apply PresentedGroup.generated_by _ (f.range.comap q) _ z
    intro j
    cases j with
    | inl b =>
      change q (PresentedGroup.of (Sum.inl b)) ∈ f.range
      have he : q (PresentedGroup.of (Sum.inl b))=1 := (QuotientGroup.eq_one_iff _).mpr (hx b)
      rw [he]
      exact f.range.one_mem
    | inr k =>
      change q (PresentedGroup.of (Sum.inr k)) ∈ f.range
      refine ⟨Multiplicative.ofAdd (FreeAbelianGroup.of k),?_⟩
      exact congrArg q (B.t_base k)
  have hf : Function.Surjective f := by
    intro z
    obtain ⟨w,rfl⟩ := QuotientGroup.mk'_surjective H z
    exact hgen w
  let : Group.IsPerfect (BoundedRelationCover M (alternatingGenerator a r m hm)) := B.perfect
  let : IsMulCommutative (BoundedRelationCover M (alternatingGenerator a r m hm) ⧸ H) :=
    IsMulCommutative.of_comm (by
      intro x y
      obtain ⟨u,rfl⟩ := hf x
      obtain ⟨v,rfl⟩ := hf y
      rw [← map_mul,← map_mul,mul_comm])
  apply top_unique
  intro z _
  exact (QuotientGroup.eq_one_iff _).mp (Subsingleton.elim (q z) 1)

end InitialCoverSystem
end GenerationUpstairs

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_FrameCompatibility
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.BankEmbedding.instCoeFunForallPointTrackPoint _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonPlacement.Configuration.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.PolygonPlacement.instCoeFunForallGenericSquareTrackPoint _root_.OAI.SimpleAmenable.PolygonPlacement.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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
section FrameCompatibility

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (hlarge : 15 < m+1) (h : B.AllPrimitiveLaws) (hr : 0<ordinary r ∧ ordinary r<1/2)

theorem frameStar_shift (I : Finset (Fin (m+1))) [Group.IsPerfect (alternatingGroup I)]
    (u : Fin (m+1) → CutRing × CutRing) (F : OffsetFrame a r m hm I u)
    (k : Multiplicative (FreeAbelianGroup (Fin m × Fin 2)))
    (d : Fin (m+1) → CutRing × CutRing)
    (hd : sourceLatticeFullMap a r m hm k = trackTranslation d) (V : polygonAlgebra a) :
    B.frameStar hlarge h hr I (d+u) (F.shift k d hd) V =
      (MulAut.conj (B.t k)).toMonoidHom.comp (B.frameStar hlarge h hr I u F V) := by
  ext s : 1
  change B.t (k*F.k) * B.polygonStar hlarge h hr V (universalMap (subtypeAlternatingHom I) s) *
    (B.t (k*F.k))⁻¹ = B.t k *
      (B.t F.k * B.polygonStar hlarge h hr V (universalMap (subtypeAlternatingHom I) s) * (B.t F.k)⁻¹) * (B.t k)⁻¹
  simp only [map_mul,mul_inv_rev,mul_assoc]

end InitialCoverSystem
end FrameCompatibility

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_TranslationRoutingHelpers
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.BankEmbedding.instCoeFunForallPointTrackPoint _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonPlacement.Configuration.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.PolygonPlacement.instCoeFunForallGenericSquareTrackPoint _root_.OAI.SimpleAmenable.PolygonPlacement.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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
section TranslationRoutingHelpers

theorem finiteBalancedVector_apply {m : ℕ} (I : Finset (Fin m)) (b : Fin m) (hb : b ∉ I)
    (u : Fin m → CutRing × CutRing) (i : Fin m) (hi : i ∈ I) :
    finiteBalancedVector I b u i=u i := by
  classical
  have hib : i≠b := fun he => hb (he ▸ hi)
  simp [finiteBalancedVector,Finset.sum_apply,Pi.sub_apply,Pi.single_apply,hib,hi]

theorem finiteBalancedVector_supported {m : ℕ} (I : Finset (Fin m)) (b : Fin m)
    (u : Fin m → CutRing × CutRing) (i : Fin m) (hi : i ∉ insert b I) :
    finiteBalancedVector I b u i=0 := by
  classical
  have hib : i≠b := fun he => hi (he ▸ Finset.mem_insert_self b I)
  have hiI : i∉I := fun hh => hi (Finset.mem_insert_of_mem hh)
  simp only [finiteBalancedVector,Finset.sum_apply,Pi.sub_apply]
  apply Finset.sum_eq_zero
  intro j hj
  have hij : i≠j := fun he => hiI (he ▸ hj)
  simp [hib,hij]

theorem finiteBalancedVector_range (a : ℕ) (r : CutRing) (m : ℕ) (hm : 2 ≤ m)
    (I : Finset (Fin (m+1))) (b : Fin (m+1)) (u : Fin (m+1) → CutRing × CutRing) :
    trackTranslation (a := a) (finiteBalancedVector I b u) ∈
      (sourceLatticeFullMap a r m hm).range := by
  classical
  unfold finiteBalancedVector
  induction I using Finset.induction_on with
  | empty => simp
  | @insert i I hi ih =>
    rw [Finset.sum_insert hi,trackTranslation_add]
    exact (sourceLatticeFullMap a r m hm).range.mul_mem
      (sourceLatticeFullMap_difference a r m hm b i (u i)) ih

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (hlarge : 15 < m+1) (h : B.AllPrimitiveLaws) (hr : 0<ordinary r ∧ ordinary r<1/2)

theorem distinctSlotStar_zero_commute (ι : Fin 5 ↪ Fin (m+1))
    (b : Fin (m+1)) (hb : b ∉ orderedTrackAlphabet ι)
    (u : Fin (m+1) → CutRing × CutRing)
    (F : OffsetFrame a r m hm (orderedTrackAlphabet ι) u) (V : polygonAlgebra a)
    (k : Multiplicative (FreeAbelianGroup (Fin m × Fin 2)))
    (d : Fin (m+1) → CutRing × CutRing)
    (hd : sourceLatticeFullMap a r m hm k=trackTranslation d)
    (hz : ∀ j, d (ι j)=0) (s : UniversalExtension (alternatingGroup (Fin 5))) :
    Commute (B.t k) (B.distinctSlotStar hlarge h hr ι u F V s) := by
  let G : CommonFrame a r m hm (orderedTrackAlphabet ι) 0 := {
    k := k
    d := d
    projection := hd
    common := by
      intro t ht
      obtain ⟨j,_,rfl⟩ := Finset.mem_map.mp ht
      exact hz j }
  have h₁ := B.polygonStar_frame_zero_commute hlarge h hr (orderedTrackAlphabet ι)
    (by simp [orderedTrackAlphabet]) b hb G V (universalMap (orderedTrackHom ι) s)
  have h₂ : Commute (B.t k) (B.t F.k) := (Commute.all k F.k).map B.t
  exact (h₂.mul_right h₁).mul_right h₂.inv_right

theorem privateRoutingFactor_shift_mem (i : Fin 5 → Fin (m+1))
    (u : Fin 5 → CutRing × CutRing) (P : PrivateRoutingBank i)
    (b : Fin (m+1)) (hb : b ∉ P.alphabet) (V : polygonAlgebra a) (j : Fin 5)
    (k : Multiplicative (FreeAbelianGroup (Fin m × Fin 2)))
    (d : Fin (m+1) → CutRing × CutRing)
    (hd : sourceLatticeFullMap a r m hm k=trackTranslation d)
    (hblock : ∀ l, d (P.row j l)=d (i j)) :
    (MulAut.conj (B.t k)) (B.privateRoutingFactor hlarge h hr i u P b hb V j) ∈
        ⨆ W : polygonAlgebra a, (B.polygonStar hlarge h hr W).range ∧
    (MulAut.conj (B.t k)) (B.privateRoutingFactor hlarge h hr i u P b hb V j) ∈
      sourceAlignedGroup a r m hm M B.t P.alphabet := by
  have hbj : b ∉ orderedTrackAlphabet (P.row j) := fun ht => hb (P.row_subset j ht)
  let F := balancedOffsetFrame a r m hm (orderedTrackAlphabet (P.row j)) b hbj (fun _ => u j)
  have he := DFunLike.congr_fun (B.frameStar_shift hlarge h hr (orderedTrackAlphabet (P.row j))
    (fun _ => u j) F k d hd V) (universalMap (orderedTrackHom (P.row j)) privateCycleStar)
  change B.distinctSlotStar hlarge h hr (P.row j) (d+(fun _ => u j)) (F.shift k d hd) V privateCycleStar =
    (MulAut.conj (B.t k)) (B.privateRoutingFactor hlarge h hr i u P b hb V j) at he
  rw [← he]
  constructor
  · exact B.distinctSlotStar_uniform_mem hlarge h hr (P.row j) b hbj _ (F.shift k d hd)
      (d (i j)+u j) (fun l => by simp only [Pi.add_apply,hblock l]) V privateCycleStar
  · exact sourceAlignedGroup_mono B.t (P.row_subset j)
      (B.frameStar_alphabet_mem hlarge h hr _ (by simp [orderedTrackAlphabet]) b hbj _
        (F.shift k d hd) V (universalMap (orderedTrackHom (P.row j)) privateCycleStar))

theorem privateRoutingWord_shift_mem (i : Fin 5 → Fin (m+1))
    (u : Fin 5 → CutRing × CutRing) (P : PrivateRoutingBank i)
    (b : Fin (m+1)) (hb : b ∉ P.alphabet) (V : polygonAlgebra a)
    (k : Multiplicative (FreeAbelianGroup (Fin m × Fin 2)))
    (d : Fin (m+1) → CutRing × CutRing)
    (hd : sourceLatticeFullMap a r m hm k=trackTranslation d)
    (hblock : ∀ j l, d (P.row j l)=d (i j)) :
    (MulAut.conj (B.t k)) (B.privateRoutingWord hlarge h hr i u P b hb V) ∈
        ⨆ W : polygonAlgebra a, (B.polygonStar hlarge h hr W).range ∧
    (MulAut.conj (B.t k)) (B.privateRoutingWord hlarge h hr i u P b hb V) ∈
      sourceAlignedGroup a r m hm M B.t P.alphabet := by
  have he : (MulAut.conj (B.t k)) (B.privateRoutingWord hlarge h hr i u P b hb V) =
      ((List.finRange 5).map (fun j =>
        (MulAut.conj (B.t k)) (B.privateRoutingFactor hlarge h hr i u P b hb V j))).prod := by
    exact (MulAut.conj (B.t k)).toMonoidHom.map_list_prod _ |>.trans (by rw [List.map_map]; rfl)
  rw [he]
  constructor
  · apply Subgroup.list_prod_mem
    intro t ht
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp ht
    exact (B.privateRoutingFactor_shift_mem hlarge h hr i u P b hb V j k d hd (hblock j)).1
  · apply Subgroup.list_prod_mem
    intro t ht
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp ht
    exact (B.privateRoutingFactor_shift_mem hlarge h hr i u P b hb V j k d hd (hblock j)).2

end InitialCoverSystem
end TranslationRoutingHelpers

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_ShiftedRouting
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.BankEmbedding.instCoeFunForallPointTrackPoint _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonPlacement.Configuration.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.PolygonPlacement.instCoeFunForallGenericSquareTrackPoint _root_.OAI.SimpleAmenable.PolygonPlacement.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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
section ShiftedRouting
namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (hlarge : 15 < m+1) (h : B.AllPrimitiveLaws) (hr : 0<ordinary r ∧ ordinary r<1/2)

namespace SlotRouting
variable {B hlarge h hr}

theorem shift_star {V : polygonAlgebra a} {i : Fin 5 → Fin (m+1)}
    {u : Fin 5 → CutRing × CutRing} (ρ : B.SlotRouting hlarge h hr V i u)
    (k : Multiplicative (FreeAbelianGroup (Fin m × Fin 2)))
    (d : Fin (m+1) → CutRing × CutRing)
    (hd : sourceLatticeFullMap a r m hm k=trackTranslation d)
    (htarget : ∀ j, d (ρ.target j)=d (i j))
    (halign : (MulAut.conj (B.t k)) ρ.word ∈
      ⨆ W : polygonAlgebra a, (B.polygonStar hlarge h hr W).range)
    (hsupp : (MulAut.conj (B.t k)) ρ.word ∈ sourceAlignedGroup a r m hm M B.t ρ.alphabet) :
    (ρ.shift k d hd htarget halign hsupp).star =
      (MulAut.conj (B.t k)).toMonoidHom.comp ρ.star := by
  ext s : 1
  have he := DFunLike.congr_fun (B.frameStar_shift hlarge h hr (orderedTrackAlphabet ρ.target)
    ρ.offsets ρ.frame k d hd V) (universalMap (orderedTrackHom ρ.target) s)
  change B.frameStar hlarge h hr _ _ _ V _ =
    B.t k*B.distinctSlotStar hlarge h hr ρ.target ρ.offsets ρ.frame V s*(B.t k)⁻¹ at he
  change (B.t k*ρ.word*(B.t k)⁻¹)⁻¹ *
    B.frameStar hlarge h hr (orderedTrackAlphabet ρ.target) (d+ρ.offsets) (ρ.frame.shift k d hd) V
      (universalMap (orderedTrackHom ρ.target) s) *((B.t k*ρ.word*(B.t k)⁻¹)⁻¹)⁻¹ =
    B.t k*(ρ.word⁻¹*B.distinctSlotStar hlarge h hr ρ.target ρ.offsets ρ.frame V s*(ρ.word⁻¹)⁻¹)*(B.t k)⁻¹
  rw [he]
  group

end SlotRouting

variable (R : alternatingGroup (Fin (m+1)) →
      Multiplicative (FreeAbelianGroup (Fin m × Fin 2)) →*
      Multiplicative (FreeAbelianGroup (Fin m × Fin 2)))
    (hR : ∀ s k, B.c s * B.t k * (B.c s)⁻¹ = B.t (R s k))
    (hwide : 100 ≤ m+1)

include R hR

theorem slotStar_zero_commute (V : polygonAlgebra a) (i : Fin 5 → Fin (m+1))
    (u : Fin 5 → CutRing × CutRing)
    (hinj : Function.Injective (SlotMap a (m+1) V (fun j => (i j,u j))))
    (k : Multiplicative (FreeAbelianGroup (Fin m × Fin 2)))
    (d : Fin (m+1) → CutRing × CutRing)
    (hd : sourceLatticeFullMap a r m hm k=trackTranslation d)
    (J : Finset (Fin (m+1))) (hJ : J.card≤28)
    (hsupp : ∀ t, t∉J → d t=0) (hz : ∀ j, d (i j)=0)
    (s : UniversalExtension (alternatingGroup (Fin 5))) :
    Commute (B.t k) (B.slotStar hlarge h hr hwide V i u hinj s) := by
  classical
  have hres : 20 ≤ ((Finset.univ : Finset (Fin (m+1))) \
      (J ∪ Finset.univ.image i)).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    have h₁ := Finset.card_union_le J (Finset.univ.image i)
    have h₂ := Finset.card_image_le (f := i) (s := Finset.univ)
    simp only [Finset.card_univ,Fintype.card_fin] at h₂ ⊢
    omega
  obtain ⟨P,hP⟩ := exists_privateRoutingBank i J hres
  obtain ⟨b,_,hb⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show P.alphabet.card < (Finset.univ : Finset (Fin (m+1))).card by
      have hc := P.alphabet_card
      simp only [Finset.card_univ,Fintype.card_fin]
      omega)
  let ρ := SlotRouting.privateBank (B := B) (hlarge := hlarge) (h := h) (hr := hr)
    V i u P b hb hinj
  rw [B.slotStar_eq_routing hlarge h hr R hR hwide V i u hinj ρ]
  have hzrow (j l : Fin 5) : d (P.row j l)=0 := by
    by_cases hl : l=0
    · subst l; rw [P.source j]; exact hz j
    · exact hsupp _ (hP j l hl)
  have hw : Commute (B.t k) ρ.word := by
    change Commute (B.t k) (((List.finRange 5).map _).prod)
    apply Commute.list_prod_right
    intro z hmem
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hmem
    exact B.distinctSlotStar_zero_commute hlarge h hr (P.row j) b
      (fun ht => hb (P.row_subset j ht)) (fun _ => u j) _ V k d hd (hzrow j) privateCycleStar
  have ht : Commute (B.t k) (B.distinctSlotStar hlarge h hr ρ.target ρ.offsets ρ.frame V s) :=
    B.distinctSlotStar_zero_commute hlarge h hr ρ.target b
      (by intro ht; obtain ⟨j,_,he⟩ := Finset.mem_map.mp ht
          exact hb (he ▸ P.row_subset j (orderedTrackAlphabet_mem _ 1)))
      ρ.offsets ρ.frame V k d hd (fun j => hzrow j 1) s
  exact (hw.inv_right.mul_right ht).mul_right hw.inv_right.inv_right

end InitialCoverSystem
end ShiftedRouting

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_TranslationTransport
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.BankEmbedding.instCoeFunForallPointTrackPoint _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonPlacement.Configuration.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.PolygonPlacement.instCoeFunForallGenericSquareTrackPoint _root_.OAI.SimpleAmenable.PolygonPlacement.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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
section TranslationTransport

namespace PrivateRoutingBank
variable {m : ℕ} {i : Fin 5 → Fin m} (P : PrivateRoutingBank i)

theorem balancedShift_row (b : Fin m) (hb : b ∉ P.alphabet)
    (d : Fin m → CutRing × CutRing) (j l : Fin 5) :
    P.balancedShift b d (P.row j l)=d (i j) := by
  rw [balancedShift,finiteBalancedVector_apply P.alphabet b hb _ _
    (P.row_subset j (orderedTrackAlphabet_mem _ l)),P.blockOffsets_apply]

theorem balancedShift_source (b : Fin m) (hb : b ∉ P.alphabet)
    (d : Fin m → CutRing × CutRing) (j : Fin 5) :
    P.balancedShift b d (i j)=d (i j) :=
  (congrArg (P.balancedShift b d) (P.source j)).symm.trans (P.balancedShift_row b hb d j 0)

theorem balancedShift_block (b : Fin m) (hb : b ∉ P.alphabet)
    (d : Fin m → CutRing × CutRing) (j l : Fin 5) :
    P.balancedShift b d (P.row j l)=P.balancedShift b d (i j) :=
  (P.balancedShift_row b hb d j l).trans (P.balancedShift_source b hb d j).symm

theorem difference_support (b : Fin m) (d : Fin m → CutRing × CutRing)
    (J : Finset (Fin m)) (hsupp : ∀ t, t∉J → d t=0)
    (t : Fin m) (ht : t∉J ∪ insert b P.alphabet) : (d-P.balancedShift b d) t=0 := by
  have htJ : t∉J := fun hh => ht (Finset.mem_union_left _ hh)
  have htP : t∉insert b P.alphabet := fun hh => ht (Finset.mem_union_right _ hh)
  rw [Pi.sub_apply]
  exact sub_eq_zero.mpr ((hsupp t htJ).trans
    (finiteBalancedVector_supported P.alphabet b (P.blockOffsets d) t htP).symm)

theorem difference_source (b : Fin m) (hb : b ∉ P.alphabet)
    (d : Fin m → CutRing × CutRing) (j : Fin 5) :
    (d - P.balancedShift b d) (i j)=0 := by
  rw [Pi.sub_apply,P.balancedShift_source b hb d j,sub_self]

theorem difference_alphabet_card (b : Fin m) (J : Finset (Fin m)) (hJ : J.card≤2) :
    (J ∪ insert b P.alphabet).card≤28 := by
  have hc := P.alphabet_card
  have h₁ := Finset.card_union_le J (insert b P.alphabet)
  have h₂ := Finset.card_insert_le b P.alphabet
  omega

end PrivateRoutingBank

theorem exists_privateRoutingBank_with_balance {m : ℕ} (i : Fin 5 → Fin m)
    (hwide : 26 ≤ m) : ∃ P : PrivateRoutingBank i, ∃ b : Fin m, b ∉ P.alphabet := by
  classical
  have hres : 20 ≤ ((Finset.univ : Finset (Fin m)) \
      (∅ ∪ Finset.univ.image i)).card := by
    rw [Finset.empty_union,Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    have hc := Finset.card_image_le (f := i) (s := Finset.univ)
    simp only [Finset.card_univ,Fintype.card_fin] at hc ⊢
    omega
  obtain ⟨P,_⟩ := exists_privateRoutingBank i ∅ hres
  obtain ⟨b,_,hb⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show P.alphabet.card < (Finset.univ : Finset (Fin m)).card by
      have hc := P.alphabet_card
      simp only [Finset.card_univ,Fintype.card_fin]
      omega)
  exact ⟨P,b,hb⟩

theorem translation_conjugate_eq {A H : Type*} [CommGroup A] [Group H]
    (t : A →* H) (k l : A) (x : H) (hc : Commute (t (k*l⁻¹)) x) :
    t k*x*(t k)⁻¹=t l*x*(t l)⁻¹ := by
  let δ := k*l⁻¹
  have hkk : k=l*δ := by dsimp [δ]; simp only [mul_comm k l⁻¹,← mul_assoc,mul_inv_cancel,one_mul]
  have hcc : t δ*x*(t δ)⁻¹=x := by rw [hc.eq,mul_assoc,mul_inv_cancel,mul_one]
  calc
    t k*x*(t k)⁻¹ = t l*(t δ*x*(t δ)⁻¹)*(t l)⁻¹ := by rw [hkk,map_mul]; group
    _ = t l*x*(t l)⁻¹ := by rw [hcc]

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (hlarge : 15 < m+1) (h : B.AllPrimitiveLaws) (hr : 0<ordinary r ∧ ordinary r<1/2)
    (R : alternatingGroup (Fin (m+1)) →
      Multiplicative (FreeAbelianGroup (Fin m × Fin 2)) →*
      Multiplicative (FreeAbelianGroup (Fin m × Fin 2)))
    (hR : ∀ s k, B.c s * B.t k * (B.c s)⁻¹ = B.t (R s k))
    (hwide : 100 ≤ m+1)

include R hR

theorem slotStar_translation_bank (V : polygonAlgebra a)
    (i : Fin 5 → Fin (m+1)) (u : Fin 5 → CutRing × CutRing)
    (hinj : Function.Injective (SlotMap a (m+1) V (fun j => (i j,u j))))
    (P : PrivateRoutingBank i) (b : Fin (m+1)) (hb : b ∉ P.alphabet)
    (k : Multiplicative (FreeAbelianGroup (Fin m × Fin 2)))
    (d : Fin (m+1) → CutRing × CutRing)
    (hd : sourceLatticeFullMap a r m hm k=trackTranslation d)
    (hblock : ∀ j l, d (P.row j l)=d (i j)) :
    (MulAut.conj (B.t k)).toMonoidHom.comp (B.slotStar hlarge h hr hwide V i u hinj) =
      B.slotStar hlarge h hr hwide V i (fun j => d (i j)+u j)
        (SlotMap_shift_injective V i u hinj d) := by
  let ρ := SlotRouting.privateBank (B := B) (hlarge := hlarge) (h := h) (hr := hr)
    V i u P b hb hinj
  have htarget (j : Fin 5) : d (ρ.target j)=d (i j) := hblock j 1
  have hmem := B.privateRoutingWord_shift_mem hlarge h hr i u P b hb V k d hd hblock
  let σ := ρ.shift k d hd htarget hmem.1 hmem.2
  rw [B.slotStar_eq_routing hlarge h hr R hR hwide V i u hinj ρ,
    B.slotStar_eq_routing hlarge h hr R hR hwide V i _ _ σ]
  exact (ρ.shift_star k d hd htarget hmem.1 hmem.2).symm

theorem slotStar_translation_difference_commute (V : polygonAlgebra a)
    (i : Fin 5 → Fin (m+1)) (u : Fin 5 → CutRing × CutRing)
    (hinj : Function.Injective (SlotMap a (m+1) V (fun j => (i j,u j))))
    (P : PrivateRoutingBank i) (b : Fin (m+1)) (hb : b ∉ P.alphabet)
    (k k' : Multiplicative (FreeAbelianGroup (Fin m × Fin 2)))
    (d : Fin (m+1) → CutRing × CutRing)
    (hd : sourceLatticeFullMap a r m hm k=trackTranslation d)
    (hk' : sourceLatticeFullMap a r m hm k'=trackTranslation (P.balancedShift b d))
    (J : Finset (Fin (m+1))) (hJ : J.card≤2) (hsupp : ∀ t, t∉J → d t=0)
    (s : UniversalExtension (alternatingGroup (Fin 5))) :
    Commute (B.t (k*k'⁻¹)) (B.slotStar hlarge h hr hwide V i u hinj s) := by
  have hδ : sourceLatticeFullMap a r m hm (k*k'⁻¹)=
      trackTranslation (d-P.balancedShift b d) := by
    rw [map_mul,map_inv,hd,hk',trackTranslation_sub]
  exact B.slotStar_zero_commute hlarge h hr R hR hwide V i u hinj (k*k'⁻¹)
    (d-P.balancedShift b d) hδ (J ∪ insert b P.alphabet)
    (P.difference_alphabet_card b J hJ) (P.difference_support b d J hsupp)
    (P.difference_source b hb d) s

theorem slotStar_translation_two_support (V : polygonAlgebra a)
    (i : Fin 5 → Fin (m+1)) (u : Fin 5 → CutRing × CutRing)
    (hinj : Function.Injective (SlotMap a (m+1) V (fun j => (i j,u j))))
    (k : Multiplicative (FreeAbelianGroup (Fin m × Fin 2)))
    (d : Fin (m+1) → CutRing × CutRing)
    (hd : sourceLatticeFullMap a r m hm k=trackTranslation d)
    (J : Finset (Fin (m+1))) (hJ : J.card≤2)
    (hsupp : ∀ t, t∉J → d t=0) :
    (MulAut.conj (B.t k)).toMonoidHom.comp (B.slotStar hlarge h hr hwide V i u hinj) =
      B.slotStar hlarge h hr hwide V i (fun j => d (i j)+u j)
        (SlotMap_shift_injective V i u hinj d) := by
  obtain ⟨P,b,hb⟩ := exists_privateRoutingBank_with_balance i (by omega)
  let v := P.balancedShift b d
  obtain ⟨k',hk'⟩ := finiteBalancedVector_range a r m hm P.alphabet b (P.blockOffsets d)
  have hv : sourceLatticeFullMap a r m hm k'=trackTranslation v := hk'
  have he := B.slotStar_translation_bank hlarge h hr R hR hwide V i u hinj P b hb k' v hv
    (P.balancedShift_block b hb d)
  have hoff : (fun j => v (i j)+u j)=(fun j => d (i j)+u j) :=
    funext (fun j => congrArg (fun z => z+u j) (P.balancedShift_source b hb d j))
  have he' : (MulAut.conj (B.t k')).toMonoidHom.comp (B.slotStar hlarge h hr hwide V i u hinj) =
      B.slotStar hlarge h hr hwide V i (fun j => d (i j)+u j)
        (SlotMap_shift_injective V i u hinj d) := by simpa only [hoff] using he
  rw [← he']
  ext s : 1
  apply translation_conjugate_eq B.t k k'
  exact B.slotStar_translation_difference_commute hlarge h hr R hR hwide V i u hinj
    P b hb k k' d hd hk' J hJ hsupp s

end InitialCoverSystem
end TranslationTransport

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_LatticeTranslationTransport
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.BankEmbedding.instCoeFunForallPointTrackPoint _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonPlacement.Configuration.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.PolygonPlacement.instCoeFunForallGenericSquareTrackPoint _root_.OAI.SimpleAmenable.PolygonPlacement.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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
section LatticeTranslationTransport

theorem sourceGeneratorOffsets_support (m : ℕ) (j : Fin m × Fin 2)
    (t : Fin (m+1)) (ht : t ∉ ({j.1.castSucc,Fin.last m} : Finset (Fin (m+1)))) :
    sourceGeneratorOffsets m j t=0 := by
  classical
  have hi : t≠j.1.castSucc := fun he => ht (he ▸ Finset.mem_insert_self _ _)
  have hl : t≠Fin.last m := fun he => ht (he ▸ Finset.mem_insert_of_mem
    (Finset.mem_singleton_self _))
  simp [sourceGeneratorOffsets,Pi.sub_apply,hi,hl]

theorem sourceLatticeFullMap_offsets (a : ℕ) (r : CutRing) (m : ℕ) (hm : 2 ≤ m)
    (k : FreeAbelianGroup (Fin m × Fin 2)) :
    sourceLatticeFullMap a r m hm (Multiplicative.ofAdd k)=
      trackTranslation (sourceLatticeOffsets m k) := by
  induction k using FreeAbelianGroup.induction_on with
  | zero => simp only [map_zero,ofAdd_zero,map_one,trackTranslation_zero]
  | of j =>
    rw [sourceLatticeOffsets_of]
    exact sourceLatticeFullMap_of a r m hm j
  | neg j ih =>
    change sourceLatticeFullMap a r m hm ((Multiplicative.ofAdd (FreeAbelianGroup.of j))⁻¹)=_
    rw [map_inv,ih,map_neg,trackTranslation_neg]
  | add k l ihk ihl =>
    change sourceLatticeFullMap a r m hm (Multiplicative.ofAdd k*Multiplicative.ofAdd l)=_
    rw [map_mul,ihk,ihl,map_add,trackTranslation_add]

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (hlarge : 15 < m+1) (h : B.AllPrimitiveLaws) (hr : 0<ordinary r ∧ ordinary r<1/2)
    (R : alternatingGroup (Fin (m+1)) →
      Multiplicative (FreeAbelianGroup (Fin m × Fin 2)) →*
      Multiplicative (FreeAbelianGroup (Fin m × Fin 2)))
    (hR : ∀ s k, B.c s * B.t k * (B.c s)⁻¹ = B.t (R s k))
    (hwide : 100 ≤ m+1)

include R hR

theorem slotStar_translation_lattice (k : FreeAbelianGroup (Fin m × Fin 2))
    (V : polygonAlgebra a) (i : Fin 5 → Fin (m+1)) (u : Fin 5 → CutRing × CutRing)
    (hinj : Function.Injective (SlotMap a (m+1) V (fun j => (i j,u j)))) :
    (MulAut.conj (B.t (Multiplicative.ofAdd k))).toMonoidHom.comp
      (B.slotStar hlarge h hr hwide V i u hinj) =
      B.slotStar hlarge h hr hwide V i (fun j => sourceLatticeOffsets m k (i j)+u j)
        (SlotMap_shift_injective V i u hinj (sourceLatticeOffsets m k)) := by
  induction k using FreeAbelianGroup.induction_on generalizing u with
  | zero =>
    simp only [ofAdd_zero,map_one,map_zero,Pi.zero_apply,zero_add]
    ext s : 1
    rfl
  | of j =>
    simpa only [sourceLatticeOffsets_of] using B.slotStar_translation_two_support hlarge h hr R hR hwide V i u hinj
      (Multiplicative.ofAdd (FreeAbelianGroup.of j)) (sourceGeneratorOffsets m j)
      (sourceLatticeFullMap_of a r m hm j) {j.1.castSucc,Fin.last m}
      (by exact le_trans (Finset.card_insert_le _ _) (by simp)) (sourceGeneratorOffsets_support m j)
  | neg j _ =>
    have hd := sourceLatticeFullMap_offsets a r m hm (-FreeAbelianGroup.of j)
    exact B.slotStar_translation_two_support hlarge h hr R hR hwide V i u hinj
      (Multiplicative.ofAdd (-FreeAbelianGroup.of j)) _ hd {j.1.castSucc,Fin.last m}
      (by exact le_trans (Finset.card_insert_le _ _) (by simp)) (by
        intro t ht
        rw [map_neg,sourceLatticeOffsets_of,Pi.neg_apply,sourceGeneratorOffsets_support m j t ht,neg_zero])
  | add k l ihk ihl =>
    have hl := DFunLike.congr_fun (ihl u hinj)
    have hk := DFunLike.congr_fun (ihk (fun j => sourceLatticeOffsets m l (i j)+u j)
      (SlotMap_shift_injective V i u hinj (sourceLatticeOffsets m l)))
    have hoff : (fun j => sourceLatticeOffsets m k (i j)+(sourceLatticeOffsets m l (i j)+u j)) =
        (fun j => sourceLatticeOffsets m (k+l) (i j)+u j) := by
      funext j
      rw [map_add,Pi.add_apply,add_assoc]
    ext s : 1
    change B.t (Multiplicative.ofAdd k*Multiplicative.ofAdd l)*
      B.slotStar hlarge h hr hwide V i u hinj s*
        (B.t (Multiplicative.ofAdd k*Multiplicative.ofAdd l))⁻¹ = _
    rw [map_mul]
    calc
      _ = B.t (Multiplicative.ofAdd k)*
          (B.t (Multiplicative.ofAdd l)* B.slotStar hlarge h hr hwide V i u hinj s*
            (B.t (Multiplicative.ofAdd l))⁻¹)*(B.t (Multiplicative.ofAdd k))⁻¹ := by group
      _ = _ := by
        rw [show B.t (Multiplicative.ofAdd l)*B.slotStar hlarge h hr hwide V i u hinj s*
          (B.t (Multiplicative.ofAdd l))⁻¹ = _ from hl s]
        exact (hk s).trans (by simp only [hoff])

end InitialCoverSystem
end LatticeTranslationTransport

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_SlotInputGeneration
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.BankEmbedding.instCoeFunForallPointTrackPoint _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonPlacement.Configuration.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.PolygonPlacement.instCoeFunForallGenericSquareTrackPoint _root_.OAI.SimpleAmenable.PolygonPlacement.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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
section SlotInputGeneration

theorem orderedTrackHom_bijective {m : ℕ} (ι : Fin 5 ↪ Fin m) :
    Function.Bijective (orderedTrackHom ι) := by
  have hi : Function.Injective (orderedTrackHom ι) := by
    intro s t he
    apply Subtype.ext
    apply Equiv.Perm.viaEmbeddingHom_injective ι
    have hh := congrArg (subtypeAlternatingHom (orderedTrackAlphabet ι)) he
    rw [← MonoidHom.comp_apply,← MonoidHom.comp_apply,orderedTrackHom_comp] at hh
    exact congrArg Subtype.val hh
  let e := (orderedTrackEquiv ι).altCongrHom
  have hs := Finite.surjective_of_injective (e.symm.injective.comp hi)
  refine ⟨hi,fun y => ?_⟩
  obtain ⟨x,hx⟩ := hs (e.symm y)
  exact ⟨x,e.symm.injective hx⟩

theorem smallPermutation_fiveRepresentation {m : ℕ} (hm : 5 ≤ m)
    (s : alternatingGroup (Fin m)) (hs : s.val.support.card≤5) :
    ∃ (ι : Fin 5 ↪ Fin m) (t : alternatingGroup (Fin 5)), fiveAlternatingHom ι t=s := by
  classical
  obtain ⟨I,hSI,_,hI⟩ := Finset.exists_subsuperset_card_eq
    (Finset.subset_univ s.val.support) hs (by simpa using hm : 5≤(Finset.univ : Finset (Fin m)).card)
  let e : Fin 5 ≃ I := (Fintype.equivFinOfCardEq (by simpa using hI : Fintype.card I=5)).symm
  let ι : Fin 5 ↪ Fin m := e.toEmbedding.trans (Function.Embedding.subtype _)
  have hsub : s.val.support ⊆ orderedTrackAlphabet ι := by
    intro x hx
    exact Finset.mem_map.mpr ⟨e.symm ⟨x,hSI hx⟩,Finset.mem_univ _,
      congrArg Subtype.val (e.apply_symm_apply _)⟩
  obtain ⟨v,hv⟩ := (subtypeAlternatingHom_mem_range (orderedTrackAlphabet ι) s).mpr hsub
  obtain ⟨t,ht⟩ := (orderedTrackHom_bijective ι).2 v
  refine ⟨ι,t,?_⟩
  rw [← DFunLike.congr_fun (orderedTrackHom_comp ι) t,MonoidHom.comp_apply,ht,hv]

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (hlarge : 15 < m+1) (h : B.AllPrimitiveLaws) (hr : 0<ordinary r ∧ ordinary r<1/2)

theorem polygonStar_initial_alphabet (j : Fin 5) (I : FiveAlphabet (Fin (m+1))) :
    (B.polygonStar hlarge h hr (initialTest a r j)).comp
      (universalMap (subtypeAlternatingHom I.val)) =
    (B.initialAlphabet I.val j).comp (universalProjection (alternatingGroup I.val)) := by
  let P : Unit → Fin 5 × (CutRing × CutRing) := fun _ => (j,0)
  have hp : primitiveTests (a := a) (r := r) P ()=initialTest a r j := by
    simp only [primitiveTests,primitiveFamilyTests,P,spatialTranslate_zero]
  rw [← hp,B.polygonStar_eq hlarge h hr P _ (resolved_test _ ())]
  rw [B.fullGeometricSector_small_input hlarge P (fun J _ b hb => h Unit P J b hb) P () () rfl I]
  change (B.primitiveCopy I.val _ _ (j,0)).comp _ = _
  rw [B.primitiveCopy_zero]

variable (R : alternatingGroup (Fin (m+1)) →
      Multiplicative (FreeAbelianGroup (Fin m × Fin 2)) →*
      Multiplicative (FreeAbelianGroup (Fin m × Fin 2)))
    (hR : ∀ s k, B.c s * B.t k * (B.c s)⁻¹ = B.t (R s k))
    (hwide : 100 ≤ m+1)

theorem slotGroup_mem (V : polygonAlgebra a) (i : Fin 5 → Fin (m+1))
    (u : Fin 5 → CutRing × CutRing)
    (hi : Function.Injective (SlotMap a (m+1) V (fun j => (i j,u j))))
    (s : UniversalExtension (alternatingGroup (Fin 5))) :
    B.slotStar hlarge h hr hwide V i u hi s ∈ B.slotGroup hlarge h hr hwide :=
  Subgroup.subset_closure ⟨V,i,u,hi,s,rfl⟩

include R hR

theorem translated_initial_mem_slotGroup (b : SmallConditional m)
    (k : Multiplicative (FreeAbelianGroup (Fin m × Fin 2))) :
    B.t k*PresentedGroup.of (Sum.inl b)*(B.t k)⁻¹ ∈ B.slotGroup hlarge h hr hwide := by
  obtain ⟨ι,s,hs⟩ := smallPermutation_fiveRepresentation (by omega : 5 ≤ m+1)
    (⟨b.2.val,b.2.property.1⟩ : alternatingGroup (Fin (m+1))) b.2.property.2
  obtain ⟨t,ht⟩ := universalProjection_surjective (alternatingGroup (Fin 5)) s
  let I : FiveAlphabet (Fin (m+1)) := ⟨orderedTrackAlphabet ι,Finset.subset_univ _,by
    simp [orderedTrackAlphabet]⟩
  let d := sourceLatticeOffsets m (Multiplicative.toAdd k)
  let F : OffsetFrame a r m hm (orderedTrackAlphabet ι) d := {
    k := k
    d := d
    projection := sourceLatticeFullMap_offsets a r m hm (Multiplicative.toAdd k)
    prescribed := fun _ _ => rfl }
  have he : B.distinctSlotStar hlarge h hr ι d F (initialTest a r b.1) t =
      B.t k*PresentedGroup.of (Sum.inl b)*(B.t k)⁻¹ := by
    change B.t k * B.polygonStar hlarge h hr (initialTest a r b.1)
      (universalMap (subtypeAlternatingHom I.val) (universalMap (orderedTrackHom ι) t)) * (B.t k)⁻¹ = _
    rw [show B.polygonStar hlarge h hr (initialTest a r b.1)
      (universalMap (subtypeAlternatingHom I.val) (universalMap (orderedTrackHom ι) t)) =
      B.initialAlphabet I.val b.1 (universalProjection _ (universalMap (orderedTrackHom ι) t)) from
        DFunLike.congr_fun (B.polygonStar_initial_alphabet hlarge h hr b.1 I) _]
    rw [show universalProjection _ (universalMap (orderedTrackHom ι) t)=orderedTrackHom ι s from
      (DFunLike.congr_fun (universalMap_spec (orderedTrackHom ι)) t).trans (by rw [MonoidHom.comp_apply,ht])]
    change B.t k*B.initialConditional b.1 (subtypeAlternatingHom (orderedTrackAlphabet ι) (orderedTrackHom ι s))*(B.t k)⁻¹=_
    have hh := DFunLike.congr_fun (orderedTrackHom_comp ι) s
    change subtypeAlternatingHom (orderedTrackAlphabet ι) (orderedTrackHom ι s) = fiveAlternatingHom ι s at hh
    rw [hh,hs,B.initialConditional_input _ _ b.2.property.2]
    rfl
  rw [← he,← DFunLike.congr_fun (B.slotStar_distinct hlarge h hr R hR hwide
    (initialTest a r b.1) ι d F (slots_injective_of_tracks _ _ ι.injective)) t]
  exact B.slotGroup_mem hlarge h hr hwide _ _ _ _ t

theorem slotGroup_eq_top : B.slotGroup hlarge h hr hwide=⊤ := by
  apply top_unique
  rw [← B.sourceAlignedGroup_univ_eq_top]
  change alignedGroup B.t (fun b : SmallConditional m => PresentedGroup.of (Sum.inl b))
    (fun b => b.2.val.support ⊆ Finset.univ) ≤ _
  apply (Subgroup.closure_le _).mpr
  rintro z ⟨b,_,k,rfl⟩
  exact B.translated_initial_mem_slotGroup hlarge h hr R hR hwide b k

end InitialCoverSystem
end SlotInputGeneration

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_WholeCoverCentrality
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.BankEmbedding.instCoeFunForallPointTrackPoint _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonPlacement.Configuration.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.PolygonPlacement.instCoeFunForallGenericSquareTrackPoint _root_.OAI.SimpleAmenable.PolygonPlacement.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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
section WholeCoverCentrality
namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (hlarge : 15 < m+1) (h : B.AllPrimitiveLaws) (hr : 0<ordinary r ∧ ordinary r<1/2)

theorem initial_input_mem_polygonStars (b : SmallConditional m) :
    PresentedGroup.of (Sum.inl b) ∈
      ⨆ W : polygonAlgebra a, (B.polygonStar hlarge h hr W).range := by
  obtain ⟨ι,s,hs⟩ := smallPermutation_fiveRepresentation (by omega : 5 ≤ m+1)
    (⟨b.2.val,b.2.property.1⟩ : alternatingGroup (Fin (m+1))) b.2.property.2
  obtain ⟨t,ht⟩ := universalProjection_surjective (alternatingGroup (Fin 5)) s
  let I : FiveAlphabet (Fin (m+1)) := ⟨orderedTrackAlphabet ι,Finset.subset_univ _,by
    simp [orderedTrackAlphabet]⟩
  apply le_iSup (fun W : polygonAlgebra a => (B.polygonStar hlarge h hr W).range)
    (initialTest a r b.1)
  refine ⟨universalMap (subtypeAlternatingHom I.val) (universalMap (orderedTrackHom ι) t),?_⟩
  rw [show B.polygonStar hlarge h hr (initialTest a r b.1)
    (universalMap (subtypeAlternatingHom I.val) (universalMap (orderedTrackHom ι) t)) =
    B.initialAlphabet I.val b.1 (universalProjection _ (universalMap (orderedTrackHom ι) t)) from
      DFunLike.congr_fun (B.polygonStar_initial_alphabet hlarge h hr b.1 I) _]
  rw [show universalProjection _ (universalMap (orderedTrackHom ι) t)=orderedTrackHom ι s from
    (DFunLike.congr_fun (universalMap_spec (orderedTrackHom ι)) t).trans (by rw [MonoidHom.comp_apply,ht])]
  change B.initialConditional b.1 (subtypeAlternatingHom (orderedTrackAlphabet ι) (orderedTrackHom ι s))=_
  have hh := DFunLike.congr_fun (orderedTrackHom_comp ι) s
  change subtypeAlternatingHom (orderedTrackAlphabet ι) (orderedTrackHom ι s) = fiveAlternatingHom ι s at hh
  rw [hh,hs,B.initialConditional_input _ _ b.2.property.2]
  rfl

variable (R : alternatingGroup (Fin (m+1)) →
      Multiplicative (FreeAbelianGroup (Fin m × Fin 2)) →*
      Multiplicative (FreeAbelianGroup (Fin m × Fin 2)))
    (hR : ∀ s k, B.c s * B.t k * (B.c s)⁻¹ = B.t (R s k))
    (hwide : 100 ≤ m+1)
include R hR

theorem uniformSlotTransport_initial (b : SmallConditional m) :
    B.UniformSlotTransport hlarge h hr hwide (PresentedGroup.of (Sum.inl b)) := by
  intro V i k u v htr hi hk
  have hspatial : ∀ (j : Fin 5) (x : V.val), translate a (u j) x.val=translate a (v j) x.val := by
    intro j x
    have he := congrArg Prod.snd (htr j x)
    have hp := coverMap_of M (alternatingGenerator a r m hm) (Sum.inl b)
    have hh := congrArg (fun g : polygonAlternatingGroup a (m+1) =>
      (g.val.val (i j,translate a (u j) x.val)).2) hp
    exact hh.symm.trans he
  have heq : SlotMap a (m+1) V (fun j => (k j,u j))=
      SlotMap a (m+1) V (fun j => (k j,v j)) := by
    funext p
    exact congrArg (fun z => (k p.1,z)) (hspatial p.1 p.2)
  have hk' : Function.Injective (SlotMap a (m+1) V (fun j => (k j,u j))) := by
    rw [heq]; exact hk
  have htr' : ∀ (j : Fin 5) (x : V.val),
      (coverMap M (alternatingGenerator a r m hm) (PresentedGroup.of (Sum.inl b))).val.val
        (i j,translate a (u j) x.val)=(k j,translate a (u j) x.val) := by
    intro j x
    exact (htr j x).trans (congrArg (fun z => (k j,z)) (hspatial j x).symm)
  have ht := B.slotStar_aligned_transport hlarge h hr R hR hwide V i k u hi hk'
    b.2.val.support b.2.property.2 (PresentedGroup.of (Sum.inl b))
    (B.initial_input_mem_polygonStars hlarge h hr b)
    (alignedGroup_input B.t _ _ b (Finset.Subset.refl _)) htr'
  exact ht.trans (B.slotStar_parameterwise hlarge h hr R hR hwide V k k u v hk' hk
    (fun j x => congrArg (fun z => (k j,z)) (hspatial j x)))

theorem uniformSlotTransport_lattice
    (k₀ : Multiplicative (FreeAbelianGroup (Fin m × Fin 2))) :
    B.UniformSlotTransport hlarge h hr hwide (B.t k₀) := by
  intro V i k u v htr hi hk
  let d := sourceLatticeOffsets m (Multiplicative.toAdd k₀)
  let u' := fun j => d (i j)+u j
  have hi' := SlotMap_shift_injective V i u hi d
  have ht := B.slotStar_translation_lattice hlarge h hr R hR hwide
    (Multiplicative.toAdd k₀) V i u hi
  apply ht.trans
  apply B.slotStar_parameterwise hlarge h hr R hR hwide V i k u' v hi' hk
  intro j x
  have he := htr j x
  rw [show coverMap M (alternatingGenerator a r m hm) (B.t k₀)=sourceLatticeMap a r m hm k₀ from
    DFunLike.congr_fun B.t_projection k₀] at he
  change (sourceLatticeFullMap a r m hm k₀).val (i j,translate a (u j) x.val)=_ at he
  have hp := congrArg (fun g : polygonFullGroup a (m+1) =>
    g.val (i j,translate a (u j) x.val))
      (sourceLatticeFullMap_offsets a r m hm (Multiplicative.toAdd k₀))
  have hh := hp.symm.trans he
  change (i j,translate a (d (i j)) (translate a (u j) x.val))=_ at hh
  simpa only [u',translate_add] using hh

theorem uniformSlotTransport_all
    (z : BoundedRelationCover M (alternatingGenerator a r m hm)) :
    B.UniformSlotTransport hlarge h hr hwide z := by
  change z ∈ B.slotTransportSubgroup hlarge h hr hwide R hR
  apply PresentedGroup.generated_by _ (B.slotTransportSubgroup hlarge h hr hwide R hR) _ z
  intro j
  cases j with
  | inl b => exact B.uniformSlotTransport_initial hlarge h hr R hR hwide b
  | inr k =>
    have he := B.uniformSlotTransport_lattice hlarge h hr R hR hwide
      (Multiplicative.ofAdd (FreeAbelianGroup.of k))
    rw [B.t_base] at he
    exact he

include hlarge h hr hwide

theorem coverMap_kernel_central_oai :
    (coverMap M (alternatingGenerator a r m hm)).ker ≤
      Subgroup.center (BoundedRelationCover M (alternatingGenerator a r m hm)) := by
  intro w hw
  have hw' : coverMap M (alternatingGenerator a r m hm) w=1 := hw
  have hc : ∀ z∈ B.slotGroup hlarge h hr hwide, Commute w z := by
    intro z hz
    induction hz using Subgroup.closure_induction with
    | mem z hz =>
      obtain ⟨V,i,u,hi,s,rfl⟩ := hz
      have he := B.uniformSlotTransport_all hlarge h hr R hR hwide w V i i u u
        (by intro j x; rw [hw']; rfl) hi hi
      have hh := DFunLike.congr_fun he s
      change w*B.slotStar hlarge h hr hwide V i u hi s*w⁻¹=
        B.slotStar hlarge h hr hwide V i u hi s at hh
      exact mul_inv_eq_iff_eq_mul.mp hh
    | one => exact Commute.one_right w
    | mul x y _ _ hx hy => exact hx.mul_right hy
    | inv x _ hx => exact hx.inv_right
  rw [Subgroup.mem_center_iff]
  intro z
  have hh : z∈B.slotGroup hlarge h hr hwide := by
    rw [B.slotGroup_eq_top hlarge h hr R hR hwide]
    trivial
  exact (hc z hh).eq.symm

end InitialCoverSystem
end WholeCoverCentrality

end SimpleAmenable
end
end

end OAI
end

theorem solution : type_of% @OAI.SimpleAmenable.InitialCoverSystem.coverMap_kernel_central_oai := @OAI.SimpleAmenable.InitialCoverSystem.coverMap_kernel_central_oai
