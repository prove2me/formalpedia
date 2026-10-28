-- Prove2me | solution 1 for OAI.SimpleAmenable.InitialCoverSystem.growth_axis_law_of_anchor
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T03:54:28.722218+00:00
-- url     : https://prove2.me/submissions/06ceb356-4076-4109-86de-48c1286b809e

import Mathlib
import Definitions.Def_OAIQ65Sa008
import Definitions.Def_OAIQ65Sa009

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_PairLawAssembly
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.TranslationFiltered.regular_filtered
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
section PairLawAssembly
variable {G E ι : Type*} [Group G] [Group E]

variable [Fintype ι]
variable (A B : ι → Subgroup G) (h : ∀ i, CommutingFactors (A i) (B i))
    (hz : Subgroup.center G = ⊥)

theorem range_comp_subset {X Y Z : Type*} [Group X] [Group Y] [Group Z]
    (f : Y →* Z) (g : X →* Y) : (f.comp g).range ≤ f.range := by
  rintro y ⟨x, rfl⟩
  exact ⟨g x, rfl⟩

end PairLawAssembly

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_SectorControl
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

section AlphabetInclusion

variable {α : Type*} [Fintype α] [DecidableEq α]

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)

theorem primitiveFamily_range_inclusion {ι : Type*} {I J : Finset (Fin (m+1))} (hIJ : I ⊆ J)
    (b c : Fin (m+1)) (hb : b ∉ I) (hc : c ∉ J)
    (P : ι → Fin 5 × (CutRing × CutRing)) :
    (copyFamilyEval (B.primitiveFamily I b hb P)).range ≤
      (copyFamilyEval (B.primitiveFamily J c hc P)).range := by
  rw [copyFamilyEval_range,copyFamilyEval_range]
  apply iSup_le
  intro i x hx
  obtain ⟨s,rfl⟩ := hx
  apply le_iSup (fun z => (B.primitiveFamily J c hc P z).range) i
  exact ⟨subalphabetHom hIJ s,DFunLike.congr_fun (B.primitiveFamily_inclusion hIJ b c hb hc P i) s⟩

end InitialCoverSystem
end AlphabetInclusion

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_WindowSubfamilies
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

section CircularIntervals

theorem coordinateInterval_mono {a : ℕ} (j : Fin 2) (u v u' v' : CutRing)
    (hu : ordinary u' ≤ ordinary u) (huv : ordinary u ≤ ordinary v)
    (hv : ordinary v ≤ ordinary v') (hlen : ordinary v'-ordinary u' < 1) :
    coordinateInterval a j u v ≤ coordinateInterval a j u' v' := by
  intro p hp
  obtain ⟨k,hk⟩ := (mem_coordinateBetween_iff j u v huv (by linarith) p).mp hp
  exact (mem_coordinateBetween_iff j u' v' (by linarith) hlen p).mpr
    ⟨k,hu.trans hk.1,hk.2.trans_le hv⟩

end CircularIntervals

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_WindowCells
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.SimpleAmenable.instCountableCutRing _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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
section WindowCells

attribute [local instance] cutOrdinaryOrder

theorem windowInterior_zero (n : ℕ) (hn : 0 < n) :
    windowInterior n ⟨0,hn⟩ = 0 := by
  have hmem : (0:CutRing) ∈ windowEndpointSet n := by
    apply Finset.mem_image.mpr
    exact ⟨⟨0,hn⟩,Finset.mem_univ _,by simp⟩
  have hrange := Finset.range_orderEmbOfFin (windowEndpointSet n) (windowEndpointSet_card n)
  have hx : (0:CutRing) ∈ Set.range (windowInterior n) := by
    change (0:CutRing) ∈ Set.range ((windowEndpointSet n).orderEmbOfFin (windowEndpointSet_card n))
    rw [hrange]; exact hmem
  obtain ⟨i,hi⟩ := hx
  apply ordinary_injective
  have hle := (windowInterior n).monotone (show (⟨0,hn⟩:Fin n) ≤ i by exact Nat.zero_le _)
  change ordinary (windowInterior n ⟨0,hn⟩) ≤ ordinary (windowInterior n i) at hle
  rw [hi,map_zero] at hle
  rw [map_zero]
  exact le_antisymm hle (windowInterior_bounds n ⟨0,hn⟩).1

theorem windowCut_zero (n : ℕ) (q : ℤ) (hn : 0 < n) :
    windowCut n q 0 = (q:CutRing)*cutTau := by
  simp only [windowCut,Fin.val_zero,dite_eq_left hn,windowInterior_zero n hn,add_zero]

theorem windowCut_last (n : ℕ) (q : ℤ) :
    windowCut n q (Fin.last n) = (q:CutRing)*cutTau+1 := by
  simp [windowCut]

end WindowCells

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_WindowCellPartition
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
section WindowCellPartition

theorem finite_interval_cell {n : ℕ} {x : Fin (n+1) → ℝ}
    (_hn : 1 ≤ n) (t : ℝ) (hl : x 0 ≤ t) (hu : t < x (Fin.last n)) :
    ∃ i : Fin n, x i.castSucc ≤ t ∧ t < x i.succ := by
  classical
  let S : Finset (Fin (n+1)) := Finset.univ.filter fun i => x i ≤ t
  have hS : S.Nonempty := ⟨0,by simpa only [S,Finset.mem_filter,Finset.mem_univ,true_and] using hl⟩
  let i := S.max' hS
  have hi : x i ≤ t := (Finset.mem_filter.mp (Finset.max'_mem S hS)).2
  have hin : i.val < n := by
    have hil : i.val ≤ n := Nat.le_of_lt_succ i.isLt
    by_contra hh
    have he : i = Fin.last n := Fin.ext (by change i.val = n; omega)
    rw [he] at hi
    linarith
  refine ⟨⟨i.val,hin⟩,hi,?_⟩
  by_contra hh
  have hj : (⟨i.val+1,by omega⟩ : Fin (n+1)) ∈ S := by
    simp only [S,Finset.mem_filter,Finset.mem_univ,true_and]
    exact le_of_not_gt hh
  have he := Finset.le_max' S _ hj
  change i.val+1 ≤ i.val at he
  omega

theorem liftedCoordinate_bounds {a : ℕ} (j : Fin 2) (z : CutRing) (p : GenericSquare a) :
    ordinary z ≤ liftedCoordinate j z p ∧ liftedCoordinate j z p < ordinary z+1 := by
  have hh := Int.fract_nonneg (coordinate j p-ordinary z)
  have hh' := Int.fract_lt_one (coordinate j p-ordinary z)
  simp only [Int.fract,liftedCoordinate] at *
  constructor <;> linarith

theorem windowCell_mem {a : ℕ} (j : Fin 2) (n : ℕ) (hn : 201 ≤ n) (q : ℤ)
    (i : Fin n) (p : GenericSquare a) :
    p ∈ (windowCell a j n q i).val ↔
      ordinary (windowCut n q i.castSucc) ≤ liftedCoordinate j ((q:CutRing)*cutTau) p ∧
      liftedCoordinate j ((q:CutRing)*cutTau) p < ordinary (windowCut n q i.succ) := by
  have hn' : (200:ℝ) < n := by exact_mod_cast (by omega : 200 < n)
  have hlen : ordinary (windowCut n q i.succ)-ordinary (windowCut n q i.castSucc) < 1 :=
    (windowCut_mesh n q i).trans_lt ((div_lt_one (by linarith)).mpr hn')
  have hord := (windowCut_strictMono n q (Fin.castSucc_lt_succ (i := i))).le
  change p ∈ coordinateBetween _ _ _ _ ↔ _
  rw [mem_coordinateBetween_iff j _ _ hord hlen p]
  constructor
  · rintro ⟨k,hk,hk'⟩
    have hb := windowCut_bounds n q i.castSucc
    have hb' := windowCut_bounds n q i.succ
    have hfloor : (⌊coordinate j p-ordinary ((q:CutRing)*cutTau)⌋:ℤ) = -k := by
      apply Int.floor_eq_iff.mpr
      simp only [Int.cast_neg]
      constructor <;> linarith
    simp only [liftedCoordinate,hfloor,Int.cast_neg,sub_neg_eq_add]
    exact ⟨hk,hk'⟩
  · rintro ⟨hl,hu⟩
    refine ⟨-⌊coordinate j p-ordinary ((q:CutRing)*cutTau)⌋,?_,?_⟩
    · simpa only [Int.cast_neg,sub_eq_add_neg,liftedCoordinate] using hl
    · simpa only [Int.cast_neg,sub_eq_add_neg,liftedCoordinate] using hu

theorem windowCell_cover {a : ℕ} (j : Fin 2) (n : ℕ) (hn : 201 ≤ n) (q : ℤ)
    (p : GenericSquare a) : ∃ i : Fin n, p ∈ (windowCell a j n q i).val := by
  have hb := liftedCoordinate_bounds j ((q:CutRing)*cutTau) p
  have hz := windowCut_zero n q (by omega)
  have hh := windowCut_last n q
  obtain ⟨i,hi⟩ := finite_interval_cell (x := fun i => ordinary (windowCut n q i))
    (by omega) (liftedCoordinate j ((q:CutRing)*cutTau) p)
    (by simpa only [hz] using hb.1) (by simpa only [hh,map_add,map_one] using hb.2)
  exact ⟨i,(windowCell_mem j n hn q i p).mpr hi⟩

theorem windowCell_pairwise_disjoint {a : ℕ} (j : Fin 2) (n : ℕ) (hn : 201 ≤ n) (q : ℤ) :
    Pairwise fun i k : Fin n => Disjoint (windowCell a j n q i).val (windowCell a j n q k).val := by
  intro i k hik
  apply Set.disjoint_left.mpr
  intro p hp hp'
  have hi := (windowCell_mem j n hn q i p).mp hp
  have hk := (windowCell_mem j n hn q k p).mp hp'
  rcases lt_or_gt_of_ne hik with hh | hh
  · have he := (windowCut_strictMono n q).monotone
      (show i.succ ≤ k.castSucc from by change i.val+1 ≤ k.val; change i.val < k.val at hh; omega)
    linarith
  · have he := (windowCut_strictMono n q).monotone
      (show k.succ ≤ i.castSucc from by change k.val+1 ≤ i.val; change k.val < i.val at hh; omega)
    linarith

end WindowCellPartition

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_CellGeometry
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
section CellGeometry

theorem windowCell_axis_resolved {a : ℕ} {r : CutRing} (j : Fin 2) (n : ℕ) (hn : 0 < n) (q : ℤ) (i : Fin n) :
    ResolvedBy (fun z => (InitialCoverSystem.primitiveTests (a := a) (r := r)
      (axisWindowPrimitives j n q) z).val) (windowCell a j n q i).val :=
  axisInterval_resolved j n q _ _ (windowCut_label n q hn i.castSucc) (windowCut_label n q hn i.succ)

end CellGeometry

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_FiniteSectorPartition
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
section FiniteSectorPartition
namespace ActualLawfulTable
variable {E H Q Ω κ : Type*} [Group E] [Group H] [Group Q] [Group.IsPerfect E]
    {q : H →* Q} {v : (Ω → E) →* Q} (T : ActualLawfulTable q v)

theorem sector_range_le_biUnion (W : κ → Set Ω) (S : Finset κ)
    (hdisjoint : Pairwise fun i j => Disjoint (W i) (W j)) (K : Subgroup H)
    (hK : ∀ i ∈ S, (T.sector (W i)).range ≤ K) :
    (T.sector (⋃ i ∈ S, W i)).range ≤ K := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    have hd : Disjoint (W i) (⋃ j ∈ S, W j) := by
      apply Set.disjoint_iUnion_right.mpr
      intro j
      apply Set.disjoint_iUnion_right.mpr
      intro hj
      exact hdisjoint (by intro he; subst j; exact hi hj)
    have he : (⋃ j ∈ insert i S, W j) = W i ∪ ⋃ j ∈ S, W j := by
      ext x
      simp only [Set.mem_iUnion,Finset.mem_insert,Set.mem_union]
      constructor
      · rintro ⟨j,(rfl|hj),hx⟩
        · exact Or.inl hx
        · exact Or.inr ⟨j,hj,hx⟩
      · rintro (hx|⟨j,hj,hx⟩)
        · exact ⟨i,Or.inl rfl,hx⟩
        · exact ⟨j,Or.inr hj,hx⟩
    rw [he,T.sector_union hd]
    rintro x ⟨s,rfl⟩
    exact K.mul_mem (hK i (Finset.mem_insert_self i S) ⟨s,rfl⟩)
      (ih (fun j hj => hK j (Finset.mem_insert_of_mem hj)) ⟨s,rfl⟩)

theorem sector_range_le_partition [Fintype κ] (W : κ → Set Ω) (V : Set Ω)
    (hdisjoint : Pairwise fun i j => Disjoint (W i) (W j))
    (hcover : ∀ ω, ω ∈ V ↔ ∃ i, ω ∈ W i) :
    (T.sector V).range ≤ ⨆ i, (T.sector (W i)).range := by
  have he : V = ⋃ i ∈ (Finset.univ : Finset κ), W i := by
    ext ω
    simpa only [Set.mem_iUnion,Finset.mem_univ,exists_true_left] using hcover ω
  rw [he]
  exact T.sector_range_le_biUnion W Finset.univ hdisjoint _
    (fun i _ => le_iSup (fun j => (T.sector (W j)).range) i)

end ActualLawfulTable

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M) {ι κ : Type*} [Finite ι] [Fintype κ]
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem fullGeometricSector_partition_range (hlarge : 15 < m+1)
    (P : ι → Fin 5 × (CutRing × CutRing))
    (h : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb P)
    (V : polygonAlgebra a) (W : κ → polygonAlgebra a)
    (hW : ∀ i, ResolvedBy (fun z => (primitiveTests (a := a) (r := r) P z).val) (W i).val)
    (hdisjoint : Pairwise fun i j => Disjoint (W i).val (W j).val)
    (hcover : ∀ p, p ∈ V.val ↔ ∃ i, p ∈ (W i).val) :
    (B.fullGeometricSector hlarge P h V).range ≤
      ⨆ i, (B.fullGeometricSector hlarge P h (W i)).range := by
  apply (B.fullPrimitiveTable hlarge P h).sector_range_le_partition
  · intro i j hij
    exact resolvedPolygonMask_disjoint _ (hW i) (hdisjoint hij)
  · intro ω
    constructor
    · rintro ⟨p,hp,hpV⟩
      obtain ⟨i,hi⟩ := (hcover p).mp hpV
      exact ⟨i,p,hp,hi⟩
    · rintro ⟨i,p,hp,hi⟩
      exact ⟨p,hp,(hcover p).mpr ⟨i,hi⟩⟩

end InitialCoverSystem

end FiniteSectorPartition

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_AxisCutSequences
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
section AxisCutSequences

namespace AxisCutSequence
variable {n K : ℕ} (D : AxisCutSequence n K)

variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (hlarge : 15 < m+1) (g : B.CoordinateWindowLaw n) (d : Fin 2)

theorem prefix_last : D.prefixCopy B hlarge g d K = D.anchorCopy B hlarge g d := by
  have hi : D.index K = Fin.last K := by ext; simp [index]
  simp only [prefixCopy,hi]
  exact (D.anchorCopy_eq B hlarge g d (Fin.last K)).symm

end AxisCutSequence
end AxisCutSequences

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_SortedAxisCuts
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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
section SortedAxisCuts
attribute [local instance] cutOrdinaryOrder

theorem labelLift_eq (u z : CutRing) (hz : ordinary u ≤ ordinary z ∧ ordinary z < ordinary u+1) :
    labelLift u (endpointLabel z)=z := by
  have hc : cutFraction (((endpointLabel z:CutRing)*cutTau)-u) = cutFraction (z-u) := by
    rw [cutFraction_label (((endpointLabel z:CutRing)*cutTau)-u),cutFraction_label (z-u)]
    simp only [endpointLabel_sub,endpointLabel_labelTau]
  rw [labelLift,hc,cutFraction_eq_self (z-u) (by simp only [map_sub]; constructor <;> linarith)]
  ring

theorem mem_anchorCutSet (N : ℕ) (p : ℤ) (u v z : CutRing)
    (hl : p ≤ endpointLabel z ∧ endpointLabel z < p+N)
    (hz : ordinary u ≤ ordinary z ∧ ordinary z ≤ ordinary v)
    (hlen : ordinary v-ordinary u < 1) : z ∈ anchorCutSet N p u v := by
  classical
  apply Finset.mem_insert_of_mem
  apply Finset.mem_insert_of_mem
  apply Finset.mem_filter.mpr
  refine ⟨?_,hz.2⟩
  have hn : (endpointLabel z-p).toNat < N := by omega
  apply Finset.mem_image.mpr
  refine ⟨⟨(endpointLabel z-p).toNat,hn⟩,Finset.mem_univ _,?_⟩
  have hh : p+(((endpointLabel z-p).toNat:ℕ):ℤ) = endpointLabel z := by omega
  rw [hh]
  exact labelLift_eq u z ⟨hz.1,by linarith⟩

end SortedAxisCuts

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_AxisAnchorFamily
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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
section AxisAnchorFamily

namespace AxisAnchorFamily
variable {n l : ℕ} {q : ℤ} (A : AxisAnchorFamily n l q)

variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (hlarge : 15 < m+1) (g : B.CoordinateWindowLaw n)
    (d : Fin 2) (hl : 201 ≤ l) (hln : l ≤ n)

include hl in
theorem anchorCopy_eq_cell (i : Fin l) :
    (A.cuts i).anchorCopy B hlarge g d = B.axisSector hlarge n g d l hln q (windowCell a d l q i) := by
  change B.axisSector hlarge n g d _ _ _ (coordinateInterval a d _ _) =
    B.axisSector hlarge n g d l hln q (coordinateInterval a d _ _)
  rw [← A.lower,← A.upper]
  apply B.axisInterval_copy_eq
  · exact (A.cuts i).lower_label 0
  · exact (A.cuts i).upper_label 0
  · rw [A.lower]; exact windowCut_label l q (by omega) _
  · rw [A.upper]; exact windowCut_label l q (by omega) _

end AxisAnchorFamily
end AxisAnchorFamily

section GrowthAnchors
attribute [local instance] cutOrdinaryOrder

namespace growthAnchorFamily
variable (n : ℕ) (hn : 1005 ≤ n) (p : ℤ)
local notation "A" => growthAnchorFamily n hn p

theorem mem (i : Fin (growthAnchorLength n)) (j : Fin ((A).count i+1)) :
    ((A).cuts i).cut j ∈ anchorCutSet (growthNewLength n) p
      (windowCut (growthAnchorLength n) (growthAnchorStart n p) i.castSucc)
      (windowCut (growthAnchorLength n) (growthAnchorStart n p) i.succ) :=
  Finset.orderEmbOfFin_mem _ _ j

theorem range (i : Fin (growthAnchorLength n)) :
    Set.range ((A).cuts i).cut = (anchorCutSet (growthNewLength n) p
      (windowCut (growthAnchorLength n) (growthAnchorStart n p) i.castSucc)
      (windowCut (growthAnchorLength n) (growthAnchorStart n p) i.succ) : Set CutRing) :=
  Finset.range_orderEmbOfFin _ _

theorem labels (i : Fin (growthAnchorLength n)) (j : Fin ((A).count i+1)) :
    p ≤ endpointLabel (((A).cuts i).cut j) ∧ endpointLabel (((A).cuts i).cut j) < p+growthNewLength n := by
  apply anchorCutSet_labels _ _ _ _ ?_ ?_ _ (mem n hn p i j)
  · have hh := growth_anchor_label hn p i.castSucc
    have hlens := growth_lengths hn
    constructor <;> omega
  · have hh := growth_anchor_label hn p i.succ
    have hlens := growth_lengths hn
    constructor <;> omega

end growthAnchorFamily
end GrowthAnchors

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_ClippedIntervals
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
section ClippedIntervals
attribute [local instance] cutOrdinaryOrder

theorem coordinateInterval_mem_lifted {a : ℕ} (d : Fin 2) (b u v : CutRing)
    (hbu : ordinary b ≤ ordinary u) (huv : ordinary u ≤ ordinary v)
    (hvb : ordinary v < ordinary b+1) (x : GenericSquare a) :
    x ∈ (coordinateInterval a d u v).val ↔
      ordinary u ≤ liftedCoordinate d b x ∧ liftedCoordinate d b x < ordinary v := by
  change x ∈ coordinateBetween a d u v ↔ _
  rw [mem_coordinateBetween_iff d u v huv (by linarith) x]
  constructor
  · rintro ⟨k,hk,hk'⟩
    have hf : (⌊coordinate d x-ordinary b⌋:ℤ) = -k := by
      apply Int.floor_eq_iff.mpr
      simp only [Int.cast_neg]
      constructor <;> linarith
    simp only [liftedCoordinate,hf,Int.cast_neg,sub_neg_eq_add]
    exact ⟨hk,hk'⟩
  · rintro ⟨hk,hk'⟩
    refine ⟨-⌊coordinate d x-ordinary b⌋,?_,?_⟩
    · simpa only [liftedCoordinate,Int.cast_neg,sub_eq_add_neg] using hk
    · simpa only [liftedCoordinate,Int.cast_neg,sub_eq_add_neg] using hk'

theorem coordinateInterval_prefix_difference {a : ℕ} (d : Fin 2) (b u v : CutRing)
    (hbu : ordinary b ≤ ordinary u) (huv : ordinary u ≤ ordinary v)
    (hvb : ordinary v < ordinary b+1) :
    coordinateInterval a d u v = coordinateInterval a d b v \ coordinateInterval a d b u := by
  apply Subtype.ext
  ext x
  change x ∈ (coordinateInterval a d u v).val ↔
    x ∈ (coordinateInterval a d b v).val ∧ x ∉ (coordinateInterval a d b u).val
  rw [coordinateInterval_mem_lifted d b u v hbu huv hvb,
    coordinateInterval_mem_lifted d b b v le_rfl (hbu.trans huv) hvb,
    coordinateInterval_mem_lifted d b b u le_rfl hbu (by linarith)]
  have hb := (liftedCoordinate_bounds d b x).1
  constructor
  · rintro ⟨h,h'⟩; exact ⟨⟨hb,h'⟩,by rintro ⟨_,h''⟩; linarith⟩
  · rintro ⟨⟨_,h'⟩,h⟩; exact ⟨by by_contra hh; exact h ⟨hb,lt_of_not_ge hh⟩,h'⟩

theorem coordinateInterval_prefix_clip {a : ℕ} (d : Fin 2) (u v z : CutRing)
    (huv : ordinary u ≤ ordinary v) (hv : ordinary v < ordinary u+1)
    (huz : ordinary u ≤ ordinary z) (hz : ordinary z < ordinary u+1) :
    coordinateInterval a d u v ⊓ coordinateInterval a d u z = coordinateInterval a d u (min v z) := by
  by_cases h : ordinary v ≤ ordinary z
  · have hh : v ≤ z := h
    rw [min_eq_left hh]
    exact inf_eq_left.mpr (coordinateInterval_mono d u v u z le_rfl huv h (by linarith))
  · have hh : z ≤ v := le_of_not_ge h
    rw [min_eq_right hh]
    exact inf_eq_right.mpr (coordinateInterval_mono d u z u v le_rfl huz hh (by linarith))

theorem coordinateInterval_label_eq {a : ℕ} (d : Fin 2) (u v u' v' : CutRing)
    (hu : endpointLabel u=endpointLabel u') (hv : endpointLabel v=endpointLabel v') :
    coordinateInterval a d u v = coordinateInterval a d u' v' := by
  have hu' : u = u'+((u.re-u'.re:ℤ):CutRing) := by
    apply QuadraticAlgebra.ext <;> simp [show u.im = u'.im from hu]
  have hv' : v = v'+((v.re-v'.re:ℤ):CutRing) := by
    apply QuadraticAlgebra.ext <;> simp [show v.im = v'.im from hv]
  apply Subtype.ext
  change coordinateBetween a d u v = coordinateBetween a d u' v'
  rw [hu',hv',coordinateBetween_period]

theorem clippedLabel_bounds (u v : CutRing) (q : ℤ) (huv : ordinary u ≤ ordinary v) :
    ordinary u ≤ ordinary (clippedLabel u v q) ∧ ordinary (clippedLabel u v q) ≤ ordinary v := by
  change u ≤ min v (labelLift u q) ∧ min v (labelLift u q) ≤ v
  exact ⟨le_min huv (labelLift_bounds u q).1,min_le_left _ _⟩

theorem clippedLabel_label (u v : CutRing) (q : ℤ) :
    endpointLabel (clippedLabel u v q)=endpointLabel v ∨ endpointLabel (clippedLabel u v q)=q := by
  unfold clippedLabel
  rcases le_total v (labelLift u q) with h|h
  · rw [min_eq_left h]; exact Or.inl rfl
  · rw [min_eq_right h]; exact Or.inr (endpointLabel_labelLift u q)

theorem clippedLabel_mem (N : ℕ) (p : ℤ) (u v : CutRing) (q : ℤ)
    (huv : ordinary u ≤ ordinary v) (hlen : ordinary v-ordinary u < 1)
    (hv : p ≤ endpointLabel v ∧ endpointLabel v < p+N)
    (hq : p ≤ q ∧ q < p+N) : clippedLabel u v q ∈ anchorCutSet N p u v := by
  apply mem_anchorCutSet N p u v _ ?_ (clippedLabel_bounds u v q huv) hlen
  rcases clippedLabel_label u v q with h|h <;> rw [h] <;> assumption

theorem coordinateInterval_anchor_formula {a : ℕ} (d : Fin 2) (u v s t : CutRing)
    (huv : ordinary u ≤ ordinary v) (hlen : ordinary v-ordinary u < 1) :
    coordinateInterval a d u v ⊓ coordinateInterval a d s t =
      if ordinary (labelLift u (endpointLabel s)) ≤ ordinary (labelLift u (endpointLabel t)) then
        coordinateInterval a d u (clippedLabel u v (endpointLabel t)) \
          coordinateInterval a d u (clippedLabel u v (endpointLabel s))
      else coordinateInterval a d u v \ (coordinateInterval a d u (clippedLabel u v (endpointLabel s)) \
          coordinateInterval a d u (clippedLabel u v (endpointLabel t))) := by
  let s' := labelLift u (endpointLabel s)
  let t' := labelLift u (endpointLabel t)
  have hs := labelLift_bounds u (endpointLabel s)
  have ht := labelLift_bounds u (endpointLabel t)
  rw [coordinateInterval_label_eq d s t s' t' (by simp [s']) (by simp [t'])]
  split_ifs with h
  · rw [coordinateInterval_prefix_difference d u s' t' hs.1 h ht.2]
    have hset : ∀ (A B C : polygonAlgebra a), A ⊓ (B \ C) = (A ⊓ B) \ (A ⊓ C) := by
      intro A B C; apply Subtype.ext; ext x; change _ ∧ (_ ∧ ¬_) ↔ (_ ∧ _) ∧ ¬(_ ∧ _); tauto
    rw [hset,coordinateInterval_prefix_clip d u v t' huv (by linarith) ht.1 ht.2,
      coordinateInterval_prefix_clip d u v s' huv (by linarith) hs.1 hs.2]
    rfl
  · have hts : ordinary t' < ordinary s' := lt_of_not_ge h
    have he : coordinateInterval a d s' t' = (coordinateInterval a d t' s')ᶜ := by
      apply Subtype.ext
      exact coordinateBetween_reverse d t' s' (by
        rw [map_sub,Int.fract_eq_self.mpr ⟨by linarith,by linarith⟩]; linarith)
    rw [he,coordinateInterval_prefix_difference d u t' s' ht.1 hts.le hs.2]
    have hset : ∀ (A B C : polygonAlgebra a), A ⊓ (B \ C)ᶜ = A \ ((A ⊓ B) \ (A ⊓ C)) := by
      intro A B C; apply Subtype.ext; ext x; change _ ∧ ¬(_ ∧ ¬_) ↔ _ ∧ ¬((_ ∧ _) ∧ ¬(_ ∧ _)); tauto
    rw [hset,coordinateInterval_prefix_clip d u v s' huv (by linarith) hs.1 hs.2,
      coordinateInterval_prefix_clip d u v t' huv (by linarith) ht.1 ht.2]
    rfl

end ClippedIntervals

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_SectorDifferenceRange
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
section SectorDifferenceRange
namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M) {ι : Type*} [Finite ι]
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem fullGeometricSector_sdiff_range (hlarge : 15 < m+1)
    (P : ι → Fin 5 × (CutRing × CutRing))
    (h : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb P)
    (V W : polygonAlgebra a) (hWV : W ≤ V)
    (hW : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) P i).val) W.val)
    (K : Subgroup (BoundedRelationCover M (alternatingGenerator a r m hm)))
    (hV : (B.fullGeometricSector hlarge P h V).range ≤ K)
    (hW' : (B.fullGeometricSector hlarge P h W).range ≤ K) :
    (B.fullGeometricSector hlarge P h (V \ W)).range ≤ K := by
  have he : W ⊔ (V \ W) = V := by
    apply Subtype.ext
    ext x
    change (x ∈ W.val ∨ x ∈ V.val ∧ x ∉ W.val) ↔ x ∈ V.val
    constructor
    · rintro (hx|hx); exact hWV hx; exact hx.1
    · intro hx; by_cases hh : x ∈ W.val; exact Or.inl hh; exact Or.inr ⟨hx,hh⟩
  have hd : Disjoint W.val (V \ W).val := Set.disjoint_left.mpr (by rintro x hx ⟨_,h⟩; exact h hx)
  rintro x ⟨s,rfl⟩
  have hh := B.fullGeometricSector_union hlarge P h W (V \ W) hW hd s
  rw [he] at hh
  have hm := K.mul_mem (K.inv_mem (hW' ⟨s,rfl⟩)) (hV ⟨s,rfl⟩)
  rw [hh,inv_mul_cancel_left] at hm
  exact hm

end InitialCoverSystem
end SectorDifferenceRange

section AnchorIntersectionRange
attribute [local instance] cutOrdinaryOrder
namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem axisSector_anchor_intersection_range (hlarge : 15 < m+1) (n : ℕ) (g : B.CoordinateWindowLaw n)
    (d : Fin 2) (k : ℕ) (hk : k ≤ n) (p : ℤ) (u v s t : CutRing)
    (huv : ordinary u ≤ ordinary v) (hlen : ordinary v-ordinary u < 1)
    (hu : p ≤ endpointLabel u ∧ endpointLabel u < p+k)
    (hv : p ≤ endpointLabel v ∧ endpointLabel v < p+k)
    (hs : p ≤ endpointLabel s ∧ endpointLabel s < p+k)
    (ht : p ≤ endpointLabel t ∧ endpointLabel t < p+k)
    (K : Subgroup (BoundedRelationCover M (alternatingGenerator a r m hm)))
    (hU : (B.axisSector hlarge n g d k hk p (coordinateInterval a d u v)).range ≤ K)
    (hS : (B.axisSector hlarge n g d k hk p
      (coordinateInterval a d u (clippedLabel u v (endpointLabel s)))).range ≤ K)
    (hT : (B.axisSector hlarge n g d k hk p
      (coordinateInterval a d u (clippedLabel u v (endpointLabel t)))).range ≤ K) :
    (B.axisSector hlarge n g d k hk p
      (coordinateInterval a d u v ⊓ coordinateInterval a d s t)).range ≤ K := by
  let S := coordinateInterval a d u (clippedLabel u v (endpointLabel s))
  let T := coordinateInterval a d u (clippedLabel u v (endpointLabel t))
  have hsl : p ≤ endpointLabel (clippedLabel u v (endpointLabel s)) ∧
      endpointLabel (clippedLabel u v (endpointLabel s)) < p+k := by
    rcases clippedLabel_label u v (endpointLabel s) with h|h <;> rw [h] <;> assumption
  have htl : p ≤ endpointLabel (clippedLabel u v (endpointLabel t)) ∧
      endpointLabel (clippedLabel u v (endpointLabel t)) < p+k := by
    rcases clippedLabel_label u v (endpointLabel t) with h|h <;> rw [h] <;> assumption
  have hSr := axisInterval_resolved (a := a) (r := r) d k p u _ hu hsl
  have hTr := axisInterval_resolved (a := a) (r := r) d k p u _ hu htl
  have hSb := clippedLabel_bounds u v (endpointLabel s) huv
  have hTb := clippedLabel_bounds u v (endpointLabel t) huv
  rw [coordinateInterval_anchor_formula d u v s t huv hlen]
  split_ifs with h
  · apply B.fullGeometricSector_sdiff_range hlarge _ _ T S ?_ hSr K hT hS
    apply coordinateInterval_mono d _ _ _ _ le_rfl hSb.1 ?_ (by linarith)
    exact min_le_min_left v h
  · have hST : T ≤ S := by
      apply coordinateInterval_mono d _ _ _ _ le_rfl hTb.1 ?_ (by linarith)
      exact min_le_min_left v (le_of_not_ge h)
    have hdiff : (B.axisSector hlarge n g d k hk p (S \ T)).range ≤ K :=
      B.fullGeometricSector_sdiff_range hlarge _ _ S T hST hTr K hS hT
    apply B.fullGeometricSector_sdiff_range hlarge _ _ _ (S \ T) ?_ ?_ K hU hdiff
    · exact (sdiff_le : S \ T ≤ S).trans (coordinateInterval_mono d _ _ _ _ le_rfl hSb.1 hSb.2 hlen)
    · exact BooleanSubalgebra.sdiff_mem (L := resolvedAlgebra _) hSr hTr

end InitialCoverSystem
end AnchorIntersectionRange

section AnchorGeneration
namespace AxisAnchorFamily
variable {n l : ℕ} {q : ℤ} (A : AxisAnchorFamily n l q)
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (hlarge : 15 < m+1) (g : B.CoordinateWindowLaw n) (d : Fin 2)

theorem anchor_range_prefixGroup (i : Fin l) :
    ((A.cuts i).anchorCopy B hlarge g d).range ≤ A.prefixGroup B hlarge g d := by
  unfold prefixGroup
  rw [← (A.cuts i).prefix_last B hlarge g d]
  exact (le_iSup (fun j : Fin (A.count i+1) => ((A.cuts i).prefixCopy B hlarge g d j.val).range)
    (Fin.last (A.count i))).trans (le_iSup (fun i : Fin l => ⨆ j : Fin (A.count i+1),
      ((A.cuts i).prefixCopy B hlarge g d j.val).range) i)

theorem interval_prefix_range (i : Fin l) (k : ℕ) (hk : k ≤ n) (p : ℤ) (v : CutRing)
    (hu : p ≤ endpointLabel ((A.cuts i).cut 0) ∧ endpointLabel ((A.cuts i).cut 0) < p+k)
    (hv : p ≤ endpointLabel v ∧ endpointLabel v < p+k)
    (hcut : v ∈ Set.range (A.cuts i).cut) :
    (B.axisSector hlarge n g d k hk p (coordinateInterval a d ((A.cuts i).cut 0) v)).range ≤
      A.prefixGroup B hlarge g d := by
  unfold prefixGroup
  obtain ⟨j,rfl⟩ := hcut
  have he : B.axisSector hlarge n g d k hk p (coordinateInterval a d ((A.cuts i).cut 0) ((A.cuts i).cut j)) =
      (A.cuts i).prefixCopy B hlarge g d j.val := by
    simp only [AxisCutSequence.prefixCopy,AxisCutSequence.index_fin]
    exact B.axisInterval_copy_eq hlarge n g d _ _ _ _ _ _ _ _ hu hv
      ((A.cuts i).lower_label j) ((A.cuts i).cut_label j)
  rw [he]
  exact (le_iSup (fun j : Fin (A.count i+1) => ((A.cuts i).prefixCopy B hlarge g d j.val).range) j).trans
    (le_iSup (fun i : Fin l => ⨆ j : Fin (A.count i+1),
      ((A.cuts i).prefixCopy B hlarge g d j.val).range) i)

theorem old_interval_range (hl : 201 ≤ l) (k : ℕ) (hk : k ≤ n) (p : ℤ) (s t : CutRing)
    (hs : p ≤ endpointLabel s ∧ endpointLabel s < p+k)
    (ht : p ≤ endpointLabel t ∧ endpointLabel t < p+k)
    (hanchor : ∀ j : Fin (l+1), p ≤ endpointLabel (windowCut l q j) ∧ endpointLabel (windowCut l q j) < p+k)
    (hcuts : ∀ i : Fin l, ∀ z ∈ ({s,t} : Finset CutRing),
      clippedLabel ((A.cuts i).cut 0) ((A.cuts i).cut (Fin.last (A.count i))) (endpointLabel z) ∈
        Set.range (A.cuts i).cut) :
    (B.axisSector hlarge n g d k hk p (coordinateInterval a d s t)).range ≤ A.prefixGroup B hlarge g d := by
  classical
  let f : Fin l → polygonAlgebra a := fun i => windowCell a d l q i ⊓ coordinateInterval a d s t
  have hV := axisInterval_resolved (a := a) (r := r) d k p s t hs ht
  have hW (i : Fin l) : ResolvedBy (fun j => (InitialCoverSystem.primitiveTests (a := a) (r := r)
      (axisWindowPrimitives d k p) j).val) (f i).val := by
    exact BooleanSubalgebra.inf_mem (L := resolvedAlgebra _)
      (axisInterval_resolved d k p _ _ (hanchor i.castSucc) (hanchor i.succ)) hV
  apply (B.fullGeometricSector_partition_range hlarge (axisWindowPrimitives d k p)
    (fun I _ b hb => B.axisFamilyLaw n g d k hk p I b hb) _ f hW ?_ ?_).trans
  · apply iSup_le
    intro i
    change (B.axisSector hlarge n g d k hk p (windowCell a d l q i ⊓ coordinateInterval a d s t)).range ≤ _
    have hlu := hanchor i.castSucc
    have hlv := hanchor i.succ
    rw [← A.lower i] at hlu
    rw [← A.upper i] at hlv
    change (B.axisSector hlarge n g d k hk p (coordinateInterval a d _ _ ⊓ _)).range ≤ _
    rw [← A.lower i,← A.upper i]
    apply B.axisSector_anchor_intersection_range hlarge n g d k hk p _ _ s t
      ((A.cuts i).ordered (Fin.last (A.count i))).1 (A.intervalLength hl i) hlu hlv hs ht
    · have he : B.axisSector hlarge n g d k hk p
          (coordinateInterval a d ((A.cuts i).cut 0) ((A.cuts i).cut (Fin.last (A.count i)))) =
          (A.cuts i).anchorCopy B hlarge g d := by
        exact B.axisInterval_copy_eq hlarge n g d _ _ _ _ _ _ _ _ hlu hlv
          ((A.cuts i).lower_label 0) ((A.cuts i).upper_label 0)
      rw [he]
      exact A.anchor_range_prefixGroup B hlarge g d i
    · apply A.interval_prefix_range B hlarge g d i k hk p _ hlu ?_ (hcuts i s (by simp))
      rcases clippedLabel_label ((A.cuts i).cut 0) ((A.cuts i).cut (Fin.last (A.count i))) (endpointLabel s) with h|h
      · rw [h]; exact hlv
      · rw [h]; exact hs
    · apply A.interval_prefix_range B hlarge g d i k hk p _ hlu ?_ (hcuts i t (by simp))
      rcases clippedLabel_label ((A.cuts i).cut 0) ((A.cuts i).cut (Fin.last (A.count i))) (endpointLabel t) with h|h
      · rw [h]; exact hlv
      · rw [h]; exact ht
  · intro i j hij
    exact (windowCell_pairwise_disjoint d l hl q hij).mono Set.inter_subset_left Set.inter_subset_left
  · intro x
    constructor
    · intro hx
      obtain ⟨i,hi⟩ := windowCell_cover d l hl q x
      exact ⟨i,hi,hx⟩
    · rintro ⟨i,hi⟩; exact hi.2

end AxisAnchorFamily
end AnchorGeneration

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_AnchorConstants
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
section AnchorConstants
namespace AxisAnchorFamily
variable {n l : ℕ} {q : ℤ} (A : AxisAnchorFamily n l q)
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (hlarge : 15 < m+1) (g : B.CoordinateWindowLaw n) (d : Fin 2)

theorem constant_range_prefixGroup (hl : 201 ≤ l) (hln : l ≤ n) :
    B.c.range ≤ A.prefixGroup B hlarge g d := by
  have hh := B.fullGeometricSector_partition_range hlarge (axisWindowPrimitives d l q)
    (fun I _ b hb => B.axisFamilyLaw n g d l hln q I b hb) (wholePolygon a)
    (windowCell a d l q) (windowCell_axis_resolved d l (by omega) q)
    (windowCell_pairwise_disjoint d l hl q) (by
      intro x; constructor
      · intro _; exact windowCell_cover d l hl q x
      · intro _; trivial)
  rw [B.fullGeometricSector_whole] at hh
  have hr : (B.c.comp (universalProjection (alternatingGroup (Fin (m+1))))).range = B.c.range := by
    apply le_antisymm
    · rintro x ⟨s,rfl⟩; exact ⟨_,rfl⟩
    rintro x ⟨s,rfl⟩
    obtain ⟨t,ht⟩ := universalProjection_surjective (alternatingGroup (Fin (m+1))) s
    exact ⟨t,by simp only [MonoidHom.comp_apply,ht]⟩
  rw [hr] at hh
  apply hh.trans
  apply iSup_le
  intro i
  change (B.axisSector hlarge n g d l hln q (windowCell a d l q i)).range ≤ _
  rw [← A.anchorCopy_eq_cell B hlarge g d hl hln i]
  exact A.anchor_range_prefixGroup B hlarge g d i

end AxisAnchorFamily
end AnchorConstants

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_GrowthGeneration
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
section GrowthGeneration
attribute [local instance] cutOrdinaryOrder

namespace growthAnchorFamily
variable (n : ℕ) (hn : 1005 ≤ n) (p : ℤ)
local notation "A" => growthAnchorFamily n hn p

theorem clipped_mem_range (i : Fin (growthAnchorLength n)) (q : ℤ)
    (hq : p ≤ q ∧ q < p+growthNewLength n) :
    clippedLabel ((A).cuts i |>.cut 0) (((A).cuts i).cut (Fin.last ((A).count i))) q ∈
      Set.range ((A).cuts i).cut := by
  rw [range,← (A).lower,← (A).upper]
  exact clippedLabel_mem _ _ _ _ _ (((A).cuts i).ordered (Fin.last ((A).count i))).1
    ((A).intervalLength (growth_lengths hn).2.2.2.1 i)
    (labels n hn p i (Fin.last ((A).count i))) hq

end growthAnchorFamily

theorem growth_edge_window {n : ℕ} (hn : 1005 ≤ n) (p : ℤ) (j : Fin (growthNewLength n-1)) :
    ∃ q : ℤ,
      (q ≤ p+(j.val:ℤ) ∧ p+(j.val:ℤ)+1 < q+growthOldLength n) ∧
      ∀ i : Fin (growthAnchorLength n+1),
        q ≤ endpointLabel (windowCut (growthAnchorLength n) (growthAnchorStart n p) i) ∧
        endpointLabel (windowCut (growthAnchorLength n) (growthAnchorStart n p) i) < q+growthOldLength n := by
  have hlens := growth_lengths hn
  by_cases h : p+(j.val:ℤ)+1 < p+growthOldLength n
  · refine ⟨p,⟨by omega,h⟩,?_⟩
    intro i
    have hi := growth_anchor_label hn p i
    constructor <;> omega
  · refine ⟨growthAnchorStart n p,?_,?_⟩
    · dsimp [growthAnchorStart]
      have hj := j.isLt
      have hover : growthNewLength n+201 ≤ 2*growthOldLength n := by
        simp only [growthNewLength,growthOldLength]; omega
      constructor <;> omega
    · intro i
      have hi := growth_anchor_label hn p i
      dsimp [growthAnchorStart] at hi ⊢
      constructor <;> omega

theorem axisWindowPrimitive_interval {a : ℕ} {r : CutRing} (d : Fin 2) (k : ℕ) (p : ℤ)
    (j : Fin (k-1)) :
    InitialCoverSystem.primitiveTests (a := a) (r := r) (axisWindowPrimitives d k p) j =
      coordinateInterval a d (((p+(j.val:ℤ)):CutRing)*cutTau)
        (((p+(j.val:ℤ)+1):CutRing)*cutTau) := by
  apply Subtype.ext
  change (spatialTranslate (coordinateShift d (((p+(j.val:ℤ)):CutRing)*cutTau))
    (initialTest a r (coordinateTestIndex d))).val = coordinateBetween a d _ _
  rw [initialTest_coordinate]
  unfold coordinateBetween
  have he : (((p+(j.val:ℤ)+1):CutRing)*cutTau)-(((p+(j.val:ℤ)):CutRing)*cutTau) = cutTau := by ring
  rw [he,coordinateArc_tau]
  rfl

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

omit [Group.IsPerfect (alternatingGroup (Fin (m+1)))] in

theorem primitiveFamily_range_full_all {ι : Type*} (hlarge : 15 < m+1)
    (P : ι → Fin 5 × (CutRing × CutRing)) (I : Finset (Fin (m+1)))
    (b : Fin (m+1)) (hb : b ∉ I) :
    (copyFamilyEval (B.primitiveFamily I b hb P)).range ≤
      (smallFamilyEval (B.smallPrimitiveInputs hlarge P)).range := by
  classical
  let J : Finset (Fin (m+1)) := Finset.univ.erase b
  have hIJ : I ⊆ J := by intro x hx; exact Finset.mem_erase.mpr ⟨by intro he; subst x; exact hb hx,Finset.mem_univ _⟩
  have hJ : 5 ≤ J.card := by simp [J]; omega
  have hbJ : b ∉ J := Finset.notMem_erase _ _
  exact (B.primitiveFamily_range_inclusion hIJ b b hb hbJ P).trans
    (B.primitiveFamily_range_full hlarge P J hJ b hbJ)

theorem primitiveCopy_range_fullSector {ι : Type*} [Finite ι] (hlarge : 15 < m+1)
    (P : ι → Fin 5 × (CutRing × CutRing))
    (h : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb P)
    (I : Finset (Fin (m+1))) (hI : 5 ≤ I.card) (b : Fin (m+1)) (hb : b ∉ I)
    (g : B.PrimitiveFamilyLaw I b hb P) (j : ι) :
    (B.primitiveCopy I b hb (P j)).range ≤
      (B.fullGeometricSector hlarge P h (primitiveTests (a := a) (r := r) P j)).range := by
  let := alphabetPerfect I hI
  rintro x ⟨s,rfl⟩
  obtain ⟨t,ht⟩ := universalProjection_surjective (alternatingGroup I) s
  refine ⟨universalMap (subtypeAlternatingHom I) t,?_⟩
  have hh := B.fullGeometricSector_inclusion hlarge P h I hI b hb g
    (primitiveTests (a := a) (r := r) P j) (resolved_test _ j)
  rw [B.geometricSector_input I b hb P g j] at hh
  exact (DFunLike.congr_fun hh t).trans (by simp only [MonoidHom.comp_apply,ht])

end InitialCoverSystem
end GrowthGeneration

section GrowthAxisLaw
namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem growth_axis_range_prefixGroup (hlarge : 15 < m+1) (n : ℕ) (hn : 1005 ≤ n)
    (g : B.CoordinateWindowLaw n) (d : Fin 2) (p : ℤ) :
    (smallFamilyEval (B.smallPrimitiveInputs hlarge (axisWindowPrimitives d (growthNewLength n) p))).range ≤
      (growthAnchorFamily n hn p).prefixGroup B hlarge g d := by
  classical
  let A := growthAnchorFamily n hn p
  have hlens := growth_lengths hn
  rw [smallFamilyEval_range]
  apply iSup_le
  intro I
  apply iSup_le
  intro j
  cases j with
  | none =>
    change (B.initialAlphabet I.val 0).range ≤ _
    rw [B.initialAlphabet_zero]
    exact (range_comp_subset B.c _).trans
      (A.constant_range_prefixGroup B hlarge g d hlens.2.2.2.1 hlens.2.2.2.2.1)
  | some j =>
    let b := smallAlphabetBalance hlarge I.val (by rw [I.property.2]; omega)
    have hb : b ∉ I.val := smallAlphabetBalance_notMem hlarge I.val _
    change (B.primitiveCopy I.val b hb (axisWindowPrimitives d (growthNewLength n) p j)).range ≤ _
    obtain ⟨q,hq,ha⟩ := growth_edge_window hn p j
    let i : Fin (growthOldLength n-1) := ⟨(p+(j.val:ℤ)-q).toNat,by
      have he : ((p+(j.val:ℤ)-q).toNat:ℤ) = p+(j.val:ℤ)-q := Int.toNat_of_nonneg (by omega)
      omega⟩
    have hi : q+(i.val:ℤ) = p+(j.val:ℤ) := by
      have he : ((p+(j.val:ℤ)-q).toNat:ℤ) = p+(j.val:ℤ)-q := Int.toNat_of_nonneg (by omega)
      dsimp [i]; omega
    have he : axisWindowPrimitives d (growthOldLength n) q i =
        axisWindowPrimitives d (growthNewLength n) p j := by
      unfold axisWindowPrimitives
      congr 2
      exact congrArg (fun z : ℤ => (z:CutRing)*cutTau) hi
    rw [← he]
    have hh := B.primitiveCopy_range_fullSector hlarge (axisWindowPrimitives d (growthOldLength n) q)
      (fun I _ b hb => B.axisFamilyLaw n g d _ hlens.1 q I b hb) I.val (by rw [I.property.2]) b hb
      (B.axisFamilyLaw n g d _ hlens.1 q I.val b hb) i
    apply hh.trans
    rw [axisWindowPrimitive_interval]
    change (B.axisSector hlarge n g d (growthOldLength n) hlens.1 q
      (coordinateInterval a d (((q+(i.val:ℤ)):CutRing)*cutTau)
        (((q+(i.val:ℤ)+1):CutRing)*cutTau))).range ≤ _
    have he0 : (((q+(i.val:ℤ)):CutRing)*cutTau) = (((p+(j.val:ℤ)):CutRing)*cutTau) := by exact_mod_cast congrArg (fun z : ℤ => (z:CutRing)*cutTau) hi
    have he1 : (((q+(i.val:ℤ)+1):CutRing)*cutTau) = (((p+(j.val:ℤ)+1):CutRing)*cutTau) := by
      congr 1; exact_mod_cast (show q+(i.val:ℤ)+1 = p+(j.val:ℤ)+1 by omega)
    rw [he0,he1]
    have hl0 : endpointLabel (((p+(j.val:ℤ)):CutRing)*cutTau) = p+(j.val:ℤ) := by
      simpa only [Int.cast_add] using endpointLabel_int_mul_tau (p+(j.val:ℤ))
    have hl1 : endpointLabel (((p+(j.val:ℤ)+1):CutRing)*cutTau) = p+(j.val:ℤ)+1 := by
      simpa only [Int.cast_add,Int.cast_one] using endpointLabel_int_mul_tau (p+(j.val:ℤ)+1)
    apply A.old_interval_range B hlarge g d hlens.2.2.2.1 (growthOldLength n) hlens.1 q _ _
    · simp only [hl0]
      omega
    · simp only [hl1]
      omega
    · exact ha
    · intro i z hz
      apply growthAnchorFamily.clipped_mem_range n hn p i
      simp only [Finset.mem_insert,Finset.mem_singleton] at hz
      rcases hz with rfl|rfl <;> simp only [hl0,hl1]
      all_goals have hj := j.isLt; omega

theorem growth_axis_law_of_anchor_oai (hlarge : 15 < m+1) (n : ℕ) (hn : 1005 ≤ n)
    (g : B.CoordinateWindowLaw n) (d : Fin 2) (p : ℤ)
    (h : CentralOn (coverMap M (alternatingGenerator a r m hm))
      ((growthAnchorFamily n hn p).prefixGroup B hlarge g d))
    (I : Finset (Fin (m+1))) (b : Fin (m+1)) (hb : b ∉ I) :
    B.PrimitiveFamilyLaw I b hb (axisWindowPrimitives d (growthNewLength n) p) := by
  apply CentralOn.mono h
  exact (B.primitiveFamily_range_full_all hlarge _ I b hb).trans
    (B.growth_axis_range_prefixGroup hlarge n hn g d p)

end InitialCoverSystem
end GrowthAxisLaw

end SimpleAmenable
end
end

end OAI
end

theorem solution : type_of% @OAI.SimpleAmenable.InitialCoverSystem.growth_axis_law_of_anchor_oai := @OAI.SimpleAmenable.InitialCoverSystem.growth_axis_law_of_anchor_oai
