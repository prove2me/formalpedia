-- Prove2me | solution 1 for OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.formalRectangleMasks
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T04:57:25.609534+00:00
-- url     : https://prove2.me/submissions/af6e911f-924c-4208-821c-73f57e2aa846

import Mathlib
import Definitions.Def_OAIQ65Sa015

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_CanonicalSectors
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
section CanonicalSectors
open scoped commutatorElement

variable {E H Q : Type*} [Group E] [Group H] [Group Q]

variable {Ω : Type*}

variable [Group.IsPerfect E]

theorem centralSector_spec (φ : (Ω → E) →* H ⧸ Subgroup.center H) (U : Set Ω)
    (s : UniversalExtension E) :
    QuotientGroup.mk' (Subgroup.center H) (centralSector φ U s) =
      φ (sectorMask U (universalProjection E s)) :=
  DFunLike.congr_fun (universalLift_spec (QuotientGroup.mk' (Subgroup.center H))
    (QuotientGroup.mk'_surjective (Subgroup.center H))
    (by rw [QuotientGroup.ker_mk']) (φ.comp (sectorMask U))) s

@[simp] theorem centralSector_empty (φ : (Ω → E) →* H ⧸ Subgroup.center H) :
    centralSector φ ∅ = 1 := by
  apply perfect_lift_unique (QuotientGroup.mk' (Subgroup.center H))
    (by rw [QuotientGroup.ker_mk'])
  ext s
  simp only [MonoidHom.comp_apply, centralSector_spec, MonoidHom.one_apply, map_one]
  have h : sectorMask (∅ : Set Ω) (universalProjection E s) = 1 := by ext ω; simp
  rw [h, map_one]

end CanonicalSectors

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_CentralRangeReflection
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
section CentralRangeReflection
open scoped commutatorElement

theorem perfect_range_le_of_central_image {G H Q : Type*} [Group G] [Group H]
    [Group Q] [Group.IsPerfect G] (f : G →* H) (q : H →* Q)
    (hc : q.ker ≤ Subgroup.center H) (K : Subgroup H)
    (himage : (q.comp f).range ≤ K.map q) : f.range ≤ K := by
  have he : f.range = ⁅f.range,f.range⁆ := by
    rw [← map_commutator_eq,Group.IsPerfect.commutator_eq_top,← MonoidHom.range_eq_map]
  rw [he]
  apply Subgroup.commutator_le.mpr
  intro x hx y hy
  obtain ⟨u,hu⟩ := hx
  obtain ⟨v,hv⟩ := hy
  obtain ⟨k,hk,hkx⟩ := Subgroup.mem_map.mp (himage ⟨u,by simpa using congrArg q hu⟩)
  obtain ⟨l,hl,hly⟩ := Subgroup.mem_map.mp (himage ⟨v,by simpa using congrArg q hv⟩)
  have hz : k⁻¹*x ∈ Subgroup.center H := hc (by
    change q (k⁻¹*x) = 1
    simp only [map_mul,map_inv,hkx,inv_mul_cancel])
  have hw : l⁻¹*y ∈ Subgroup.center H := hc (by
    change q (l⁻¹*y) = 1
    simp only [map_mul,map_inv,hly,inv_mul_cancel])
  have hz' (a : H) : ⁅k⁻¹*x,a⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr ((Subgroup.mem_center_iff.mp hz a).symm)
  have hw' (a : H) : ⁅a,l⁻¹*y⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hw a)
  have hxy : ⁅x,y⁆ = ⁅k,l⁆ := by
    have hex : x=k*(k⁻¹*x) := by simp
    have hey : y=l*(l⁻¹*y) := by simp
    conv_lhs => rw [hex,hey]
    rw [commutatorElement_mul_left_eq_conj_mul,hz']
    simp only [mul_one,mul_inv_cancel,one_mul]
    rw [commutatorElement_mul_right_eq_mul_conj,hw']
    simp only [mul_one,mul_inv_cancel_right]
  rw [hxy]
  exact K.mul_mem (K.mul_mem (K.mul_mem hk hl) (K.inv_mem hk)) (K.inv_mem hl)

end CentralRangeReflection

end SimpleAmenable
end
end

end OAI
end

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
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_PairControl
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

section AssignmentExclusions
variable {E S G K ι Ω : Type*} [Group E] [Group S] [Group G] [Group K]

theorem formalAssignmentEval_surjective [Finite ι] [Group.IsPerfect S]
    (π : E →* S) (hπ : Function.Surjective π) : Function.Surjective (formalAssignmentEval (ι := ι) π) := by
  have hv : Function.Surjective (assignmentEval (E := S) (fun i : ι => {σ : ι → Bool | σ i = true})) := by
    apply assignmentEval_surjective
    intro σ τ h
    funext i
    exact Bool.eq_iff_iff.mpr (h i)
  have hw : Function.Surjective (copySourceMap (ι := ι) π) := by
    apply FreeGroup.map_surjective
    rintro ⟨i,s⟩
    obtain ⟨t,rfl⟩ := hπ s
    exact ⟨(i,t),rfl⟩
  exact hv.comp hw

end AssignmentExclusions

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_FormalStarTables
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
section FormalStarTables
variable {α ι H : Type*} [Fintype α] [DecidableEq α] [Group H]
    [Group.IsPerfect (alternatingGroup α)]

theorem star_small_range_eq (hα : 5 ≤ Fintype.card α)
    (F : Option ι → TrackStar α →* H)
    (f : (I : FiveAlphabet α) → Option ι → alternatingGroup I.val →* H)
    (hspec : ∀ I i, (F i).comp (universalMap (subtypeAlternatingHom I.val))=
      (f I i).comp (universalProjection (alternatingGroup I.val))) :
    (copyFamilyEval F).range=(smallFamilyEval f).range := by
  rw [copyFamilyEval_range,smallFamilyEval_range,iSup_comm]
  apply iSup_congr
  intro i
  rw [MonoidHom.range_eq_map,← universal_five_alphabet_generate hα,Subgroup.map_iSup]
  apply iSup_congr
  intro I
  rw [← MonoidHom.range_comp,hspec]
  apply le_antisymm (range_comp_subset _ _)
  rintro x ⟨s,rfl⟩
  obtain ⟨t,rfl⟩ := universalProjection_surjective (alternatingGroup I.val) s
  exact ⟨t,rfl⟩

end FormalStarTables

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_StarProjection
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.BankEmbedding.instCoeFunForallPointTrackPoint _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonPlacement.Configuration.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.PolygonPlacement.instCoeFunForallGenericSquareTrackPoint _root_.OAI.SimpleAmenable.PolygonPlacement.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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
section ActualStarProjection
variable {a m : ℕ} {ι : Type*} [Finite ι]

theorem formalPolygonTable_whole (U : ι → polygonAlgebra a) (s : alternatingGroup (Fin (m+1))) :
    formalPolygonTable U (sectorMask Set.univ s) = conditionalAlternatingHom (wholePolygon a) s := by
  change actualPolygonTableHom U _ = _
  have he : assignmentPullback (fun ω : Set.range (polygonAssignment U) => ω.val)
      (sectorMask Set.univ s) = sectorMask Set.univ s := by
    ext ω; simp [assignmentPullback,sectorMask]
  rw [he]
  exact actualPolygonTableHom_whole U s

theorem formalPolygonTable_test (U : ι → polygonAlgebra a) (i : ι) (s : alternatingGroup (Fin (m+1))) :
    formalPolygonTable U (sectorMask {σ | σ i = true} s) = conditionalAlternatingHom (U i) s := by
  change actualPolygonTableHom U _ = _
  have he : assignmentPullback (fun ω : Set.range (polygonAssignment U) => ω.val)
      (sectorMask {σ | σ i = true} s) = polygonTableInput U i s := by rfl
  rw [he]
  exact actualPolygonTableHom_input U i s

end ActualStarProjection

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
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_FormalLaws
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

section CanonicalPrimitiveStars
namespace InitialCoverSystem.PatchAtlas
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    {B : InitialCoverSystem a r m hm M}
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))] (A : B.PatchAtlas)
    {ι : Type*}

theorem starFamily_small (hlarge : 15 < m+1) (P : ι → Fin 5 × (CutRing × CutRing))
    (I : FiveAlphabet (Fin (m+1))) (i : Option ι) :
    (A.starFamily hlarge P i).comp (universalMap (subtypeAlternatingHom I.val))=
      (B.smallPrimitiveInputs hlarge P I i).comp (universalProjection (alternatingGroup I.val)) := by
  cases i with
  | none =>
    change (B.c.comp _).comp _=(B.initialAlphabet I.val 0).comp _
    rw [MonoidHom.comp_assoc,universalMap_spec,← MonoidHom.comp_assoc,B.initialAlphabet_zero]
  | some i =>
    apply B.fullGeometricSector_small_input hlarge _ _ P (Sum.inl (P i).1) i _ I
    simp [translatedTemplate,initialPatchPrimitives]

end InitialCoverSystem.PatchAtlas
end CanonicalPrimitiveStars

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_FormalSectorSubfamily
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
section FormalSectorSubfamily
namespace FormalStarTable
variable {α ι κ H Q : Type*} [Fintype α] [DecidableEq α] [Group H] [Group Q]
    [Group.IsPerfect (alternatingGroup α)]
    {F : Option ι → TrackStar α →* H} (T : FormalStarTable F)

omit [Group.IsPerfect (alternatingGroup α)] in
theorem input_eval : T.carrier.subtype.comp (copyFamilyEval T.input)=copyFamilyEval F := by
  rw [← copyFamilyEval_comp]
  congr 1
  funext i
  exact T.inclusion i

omit [Group.IsPerfect (alternatingGroup α)] in
theorem input_surjective : Function.Surjective (copyFamilyEval T.input) := by
  intro x
  have hx : x.val ∈ (copyFamilyEval F).range := by rw [← T.carrier_eq]; exact x.property
  obtain ⟨w,hw⟩ := hx
  refine ⟨w,Subtype.ext ?_⟩
  have he := DFunLike.congr_fun T.input_eval w
  exact he.trans hw

omit [Group.IsPerfect (alternatingGroup α)] in
theorem model_eval : T.model.comp (formalAssignmentEval (universalProjection (alternatingGroup α)))=
    (QuotientGroup.mk' _).comp (copyFamilyEval T.input) := by
  apply FreeGroup.ext_hom
  rintro ⟨i,s⟩
  have hh := DFunLike.congr_fun (T.spec i) s
  simpa only [MonoidHom.comp_apply,formalAssignmentEval,copySourceMap,FreeGroup.map.of,
    assignmentEval,copyFamilyEval_of] using hh

theorem sector_subfamily_range [Finite κ] (v : κ → ι) (V : Set (κ → Bool)) :
    (T.sector ((fun σ : ι → Bool => σ ∘ v) ⁻¹' V)).range ≤
      (copyFamilyEval (fun i : Option κ => F (i.map v))).range := by
  classical
  let K := ((copyFamilyEval (fun i : Option κ => F (i.map v))).range).comap T.carrier.subtype
  let q := QuotientGroup.mk' (Subgroup.center T.carrier)
  let J := (K.map q).comap (T.model.comp (assignmentPullback (fun σ : ι → Bool => σ ∘ v)))
  have hm (i : Option κ) (s : alternatingGroup α) :
      maskFamily (fun j : κ => {σ : κ → Bool | σ j=true}) i s ∈ J := by
    obtain ⟨t,rfl⟩ := universalProjection_surjective (alternatingGroup α) s
    change T.model (assignmentPullback (fun σ : ι → Bool => σ ∘ v)
      (maskFamily (fun j : κ => {σ : κ → Bool | σ j=true}) i (universalProjection _ t))) ∈ K.map q
    have he : assignmentPullback (fun σ : ι → Bool => σ ∘ v)
        (maskFamily (fun j : κ => {σ : κ → Bool | σ j=true}) i (universalProjection _ t))=
        maskFamily (fun j : ι => {σ : ι → Bool | σ j=true}) (i.map v) (universalProjection _ t) := by
      cases i <;> rfl
    rw [he]
    have hs := DFunLike.congr_fun (T.spec (i.map v)) t
    simp only [MonoidHom.comp_apply] at hs
    rw [hs]
    apply Subgroup.mem_map.mpr
    refine ⟨T.input (i.map v) t,?_,rfl⟩
    change T.carrier.subtype (T.input (i.map v) t) ∈ (copyFamilyEval (fun i : Option κ => F (i.map v))).range
    rw [← MonoidHom.comp_apply,T.inclusion]
    exact ⟨FreeGroup.of (i,t),copyFamilyEval_of _ i t⟩
  have hJ : J=⊤ := assignment_group_generated
    (fun j : κ => {σ : κ → Bool | σ j=true})
    (fun σ τ he => funext (fun i => Bool.eq_iff_iff.mpr (he i))) J (hm none) (fun i => hm (some i))
  have hsec : (centralSector T.model ((fun σ : ι → Bool => σ ∘ v) ⁻¹' V)).range ≤ K := by
    apply perfect_range_le_of_central_image _ q (by rw [QuotientGroup.ker_mk']) K
    rintro x ⟨s,rfl⟩
    change q (centralSector T.model _ s) ∈ K.map q
    rw [centralSector_spec]
    have he : sectorMask ((fun σ : ι → Bool => σ ∘ v) ⁻¹' V) (universalProjection _ s)=
        assignmentPullback (fun σ : ι → Bool => σ ∘ v) (sectorMask V (universalProjection _ s)) := by
      rfl
    rw [he]
    have hh : sectorMask V (universalProjection _ s) ∈ J := by rw [hJ]; trivial
    exact hh
  rintro x ⟨s,rfl⟩
  exact hsec ⟨s,rfl⟩

theorem sector_forward [Finite ι] (γ : T.carrier →* Q) (hγ : Function.Surjective γ)
    (hz : Subgroup.center Q=⊥) (δ : ((ι → Bool) → alternatingGroup α) →* Q)
    (hδ : ∀ i, γ.comp (T.input i)=δ.comp
      ((maskFamily (fun j : ι => {σ : ι → Bool | σ j=true}) i).comp (universalProjection _)))
    (V : Set (ι → Bool)) (s : TrackStar α) :
    γ (centralSector T.model V s)=δ (sectorMask V (universalProjection _ s)) := by
  have hc : Subgroup.center T.carrier ≤ γ.ker := by
    intro x hx
    have hh : γ x ∈ Subgroup.center Q := by
      apply Subgroup.mem_center_iff.mpr
      intro y
      obtain ⟨t,rfl⟩ := hγ y
      simpa only [map_mul] using congrArg γ (Subgroup.mem_center_iff.mp hx t)
    simpa only [hz,Subgroup.mem_bot,MonoidHom.mem_ker] using hh
  let γ' := QuotientGroup.lift (Subgroup.center T.carrier) γ hc
  have he : γ'.comp T.model=δ := by
    apply MonoidHom.cancel_right (formalAssignmentEval_surjective
      (universalProjection (alternatingGroup α)) (universalProjection_surjective _)) |>.mp
    rw [MonoidHom.comp_assoc,T.model_eval]
    apply FreeGroup.ext_hom
    rintro ⟨i,t⟩
    have hh := DFunLike.congr_fun (hδ i) t
    simpa only [MonoidHom.comp_apply,copyFamilyEval_of,formalAssignmentEval,copySourceMap,
      FreeGroup.map.of,assignmentEval,γ',QuotientGroup.mk'_apply,QuotientGroup.lift_mk] using hh
  have hh := DFunLike.congr_fun he (sectorMask V (universalProjection _ s))
  change γ' (T.model _)=_ at hh
  rw [← centralSector_spec] at hh
  exact hh

end FormalStarTable
end FormalSectorSubfamily

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_FormalSectorProjection
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
section FormalSectorProjection
variable {α ι Ω H Q : Type*} [Fintype α] [DecidableEq α] [Group H] [Group Q]

theorem alternating_function_center (hα : 4 ≤ Nat.card α) :
    Subgroup.center (Ω → alternatingGroup α)=⊥ := by
  rw [Subgroup.center_pi]
  simp only [alternatingGroup.center_eq_bot hα,Subgroup.pi_bot]

theorem assignmentPullback_surjective {X Y E : Type*} [Group E] (v : X → Y)
    (hv : Function.Injective v) : Function.Surjective (assignmentPullback (E := E) v) := by
  classical
  intro f
  refine ⟨Function.extend v f (fun _ => 1),?_⟩
  ext x
  exact congrFun (Function.extend_comp hv f (fun _ => 1)) x

namespace FormalStarTable
variable [Group.IsPerfect (alternatingGroup α)] [Finite ι]
    {F : Option ι → TrackStar α →* H} (T : FormalStarTable F)

theorem sector_projection (hα : 4 ≤ Nat.card α)
    (q : H →* Q) (ρ : (Ω → alternatingGroup α) →* Q) (hρ : Function.Injective ρ)
    (δ : ((ι → Bool) → alternatingGroup α) →* (Ω → alternatingGroup α))
    (hδ : Function.Surjective δ)
    (hp : ∀ i, q.comp (F i)=ρ.comp (δ.comp
      ((maskFamily (fun j : ι => {σ : ι → Bool | σ j=true}) i).comp (universalProjection _))))
    (V : Set (ι → Bool)) (s : TrackStar α) :
    q (T.sector V s)=ρ (δ (sectorMask V (universalProjection _ s))) := by
  let e := copyFamilyEval T.input
  let v := δ.comp (formalAssignmentEval (universalProjection (alternatingGroup α)))
  have hv : Function.Surjective v := hδ.comp (formalAssignmentEval_surjective
    (universalProjection (alternatingGroup α)) (universalProjection_surjective _))
  have he : (q.comp T.carrier.subtype).comp e=ρ.comp v := by
    rw [MonoidHom.comp_assoc,T.input_eval]
    apply FreeGroup.ext_hom
    rintro ⟨i,t⟩
    have hh := DFunLike.congr_fun (hp i) t
    simpa only [MonoidHom.comp_apply,v,formalAssignmentEval,copySourceMap,FreeGroup.map.of,
      assignmentEval,copyFamilyEval_of] using hh
  have hk : ∀ w, e w=1 → v w=1 := by
    intro w hw
    apply hρ
    have hh := DFunLike.congr_fun he w
    change q ((e w).val)=ρ (v w) at hh
    rw [hw,Subgroup.coe_one,map_one] at hh
    simpa only [map_one] using hh.symm
  let γ : T.carrier →* (Ω → alternatingGroup α) :=
    e.liftOfSurjective T.input_surjective ⟨v,hk⟩
  have hγe : γ.comp e=v := e.liftOfRightInverse_comp _ _ _
  have hγ : Function.Surjective γ := by
    intro x
    obtain ⟨w,rfl⟩ := hv x
    exact ⟨e w,DFunLike.congr_fun hγe w⟩
  have hγp : q.comp T.carrier.subtype=ρ.comp γ := by
    apply (MonoidHom.cancel_right T.input_surjective).mp
    change (q.comp T.carrier.subtype).comp e=(ρ.comp γ).comp e
    change (q.comp T.carrier.subtype).comp e=ρ.comp (γ.comp e)
    rw [hγe]
    exact he
  have hγi (i : Option ι) : γ.comp (T.input i)=δ.comp
      ((maskFamily (fun j : ι => {σ : ι → Bool | σ j=true}) i).comp (universalProjection _)) := by
    apply MonoidHom.ext
    intro t
    have hh := DFunLike.congr_fun hγe (FreeGroup.of (i,t))
    simpa only [MonoidHom.comp_apply,e,v,copyFamilyEval_of,formalAssignmentEval,
      copySourceMap,FreeGroup.map.of,assignmentEval] using hh
  have hs := T.sector_forward γ hγ (alternating_function_center hα) δ hγi V s
  have hh := DFunLike.congr_fun hγp (centralSector T.model V s)
  simpa only [MonoidHom.comp_apply,sector,hs] using hh

end FormalStarTable
end FormalSectorProjection

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_PrimitiveFormalSectors
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
section PrimitiveFormalSectors
namespace InitialCoverSystem.PatchAtlas
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    {B : InitialCoverSystem a r m hm M}
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))] (A : B.PatchAtlas)
    {ι κ : Type*} [Finite ι] [Finite κ]

omit [Finite ι] in
theorem starFamily_projection (hlarge : 15 < m+1) (P : ι → Fin 5 × (CutRing × CutRing))
    (i : Option ι) :
    (coverMap M (alternatingGenerator a r m hm)).comp (A.starFamily hlarge P i)=
      (conditionalAlternatingHom (match i with
        | none => wholePolygon a
        | some i => primitiveTests (a := a) (r := r) P i)).comp (universalProjection _) := by
  cases i with
  | none => exact congrArg (fun f => f.comp (universalProjection _)) B.c_projection
  | some i =>
    apply B.fullGeometricSector_projection
    have he : spatialTranslate (P i).2 (initialTest a r (P i).1)=
        primitiveTests (a := a) (r := r)
          (translatedTemplate (initialPatchPrimitives r A.geometry.mesh) (P i).2) (Sum.inl (P i).1) := by
      simp [primitiveTests,primitiveFamilyTests,translatedTemplate,initialPatchPrimitives]
    rw [he]
    exact resolved_test _ _

theorem formalSector_projection (hlarge : 15 < m+1)
    (P : ι → Fin 5 × (CutRing × CutRing))
    (T : FormalStarTable (A.starFamily hlarge P))
    (V : Set (ι → Bool)) (s : TrackStar (Fin (m+1))) :
    coverMap M (alternatingGenerator a r m hm) (T.sector V s)=
      formalPolygonTable (primitiveTests (a := a) (r := r) P)
        (sectorMask V (universalProjection _ s)) := by
  apply T.sector_projection (by simp only [Nat.card_fin]; omega)
    (coverMap M (alternatingGenerator a r m hm)) (actualPolygonTableHom _)
    (actualPolygonTableHom_injective _)
    (assignmentPullback (fun σ : Set.range (polygonAssignment (primitiveTests (a := a) (r := r) P)) => σ.val))
    (assignmentPullback_surjective _ Subtype.val_injective)
  intro i
  rw [A.starFamily_projection]
  ext t : 1
  cases i with
  | none => exact (formalPolygonTable_whole _ _).symm
  | some i => exact (formalPolygonTable_test (primitiveTests (a := a) (r := r) P) i (universalProjection _ t)).symm

theorem formalSector_subfamily_eq (hlarge : 15 < m+1)
    (P : ι → Fin 5 × (CutRing × CutRing))
    (T : FormalStarTable (A.starFamily hlarge P)) (v : κ → ι)
    (h : ∀ I, I.card≤15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb (P ∘ v))
    (U : Set (κ → Bool)) (V : polygonAlgebra a)
    (hV : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) (P ∘ v) i).val) V.val)
    (hUV : ∀ x, polygonAssignment (primitiveTests (a := a) (r := r) (P ∘ v)) x ∈ U ↔ x ∈ V.val) :
    T.sector ((fun σ : ι → Bool => σ ∘ v) ⁻¹' U)=
      B.fullGeometricSector hlarge (P ∘ v) h V := by
  apply (B.fullPrimitiveFamily_central hlarge (P ∘ v) h).lift_unique
    (coverMap M (alternatingGenerator a r m hm))
    (smallFamilyEval (B.smallPrimitiveInputs hlarge (P ∘ v))).range
  · have hh := T.sector_subfamily_range v U
    have he : (fun i : Option κ => A.starFamily hlarge P (i.map v))=
        A.starFamily hlarge (P ∘ v) := by
      funext i; cases i <;> rfl
    rw [he,star_small_range_eq (by simpa using (by omega : 5 ≤ m+1)) _ _
      (A.starFamily_small hlarge (P ∘ v))] at hh
    exact hh
  · rintro x ⟨s,rfl⟩
    exact (B.fullPrimitiveTable hlarge (P ∘ v) h).sector_mem _ s
  · rw [B.fullGeometricSector_projection hlarge (P ∘ v) h V hV]
    apply MonoidHom.ext
    intro s
    rw [MonoidHom.comp_apply,A.formalSector_projection]
    apply Subtype.ext
    apply Subtype.ext
    apply Equiv.ext
    intro p
    change (actualPolygonTableHom _ _).val.val p = _
    rw [actualPolygonTableHom_apply]
    change ((sectorMask ((fun σ : ι → Bool => σ ∘ v) ⁻¹' U) (universalProjection _ s)
      (polygonAssignment (primitiveTests (a := a) (r := r) P) p.2)).val p.1,p.2)=
      conditionalPerm V (universalProjection _ s).val p
    rw [conditionalPerm_apply]
    have he : polygonAssignment (primitiveTests (a := a) (r := r) P) p.2 ∘ v=
        polygonAssignment (primitiveTests (a := a) (r := r) (P ∘ v)) p.2 := rfl
    have hp : polygonAssignment (primitiveTests (a := a) (r := r) P) p.2 ∈
        ((fun σ : ι → Bool => σ ∘ v) ⁻¹' U) ↔ p.2 ∈ V.val := by
      change _ ∘ v ∈ U ↔ _
      rw [he]
      exact hUV p.2
    by_cases hx : p.2 ∈ V.val
    · rw [sectorMask_of_mem _ _ _ (hp.mpr hx),ite_eq_left hx]
    · rw [sectorMask_of_not_mem _ _ _ (fun h => hx (hp.mp h)),ite_eq_right hx]
      rfl

end InitialCoverSystem.PatchAtlas
end PrimitiveFormalSectors

section FormalRectangleSplits

theorem resolvedPartitionSelector {a : ℕ} {ι D : Type*} [Nonempty D]
    (R : ι → polygonAlgebra a) (W : D → polygonAlgebra a)
    (hW : ∀ d, ResolvedBy (fun i => (R i).val) (W d).val)
    (hcover : ∀ x, ∃ d, x ∈ (W d).val)
    (hdisjoint : Pairwise fun d e => Disjoint (W d).val (W e).val) :
    ∃ χ : (ι → Bool) → D, ∀ x d, χ (polygonAssignment R x)=d ↔ x ∈ (W d).val := by
  classical
  let C (σ : ι → Bool) (d : D) := ∃ x, polygonAssignment R x=σ ∧ x ∈ (W d).val
  let χ (σ : ι → Bool) : D := if h : ∃ d, C σ d then h.choose else Classical.choice inferInstance
  refine ⟨χ,?_⟩
  intro x d
  have hc : ∃ d, C (polygonAssignment R x) d := by
    obtain ⟨e,he⟩ := hcover x
    exact ⟨e,x,rfl,he⟩
  have hm : x ∈ (W (χ (polygonAssignment R x))).val := by
    have hh : C (polygonAssignment R x) (χ (polygonAssignment R x)) := by
      dsimp only [χ]
      rw [dite_eq_left hc]
      exact hc.choose_spec
    obtain ⟨y,hy,hm⟩ := hh
    exact (hW _ y x ((polygonAssignment_eq_iff R y x).mp hy)).mp hm
  constructor
  · intro he
    rwa [← he]
  · intro hd
    by_contra he
    exact Set.disjoint_left.mp (hdisjoint he) hm hd

end FormalRectangleSplits

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_FormalGridPieces
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

section PrimitiveRectangleMasks
namespace InitialCoverSystem.PatchAtlas
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    {B : InitialCoverSystem a r m hm M}
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))] (A : B.PatchAtlas)
    {ι κ D : Type*} [Finite ι] [Finite κ] [Nonempty D]

theorem formalRectangleMasks_oai (hlarge : 15 < m+1)
    (P : ι → Fin 5 × (CutRing × CutRing)) (T : FormalStarTable (A.starFamily hlarge P))
    (v : κ → ι)
    (h : ∀ I, I.card≤15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb (P ∘ v))
    (W : D → polygonAlgebra a)
    (hW : ∀ d, ResolvedBy (fun i => (primitiveTests (a := a) (r := r) (P ∘ v) i).val) (W d).val)
    (hcover : ∀ x, ∃ d, x ∈ (W d).val)
    (hd : Pairwise fun d e => Disjoint (W d).val (W e).val) :
    ∃ C : D → Set (ι → Bool),
      (Pairwise fun d e => Disjoint (C d) (C e)) ∧
      (∀ σ, ∃ d, σ ∈ C d) ∧
      (∀ d, T.sector (C d)=B.fullGeometricSector hlarge (P ∘ v) h (W d)) ∧
      (∀ d, T.sector (C d)ᶜ=B.fullGeometricSector hlarge (P ∘ v) h (W d)ᶜ) ∧
      (∀ x d, polygonAssignment (primitiveTests (a := a) (r := r) P) x ∈ C d ↔ x ∈ (W d).val) := by
  obtain ⟨χ,hχ⟩ := resolvedPartitionSelector (primitiveTests (a := a) (r := r) (P ∘ v)) W hW hcover hd
  let C (d : D) : Set (ι → Bool) := {σ | χ (σ ∘ v)=d}
  refine ⟨C,?_,?_,?_,?_,?_⟩
  · intro d e hde
    apply Set.disjoint_left.mpr
    intro σ hd he
    exact hde (hd.symm.trans he)
  · intro σ
    exact ⟨χ (σ ∘ v),rfl⟩
  · intro d
    exact A.formalSector_subfamily_eq hlarge P T v h {σ | χ σ=d} (W d) (hW d)
      (fun x => hχ x d)
  · intro d
    exact A.formalSector_subfamily_eq hlarge P T v h {σ | χ σ≠d} (W d)ᶜ
      (fun x y he => not_congr (hW d x y he)) (fun x => not_congr (hχ x d))
  · intro x d
    exact hχ x d

end InitialCoverSystem.PatchAtlas
end PrimitiveRectangleMasks

end SimpleAmenable
end
end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.formalRectangleMasks_oai.{u_1, u_2, u_3} := @OAI.SimpleAmenable.InitialCoverSystem.PatchAtlas.formalRectangleMasks_oai.{u_1, u_2, u_3}
