-- Prove2me | solution 1 for OAI.SimpleAmenable.primitive_laws_eventually
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T05:04:54.625069+00:00
-- url     : https://prove2.me/submissions/2e7ea405-6797-40d6-9e96-eb37d3eda9e4

import Mathlib
import Definitions.Def_OAIQ65Sa012
import Definitions.Def_OAIQ65Sa018
import Theorems.Thm_OAI_SimpleAmenable_InitialCoverSystem_PatchAtlas_formalRectangleMasks
import Theorems.Thm_OAI_SimpleAmenable_InitialCoverSystem_PatchAtlas_primitive_family_global_templates
import Theorems.Thm_OAI_SimpleAmenable_InitialCoverSystem_PatchAtlas_translated_slope_coordinate_formal_law
import Theorems.Thm_OAI_SimpleAmenable_InitialCoverSystem_independent_actual_patching
import Theorems.Thm_OAI_SimpleAmenable_finePatchAtlas_eventually
import Theorems.Thm_OAI_SimpleAmenable_formal_pairs_assemble

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_NestedCutCalculus
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
section ConditionalControl
variable {E H : Type*} [Group E] [Group H]

theorem conj_mul_of_commute (a b k : H) (h : Commute b k) :
    (a*b)*k*(a*b)⁻¹ = a*k*a⁻¹ := by
  calc
    _ = a*(b*k*b⁻¹)*a⁻¹ := by group
    _ = a*k*a⁻¹ := by rw [h.eq]; group

end ConditionalControl

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_AlphabetAlignedGeneration
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

section CentralLaws

variable {D M H : Type*} [Group D] [Group M] [Group H]

theorem hasCentralLaw_iff_modelMap (v : D →* M) (f : D →* H)
    (hv : Function.Surjective v) : HasCentralLaw v f ↔
    ∃ φ : M →* H ⧸ Subgroup.center H,
      φ.comp v = (QuotientGroup.mk' (Subgroup.center H)).comp f := by
  constructor
  · intro h
    exact ⟨v.liftOfSurjective hv ⟨_,h⟩, v.liftOfRightInverse_comp _ _ _⟩
  · rintro ⟨φ,hφ⟩ w hw
    change QuotientGroup.mk' (Subgroup.center H) (f w) = 1
    have hh := DFunLike.congr_fun hφ w
    change φ (v w) = _ at hh
    rw [show v w = 1 from hw, map_one] at hh
    exact hh.symm

theorem centralLaw_modelMap_surjective (v : D →* M) (f : D →* H)
    (hf : Function.Surjective f) (φ : M →* H ⧸ Subgroup.center H)
    (hφ : φ.comp v = (QuotientGroup.mk' (Subgroup.center H)).comp f) :
    Function.Surjective φ := by
  intro x
  obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center H) x
  obtain ⟨w,rfl⟩ := hf y
  exact ⟨v w, DFunLike.congr_fun hφ w⟩

end CentralLaws

end SimpleAmenable
end
end

end OAI
end

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

theorem centralSector_commute (φ : (Ω → E) →* H ⧸ Subgroup.center H)
    {U V : Set Ω} (huv : Disjoint U V) (s t : UniversalExtension E) :
    Commute (centralSector φ U s) (centralSector φ V t) := by
  apply perfect_maps_commute_of_central (QuotientGroup.mk' (Subgroup.center H))
    (by rw [QuotientGroup.ker_mk']) (centralSector φ U) (centralSector φ V) ?_ s t
  intro x y
  rw [centralSector_spec, centralSector_spec]
  exact (sectorMask_commute huv _ _).map φ

theorem centralSector_union (φ : (Ω → E) →* H ⧸ Subgroup.center H)
    {U V : Set Ω} (huv : Disjoint U V) (s : UniversalExtension E) :
    centralSector φ (U ∪ V) s = centralSector φ U s * centralSector φ V s := by
  let p := commutingProduct (centralSector φ U) (centralSector φ V)
    (centralSector_commute φ huv)
  have hp : centralSector φ (U ∪ V) = p := by
    apply perfect_lift_unique (QuotientGroup.mk' (Subgroup.center H))
      (by rw [QuotientGroup.ker_mk'])
    ext t
    simp only [MonoidHom.comp_apply, p, commutingProduct_apply, map_mul, centralSector_spec]
    rw [sectorMask_disjoint_union huv, map_mul]
  exact DFunLike.congr_fun hp s

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

section FormalSectorSupport
variable {E E' H Ω ι : Type*} [Group E] [Group E'] [Group H]

theorem assignmentPost_mask (ψ : E' →* E) (U : Set Ω) (s : E') :
    assignmentPost ψ (sectorMask U s) = sectorMask U (ψ s) := by
  classical
  ext ω
  by_cases h : ω ∈ U <;> simp [assignmentPost,sectorMask,h]

theorem centralSector_supported [Group.IsPerfect E] [Group.IsPerfect E']
    [Finite Ω] [Finite ι] (φ : (Ω → E) →* H ⧸ Subgroup.center H)
    (U : ι → Set Ω) (hsep : ∀ ω ν, (∀ i, ω ∈ U i ↔ ν ∈ U i) → ω=ν)
    (ψ : E' →* E) (K : Subgroup H)
    (hwhole : ∀ s, φ (sectorMask Set.univ (ψ s)) ∈ K.map (QuotientGroup.mk' _))
    (hU : ∀ i s, φ (sectorMask (U i) (ψ s)) ∈ K.map (QuotientGroup.mk' _))
    (V : Set Ω) :
    ((centralSector φ V).comp (universalMap ψ)).range ≤ K := by
  let q := QuotientGroup.mk' (Subgroup.center H)
  let J := (K.map q).comap (φ.comp (assignmentPost ψ))
  have hJ : J=⊤ := assignment_group_generated U hsep J
    (fun s => by change φ (assignmentPost ψ (sectorMask Set.univ s)) ∈ K.map q
                 rw [assignmentPost_mask]; exact hwhole s)
    (fun i s => by change φ (assignmentPost ψ (sectorMask (U i) s)) ∈ K.map q
                   rw [assignmentPost_mask]; exact hU i s)
  apply perfect_range_le_of_central_image _ q (by rw [QuotientGroup.ker_mk']) K
  rintro y ⟨s,rfl⟩
  change q (centralSector φ V (universalMap ψ s)) ∈ K.map q
  rw [centralSector_spec]
  have hs := DFunLike.congr_fun (universalMap_spec ψ) s
  change universalProjection E (universalMap ψ s)=ψ (universalProjection E' s) at hs
  rw [hs,← assignmentPost_mask]
  have hmem : sectorMask V (universalProjection E' s) ∈ J := by rw [hJ]; trivial
  exact hmem

theorem centralSector_control [Group.IsPerfect E]
    (φ : (Ω → E) →* H ⧸ Subgroup.center H) {U V : Set Ω} (hUV : U ⊆ V) :
    SameActionOn (centralSector φ V) (centralSector φ Set.univ) (centralSector φ U).range := by
  intro s x hx
  obtain ⟨t,rfl⟩ := hx
  have hd : Disjoint V Vᶜ := disjoint_compl_right_iff.mpr le_rfl
  have he := centralSector_union φ hd s
  rw [Set.union_compl_self] at he
  rw [he]
  exact (conj_mul_of_commute _ _ _
    (centralSector_commute φ (disjoint_compl_left_iff.mpr hUV) s t)).symm

end FormalSectorSupport

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_SectorControl
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.BankEmbedding.instCoeFunForallPointTrackPoint _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.instFaithfulObjLabelledFunctor _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.realize_faithful _root_.OAI.SimpleAmenable.PolygonPlacement.Configuration.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.PolygonPlacement.instCoeFunForallGenericSquareTrackPoint _root_.OAI.SimpleAmenable.PolygonPlacement.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.SimpleAmenable.instIsNoetherianRingPolygonGroupRing _root_.OAI.TranslationFiltered.regular_filtered
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
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_FullSector
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.BankEmbedding.instCoeFunForallPointTrackPoint _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.instFaithfulObjLabelledFunctor _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.realize_faithful _root_.OAI.SimpleAmenable.PolygonPlacement.Configuration.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.PolygonPlacement.instCoeFunForallGenericSquareTrackPoint _root_.OAI.SimpleAmenable.PolygonPlacement.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.SimpleAmenable.instIsNoetherianRingPolygonGroupRing _root_.OAI.TranslationFiltered.regular_filtered
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
section FullSectorSupport
namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M) {ι : Type*} [Finite ι]
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem fullGeometricSector_supported (hlarge : 15 < m+1)
    (P : ι → Fin 5 × (CutRing × CutRing))
    (h : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb P)
    (V : polygonAlgebra a)
    (hV : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) P i).val) V.val) :
    SmallSupported (sourceAlignedGroup a r m hm M B.t) (B.fullGeometricSector hlarge P h V) := by
  intro I
  let b := smallAlphabetBalance hlarge I.val (by have hh := I.property.2; omega)
  have hb : b ∉ I.val := smallAlphabetBalance_notMem hlarge I.val _
  rw [B.fullGeometricSector_inclusion hlarge P h I.val I.property.1 b hb (h _ (by have hh := I.property.2; omega) b hb) V hV]
  rintro x ⟨t,rfl⟩
  exact B.geometricSector_aligned I.val b hb P _ V t

theorem constant_small_supported :
    SmallSupported (sourceAlignedGroup a r m hm M B.t)
      (B.c.comp (universalProjection (alternatingGroup (Fin (m+1))))) := by
  intro I
  rw [MonoidHom.comp_assoc,universalMap_spec,← MonoidHom.comp_assoc,← B.initialAlphabet_zero]
  rintro x ⟨t,rfl⟩
  exact B.initialAlphabet_aligned I.val 0 _

theorem fullGeometricSector_commute (hlarge : 15 < m+1)
    (P : ι → Fin 5 × (CutRing × CutRing))
    (h : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb P)
    (V W : polygonAlgebra a)
    (hV : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) P i).val) V.val)
    (hVW : Disjoint V.val W.val)
    (s t : UniversalExtension (alternatingGroup (Fin (m+1)))) :
    Commute (B.fullGeometricSector hlarge P h V s) (B.fullGeometricSector hlarge P h W t) :=
  (B.fullPrimitiveTable hlarge P h).sector_commute (resolvedPolygonMask_disjoint _ hV hVW) s t

end InitialCoverSystem
end FullSectorSupport

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_WindowCellPartition
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

end WindowCellPartition

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

theorem formalStarTable_of_small [Finite ι] (hα : 5 ≤ Fintype.card α)
    (F : Option ι → TrackStar α →* H)
    (f : (I : FiveAlphabet α) → Option ι → alternatingGroup I.val →* H)
    (hspec : ∀ I i, (F i).comp (universalMap (subtypeAlternatingHom I.val))=
      (f I i).comp (universalProjection (alternatingGroup I.val)))
    (hlaw : HasCentralLaw (smallFamilyModel (fun i : ι => {σ : ι → Bool | σ i=true}))
      (smallFamilyEval f).rangeRestrict) : Nonempty (FormalStarTable F) := by
  classical
  let K := (smallFamilyEval f).range
  have hmem : ∀ i s, F i s ∈ K := by
    intro i s
    change F i s ∈ (smallFamilyEval f).range
    rw [← star_small_range_eq hα F f hspec]
    exact ⟨FreeGroup.of (i,s),copyFamilyEval_of F i s⟩
  let F' : Option ι → TrackStar α →* K := fun i => (F i).codRestrict K (hmem i)
  have hsep : ∀ σ τ : ι → Bool,
      (∀ i, σ ∈ {σ : ι → Bool | σ i=true} ↔ τ ∈ {σ : ι → Bool | σ i=true}) → σ=τ := by
    intro σ τ he
    funext i
    exact Bool.eq_iff_iff.mpr (he i)
  obtain ⟨φ,hφ⟩ := (hasCentralLaw_iff_modelMap _ _ (smallFamilyModel_surjective _ hsep hα)).mp hlaw
  refine ⟨⟨K,(star_small_range_eq hα F f hspec).symm,F',(fun _ => rfl),φ,centralLaw_modelMap_surjective _ _
    (smallFamilyEval f).rangeRestrict_surjective φ hφ,?_⟩⟩
  intro i
  apply universal_five_alphabet_hom_ext hα
  intro I
  ext s
  have hp := DFunLike.congr_fun (universalMap_spec (subtypeAlternatingHom I.val)) s
  have he : F' i (universalMap (subtypeAlternatingHom I.val) s)=
      (smallFamilyEval f).rangeRestrict (FreeGroup.of ⟨I,i,universalProjection _ s⟩) := by
    apply Subtype.ext
    change F i (universalMap (subtypeAlternatingHom I.val) s)=
      smallFamilyEval f (FreeGroup.of ⟨I,i,universalProjection _ s⟩)
    rw [smallFamilyEval_of]
    exact DFunLike.congr_fun (hspec I i) s
  simp only [MonoidHom.comp_apply,he]
  have hh := DFunLike.congr_fun hφ (FreeGroup.of ⟨I,i,universalProjection _ s⟩)
  simp only [MonoidHom.comp_apply] at hp hh
  rw [hp]
  exact hh

namespace FormalStarTable
variable {F : Option ι → TrackStar α →* H} (T : FormalStarTable F)

theorem sector_input (i : Option ι) :
    T.sector (match i with | none => Set.univ | some i => {σ | σ i=true})=F i := by
  rw [← T.inclusion i]
  apply congrArg (T.carrier.subtype.comp)
  apply perfect_lift_unique (QuotientGroup.mk' (Subgroup.center T.carrier))
    (by rw [QuotientGroup.ker_mk'])
  ext s
  simp only [MonoidHom.comp_apply,centralSector_spec]
  cases i with
  | none => simpa only [MonoidHom.comp_apply,maskFamily] using DFunLike.congr_fun (T.spec none) s
  | some i => simpa only [MonoidHom.comp_apply,maskFamily] using DFunLike.congr_fun (T.spec (some i)) s

theorem sector_control {U V : Set (ι → Bool)} (hUV : U ⊆ V) :
    SameActionOn (T.sector V) (F none) (T.sector U).range := by
  rw [← T.sector_input none]
  rintro s x ⟨t,rfl⟩
  exact congrArg Subtype.val (centralSector_control T.model hUV s _ ⟨t,rfl⟩)

theorem sector_supported [Finite ι] (L : Finset α → Subgroup H)
    (hF : ∀ i, SmallSupported L (F i)) (U : Set (ι → Bool)) :
    SmallSupported L (T.sector U) := by
  classical
  intro I
  let K := (L I.val).comap T.carrier.subtype
  have hsep : ∀ σ τ : ι → Bool,
      (∀ i, σ ∈ {σ : ι → Bool | σ i=true} ↔ τ ∈ {σ : ι → Bool | σ i=true}) → σ=τ := by
    intro σ τ he
    funext i
    exact Bool.eq_iff_iff.mpr (he i)
  have hm (i : Option ι) (s : alternatingGroup I.val) :
      T.model (maskFamily (fun j : ι => {σ : ι → Bool | σ j=true}) i (subtypeAlternatingHom I.val s)) ∈
        K.map (QuotientGroup.mk' _) := by
    obtain ⟨t,rfl⟩ := universalProjection_surjective (alternatingGroup I.val) s
    have hπ := DFunLike.congr_fun (universalMap_spec (subtypeAlternatingHom I.val)) t
    have hs := DFunLike.congr_fun (T.spec i) (universalMap (subtypeAlternatingHom I.val) t)
    simp only [MonoidHom.comp_apply] at hπ hs
    rw [hπ] at hs
    rw [hs]
    apply Subgroup.mem_map.mpr
    refine ⟨T.input i (universalMap (subtypeAlternatingHom I.val) t),?_,rfl⟩
    change T.carrier.subtype (T.input i (universalMap (subtypeAlternatingHom I.val) t)) ∈ L I.val
    rw [← MonoidHom.comp_apply,T.inclusion]
    exact hF i I ⟨t,rfl⟩
  have hh := centralSector_supported T.model (fun j : ι => {σ : ι → Bool | σ j=true})
    hsep (subtypeAlternatingHom I.val) K (hm none) (fun i => hm (some i)) U
  rintro x ⟨s,rfl⟩
  exact hh ⟨s,rfl⟩

end FormalStarTable
end FormalStarTables

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_GridPrimitiveInputs
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.BankEmbedding.instCoeFunForallPointTrackPoint _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.instFaithfulObjLabelledFunctor _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.realize_faithful _root_.OAI.SimpleAmenable.PolygonPlacement.Configuration.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.PolygonPlacement.instCoeFunForallGenericSquareTrackPoint _root_.OAI.SimpleAmenable.PolygonPlacement.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.SimpleAmenable.instIsNoetherianRingPolygonGroupRing _root_.OAI.TranslationFiltered.regular_filtered
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
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_FormalLawReindex
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.BankEmbedding.instCoeFunForallPointTrackPoint _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.instFaithfulObjLabelledFunctor _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.realize_faithful _root_.OAI.SimpleAmenable.PolygonPlacement.Configuration.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.PolygonPlacement.instCoeFunForallGenericSquareTrackPoint _root_.OAI.SimpleAmenable.PolygonPlacement.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.SimpleAmenable.instIsNoetherianRingPolygonGroupRing _root_.OAI.TranslationFiltered.regular_filtered
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
section FormalLawReindex
variable {α ι κ H : Type*} [Fintype α] [DecidableEq α] [Group H]

theorem smallFamilyEval_reindex
    (F : (I : FiveAlphabet α) → Option ι → alternatingGroup I.val →* H) (v : κ → ι) :
    smallFamilyEval (fun I i => F I (i.map v))=(smallFamilyEval F).comp (smallFamilyReindex v) := by
  apply FreeGroup.ext_hom
  rintro ⟨I,i,s⟩
  simp only [MonoidHom.comp_apply,smallFamilyReindex,FreeGroup.map.of,smallFamilyEval_of]

theorem smallFormalModel_reindex (v : κ → ι) :
    (smallFamilyModel (α := α) (fun i : ι => {σ : ι → Bool | σ i=true})).comp (smallFamilyReindex v)=
      (assignmentPullback (fun σ : ι → Bool => σ ∘ v)).comp
        (smallFamilyModel (fun i : κ => {σ : κ → Bool | σ i=true})) := by
  apply FreeGroup.ext_hom
  rintro ⟨I,i,s⟩
  ext σ
  simp only [MonoidHom.comp_apply,smallFamilyReindex,FreeGroup.map.of,smallFamilyModel,smallFamilyEval_of]
  cases i <;> simp [maskFamily,sectorMask,assignmentPullback,Function.comp_def]

theorem smallFormalLaw_reindex
    (F : (I : FiveAlphabet α) → Option ι → alternatingGroup I.val →* H)
    (h : HasCentralLaw (smallFamilyModel (fun i : ι => {σ : ι → Bool | σ i=true}))
      (smallFamilyEval F).rangeRestrict) (v : κ → ι) :
    HasCentralLaw (smallFamilyModel (fun i : κ => {σ : κ → Bool | σ i=true}))
      (smallFamilyEval (fun I i => F I (i.map v))).rangeRestrict := by
  rw [hasCentralLaw_iff]
  intro w hw
  have hm : smallFamilyModel (α := α) (fun i : ι => {σ : ι → Bool | σ i=true})
      (smallFamilyReindex v w)=1 := by
    have he := DFunLike.congr_fun (smallFormalModel_reindex (α := α) v) w
    simp only [MonoidHom.comp_apply,hw,map_one] at he
    exact he
  have hz := (hasCentralLaw_iff _ _).mp h _ hm
  apply Subgroup.mem_center_iff.mpr
  rintro ⟨x,⟨z,rfl⟩⟩
  apply Subtype.ext
  have he := congrArg Subtype.val (Subgroup.mem_center_iff.mp hz
    ((smallFamilyEval F).rangeRestrict (smallFamilyReindex v z)))
  change smallFamilyEval F (smallFamilyReindex v z)*smallFamilyEval F (smallFamilyReindex v w)=
    smallFamilyEval F (smallFamilyReindex v w)*smallFamilyEval F (smallFamilyReindex v z) at he
  change smallFamilyEval (fun I i => F I (i.map v)) z*smallFamilyEval (fun I i => F I (i.map v)) w=
    smallFamilyEval (fun I i => F I (i.map v)) w*smallFamilyEval (fun I i => F I (i.map v)) z
  simpa only [smallFamilyEval_reindex,MonoidHom.comp_apply] using he

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M) [Finite ι]

omit [Finite ι] in
theorem smallPrimitive_formal_reindex [Finite κ] (hlarge : 15 < m+1)
    (P : ι → Fin 5 × (CutRing × CutRing))
    (h : HasCentralLaw (smallFamilyModel (fun i : ι => {σ : ι → Bool | σ i=true}))
      (smallFamilyEval (B.smallPrimitiveInputs hlarge P)).rangeRestrict) (v : κ → ι) :
    HasCentralLaw (smallFamilyModel (fun i : κ => {σ : κ → Bool | σ i=true}))
      (smallFamilyEval (B.smallPrimitiveInputs hlarge (P ∘ v))).rangeRestrict := by
  have he : B.smallPrimitiveInputs hlarge (P ∘ v)=
      fun I i => B.smallPrimitiveInputs hlarge P I (i.map v) := by
    funext I i
    cases i <;> rfl
  rw [he]
  exact smallFormalLaw_reindex _ h v

end InitialCoverSystem
end FormalLawReindex

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_FormalLaws
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.BankEmbedding.instCoeFunForallPointTrackPoint _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.instFaithfulObjLabelledFunctor _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.realize_faithful _root_.OAI.SimpleAmenable.PolygonPlacement.Configuration.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.PolygonPlacement.instCoeFunForallGenericSquareTrackPoint _root_.OAI.SimpleAmenable.PolygonPlacement.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.SimpleAmenable.instIsNoetherianRingPolygonGroupRing _root_.OAI.TranslationFiltered.regular_filtered
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
section ActualFormalLaws
variable {a : ℕ} {α ι : Type*} [Fintype α] [DecidableEq α]

theorem smallActualModel_pullback (U : ι → polygonAlgebra a) :
    smallFamilyModel (α := α) (actualTestMask U)=
      (assignmentPullback (fun σ : Set.range (polygonAssignment U) => σ.val)).comp
        (smallFamilyModel (fun i : ι => {σ : ι → Bool | σ i=true})) := by
  apply FreeGroup.ext_hom
  rintro ⟨I,i,s⟩
  ext σ
  simp only [MonoidHom.comp_apply,smallFamilyModel,smallFamilyEval_of]
  cases i <;> simp [maskFamily,sectorMask,assignmentPullback,actualTestMask]
  rfl

namespace InitialCoverSystem
variable {m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M) [Finite ι]

theorem smallPrimitive_formal_of_actual (hlarge : 15 < m+1)
    (P : ι → Fin 5 × (CutRing × CutRing))
    (h : ∀ I, I.card≤15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb P) :
    HasCentralLaw (smallFamilyModel (fun i : ι => {σ : ι → Bool | σ i=true}))
      (smallFamilyEval (B.smallPrimitiveInputs hlarge P)).rangeRestrict := by
  rw [hasCentralLaw_iff]
  intro w hw
  apply B.fullPrimitiveFamily_central hlarge P h
  change coverMap M (alternatingGenerator a r m hm)
    (smallFamilyEval (B.smallPrimitiveInputs hlarge P) w)=1
  have he := DFunLike.congr_fun (B.fullPrimitiveProjection hlarge P) w
  simp only [MonoidHom.comp_apply] at he
  rw [he,smallActualModel_pullback,MonoidHom.comp_apply,hw,map_one,map_one]

end InitialCoverSystem
end ActualFormalLaws

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

theorem starFamily_supported (hlarge : 15 < m+1) (P : ι → Fin 5 × (CutRing × CutRing))
    (i : Option ι) :
    SmallSupported (sourceAlignedGroup a r m hm M B.t) (A.starFamily hlarge P i) := by
  cases i with
  | none => exact B.constant_small_supported
  | some i =>
    apply B.fullGeometricSector_supported
    have he : spatialTranslate (P i).2 (initialTest a r (P i).1)=
        primitiveTests (a := a) (r := r)
          (translatedTemplate (initialPatchPrimitives r A.geometry.mesh) (P i).2) (Sum.inl (P i).1) := by
      simp [primitiveTests,primitiveFamilyTests,translatedTemplate,initialPatchPrimitives]
    rw [he]
    exact resolved_test _ _

end InitialCoverSystem.PatchAtlas
end CanonicalPrimitiveStars

section OneSlopeFormalTable

namespace InitialCoverSystem.PatchAtlas
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    {B : InitialCoverSystem a r m hm M}
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))] (A : B.PatchAtlas)
    {ι : Type*}

omit [Group.IsPerfect (alternatingGroup (Fin (m+1)))] in
include A in
theorem primitive_self_formal_law (hlarge : 15 < m+1) (p : Fin 5 × (CutRing × CutRing)) :
    HasCentralLaw (smallFamilyModel (fun i : Bool => {σ : Bool → Bool | σ i=true}))
      (smallFamilyEval (B.smallPrimitiveInputs hlarge (fun _ : Bool => p))).rangeRestrict := by
  apply B.smallPrimitive_formal_of_actual
  intro I hI b hb
  have hh := PrimitiveFamilyLaw.reindex B I b hb
    (translatedTemplate (initialPatchPrimitives r A.geometry.mesh) p.2)
    (A.initial p.2 I b hb) (fun _ : Bool => Sum.inl p.1)
  have he : (translatedTemplate (initialPatchPrimitives r A.geometry.mesh) p.2) ∘
      (fun _ : Bool => Sum.inl p.1)=(fun _ : Bool => p) := by
    funext i
    simp [translatedTemplate,initialPatchPrimitives]
  rwa [he] at hh

include A in

theorem oneSlope_pairs_formal_law [Finite ι] (hlarge : 25 ≤ m+1)
    (hr : 0<ordinary r ∧ ordinary r<1/2) (ha : 0<a)
    (d : Fin 2) (u : CutRing × CutRing) (j : ι → Fin 2) (v : ι → CutRing × CutRing)
    (i k : Option ι) :
    HasCentralLaw (smallFamilyModel (fun b : Bool => {σ : Bool → Bool | σ b=true}))
      (smallFamilyEval (B.smallPrimitiveInputs (by omega)
        (primitivePair (oneSlopeCoordinates d u j v) i k))).rangeRestrict := by
  cases i with
  | none =>
    cases k with
    | none =>
      have he : primitivePair (oneSlopeCoordinates d u j v) none none=(fun _ : Bool => (slopeTestIndex d,u)) := by
        funext b; cases b <;> rfl
      rw [he]
      exact A.primitive_self_formal_law (by omega) (slopeTestIndex d,u)
    | some k =>
      have hh := B.smallPrimitive_formal_reindex (by omega) _
        (A.translated_slope_coordinate_formal_law hlarge hr ha d (j k) u (v k))
        (fun b : Bool => if b then (1 : Fin 2) else 0)
      have he : ![(slopeTestIndex d,u),(coordinateTestIndex (j k),v k)] ∘
          (fun b : Bool => if b then (1 : Fin 2) else 0)=
          primitivePair (oneSlopeCoordinates d u j v) none (some k) := by
        funext b; cases b <;> rfl
      rwa [he] at hh
  | some i =>
    cases k with
    | none =>
      have hh := B.smallPrimitive_formal_reindex (by omega) _
        (A.translated_slope_coordinate_formal_law hlarge hr ha d (j i) u (v i))
        (fun b : Bool => if b then (0 : Fin 2) else 1)
      have he : ![(slopeTestIndex d,u),(coordinateTestIndex (j i),v i)] ∘
          (fun b : Bool => if b then (0 : Fin 2) else 1)=
          primitivePair (oneSlopeCoordinates d u j v) (some i) none := by
        funext b; cases b <;> rfl
      rwa [he] at hh
    | some k =>
      have he : primitivePair (oneSlopeCoordinates d u j v) (some i) (some k)=
          fun b : Bool => (coordinateTestIndex (if b then j k else j i),if b then v k else v i) := by
        funext b; cases b <;> rfl
      rw [he]
      exact B.smallPrimitive_formal_of_actual (by omega) _
        (fun I _ b hb => B.coordinateFamilyLaw_all A.rectangles.rectangles _ _ I b hb)

theorem starFamily_formal_table [Fintype ι] (hlarge : 20 ≤ m+1)
    (P : ι → Fin 5 × (CutRing × CutRing))
    (hpair : ∀ i j, HasCentralLaw (smallFamilyModel (fun b : Bool => {σ : Bool → Bool | σ b=true}))
      (smallFamilyEval (B.smallPrimitiveInputs (by omega) (primitivePair P i j))).rangeRestrict) :
    Nonempty (FormalStarTable (A.starFamily (by omega) P)) := by
  classical
  have ht (i j : ι) : Nonempty (FormalStarTable (starPair (A.starFamily (by omega) P) i j)) := by
    have he : starPair (A.starFamily (by omega) P) i j=A.starFamily (by omega) (primitivePair P i j) := by
      funext k
      cases k with
      | none => rfl
      | some b => cases b <;> rfl
    rw [he]
    exact formalStarTable_of_small (by simpa using (by omega : 5 ≤ m+1)) _ _
      (A.starFamily_small (by omega) _) (hpair i j)
  exact formal_pairs_assemble (by simpa using hlarge)
    (sourceAlignedGroup a r m hm M B.t) B.c B.constant_aligned B.disjoint_aligned _
    (A.starFamily_supported (by omega) P) rfl (fun i j => Classical.choice (ht i j))

theorem oneSlope_formal_table [Fintype ι] (hlarge : 25 ≤ m+1)
    (hr : 0<ordinary r ∧ ordinary r<1/2) (ha : 0<a)
    (d : Fin 2) (u : CutRing × CutRing) (j : ι → Fin 2) (v : ι → CutRing × CutRing) :
    Nonempty (FormalStarTable (A.starFamily (by omega) (oneSlopeCoordinates d u j v))) :=
  A.starFamily_formal_table (by omega) _ (A.oneSlope_pairs_formal_law hlarge hr ha d u j v)

end InitialCoverSystem.PatchAtlas
end OneSlopeFormalTable

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_FormalGridPieces
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
section FormalGridPieces
variable {α H ι D : Type*} [Fintype α] [DecidableEq α] [Group H]
    [Group.IsPerfect (alternatingGroup α)] {κ : ι → Type*}
    (F : (i : ι) → Option (κ i) → TrackStar α →* H)
    (T : ∀ i, FormalStarTable (F i)) (U : (i : ι) → Set (κ i → Bool))
    (C : (i : ι) → D → Set (κ i → Bool))

theorem formalGridPiece_supported [∀ i, Finite (κ i)] (L : Finset α → Subgroup H)
    (hF : ∀ i j, SmallSupported L (F i j)) (d : D) (i : ι) :
    SmallSupported L (formalGridPiece F T U C d i) :=
  (T i).sector_supported L (hF i) _

theorem formalGridPiece_control (c : alternatingGroup α →* H)
    (hc : ∀ i, F i none=c.comp (universalProjection _))
    (j : D → TrackStar α →* H) (hj : ∀ i d, (T i).sector (C i d)=j d) (d : D) (i : ι) :
    SmallControlled c (formalGridPiece F T U C d i) (j d) := by
  have hh := (T i).sector_control (show U i ∩ C i d ⊆ C i d from Set.inter_subset_right)
  rw [hj,hc] at hh
  intro I s x hx
  exact hh (universalMap (subtypeAlternatingHom I.val) s) x hx

end FormalGridPieces

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_FiniteRefiningGrid
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.instFaithfulObjLabelledFunctor _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.realize_faithful _root_.OAI.SimpleAmenable.PolygonPlacement.instCoeFunForallGenericSquareTrackPoint _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.SimpleAmenable.instIsNoetherianRingPolygonGroupRing _root_.OAI.TranslationFiltered.regular_filtered
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

theorem refinedGridRectangle_cover {a N : ℕ} (hN : 0<N) (e : Fin (N+1) → CutRing)
    (he : StrictMono (fun i => ordinary (e i))) (hzero : e 0=0) (hlast : e (Fin.last N)=1)
    (hmesh : ∀ i : Fin N, ordinary (e i.succ)-ordinary (e i.castSucc)<1)
    (p : GenericSquare a) : ∃ cell : Fin 2 → Fin N, p ∈ (refinedGridRectangle a N e cell).val := by
  have h (j : Fin 2) : ∃ i : Fin N,
      ordinary (e i.castSucc) ≤ coordinate j p ∧ coordinate j p<ordinary (e i.succ) := by
    exact finite_interval_cell (x := fun i => ordinary (e i)) hN (coordinate j p)
      (by simpa only [hzero,map_zero] using (coordinate_bounds j p).1)
      (by simpa only [hlast,map_one] using (coordinate_bounds j p).2)
  choose cell hc using h
  exact ⟨cell,(refinedGridRectangle_mem e he hzero hlast hmesh cell p).mpr hc⟩

theorem refinedGridRectangle_disjoint {a N : ℕ} (e : Fin (N+1) → CutRing)
    (he : StrictMono (fun i => ordinary (e i))) (hzero : e 0=0) (hlast : e (Fin.last N)=1)
    (hmesh : ∀ i : Fin N, ordinary (e i.succ)-ordinary (e i.castSucc)<1) :
    Pairwise fun i k : Fin 2 → Fin N => Disjoint (refinedGridRectangle a N e i).val
      (refinedGridRectangle a N e k).val := by
  intro i k hik
  obtain ⟨j,hj⟩ := Function.ne_iff.mp hik
  apply Set.disjoint_left.mpr
  intro p hp hq
  have hi := (refinedGridRectangle_mem e he hzero hlast hmesh i p).mp hp j
  have hk := (refinedGridRectangle_mem e he hzero hlast hmesh k p).mp hq j
  rcases lt_or_gt_of_ne hj with hh | hh
  · have hle := he.monotone (show (i j).succ≤(k j).castSucc from by change (i j).val+1≤(k j).val; exact hh)
    linarith
  · have hle := he.monotone (show (k j).succ≤(i j).castSucc from by change (k j).val+1≤(i j).val; exact hh)
    linarith

end RefinementPartition

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_PrimitiveGlobalTemplates
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.BankEmbedding.instCoeFunForallPointTrackPoint _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.instFaithfulObjLabelledFunctor _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.realize_faithful _root_.OAI.SimpleAmenable.PolygonPlacement.Configuration.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.PolygonPlacement.instCoeFunForallGenericSquareTrackPoint _root_.OAI.SimpleAmenable.PolygonPlacement.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.SimpleAmenable.instIsNoetherianRingPolygonGroupRing _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
namespace InitialCoverSystem.PatchAtlas
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m} {B : InitialCoverSystem a r m hm M}
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))] (A : B.PatchAtlas)

theorem primitiveStar_zero (hlarge : 15 < m+1) (u : CutRing × CutRing) :
    A.primitiveStar hlarge (0,u)=B.c.comp (universalProjection _) := by
  unfold primitiveStar
  have hu : spatialTranslate u (initialTest a r 0)=wholePolygon a := by
    apply Subtype.ext
    ext p
    simp [spatialTranslate,initialTest,wholePolygon]
  rw [hu,B.fullGeometricSector_whole]

theorem primitive_table_with_coordinates {κ : Type*} [Fintype κ]
    (hlarge : 25 ≤ m+1) (hr : 0<ordinary r ∧ ordinary r<1/2) (ha : 0<a)
    (p : Fin 5 × (CutRing × CutRing)) (j : κ → Fin 2) (v : κ → CutRing × CutRing) :
    ∃ Q : Option (Option κ) → Fin 5 × (CutRing × CutRing),
      (∀ k, Q (some (some k))=(coordinateTestIndex (j k),v k)) ∧
      ∃ T : FormalStarTable (A.starFamily (by omega) Q),
      ∃ U : Set (Option (Option κ) → Bool), T.sector U=A.primitiveStar (by omega) p := by
  classical
  have hc (d : Fin 2) (u : CutRing × CutRing) (e : Fin 2) (w : CutRing × CutRing) :
      Nonempty (FormalStarTable (A.starFamily (by omega)
        (oneSlopeCoordinates d u (Option.elim' e j) (Option.elim' w v)))) :=
    A.oneSlope_formal_table hlarge hr ha d u _ _
  have hconstant (u : CutRing × CutRing) :
      ∃ Q : Option (Option κ) → Fin 5 × (CutRing × CutRing),
      (∀ k, Q (some (some k))=(coordinateTestIndex (j k),v k)) ∧
      ∃ T : FormalStarTable (A.starFamily (by omega) Q),
      ∃ U : Set (Option (Option κ) → Bool), T.sector U=A.primitiveStar (by omega) (0,u) := by
    let T := Classical.choice (hc 0 0 0 0)
    refine ⟨_,fun _ => rfl,T,Set.univ,?_⟩
    rw [T.sector_input none,A.primitiveStar_zero]
    rfl
  have hcoordinate (e : Fin 2) (w : CutRing × CutRing) :
      ∃ Q : Option (Option κ) → Fin 5 × (CutRing × CutRing),
      (∀ k, Q (some (some k))=(coordinateTestIndex (j k),v k)) ∧
      ∃ T : FormalStarTable (A.starFamily (by omega) Q),
      ∃ U : Set (Option (Option κ) → Bool), T.sector U=A.primitiveStar (by omega) (coordinateTestIndex e,w) := by
    let T := Classical.choice (hc 0 0 e w)
    refine ⟨_,fun _ => rfl,T,{σ | σ (some none)=true},?_⟩
    exact T.sector_input (some (some none))
  have hslope (d : Fin 2) (u : CutRing × CutRing) :
      ∃ Q : Option (Option κ) → Fin 5 × (CutRing × CutRing),
      (∀ k, Q (some (some k))=(coordinateTestIndex (j k),v k)) ∧
      ∃ T : FormalStarTable (A.starFamily (by omega) Q),
      ∃ U : Set (Option (Option κ) → Bool), T.sector U=A.primitiveStar (by omega) (slopeTestIndex d,u) := by
    let T := Classical.choice (hc d u 0 0)
    refine ⟨_,fun _ => rfl,T,{σ | σ none=true},?_⟩
    exact T.sector_input (some none)
  rcases p with ⟨p,u⟩
  fin_cases p
  · exact hconstant u
  · exact hcoordinate 0 u
  · exact hcoordinate 1 u
  · exact hslope 0 u
  · exact hslope 1 u

theorem primitive_family_actual_global_law {ι : Type} [Finite ι]
    (ha : 0<a) (hlarge : 25 ≤ m+1) (hr : 0<ordinary r ∧ ordinary r<1/2)
    (P : ι → Fin 5 × (CutRing × CutRing))
    (hmesh : (1+|ordinary (cutTau^a)|)*(200/(A.geometry.mesh:ℝ))<ordinary A.rectangles.radius/4) :
    HasCentralLaw (smallFamilyModel (actualTestMask (primitiveTests (a := a) (r := r) P)))
      (smallFamilyEval (B.smallPrimitiveInputs (by omega) P)).rangeRestrict := by
  classical
  let _ := Fintype.ofFinite ι
  obtain ⟨N,hN,e,he,hzero,hlast,hfine,n,q,hW,htemplates⟩ :=
    A.primitive_family_global_templates ha (by omega) hr P hmesh
  let D := Fin 2 → Fin N
  let _ : Nonempty D := ⟨fun _ => ⟨0,hN⟩⟩
  let κ := Fin 2 × Fin (n-1)
  let W : D → polygonAlgebra a := refinedGridRectangle a N e
  let Q₀ := coordinateWindowPrimitives n q
  let P' : Option ι → Fin 5 × (CutRing × CutRing) := Option.elim' (0,0) P
  have ht (i : Option ι) := A.primitive_table_with_coordinates hlarge hr ha (P' i)
    (Prod.fst : κ → Fin 2) (fun k : κ => (Q₀ k).2)
  choose Q hQ T U hU using ht
  let F := fun i => A.starFamily (by omega) (Q i)
  have hinput : formalGridInput F T U=A.starFamily (by omega) P := by
    funext i
    change (T i).sector (U i)=_
    rw [hU]
    cases i with
    | none => exact A.primitiveStar_zero (by omega) 0
    | some i => rfl
  have hsub (i : Option ι) : Q i ∘ (fun k : κ => some (some k))=Q₀ := by
    funext k
    exact hQ i k
  have hcoord (i : Option ι) : ∀ I, I.card ≤ 15 → ∀ b hb,
      B.PrimitiveFamilyLaw I b hb (Q i ∘ (fun k : κ => some (some k))) := by
    rw [hsub]
    exact fun I _ b hb => A.rectangles.rectangles n I b hb q
  have hmasks (i : Option ι) := A.formalRectangleMasks (by omega) (Q i) (T i)
    (fun k : κ => some (some k)) (hcoord i) W
    (by rw [hsub]; exact hW)
    (refinedGridRectangle_cover hN e he hzero hlast hfine)
    (refinedGridRectangle_disjoint e he hzero hlast hfine)
  choose C hdis hcover hj' hk' hactual using hmasks
  let j : D → TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm) :=
    fun d => B.windowSector (by omega) n (A.rectangles.rectangles n) q (W d)
  let k : D → TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm) :=
    fun d => B.windowSector (by omega) n (A.rectangles.rectangles n) q (W d)ᶜ
  have hj (i : Option ι) (d : D) : (T i).sector (C i d)=j d := by
    rw [hj']
    simp only [hsub]
    rfl
  have hk (i : Option ι) (d : D) : (T i).sector (C i d)ᶜ=k d := by
    rw [hk']
    simp only [hsub]
    rfl
  have hF (i : Option ι) (v) : B.AlignedSmallSupported (F i v) :=
    A.starFamily_supported (by omega) (Q i) v
  have hc (i : Option ι) : F i none=B.c.comp (universalProjection _) := rfl
  have hpieces (d : D) : ∀ i, B.AlignedSmallSupported (formalGridPiece F T U C d i) :=
    formalGridPiece_supported F T U C _ hF d
  have hcontrols (d : D) : ∀ i, SmallControlled B.c (formalGridPiece F T U C d i) (j d) :=
    formalGridPiece_control F T U C B.c hc j hj d
  have htemplates' (d : D) : ∃ L : B.LocalPatchTemplate (by omega)
      (formalGridInput F T U) (formalGridPiece F T U C d),
      ∀ x : GenericSquare a, x ∈ L.margin.val →
        polygonAssignment L.predicates x ∈ Set.range (polygonAssignment (primitiveTests (a := a) (r := r) P)) := by
    rw [hinput]
    exact htemplates d (Option ι) (formalGridPiece F T U C d) (hpieces d) (hcontrols d)
  choose L hreal using htemplates'
  apply B.independent_actual_patching hlarge F T U C hF hc hdis hcover j k hj hk
    (fun d => B.fullGeometricSector_supported (by omega) Q₀ _ (W d) (hW d))
    (fun d s t => B.fullGeometricSector_commute (by omega) Q₀ _ (W d) (W d)ᶜ
      (hW d) disjoint_compl_right s t) ?_ (B.smallPrimitiveInputs (by omega) P) ?_
    (primitiveTests (a := a) (r := r) P) L hreal
  · rw [hinput]
    rfl
  · intro I i
    rw [hinput]
    exact A.starFamily_small (by omega) P I i

end InitialCoverSystem.PatchAtlas

end SimpleAmenable

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_PrimitiveCentralLaws
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.BankEmbedding.instCoeFunForallPointTrackPoint _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.instFaithfulObjLabelledFunctor _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.realize_faithful _root_.OAI.SimpleAmenable.PolygonPlacement.Configuration.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.PolygonPlacement.instCoeFunForallGenericSquareTrackPoint _root_.OAI.SimpleAmenable.PolygonPlacement.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.SimpleAmenable.instIsNoetherianRingPolygonGroupRing _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
section PrimitiveCentralLaws
namespace InitialCoverSystem.PatchAtlas
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m} {B : InitialCoverSystem a r m hm M}
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))] (A : B.PatchAtlas)

theorem primitive_full_central {ι : Type} [Finite ι]
    (ha : 0<a) (hlarge : 25 ≤ m+1) (hr : 0<ordinary r ∧ ordinary r<1/2)
    (P : ι → Fin 5 × (CutRing × CutRing))
    (hmesh : (1+|ordinary (cutTau^a)|)*(200/(A.geometry.mesh:ℝ))<ordinary A.rectangles.radius/4) :
    CentralOn (coverMap M (alternatingGenerator a r m hm))
      (smallFamilyEval (B.smallPrimitiveInputs (by omega) P)).range := by
  apply (centralOn_range_iff_hasCentralLaw _ _ _ _ (actualPolygonTableHom_injective _)
    (B.fullPrimitiveProjection (by omega) P)).mpr
  exact A.primitive_family_actual_global_law ha hlarge hr P hmesh

theorem primitive_family_law_all {ι : Type} [Finite ι]
    (ha : 0<a) (hlarge : 25 ≤ m+1) (hr : 0<ordinary r ∧ ordinary r<1/2)
    (P : ι → Fin 5 × (CutRing × CutRing))
    (hmesh : (1+|ordinary (cutTau^a)|)*(200/(A.geometry.mesh:ℝ))<ordinary A.rectangles.radius/4)
    (I : Finset (Fin (m+1))) (b : Fin (m+1)) (hb : b ∉ I) :
    B.PrimitiveFamilyLaw I b hb P := by
  classical
  have hc := A.primitive_full_central ha hlarge hr P hmesh
  apply hc.mono
  by_cases hI : 5 ≤ I.card
  · exact B.primitiveFamily_range_full (by omega) P I hI b hb
  · have hsub : I ⊆ Finset.univ.erase b := by
      intro i hi
      exact Finset.mem_erase.mpr ⟨by intro he; subst i; exact hb hi,Finset.mem_univ i⟩
    obtain ⟨J,hIJ,hJ,hcard⟩ := Finset.exists_subsuperset_card_eq hsub (by omega : I.card≤5)
      (by simp only [Finset.card_erase_of_mem (Finset.mem_univ b),Finset.card_univ,Fintype.card_fin]; omega :
        5≤(Finset.univ.erase b : Finset (Fin (m+1))).card)
    have hbJ : b ∉ J := by intro h; exact (Finset.mem_erase.mp (hJ h)).1 rfl
    exact (B.primitiveFamily_range_inclusion hIJ b b hb hbJ P).trans
      (B.primitiveFamily_range_full (by omega) P J (by omega) b hbJ)

end InitialCoverSystem.PatchAtlas

theorem primitive_laws_eventually_oai {a m : ℕ} {r : CutRing} {hm : 2 ≤ m}
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (ha : 0<a) (hlarge : 25 ≤ m+1) (hr : 0<ordinary r ∧ ordinary r<1/2)
    (hSlope : 8000<ordinary (cutTau^a)) (hconj : |conjugate (cutTau^a)|<1/1000) :
    ∃ L : ℕ, ∀ M : ℕ, L≤M → ∀ B : InitialCoverSystem a r m hm M,
      ∀ (ι : Type) [Finite ι] (P : ι → Fin 5 × (CutRing × CutRing))
      (I : Finset (Fin (m+1))) (b : Fin (m+1)) (hb : b ∉ I),
      B.PrimitiveFamilyLaw I b hb P := by
  obtain ⟨L,hL⟩ := finePatchAtlas_eventually (hm := hm) (by omega) hr hSlope hconj
  refine ⟨L,fun M hM B => ?_⟩
  obtain ⟨A⟩ := hL M hM B
  intro ι hι P I b hb
  exact A.toPatchAtlas.primitive_family_law_all ha hlarge hr P A.far_mesh I b hb

end PrimitiveCentralLaws

end SimpleAmenable

end OAI
end

theorem solution : type_of% @OAI.SimpleAmenable.primitive_laws_eventually_oai := @OAI.SimpleAmenable.primitive_laws_eventually_oai
