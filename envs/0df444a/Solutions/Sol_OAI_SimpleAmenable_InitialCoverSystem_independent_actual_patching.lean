-- Prove2me | solution 1 for OAI.SimpleAmenable.InitialCoverSystem.independent_actual_patching
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T04:44:54.159987+00:00
-- url     : https://prove2.me/submissions/58d19e69-9ebd-49ae-948f-07638a5b95de

import Mathlib
import Definitions.Def_OAIQ65Sa014
import Theorems.Thm_OAI_SimpleAmenable_InitialCoverSystem_actual_template_actual_word_controls
import Theorems.Thm_OAI_SimpleAmenable_InitialCoverSystem_chart_action_transfer
import Theorems.Thm_OAI_SimpleAmenable_formalGridInputs_normalize

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

end FormalSectorSupport

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

namespace FormalStarTable
variable {F : Option ι → TrackStar α →* H} (T : FormalStarTable F)

theorem sector_union {U V : Set (ι → Bool)} (hd : Disjoint U V) (s : TrackStar α) :
    T.sector (U ∪ V) s=T.sector U s*T.sector V s := by
  change (centralSector T.model (U ∪ V) s).val=_
  rw [centralSector_union T.model hd]
  rfl

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
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_InvariantPatching
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
section InvariantPatching
variable {G D α ι : Type*} [Group G] [Group D]

theorem sameActionOn_free_lift (P : Subgroup G) (f g : α → G)
    (hf : ∀ i, f i ∈ (Subgroup.normalizer (P : Set G))) (hg : ∀ i, g i ∈ (Subgroup.normalizer (P : Set G)))
    (h : SameActionOn f g P) :
    SameActionOn (FreeGroup.lift f) (FreeGroup.lift g) P := by
  let F : FreeGroup α →* (Subgroup.normalizer (P : Set G)) := FreeGroup.lift (fun i => ⟨f i,hf i⟩)
  let J : FreeGroup α →* (Subgroup.normalizer (P : Set G)) := FreeGroup.lift (fun i => ⟨g i,hg i⟩)
  have hF : (Subgroup.normalizer (P : Set G)).subtype.comp F = FreeGroup.lift f := by
    apply FreeGroup.ext_hom
    intro i
    simp [F]
  have hJ : (Subgroup.normalizer (P : Set G)).subtype.comp J = FreeGroup.lift g := by
    apply FreeGroup.ext_hom
    intro i
    simp [J]
  have he : P.normalizerMonoidHom.comp F = P.normalizerMonoidHom.comp J := by
    apply FreeGroup.ext_hom
    intro i
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    simpa [F,J] using h i x.val x.property
  intro w x hx
  have hh := congrArg (fun k : FreeGroup α →* MulAut P => ((k w) ⟨x,hx⟩).val) he
  change (F w).val*x*(F w).val⁻¹ = (J w).val*x*(J w).val⁻¹ at hh
  have hf' : (F w).val = FreeGroup.lift f w := DFunLike.congr_fun hF w
  have hg' : (J w).val = FreeGroup.lift g w := DFunLike.congr_fun hJ w
  simpa only [hf',hg'] using hh

theorem normalizes_of_same_action (P : Subgroup G) (x y : G)
    (hx : x ∈ (Subgroup.normalizer (P : Set G))) (h : ∀ z ∈ P, x*z*x⁻¹=y*z*y⁻¹) :
    y ∈ (Subgroup.normalizer (P : Set G)) := by
  intro z
  constructor
  · intro hz
    rw [← h z hz]
    exact (hx z).mp hz
  · intro hz
    have hu : x⁻¹*(y*z*y⁻¹)*x ∈ P := by
      have hu' := ((Subgroup.normalizer (P : Set G)).inv_mem hx (y*z*y⁻¹)).mp hz
      rw [inv_inv] at hu'
      exact hu'
    have hh := h _ hu
    have he : x*(x⁻¹*(y*z*y⁻¹)*x)*x⁻¹ = y*z*y⁻¹ := by group
    rw [he] at hh
    have hv : z=x⁻¹*(y*z*y⁻¹)*x := by
      have ht := congrArg (fun q => y⁻¹*q*y) hh
      simpa only [mul_assoc,inv_mul_cancel,inv_mul_cancel_left,mul_inv_cancel_left,mul_one] using ht
    rwa [← hv] at hu

theorem patching_centrality (f : α → G) (P : ι → Subgroup G)
    (hgen : (FreeGroup.lift f).range ≤ ⨆ i, P i)
    (hinv : ∀ i j, f j ∈ (Subgroup.normalizer (P i : Set G)))
    (w : FreeGroup α)
    (hlocal : ∀ i, ∃ g : α → G, SameActionOn f g (P i) ∧
      FreeGroup.lift g w ∈ Subgroup.centralizer (P i : Set G)) :
    ∀ x ∈ (FreeGroup.lift f).range, Commute (FreeGroup.lift f w) x := by
  have hc : ∀ i, FreeGroup.lift f w ∈ Subgroup.centralizer (P i : Set G) := by
    intro i
    obtain ⟨g,hg,hgw⟩ := hlocal i
    have hact := sameActionOn_free_lift (P i) f g (hinv i)
      (fun j => normalizes_of_same_action (P i) _ _ (hinv i j) (hg j)) hg
    intro x hx
    have he := hact w x hx
    have he' : FreeGroup.lift g w*x*(FreeGroup.lift g w)⁻¹=x := by
      rw [← hgw x hx]; group
    rw [he'] at he
    have ht := congrArg (fun z => z*FreeGroup.lift f w) he
    exact (by simpa only [mul_assoc,inv_mul_cancel,mul_one] using ht :
      FreeGroup.lift f w*x=x*FreeGroup.lift f w).symm
  have hs : (⨆ i, P i) ≤ Subgroup.centralizer {FreeGroup.lift f w} := by
    apply iSup_le
    intro i x hx y hy
    obtain rfl : y=FreeGroup.lift f w := Set.mem_singleton_iff.mp hy
    exact (hc i x hx).symm
  intro x hx
  exact show FreeGroup.lift f w*x=x*FreeGroup.lift f w from hs (hgen hx) _ rfl

end InvariantPatching

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_SmallStarRelators
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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
section SmallStarRelators
variable {α ι Ω H Q : Type*} [Fintype α] [DecidableEq α] [Group H] [Group Q]
    [Group.IsPerfect (alternatingGroup α)]

theorem smallFamilyStarWord_eval (F : Option ι → TrackStar α →* H)
    (f : (I : FiveAlphabet α) → Option ι → alternatingGroup I.val →* H)
    (hspec : ∀ I i, (F i).comp (universalMap (subtypeAlternatingHom I.val))=
      (f I i).comp (universalProjection (alternatingGroup I.val))) :
    (copyFamilyEval F).comp smallFamilyStarWord=smallFamilyEval f := by
  apply FreeGroup.ext_hom
  rintro ⟨I,i,s⟩
  have h := DFunLike.congr_fun (hspec I i)
    (Classical.choose (universalProjection_surjective (alternatingGroup I.val) s))
  simpa only [MonoidHom.comp_apply,smallFamilyStarWord,FreeGroup.lift_apply_of,
    copyFamilyEval_of,smallFamilyEval_of,alphabetStarLift,
    Classical.choose_spec (universalProjection_surjective (alternatingGroup I.val) s)] using h

end SmallStarRelators

section CellConstantActions
namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M) {ι : Type*} [Finite ι]
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem cell_restrict_action (hlarge : 20 ≤ m+1)
    (P : ι → Fin 5 × (CutRing × CutRing))
    (h : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb P)
    (U W : polygonAlgebra a)
    (hU : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) P i).val) U.val)
    (hW : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) P i).val) W.val)
    (f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm))
    (hf : B.AlignedSmallSupported f)
    (hc : SmallControlled B.c f (B.fullGeometricSector (by omega) P h W))
    (I : ControlAlphabet (Fin (m+1))) (s : UniversalExtension (alternatingGroup I.val)) :
    ∀ x ∈ f.range,
      B.fullGeometricSector (by omega) P h U (universalMap (subtypeAlternatingHom I.val) s)*x*
        (B.fullGeometricSector (by omega) P h U (universalMap (subtypeAlternatingHom I.val) s))⁻¹ =
      B.fullGeometricSector (by omega) P h (U ⊓ W) (universalMap (subtypeAlternatingHom I.val) s)*x*
        (B.fullGeometricSector (by omega) P h (U ⊓ W) (universalMap (subtypeAlternatingHom I.val) s))⁻¹ := by
  exact B.chart_action_transfer hlarge P h U (U ⊓ W) W hU
    (fun x y hh => and_congr (hU x y hh) (hW x y hh)) hW
    (by rw [inf_assoc,inf_idem]) f hf hc I s

end InitialCoverSystem
end CellConstantActions

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_SmallFormalGlobal
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
section SmallFormalGlobal
variable {α ι Ω H : Type*} [Fintype α] [DecidableEq α] [Finite ι] [Finite Ω] [Group H]

theorem smallFamily_assignment_law
    (U : ι → Set Ω) (hsep : ∀ ω ν, (∀ i, ω ∈ U i ↔ ν ∈ U i) → ω=ν)
    (F : (I : FiveAlphabet α) → Option ι → alternatingGroup I.val →* H)
    (hlaw : ∀ S : Finset α, S.card≤15 → ∀ w ∈ smallFamilyLocal (ι := ι) S,
      smallFamilyModel U w=1 → ∀ v ∈ smallFamilyLocal (ι := ι) S,
      Commute (smallFamilyEval F w) (smallFamilyEval F v))
    (hα : 5≤Fintype.card α) :
    HasCentralLaw (smallFamilyModel U) (smallFamilyEval F).rangeRestrict := by
  classical
  let e := smallFamilyEval F
  let v := smallFamilyModel (α := α) U
  let : Group.IsPerfect e.range := smallFamilyEval_perfect F
  obtain ⟨E,_hEsub,hE⟩ := Finset.exists_subset_card_eq
    (show 5≤(Finset.univ : Finset α).card by simpa using hα)
  obtain ⟨x,hx⟩ := Finset.card_pos.mp (show 0<E.card by omega)
  obtain ⟨y,hy,hyx⟩ := Finset.exists_mem_ne (show 1<E.card by omega) x
  let a : SwapLabel α := ⟨Equiv.swap x y,x,y,Ne.symm hyx,rfl⟩
  have ha : a.val.support⊆E := by
    change (Equiv.swap x y).support⊆E
    rw [Equiv.Perm.support_swap (Ne.symm hyx)]
    exact Finset.insert_subset_iff.mpr ⟨hx,Finset.singleton_subset_iff.mpr hy⟩
  refine small_support_assignment_law (smallFamilyLocal (ι := ι)) smallFamilyLocal_mono
    v e.rangeRestrict e.rangeRestrict_surjective smallFamilyLocal_generate
    (smallFamilyModel_support U) ?_ E hE a ha ?_
  · intro S hS d hd hv z hz
    apply Commute.of_map (f := e.range.subtype) Subtype.val_injective
    exact hlaw S hS d hd hv z hz
  · intro S hS _ g hg
    exact smallFamilyModel_complete U hsep S hS g hg

end SmallFormalGlobal

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_GridFormalPatching
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
section GridFormalPatching

theorem inner_action_iSup {G J : Type*} [Group G] (P : J → Subgroup G) (x y : G)
    (h : ∀ j, ∀ z ∈ P j, x*z*x⁻¹=y*z*y⁻¹) :
    ∀ z ∈ ⨆ j, P j, x*z*x⁻¹=y*z*y⁻¹ := by
  have hh : (⨆ j, P j) ≤ MonoidHom.eqLocus (MulAut.conj x).toMonoidHom
      (MulAut.conj y).toMonoidHom := by
    apply iSup_le
    intro j z hz
    exact h j z hz
  exact hh

end GridFormalPatching

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_CrossingCellActions
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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

section LocalPatchTemplates
namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M) {ι J : Type*}
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

attribute [instance] LocalPatchTemplate.finite_index

namespace LocalPatchTemplate
variable {B} {F : Option ι → TrackStar (Fin (m+1)) →*
      BoundedRelationCover M (alternatingGenerator a r m hm)}
    {f : J → TrackStar (Fin (m+1)) →*
      BoundedRelationCover M (alternatingGenerator a r m hm)}
    {hlarge : 15 < m+1} (T : B.LocalPatchTemplate hlarge F f)

theorem masked_actions (h20 : 20 ≤ m+1)
    (hF : F none=B.c.comp (universalProjection (alternatingGroup (Fin (m+1)))))
    (hf : ∀ j, B.AlignedSmallSupported (f j)) :
    ∀ i (I : FiveAlphabet (Fin (m+1))) s j, ∀ x ∈ (f j).range,
      F i (universalMap (subtypeAlternatingHom I.val) s)*x*
        (F i (universalMap (subtypeAlternatingHom I.val) s))⁻¹ =
      B.fullGeometricSector hlarge T.tests T.lawful (marginFamily T.predicates T.margin i)
          (universalMap (subtypeAlternatingHom I.val) s)*x*
        (B.fullGeometricSector hlarge T.tests T.lawful (marginFamily T.predicates T.margin i)
          (universalMap (subtypeAlternatingHom I.val) s))⁻¹ := by
  intro i I s j x hx
  let I' : ControlAlphabet (Fin (m+1)) := ⟨I.val,by rw [I.property.2]; omega⟩
  cases i with
  | none =>
    have hh := B.cell_restrict_action h20 T.tests T.lawful (wholePolygon a) T.margin
      (fun _ _ _ => Iff.rfl) T.margin_resolved (f j) (hf j) (T.controlled j) I' s x hx
    rw [B.fullGeometricSector_whole,← hF] at hh
    have he : wholePolygon a ⊓ T.margin=T.margin := top_inf_eq _
    rw [he] at hh
    exact hh
  | some i =>
    exact (T.action i I s j x hx).trans (by
      simpa only [marginFamily,inf_comm] using B.cell_restrict_action h20 T.tests T.lawful
        (T.predicates i) T.margin (T.predicates_resolved i) T.margin_resolved
        (f j) (hf j) (T.controlled j) I' s x hx)

end LocalPatchTemplate

end InitialCoverSystem
end LocalPatchTemplates

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_PrimitiveFormalSectors
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

section FormalRectangleSplits

namespace FormalStarTable
variable {α ι κ H : Type*} [Fintype α] [DecidableEq α] [Group H]
    [Group.IsPerfect (alternatingGroup α)] {F : Option ι → TrackStar α →* H}
    (T : FormalStarTable F)

theorem sector_empty : T.sector ∅=1 := by
  ext s
  change (centralSector T.model ∅ s).val=1
  rw [centralSector_empty]
  rfl

theorem sector_range_le_biUnion (W : κ → Set (ι → Bool)) (S : Finset κ)
    (hd : Pairwise fun i j => Disjoint (W i) (W j)) (K : Subgroup H)
    (hK : ∀ i ∈ S, (T.sector (W i)).range ≤ K) :
    (T.sector (⋃ i ∈ S, W i)).range ≤ K := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [T.sector_empty]
  | @insert i S hi ih =>
    have hdis : Disjoint (W i) (⋃ j ∈ S, W j) := by
      apply Set.disjoint_iUnion_right.mpr
      intro j
      apply Set.disjoint_iUnion_right.mpr
      intro hj
      exact hd (by intro he; subst j; exact hi hj)
    have he : (⋃ j ∈ insert i S, W j)=W i ∪ ⋃ j ∈ S, W j := by
      ext x
      simp only [Set.mem_iUnion,Finset.mem_insert,Set.mem_union]
      constructor
      · rintro ⟨j,(rfl|hj),hx⟩
        · exact Or.inl hx
        · exact Or.inr ⟨j,hj,hx⟩
      · rintro (hx|⟨j,hj,hx⟩)
        · exact ⟨i,Or.inl rfl,hx⟩
        · exact ⟨j,Or.inr hj,hx⟩
    rw [he]
    rintro x ⟨s,rfl⟩
    rw [T.sector_union hdis]
    exact K.mul_mem (hK i (Finset.mem_insert_self i S) ⟨s,rfl⟩)
      (ih (fun j hj => hK j (Finset.mem_insert_of_mem hj)) ⟨s,rfl⟩)

theorem sector_range_le_partition [Fintype κ] (W : κ → Set (ι → Bool)) (V : Set (ι → Bool))
    (hd : Pairwise fun i j => Disjoint (W i) (W j))
    (hc : ∀ σ, σ ∈ V ↔ ∃ i, σ ∈ W i) :
    (T.sector V).range ≤ ⨆ i, (T.sector (W i)).range := by
  have he : V=⋃ i ∈ (Finset.univ : Finset κ), W i := by
    ext σ
    simpa only [Set.mem_iUnion,Finset.mem_univ,exists_true_left] using hc σ
  rw [he]
  exact T.sector_range_le_biUnion W Finset.univ hd _ (fun i _ => le_iSup (fun j => (T.sector (W j)).range) i)

end FormalStarTable
end FormalRectangleSplits

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

theorem formalGridPieces_generate [Fintype D]
    (hd : ∀ i, Pairwise fun d e => Disjoint (C i d) (C i e))
    (hcover : ∀ i σ, ∃ d, σ ∈ C i d) :
    (⨆ i, (formalGridInput F T U i).range : Subgroup H) ≤
      ⨆ d, ⨆ i, (formalGridPiece F T U C d i).range := by
  apply iSup_le
  intro i
  have hh := (T i).sector_range_le_partition (fun d => U i ∩ C i d) (U i)
    (fun d e hde => (hd i hde).mono Set.inter_subset_right Set.inter_subset_right)
    (fun σ => by
      constructor
      · intro hσ
        obtain ⟨d,hd⟩ := hcover i σ
        exact ⟨d,hσ,hd⟩
      · rintro ⟨d,hd⟩
        exact hd.1)
  exact hh.trans (iSup_mono fun d => le_iSup (fun i => (formalGridPiece F T U C d i).range) i)

end FormalGridPieces

section SupportedAssignmentPatching
variable {α ι D H Ω : Type*} [Fintype α] [DecidableEq α] [Finite ι] [Finite Ω] [Group H]
    [Group.IsPerfect (alternatingGroup α)]

theorem supported_assignment_patching
    (U : ι → Set Ω) (hsep : ∀ ω ν, (∀ i, ω ∈ U i ↔ ν ∈ U i) → ω=ν)
    (F : Option ι → TrackStar α →* H)
    (f : (I : FiveAlphabet α) → Option ι → alternatingGroup I.val →* H)
    (hspec : ∀ I i, (F i).comp (universalMap (subtypeAlternatingHom I.val))=
      (f I i).comp (universalProjection (alternatingGroup I.val)))
    (P : D → Subgroup H)
    (hgen : (copyFamilyEval F).range ≤ ⨆ d, P d)
    (hinv : ∀ d i s, F i s ∈ Subgroup.normalizer (P d : Set H))
    (G : D → Option ι → TrackStar α →* H)
    (hact : ∀ d (I : FiveAlphabet α) i s,
      ∀ x ∈ P d,
        F i (universalMap (subtypeAlternatingHom I.val) s)*x*
          (F i (universalMap (subtypeAlternatingHom I.val) s))⁻¹ =
        G d i (universalMap (subtypeAlternatingHom I.val) s)*x*
          (G d i (universalMap (subtypeAlternatingHom I.val) s))⁻¹)
    (hlocal : ∀ d (S : Finset α), S.card ≤ 15 → ∀ w ∈ smallFamilyLocal (ι := ι) S,
      smallFamilyModel U w=1 →
      ∀ x ∈ P d, Commute (copyFamilyEval (G d) (smallFamilyStarWord w)) x)
    (hα : 5 ≤ Fintype.card α) :
    HasCentralLaw (smallFamilyModel U)
      (smallFamilyEval f).rangeRestrict := by
  classical
  let f₀ : SmallFamilyLabel α ι → H := fun l => f l.1 l.2.1 l.2.2
  have hfs (I : FiveAlphabet α) (i : Option ι) (s : alternatingGroup I.val) :
      f I i s=F i (alphabetStarLift I s) := by
    have hh := DFunLike.congr_fun (hspec I i)
      (Classical.choose (universalProjection_surjective (alternatingGroup I.val) s))
    simpa only [MonoidHom.comp_apply,alphabetStarLift,
      Classical.choose_spec (universalProjection_surjective (alternatingGroup I.val) s)] using hh.symm
  have hgen' : (FreeGroup.lift f₀).range ≤ ⨆ d, P d := by
    rintro x ⟨w,rfl⟩
    apply hgen
    refine ⟨smallFamilyStarWord w,?_⟩
    exact DFunLike.congr_fun (smallFamilyStarWord_eval F f hspec) w
  apply smallFamily_assignment_law U hsep f ?_ hα
  intro S hS w hw hrel v _hv
  have hc := patching_centrality f₀ P hgen' (fun d l => by
    rw [show f₀ l=F l.2.1 (alphabetStarLift l.1 l.2.2) from hfs _ _ _]
    exact hinv _ _ _) w ?_
  · exact hc _ ⟨v,rfl⟩
  · intro d
    let g : SmallFamilyLabel α ι → H := fun l => G d l.2.1 (alphabetStarLift l.1 l.2.2)
    have hg : (FreeGroup.lift g)=(copyFamilyEval (G d)).comp smallFamilyStarWord := by
      apply FreeGroup.ext_hom
      rintro ⟨I,i,s⟩
      simp [g,smallFamilyStarWord]
    refine ⟨g,?_,?_⟩
    · intro l x hx
      rw [show f₀ l=F l.2.1 (alphabetStarLift l.1 l.2.2) from hfs _ _ _]
      exact hact d l.1 l.2.1 _ x hx
    · rw [hg]
      intro x hx
      exact (hlocal d S hS w hw hrel x hx).eq.symm

end SupportedAssignmentPatching

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_ClosedLocalAssignments
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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

section IndependentActualPatching
namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M) {ι D : Type*} [Finite ι] [Fintype D]
    {κ : Option ι → Type*} [∀ i, Finite (κ i)]
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem independent_actual_patching_oai (hlarge : 25 ≤ m+1)
    (F : (i : Option ι) → Option (κ i) → TrackStar (Fin (m+1)) →*
      BoundedRelationCover M (alternatingGenerator a r m hm))
    (T : ∀ i, FormalStarTable (F i)) (U : (i : Option ι) → Set (κ i → Bool))
    (C : (i : Option ι) → D → Set (κ i → Bool))
    (hF : ∀ i j, B.AlignedSmallSupported (F i j))
    (hc : ∀ i, F i none=B.c.comp (universalProjection _))
    (hd : ∀ i, Pairwise fun d e => Disjoint (C i d) (C i e))
    (hcover : ∀ i σ, ∃ d, σ ∈ C i d)
    (j k : D → TrackStar (Fin (m+1)) →*
      BoundedRelationCover M (alternatingGenerator a r m hm))
    (hj : ∀ i d, (T i).sector (C i d)=j d)
    (hk : ∀ i d, (T i).sector (C i d)ᶜ=k d)
    (hjs : ∀ d, B.AlignedSmallSupported (j d))
    (hcomm : ∀ d s t, Commute (j d s) (k d t))
    (hzero : formalGridInput F T U none=B.c.comp (universalProjection _))
    (f : (I : FiveAlphabet (Fin (m+1))) → Option ι → alternatingGroup I.val →*
      BoundedRelationCover M (alternatingGenerator a r m hm))
    (hspec : ∀ I i, (formalGridInput F T U i).comp (universalMap (subtypeAlternatingHom I.val))=
      (f I i).comp (universalProjection (alternatingGroup I.val)))
    (R : ι → polygonAlgebra a)
    (L : ∀ d, B.LocalPatchTemplate (by omega)
      (formalGridInput F T U) (formalGridPiece F T U C d))
    (hreal : ∀ d x, x ∈ (L d).margin.val →
      polygonAssignment (L d).predicates x ∈ Set.range (polygonAssignment R)) :
    HasCentralLaw (smallFamilyModel (actualTestMask R)) (smallFamilyEval f).rangeRestrict := by
  classical
  have hpieces d i : B.AlignedSmallSupported (formalGridPiece F T U C d i) :=
    formalGridPiece_supported F T U C _ hF d i
  apply supported_assignment_patching (actualTestMask R) ?_
    (formalGridInput F T U) f hspec
    (fun d => ⨆ i, (formalGridPiece F T U C d i).range) ?_ ?_
    (fun d i => B.fullGeometricSector (by omega) (L d).tests (L d).lawful
      (marginFamily (L d).predicates (L d).margin i)) ?_ ?_
    (by simp only [Fintype.card_fin]; omega)
  · intro σ τ h
    apply Subtype.ext
    funext i
    exact Bool.eq_iff_iff.mpr (h i)
  · rw [copyFamilyEval_range]
    exact formalGridPieces_generate F T U C hd hcover
  · exact formalGridInputs_normalize F T U C _ B.c
      (by simp only [Fintype.card_fin]; omega) B.constant_aligned B.disjoint_aligned
      hF hc j k hj hk hjs hcomm
  · intro d I i s
    apply inner_action_iSup
    intro e
    exact (L d).masked_actions (by omega) hzero (hpieces d) i I s e
  · intro d S hS w hw hrel
    have hh : (⨆ i, (formalGridPiece F T U C d i).range) ≤
        Subgroup.centralizer ({copyFamilyEval
          (fun i => B.fullGeometricSector (by omega) (L d).tests (L d).lawful
            (marginFamily (L d).predicates (L d).margin i))
          (smallFamilyStarWord w)} : Set _) := by
      apply iSup_le
      intro i x hx
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      exact (B.actual_template_actual_word_controls hlarge (L d).tests (L d).lawful
        (L d).predicates (L d).margin (L d).predicates_resolved (L d).margin_resolved
        _ (hpieces d i) ((L d).controlled i) S hS w hw R (hreal d) hrel x hx).symm
    intro x hx
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hh hx)).symm

end InitialCoverSystem
end IndependentActualPatching

end SimpleAmenable
end
end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.SimpleAmenable.InitialCoverSystem.independent_actual_patching_oai.{u_1, u_2, u_3} := @OAI.SimpleAmenable.InitialCoverSystem.independent_actual_patching_oai.{u_1, u_2, u_3}
