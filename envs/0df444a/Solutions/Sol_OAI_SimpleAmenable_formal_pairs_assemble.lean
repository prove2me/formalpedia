-- Prove2me | solution 1 for OAI.SimpleAmenable.formal_pairs_assemble
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T04:39:27.530355+00:00
-- url     : https://prove2.me/submissions/82909a0f-bfa4-48cd-9c7c-5567558f9e61

import Mathlib
import Definitions.Def_OAIQ65Sa014

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
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_AssignmentGeneration
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

section FiniteDirectRefinement
variable {G : Type*} [Group G]

namespace CommutingFactors
variable {A B C D : Subgroup G}

theorem projectLeft_fix (h : CommutingFactors A B)
    (hz : Subgroup.center G = ⊥) {a : G} (ha : a ∈ A) : h.projectLeft hz a = a := by
  simpa using h.projectLeft_factors hz ha B.one_mem

theorem projectLeft_kill (h : CommutingFactors A B)
    (hz : Subgroup.center G = ⊥) {b : G} (hb : b ∈ B) : h.projectLeft hz b = 1 := by
  simpa using h.projectLeft_factors hz A.one_mem hb

end CommutingFactors

end FiniteDirectRefinement

end SimpleAmenable
end
end

end OAI
end

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

theorem commute_of_conditional_move (u v k : H) (hv : Commute u v)
    (hk : Commute u (v*k*v⁻¹)) : Commute u k := by
  have h := (hv.inv_right.mul_right hk).mul_right hv
  simpa only [mul_assoc,inv_mul_cancel_left,mul_inv_cancel_right,inv_mul_cancel,mul_one] using h

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
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_ConditionalFamilyLaws
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
section ConditionalFamilyLaws

variable {ι E H Ω : Type*} [Group E] [Group H]

theorem copyFamilyEval_perfect [Group.IsPerfect E] (F : ι → E →* H) :
    Group.IsPerfect (copyFamilyEval F).range := by
  rw [copyFamilyEval_range]
  let (i : ι) : Group.IsPerfect (F i).range := Group.IsPerfect.range (F i)
  exact perfect_iSup (fun i => (F i).range)

end ConditionalFamilyLaws

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_FreshEvenBank
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
section FreshEvenBank

theorem even_move_embedding {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
    (hn : n + 2 ≤ Nat.card α) (s t : Fin n ↪ α) :
    ∃ σ : alternatingGroup α, ∀ i, σ.val (s i) = t i := by
  let :=  alternatingGroup.isMultiplyPretransitive α
  let : MulAction.IsMultiplyPretransitive (alternatingGroup α) α n :=
    MulAction.isMultiplyPretransitive_of_le (by omega : n ≤ Nat.card α - 2)
      (Nat.sub_le _ _)
  obtain ⟨σ,hσ⟩ := MulAction.exists_smul_eq (alternatingGroup α) s t
  exact ⟨σ,fun i => congrArg (fun e : Fin n ↪ α => e i) hσ⟩

theorem fresh_five_bank {α : Type*} [Fintype α] [DecidableEq α] (J : Finset α)
    (hJ : J.card + 5 ≤ Fintype.card α) :
    ∃ t : Fin 5 ↪ α, Disjoint (Finset.univ.map t) J := by
  classical
  have hc : 5 ≤ Jᶜ.card := by rw [Finset.card_compl]; omega
  have he : Nonempty (Fin 5 ↪ {x : α // x ∈ Jᶜ}) := by
    rw [Function.Embedding.nonempty_iff_card_le,Fintype.card_fin,Fintype.card_coe]
    exact hc
  obtain ⟨e⟩ := he
  refine ⟨e.trans (Function.Embedding.subtype _),?_⟩
  apply Finset.disjoint_left.mpr
  intro x hx hj
  obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hx
  exact Finset.mem_compl.mp (e i).property hj

theorem even_move_disjoint_banks {α : Type*} [Fintype α] [DecidableEq α]
    (s t : Fin 5 ↪ α) (hd : Disjoint (Finset.univ.map s) (Finset.univ.map t)) :
    ∃ σ : alternatingGroup α,
      (∀ i, σ.val (s i) = t i) ∧
      σ.val.support ⊆ (Finset.univ.map s) ∪ (Finset.univ.map t) := by
  classical
  let S := (Finset.univ.map s) ∪ (Finset.univ.map t)
  let T := {x : α // x ∈ S}
  let s' : Fin 5 ↪ T := ⟨fun i => ⟨s i,Finset.mem_union_left _ (Finset.mem_map.mpr
    ⟨i,Finset.mem_univ _,rfl⟩)⟩,fun _ _ h => s.injective (congrArg Subtype.val h)⟩
  let t' : Fin 5 ↪ T := ⟨fun i => ⟨t i,Finset.mem_union_right _ (Finset.mem_map.mpr
    ⟨i,Finset.mem_univ _,rfl⟩)⟩,fun _ _ h => t.injective (congrArg Subtype.val h)⟩
  have hT : Nat.card T = 10 := by
    rw [Nat.card_eq_fintype_card,Fintype.card_coe]
    dsimp only [S]
    rw [Finset.card_union_of_disjoint hd,Finset.card_map,Finset.card_map]
    simp
  obtain ⟨ρ,hρ⟩ := even_move_embedding (by omega : 5+2 ≤ Nat.card T) s' t'
  let e : T ↪ α := Function.Embedding.subtype _
  let σ := ρ.val.viaEmbedding e
  have hσ : σ ∈ alternatingGroup α := by
    change Equiv.Perm.sign (ρ.val.viaEmbedding e) = 1
    rw [Equiv.Perm.viaEmbedding,Equiv.Perm.sign_extendDomain]
    exact ρ.property
  refine ⟨⟨σ,hσ⟩,?_,?_⟩
  · intro i
    change ρ.val.viaEmbedding e (e (s' i)) = t i
    rw [Equiv.Perm.viaEmbedding_apply,hρ]
    rfl
  · intro x hx
    by_contra hn
    have he : x ∉ Set.range e := by
      rintro ⟨y,rfl⟩
      exact hn y.property
    exact Equiv.Perm.mem_support.mp hx (Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ he)

end FreshEvenBank

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_OperationalControl
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
section OperationalControl

variable {α H : Type*} [Fintype α] [DecidableEq α] [Group H]

theorem fresh_bank_conditional_control (L : Finset α → Subgroup H)
    (c : alternatingGroup α →* H)
    (hc : ∀ σ I, ∀ x ∈ L I, c σ*x*(c σ)⁻¹ ∈ L (I.map σ.val.toEmbedding))
    (hd : ∀ I J, Disjoint I J → ∀ x ∈ L I, ∀ y ∈ L J, Commute x y)
    (s : Fin 5 ↪ α) (J : Finset α) (u x : H) (hu : u ∈ L J)
    (hx : x ∈ L (Finset.univ.map s))
    (hreserve : (J ∪ Finset.univ.map s).card + 5 ≤ Fintype.card α)
    (hv : ∀ (σ : alternatingGroup α), σ.val.support.card ≤ 10 →
      ∃ v : H, Commute u v ∧ v*x*v⁻¹ = c σ*x*(c σ)⁻¹) : Commute u x := by
  obtain ⟨t,ht⟩ := fresh_five_bank (J ∪ Finset.univ.map s) hreserve
  have hst : Disjoint (Finset.univ.map s) (Finset.univ.map t) :=
    (ht.mono_right Finset.subset_union_right).symm
  obtain ⟨σ,hσ,hsupp⟩ := even_move_disjoint_banks s t hst
  have hcard : σ.val.support.card ≤ 10 := by
    apply (Finset.card_le_card hsupp).trans
    rw [Finset.card_union_of_disjoint hst,Finset.card_map,Finset.card_map]
    simp
  obtain ⟨v,huv,hv⟩ := hv σ hcard
  apply commute_of_conditional_move u v x huv
  rw [hv]
  have hem : (Finset.univ.map s).map σ.val.toEmbedding = Finset.univ.map t := by
    rw [Finset.map_map]
    congr 1
    exact Function.Embedding.ext hσ
  have hm := hc σ (Finset.univ.map s) x hx
  rw [hem] at hm
  exact hd J (Finset.univ.map t) (ht.mono_right Finset.subset_union_left).symm u hu _ hm

end OperationalControl

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_SmallControlCalculus
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
section SmallControlCalculus
variable {α H : Type*} [Fintype α] [DecidableEq α] [Group H]
    [Group.IsPerfect (alternatingGroup α)]

omit [Fintype α] [DecidableEq α] [Group.IsPerfect (alternatingGroup α)] in
theorem five_bank_of_card (I : Finset α) (hI : I.card = 5) :
    ∃ s : Fin 5 ↪ α, Finset.univ.map s = I := by
  classical
  let e : Fin 5 ≃ I := (Fintype.equivFinOfCardEq (by simpa using hI)).symm
  let s := e.toEmbedding.trans (Function.Embedding.subtype (· ∈ I))
  refine ⟨s,?_⟩
  ext x
  constructor
  · rintro hx
    obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hx
    exact (e i).property
  · intro hx
    obtain ⟨i,hi⟩ := e.surjective ⟨x,hx⟩
    exact Finset.mem_map.mpr ⟨i,Finset.mem_univ _,congrArg Subtype.val hi⟩

omit [Group.IsPerfect (alternatingGroup α)] in

theorem small_star_representative (hα : 10 ≤ Fintype.card α)
    (σ : alternatingGroup α) (hσ : σ.val.support.card ≤ 10) :
    ∃ (I : ControlAlphabet α) (t : UniversalExtension (alternatingGroup I.val)),
      subtypeAlternatingHom I.val (universalProjection (alternatingGroup I.val) t) = σ := by
  obtain ⟨I,hSI,_,hI⟩ := Finset.exists_subsuperset_card_eq
    (Finset.subset_univ σ.val.support) hσ (by simpa using hα)
  let J : ControlAlphabet α := ⟨I,by omega,by omega⟩
  obtain ⟨s,hs⟩ := (subtypeAlternatingHom_mem_range I σ).mpr hSI
  let := alphabetPerfect I (by omega)
  obtain ⟨t,ht⟩ := universalProjection_surjective (alternatingGroup J.val) s
  exact ⟨J,t,by simpa only [ht] using hs⟩

theorem small_control_transfer (L : Finset α → Subgroup H)
    (c : alternatingGroup α →* H)
    (hc : ∀ σ I, ∀ x ∈ L I, c σ*x*(c σ)⁻¹ ∈ L (I.map σ.val.toEmbedding))
    (hd : ∀ I J, Disjoint I J → ∀ x ∈ L I, ∀ y ∈ L J, Commute x y)
    (f g : TrackStar α →* H) (hf : SmallSupported L f) (hfg : SmallControlled c f g)
    (J : Finset α) (u : H) (hu : u ∈ L J) (hreserve : J.card+10 ≤ Fintype.card α)
    (hug : ∀ (I : ControlAlphabet α) t, Commute u (g (universalMap (subtypeAlternatingHom I.val) t))) :
    ∀ x ∈ f.range, Commute u x := by
  classical
  let C := Subgroup.centralizer ({u} : Set H)
  have hC : f.range ≤ C := by
    rw [MonoidHom.range_eq_map,← universal_five_alphabet_generate (by omega : 5 ≤ Fintype.card α),
      Subgroup.map_iSup]
    apply iSup_le
    intro I
    rw [← MonoidHom.range_comp]
    rintro x ⟨t,rfl⟩
    let A : ControlAlphabet α := ⟨I.val,by have hh := I.property.2; omega,by have hh := I.property.2; omega⟩
    have hx : f (universalMap (subtypeAlternatingHom I.val) t) ∈ L I.val :=
      hf A ⟨t,rfl⟩
    obtain ⟨s,hs⟩ := five_bank_of_card I.val I.property.2
    have hx' : f (universalMap (subtypeAlternatingHom I.val) t) ∈ L (Finset.univ.map s) := by
      rwa [hs]
    have hres : (J ∪ Finset.univ.map s).card + 5 ≤ Fintype.card α := by
      rw [hs]
      have hh := Finset.card_union_le J I.val
      rw [I.property.2] at hh
      omega
    have hh := fresh_bank_conditional_control L c hc hd s J u
      (f (universalMap (subtypeAlternatingHom I.val) t)) hu hx' hres ?_
    · intro y hy
      obtain rfl := Set.mem_singleton_iff.mp hy
      exact hh.eq
    · intro σ hσ
      obtain ⟨K,v,hv⟩ := small_star_representative (by omega : 10 ≤ Fintype.card α) σ hσ
      refine ⟨g (universalMap (subtypeAlternatingHom K.val) v),hug K v,?_⟩
      have hh := hfg K v _ ⟨universalMap (subtypeAlternatingHom I.val) t,rfl⟩
      have he := DFunLike.congr_fun (universalMap_spec (subtypeAlternatingHom K.val)) v
      change universalProjection (alternatingGroup α) (universalMap (subtypeAlternatingHom K.val) v) = _ at he
      simpa only [MonoidHom.comp_apply,he,hv] using hh
  intro x hx
  exact hC hx u (Set.mem_singleton u)

end SmallControlCalculus

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_SmallControlTransfer
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
section SmallControlTransfer
variable {α H : Type*} [Fintype α] [DecidableEq α] [Group H]
    [Group.IsPerfect (alternatingGroup α)]
    (L : Finset α → Subgroup H) (c : alternatingGroup α →* H)
    (hc : ∀ σ I, ∀ x ∈ L I, c σ*x*(c σ)⁻¹ ∈ L (I.map σ.val.toEmbedding))
    (hd : ∀ I J, Disjoint I J → ∀ x ∈ L I, ∀ y ∈ L J, Commute x y)

include hc hd in

theorem small_control_disjoint (hα : 20 ≤ Fintype.card α)
    (f g j k : TrackStar α →* H)
    (hf : SmallSupported L f) (hg : SmallSupported L g) (hj : SmallSupported L j)
    (hfj : SmallControlled c f j) (hgk : SmallControlled c g k)
    (hjk : ∀ s t, Commute (j s) (k t)) : ∀ s t, Commute (f s) (g t) := by
  have hjg (I : ControlAlphabet α) (s : UniversalExtension (alternatingGroup I.val)) :
      ∀ x ∈ g.range, Commute (j (universalMap (subtypeAlternatingHom I.val) s)) x :=
    small_control_transfer L c hc hd g k hg hgk I.val _ (hj I ⟨s,rfl⟩)
      (by have hh := I.property.2; omega) (fun J t => hjk _ _)
  have hfg (I : ControlAlphabet α) (t : UniversalExtension (alternatingGroup I.val)) :
      ∀ x ∈ f.range, Commute (g (universalMap (subtypeAlternatingHom I.val) t)) x :=
    small_control_transfer L c hc hd f j hf hfj I.val _ (hg I ⟨t,rfl⟩)
      (by have hh := I.property.2; omega)
      (fun J s => (hjg J s _ ⟨universalMap (subtypeAlternatingHom I.val) t,rfl⟩).symm)
  intro s
  let C := Subgroup.centralizer ({f s} : Set H)
  have hC : g.range ≤ C := by
    rw [MonoidHom.range_eq_map,← universal_five_alphabet_generate (by omega : 5 ≤ Fintype.card α),
      Subgroup.map_iSup]
    apply iSup_le
    intro I
    rw [← MonoidHom.range_comp]
    rintro x ⟨t,rfl⟩ y hy
    obtain rfl := Set.mem_singleton_iff.mp hy
    let J : ControlAlphabet α := ⟨I.val,by have hh := I.property.2; omega,
      by have hh := I.property.2; omega⟩
    exact (hfg J t _ ⟨s,rfl⟩).eq.symm
  intro t
  exact hC ⟨t,rfl⟩ (f s) (Set.mem_singleton _)

end SmallControlTransfer

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

theorem refinement_projection (i : ι) :
    ((h i).projectLeft hz).comp (refinementEquiv A B h hz).toMonoidHom =
      (refinementEquiv A B h hz).toMonoidHom.comp
        (assignmentRestriction (fun σ : ι → Bool => refinedFactor A B Finset.univ σ)
          {σ | σ i = true}) := by
  classical
  apply MonoidHom.pi_ext
  intro σ s
  change (h i).projectLeft hz (refinementEquiv A B h hz (Pi.mulSingle σ s)) =
    refinementEquiv A B h hz
      (assignmentRestriction (fun σ : ι → Bool => refinedFactor A B Finset.univ σ)
        {σ | σ i = true} (Pi.mulSingle σ s))
  rw [refinementEquiv_single, assignmentRestriction_single]
  have hs := s.property
  simp only [refinedFactor, assignmentFactor, Subgroup.mem_iInf, Finset.mem_univ,
    forall_const] at hs
  specialize hs i
  by_cases hσ : σ i = true
  · simp only [Set.mem_ofPred_eq, hσ, ↓reduceIte, refinementEquiv_single] at hs ⊢
    exact (h i).projectLeft_fix hz hs
  · simp only [Set.mem_ofPred_eq, hσ, Bool.false_eq_true, ↓reduceIte] at hs ⊢
    rw [map_one]
    exact (h i).projectLeft_kill hz hs

theorem simultaneousAssignmentMap_test (c : E →* G) (i : ι) :
    (simultaneousAssignmentMap A B h hz c).comp (sectorMask {σ | σ i = true}) =
      ((h i).projectLeft hz).comp c := by
  ext s
  have hp := DFunLike.congr_fun (refinement_projection A B h hz i)
    ((refinementEquiv A B h hz).symm (c s))
  change (h i).projectLeft hz
      (refinementEquiv A B h hz ((refinementEquiv A B h hz).symm (c s))) =
    refinementEquiv A B h hz
      (assignmentRestriction (fun σ : ι → Bool => refinedFactor A B Finset.univ σ)
        {σ | σ i = true} ((refinementEquiv A B h hz).symm (c s))) at hp
  rw [MulEquiv.apply_symm_apply] at hp
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hp]
  change refinementEquiv A B h hz _ = refinementEquiv A B h hz _
  apply (refinementEquiv A B h hz).congr_arg
  ext σ
  by_cases hσ : σ i = true
  · simp [refinementSource, sectorMask, assignmentRestriction, hσ]
  · simp [refinementSource, sectorMask, assignmentRestriction, hσ]

theorem range_comp_subset {X Y Z : Type*} [Group X] [Group Y] [Group Z]
    (f : Y →* Z) (g : X →* Y) : (f.comp g).range ≤ f.range := by
  rintro y ⟨x, rfl⟩
  exact ⟨g x, rfl⟩

theorem simultaneous_assignment_surjection (c : E →* G) (g : ι → E →* G)
    (hinput : ∀ i, g i = ((h i).projectLeft hz).comp c)
    (hgenerate : c.range ⊔ ⨆ i, (g i).range = ⊤) :
    ∃ φ : ((ι → Bool) → E) →* G,
      Function.Surjective φ ∧ φ.comp (sectorMask Set.univ) = c ∧
        ∀ i, φ.comp (sectorMask {σ | σ i = true}) = g i := by
  let φ := simultaneousAssignmentMap A B h hz c
  have hwhole : φ.comp (sectorMask Set.univ) = c :=
    simultaneousAssignmentMap_whole A B h hz c
  have htest : ∀ i, φ.comp (sectorMask {σ | σ i = true}) = g i := by
    intro i
    exact (simultaneousAssignmentMap_test A B h hz c i).trans (hinput i).symm
  refine ⟨φ, ?_, hwhole, htest⟩
  apply MonoidHom.range_eq_top.mp
  apply top_unique
  calc
    ⊤ = c.range ⊔ ⨆ i, (g i).range := hgenerate.symm
    _ ≤ φ.range := sup_le ?_ (iSup_le fun i => ?_)
  · calc c.range = (φ.comp (sectorMask Set.univ)).range :=
            congrArg MonoidHom.range hwhole.symm
         _ ≤ φ.range := range_comp_subset φ _
  · calc (g _).range = (φ.comp (sectorMask {σ | σ _ = true})).range :=
            congrArg MonoidHom.range (htest _).symm
         _ ≤ φ.range := range_comp_subset φ _

end PairLawAssembly

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_GrowthAxisUniform
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

section SplitAssignment
variable {E S G ι κ : Type*} [Group E] [Group S] [Group G]

theorem iSup_ranges_commute (f : ι → E →* G) (g : κ → S →* G)
    (h : ∀ i j s t, Commute (f i s) (g j t)) :
    ∀ x ∈ ⨆ i, (f i).range, ∀ y ∈ ⨆ j, (g j).range, Commute x y := by
  intro x hx
  let C := Subgroup.centralizer ((⨆ j, (g j).range : Subgroup G) : Set G)
  have hf : (⨆ i, (f i).range : Subgroup G) ≤ C := by
    apply iSup_le
    intro i z hz
    obtain ⟨s,rfl⟩ := hz
    have hg : (⨆ j, (g j).range : Subgroup G) ≤ Subgroup.centralizer ({f i s} : Set G) := by
      apply iSup_le
      rintro j y ⟨t,rfl⟩ z hz
      obtain rfl := Set.mem_singleton_iff.mp hz
      exact (h i j s t).eq
    intro y hy
    exact (hg hy _ (Set.mem_singleton _)).symm
  intro y hy
  exact (show Commute y x from hf hx y hy).symm

theorem commutingFactors_of_generate (F L R : ι → E →* G)
    (hgen : (⨆ i, (F i).range : Subgroup G) = ⊤)
    (hsplit : ∀ i s, F i s = L i s*R i s)
    (hcomm : ∀ i j s t, Commute (L i s) (R j t)) :
    CommutingFactors (⨆ i, (L i).range) (⨆ i, (R i).range) := by
  have hLR := iSup_ranges_commute L R hcomm
  let p := splitFactorProduct (⨆ i, (L i).range) (⨆ i, (R i).range) hLR
  have hp : p.range = ⊤ := by
    apply top_unique
    rw [← hgen]
    apply iSup_le
    rintro i x ⟨s,rfl⟩
    exact ⟨(⟨L i s,le_iSup (fun i => (L i).range) i ⟨s,rfl⟩⟩,
      ⟨R i s,le_iSup (fun i => (R i).range) i ⟨s,rfl⟩⟩),(hsplit i s).symm⟩
  refine ⟨hLR,?_⟩
  intro x
  obtain ⟨⟨u,v⟩,huv⟩ := MonoidHom.range_eq_top.mp hp x
  exact ⟨u,u.property,v,v.property,huv.symm⟩

theorem star_split_assignment [Fintype ι] [Group.IsPerfect G]
    (π : E →* S) (_hπ : Function.Surjective π) (c : S →* G)
    (F : Option ι → E →* G) (hc : F none = c.comp π)
    (hgen : (⨆ i, (F i).range : Subgroup G) = ⊤)
    (L R : ι → Option ι → E →* G)
    (hsplit : ∀ i j s, F j s = L i j s*R i j s)
    (hcomm : ∀ i j k s t, Commute (L i j s) (R i k t))
    (hleft : ∀ i, L i none = F (some i)) :
    ∃ φ : ((ι → Bool) → S) →* (G ⧸ Subgroup.center G),
      Function.Surjective φ ∧
      φ.comp (sectorMask Set.univ) = (QuotientGroup.mk' _).comp c ∧
      ∀ i, (φ.comp (sectorMask {σ | σ i = true})).comp π =
        (QuotientGroup.mk' _).comp (F (some i)) := by
  let q : G →* G ⧸ Subgroup.center G := QuotientGroup.mk' _
  let F' := fun i => q.comp (F i)
  let L' := fun i j => q.comp (L i j)
  let R' := fun i j => q.comp (R i j)
  have hgen' : (⨆ i, (F' i).range : Subgroup (G ⧸ Subgroup.center G)) = ⊤ := by
    simp only [F',MonoidHom.range_comp]
    rw [← Subgroup.map_iSup,hgen,← MonoidHom.range_eq_map,MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)]
  have hs' i j s : F' j s = L' i j s*R' i j s := by
    dsimp [F',L',R']; rw [hsplit,map_mul]
  have hm' i j k s t : Commute (L' i j s) (R' i k t) := (hcomm i j k s t).map q
  let A := fun i => ⨆ j, (L' i j).range
  let B := fun i => ⨆ j, (R' i j).range
  have hAB i : CommutingFactors (A i) (B i) :=
    commutingFactors_of_generate F' (L' i) (R' i) hgen' (hs' i) (hm' i)
  have hz : Subgroup.center (G ⧸ Subgroup.center G) = ⊥ := perfect_center_quotient
  let g := fun i => ((hAB i).projectLeft hz).comp (q.comp c)
  have hg i : (g i).comp π = F' (some i) := by
    ext s
    change (hAB i).projectLeft hz (q (c (π s))) = q (F (some i) s)
    rw [← show F none s = c (π s) from DFunLike.congr_fun hc s]
    change (hAB i).projectLeft hz (F' none s) = F' (some i) s
    rw [hs' i none s,(hAB i).projectLeft_factors hz
      (le_iSup (fun j => (L' i j).range) none ⟨s,rfl⟩)
      (le_iSup (fun j => (R' i j).range) none ⟨s,rfl⟩)]
    exact congrArg (fun f : E →* G => q (f s)) (hleft i)
  have hggen : (q.comp c).range ⊔ ⨆ i, (g i).range = ⊤ := by
    apply top_unique
    rw [← hgen']
    apply iSup_le
    intro i
    cases i with
    | none =>
      have h : F' none = (q.comp c).comp π := by dsimp [F']; rw [hc,MonoidHom.comp_assoc]
      rw [h]
      exact (range_comp_subset _ _).trans le_sup_left
    | some i =>
      rw [← hg i]
      exact (range_comp_subset _ _).trans ((le_iSup (fun i => (g i).range) i).trans le_sup_right)
  obtain ⟨φ,hφ,hφc,hφg⟩ := simultaneous_assignment_surjection A B hAB hz (q.comp c) g (fun _ => rfl) hggen
  exact ⟨φ,hφ,hφc,fun i => by rw [hφg]; exact hg i⟩

end SplitAssignment

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_FormalCoordinates
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

section CodRestrictGeneration
variable {E G ι : Type*} [Group E] [Group G]

theorem codRestrict_iSup_top (F : ι → E →* G) (K : Subgroup G)
    (hm : ∀ i s, F i s ∈ K) (hgen : (⨆ i, (F i).range : Subgroup G) = K) :
    (⨆ i, (MonoidHom.codRestrict (F i) K (hm i)).range : Subgroup K) = ⊤ := by
  apply (Subgroup.map_injective K.subtype_injective)
  rw [Subgroup.map_iSup]
  have he (i : ι) : Subgroup.map K.subtype ((MonoidHom.codRestrict (F i) K (hm i)).range) = (F i).range := by
    rw [← MonoidHom.range_comp]
    rfl
  simp only [he]
  rw [hgen,← MonoidHom.range_eq_map,K.range_subtype]

end CodRestrictGeneration

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

theorem sector_mem (U : Set (ι → Bool)) (s : TrackStar α) :
    T.sector U s ∈ (copyFamilyEval F).range := by
  rw [← T.carrier_eq]
  exact (centralSector T.model U s).property

theorem sector_union {U V : Set (ι → Bool)} (hd : Disjoint U V) (s : TrackStar α) :
    T.sector (U ∪ V) s=T.sector U s*T.sector V s := by
  change (centralSector T.model (U ∪ V) s).val=_
  rw [centralSector_union T.model hd]
  rfl

theorem sector_commute {U V : Set (ι → Bool)} (hd : Disjoint U V) (s t : TrackStar α) :
    Commute (T.sector U s) (T.sector V t) := (centralSector_commute T.model hd s t).map T.carrier.subtype

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
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_FormalPairSplits
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
section FormalPairSplits
variable {α ι H : Type*} [Fintype α] [DecidableEq α] [Group H]
    [Group.IsPerfect (alternatingGroup α)]

variable (F : Option ι → TrackStar α →* H)
    (T : ∀ i j, FormalStarTable (starPair F i j))

theorem formalPair_container_shared (i j : ι) (b : Bool) :
    formalPairContainer F T i b=(T i j).sector {σ | σ false=b} := by
  cases b with
  | true =>
    exact ((T i i).sector_input (some false)).trans
      ((T i j).sector_input (some false)).symm
  | false =>
    ext s
    have hd : Disjoint {σ : Bool → Bool | σ false=true} {σ | σ false=false} := by
      apply Set.disjoint_left.mpr; intro σ ht hf
      exact Bool.false_ne_true (hf.symm.trans ht)
    have he : ({σ : Bool → Bool | σ false=true} ∪ {σ | σ false=false})=Set.univ := by
      ext σ; simp only [Set.mem_union,Set.mem_ofPred_eq,Set.mem_univ,iff_true]
      cases σ false <;> simp
    have hi := (T i i).sector_union hd s
    have hj := (T i j).sector_union hd s
    rw [he,(T i i).sector_input none,(T i i).sector_input (some false)] at hi
    rw [he,(T i j).sector_input none,(T i j).sector_input (some false)] at hj
    change (T i i).sector _ s=(T i j).sector _ s
    exact mul_left_cancel (hi.symm.trans hj)

theorem formalPair_split (i : ι) (j : Option ι) (s : TrackStar α) :
    F j s=formalPairSplit F T i j true s*formalPairSplit F T i j false s := by
  classical
  let U : Set (Bool → Bool) := match j with | none => Set.univ | some _ => {σ | σ true=true}
  have hd : Disjoint (U ∩ {σ | σ false=true}) (U ∩ {σ | σ false=false}) := by
    apply Set.disjoint_left.mpr; intro σ ht hf
    exact Bool.false_ne_true (hf.2.symm.trans ht.2)
  have he : (U ∩ {σ | σ false=true}) ∪ (U ∩ {σ | σ false=false})=U := by
    ext σ
    simp only [Set.mem_union,Set.mem_inter_iff,Set.mem_ofPred_eq]
    cases σ false <;> simp
  have hh := (T i (j.getD i)).sector_union hd s
  rw [he] at hh
  have hi : (T i (j.getD i)).sector U=F j := by
    cases j with
    | none => exact (T i i).sector_input none
    | some j => exact (T i j).sector_input (some true)
  rw [hi] at hh
  exact hh

theorem formalPair_split_whole (i : ι) : formalPairSplit F T i none true=F (some i) := by
  change (T i i).sector (Set.univ ∩ _)=_
  rw [Set.univ_inter]
  exact (T i i).sector_input (some false)

theorem formalPair_mem (i : ι) (j : Option ι) (b : Bool) (s : TrackStar α) :
    formalPairSplit F T i j b s ∈ (copyFamilyEval F).range := by
  have hh := (T i (j.getD i)).sector_mem
    ((match j with | none => Set.univ | some _ => {σ | σ true=true}) ∩ {σ | σ false=b}) s
  apply Set.mem_of_subset_of_mem (show (copyFamilyEval (starPair F i (j.getD i))).range ≤ _ from ?_) hh
  rw [copyFamilyEval_range,copyFamilyEval_range]
  apply iSup_le
  intro k
  cases k with
  | none => exact le_iSup (fun j => (F j).range) none
  | some b => cases b <;> exact le_iSup (fun j => (F j).range) _

theorem formalPair_supported (L : Finset α → Subgroup H)
    (hF : ∀ j, SmallSupported L (F j)) (i : ι) (j : Option ι) (b : Bool) :
    SmallSupported L (formalPairSplit F T i j b) := by
  apply FormalStarTable.sector_supported
  intro k
  cases k with
  | none => exact hF none
  | some b => cases b <;> exact hF _

theorem formalPair_container_supported (L : Finset α → Subgroup H)
    (hF : ∀ j, SmallSupported L (F j)) (i : ι) (b : Bool) :
    SmallSupported L (formalPairContainer F T i b) := by
  apply FormalStarTable.sector_supported
  intro k
  cases k with
  | none => exact hF none
  | some b => cases b <;> exact hF _

theorem formalPair_control (c : alternatingGroup α →* H)
    (hc : F none=c.comp (universalProjection (alternatingGroup α)))
    (i : ι) (j : Option ι) (b : Bool) :
    SmallControlled c (formalPairSplit F T i j b) (formalPairContainer F T i b) := by
  rw [formalPair_container_shared F T i (j.getD i)]
  have hh := (T i (j.getD i)).sector_control
    (show ((match j with | none => Set.univ | some _ => {σ | σ true=true}) ∩
      {σ | σ false=b}) ⊆ {σ | σ false=b} from Set.inter_subset_right)
  intro I s x hx
  have he := hh (universalMap (subtypeAlternatingHom I.val) s) x hx
  change _=(F none (universalMap (subtypeAlternatingHom I.val) s))*x*
    (F none (universalMap (subtypeAlternatingHom I.val) s))⁻¹ at he
  simpa only [hc,MonoidHom.comp_apply] using he

theorem formalPair_containers_commute (i : ι) (s t : TrackStar α) :
    Commute (formalPairContainer F T i true s) (formalPairContainer F T i false t) := by
  apply FormalStarTable.sector_commute
  apply Set.disjoint_left.mpr
  intro σ ht hf
  exact Bool.false_ne_true (hf.symm.trans ht)

end FormalPairSplits

section FormalPairAssembly
variable {α ι H : Type*} [Fintype α] [DecidableEq α] [Fintype ι] [Group H]
    [Group.IsPerfect (alternatingGroup α)]

theorem formal_pairs_assemble_oai (hα : 20 ≤ Fintype.card α)
    (L : Finset α → Subgroup H) (c : alternatingGroup α →* H)
    (hc : ∀ σ I, ∀ x ∈ L I, c σ*x*(c σ)⁻¹ ∈ L (I.map σ.val.toEmbedding))
    (hd : ∀ I J, Disjoint I J → ∀ x ∈ L I, ∀ y ∈ L J, Commute x y)
    (F : Option ι → TrackStar α →* H) (hF : ∀ j, SmallSupported L (F j))
    (h0 : F none=c.comp (universalProjection (alternatingGroup α)))
    (T : ∀ i j, FormalStarTable (starPair F i j)) : Nonempty (FormalStarTable F) := by
  let K := (copyFamilyEval F).range
  have hm (i : Option ι) (s : TrackStar α) : F i s ∈ K :=
    ⟨FreeGroup.of (i,s),copyFamilyEval_of F i s⟩
  let F' := fun i => (F i).codRestrict K (hm i)
  let : Group.IsPerfect K := copyFamilyEval_perfect F
  have hcm (s : alternatingGroup α) : c s ∈ K := by
    obtain ⟨t,rfl⟩ := universalProjection_surjective (alternatingGroup α) s
    rw [← MonoidHom.comp_apply,← h0]
    exact hm none t
  let c' := c.codRestrict K hcm
  have h0' : F' none=c'.comp (universalProjection (alternatingGroup α)) := by
    ext s
    exact DFunLike.congr_fun h0 s
  let Fl := fun i j => (formalPairSplit F T i j true).codRestrict K (formalPair_mem F T i j true)
  let Fr := fun i j => (formalPairSplit F T i j false).codRestrict K (formalPair_mem F T i j false)
  obtain ⟨φ,hφ,hφc,hφi⟩ := star_split_assignment
    (universalProjection (alternatingGroup α)) (universalProjection_surjective _) c' F' h0'
    (codRestrict_iSup_top F K hm (copyFamilyEval_range F).symm) Fl Fr
    (fun i j s => Subtype.ext (formalPair_split F T i j s))
    (fun i j k s t => by
      apply Subtype.ext
      exact (small_control_disjoint L c hc hd hα _ _ _ _
        (formalPair_supported F T L hF i j true)
        (formalPair_supported F T L hF i k false)
        (formalPair_container_supported F T L hF i true)
        (formalPair_control F T c h0 i j true)
        (formalPair_control F T c h0 i k false)
        (formalPair_containers_commute F T i) s t).eq)
    (fun i => by ext s; exact DFunLike.congr_fun (formalPair_split_whole F T i) s)
  refine ⟨⟨K,rfl,F',(fun _ => rfl),φ,hφ,?_⟩⟩
  intro i
  cases i with
  | none =>
    change φ.comp ((sectorMask Set.univ).comp _)=_
    rw [← MonoidHom.comp_assoc,hφc,MonoidHom.comp_assoc,← h0']
  | some i => exact hφi i

end FormalPairAssembly

end SimpleAmenable
end
end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.SimpleAmenable.formal_pairs_assemble_oai.{u_1, u_2, u_3} := @OAI.SimpleAmenable.formal_pairs_assemble_oai.{u_1, u_2, u_3}
