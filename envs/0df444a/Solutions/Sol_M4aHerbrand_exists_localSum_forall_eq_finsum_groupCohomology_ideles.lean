-- Prove2me | solution 1 for M4aHerbrand.exists_localSum_forall_eq_finsum_groupCohomology_ideles
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/48f56b00-bf9e-507d-a7f2-3b6a5b11f7d9

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_NumberField_SIdeleModule
import Definitions.Def_NumberField_PlaceAbove
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import Theorems.Thm_NumberField_PlaceDecomp_exists_localLevel_ringEquiv_adicCompletion
import Theorems.Thm_ExtCitation_LocalLevel_existsUnique_isLocalFundamentalClass
import Theorems.Thm_ExtCitation_LocalLevel_isZero_H1_and_natCard_H2_and_span_res_of_isLocalFundamentalClass
import Theorems.Thm_NumberField_PlaceDecomp_map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion
import Theorems.Thm_NumberField_PlaceDecomp_mem_adicCompletionIntegers_iff_norm_le_one_and_natCast_mem_asIdeal_of_ringEquiv
import Theorems.Thm_NumberField_PlaceDecomp_faithfulSMul_decomp
import Theorems.Thm_M4aHerbrand_injective_and_finite_and_surjective_localCoordinates_groupCohomology_ideles
import Theorems.Thm_M4aHerbrand_exists_hom_res_decomp_ideles_adicCompletion_apply
import Theorems.Thm_M4aHerbrand_exists_hom_res_infPlaceDecomp_ideles_localUnits_apply
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_M4aHerbrand_exists_localSum_forall_eq_finsum_groupCohomology_ideles
p2m_attr_erase "instance" "ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion NumberField.AdelicHaar.locallyCompactSpace_adeleRing NumberField.AdelicHaar.finite_residueField_adicCompletionIntegers NumberField.AdelicHaar.locallyCompactSpace_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_finiteAdeleRing NumberField.AdelicHaar.compactSpace_adicCompletionIntegers NumberField.AdelicHaar.t2Space_finiteAdeleRing NumberField.AdelicHaar.t2Space_matrix_adeleRing NumberField.AdelicHaar.t2Space_adeleRing NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers NumberField.AdelicHaar.t2Space_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_matrix_adeleRing NumberField.AdelicHaar.t2Space_infiniteAdeleRing NumberField.AdelicHaar.properSpace_adicCompletion M4aHerbrand.Bridge.instT2SpaceAdeleRing"
p2m_attr_erase "simp" "IsLocalRing.principalUnits_zero groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq M4aHerbrand.Bridge.finiteConorm_apply M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv"
p2m_attr_erase "simp" "RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk"
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000
p2m_open "CategoryTheory NumberField IsDedekindDomain M4aHerbrand P2MW.S_M4aHerbrand_exists_localSum_forall_eq_finsum_groupCohomology_ideles.M4aHerbrand"
open scoped NumberField.PlaceDecomp

namespace M4aHerbrand
p2m_export "M4aHerbrand" "finPart repHomOfMulEquivariant repHomOfMulEquivariant_hom_apply IdeleGaloisDescent injective_and_finite_and_surjective_localCoordinates_groupCohomology_ideles exists_hom_res_decomp_ideles_adicCompletion_apply exists_hom_res_infPlaceDecomp_ideles_localUnits_apply"
namespace LocalSum
p2m_open "M4aHerbrand"

theorem addCircle_div_eq_div_of_dvd {N : ℕ} (hN : 0 < N) {a b : ℤ} (h : (N : ℤ) ∣ a - b) :
    ((((a : ℚ) / (N : ℚ) : ℚ)) : AddCircle (1 : ℚ)) = ((((b : ℚ) / (N : ℚ) : ℚ)) : AddCircle (1 : ℚ)) := by
  obtain ⟨k, hk⟩ := h
  have hN' : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [← sub_eq_zero, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff]
  refine ⟨k, ?_⟩
  rw [zsmul_one, ← sub_div, eq_div_iff hN']
  have hk' : ((a : ℚ) - (b : ℚ)) = ((N : ℤ) : ℚ) * (k : ℚ) := by exact_mod_cast hk
  rw [hk']
  push_cast
  ring

theorem exists_addMonoidHom_addCircle {M : Type*} [AddCommGroup M] (g : M) (N : ℕ) (hN : 0 < N)
    (hgen : ∀ c : M, ∃ m : ℤ, c = m • g) (hord : ∀ m : ℤ, m • g = 0 → (N : ℤ) ∣ m) :
    ∃ ι : M →+ AddCircle (1 : ℚ), ∀ (c : M) (m : ℤ), c = m • g →
      ι c = ((((m : ℚ) / (N : ℚ) : ℚ)) : AddCircle (1 : ℚ)) := by
  classical

  have hwd : ∀ (c : M) (m m' : ℤ), c = m • g → c = m' • g → (N : ℤ) ∣ m - m' := by
    intro c m m' h h'
    apply hord
    rw [sub_zsmul, ← h, ← h']
    exact add_neg_cancel c
  let f : M → AddCircle (1 : ℚ) := fun c => (((((Classical.choose (hgen c) : ℤ) : ℚ) / (N : ℚ) : ℚ)) : AddCircle (1 : ℚ))
  have hf : ∀ (c : M) (m : ℤ), c = m • g → f c = ((((m : ℚ) / (N : ℚ) : ℚ)) : AddCircle (1 : ℚ)) := fun c m h =>
    addCircle_div_eq_div_of_dvd hN (hwd c _ _ (Classical.choose_spec (hgen c)) h)
  refine ⟨{ toFun := f, map_zero' := ?_, map_add' := ?_ }, fun c m h => hf c m h⟩
  · rw [hf 0 0 (by rw [zero_zsmul])]
    simp
  · intro c d
    obtain ⟨m, hm⟩ := hgen c
    obtain ⟨m', hm'⟩ := hgen d
    show f (c + d) = f c + f d
    rw [hf c m hm, hf d m' hm', hf (c + d) (m + m') (by rw [hm, hm', add_zsmul]), ← AddCircle.coe_add]
    push_cast
    rw [add_div]

section Cohomology

variable {G : Type} [Group G]

theorem map_top_subtype_injective (B : Rep ℤ G) :
    Function.Injective (groupCohomology.map (⊤ : Subgroup G).subtype (𝟙 (Rep.res (⊤ : Subgroup G).subtype B)) 2).hom := by
  let eT : G →* ↥(⊤ : Subgroup G) := (Subgroup.topEquiv : ↥(⊤ : Subgroup G) ≃* G).symm.toMonoidHom
  have key : groupCohomology.map (⊤ : Subgroup G).subtype (𝟙 (Rep.res (⊤ : Subgroup G).subtype B)) 2 ≫
      groupCohomology.map eT (𝟙 (Rep.res eT (Rep.res (⊤ : Subgroup G).subtype B))) 2 = 𝟙 _ := by
    rw [← groupCohomology.map_comp]
    exact groupCohomology.map_id (B := B) (n := 2)
  have hleft : ∀ y : groupCohomology B 2,
      (groupCohomology.map eT (𝟙 (Rep.res eT (Rep.res (⊤ : Subgroup G).subtype B))) 2).hom
        ((groupCohomology.map (⊤ : Subgroup G).subtype (𝟙 (Rep.res (⊤ : Subgroup G).subtype B)) 2).hom y) = y := by
    intro y
    have hy := congrArg (fun T => (ModuleCat.Hom.hom T) y) key
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hy
    exact hy
  exact Function.LeftInverse.injective hleft

variable {A B : Rep ℤ G} (θ : B ⟶ A) (θ' : A ⟶ B) (u : groupCohomology B 2)

theorem exists_eq_zsmul_map_of_span (hθ'θ : θ' ≫ θ = 𝟙 A)
    (hspan : Submodule.span ℤ {(groupCohomology.map (⊤ : Subgroup G).subtype (𝟙 (Rep.res (⊤ : Subgroup G).subtype B)) 2).hom u} = ⊤)
    (c : groupCohomology A 2) :
    ∃ m : ℤ, c = m • (groupCohomology.map (MonoidHom.id G) θ 2).hom u := by
  have hback : ∀ y : groupCohomology A 2,
      (groupCohomology.map (MonoidHom.id G) θ 2).hom ((groupCohomology.map (MonoidHom.id G) θ' 2).hom y) = y := by
    intro y
    have hc' := congrArg (fun T => (ModuleCat.Hom.hom T) y) (groupCohomology.map_id_comp θ' θ 2)
    simp only [hθ'θ, groupCohomology.map_id, ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.comp_apply,
      LinearMap.id_apply] at hc'
    exact hc'.symm
  set X' := (groupCohomology.map (MonoidHom.id G) θ' 2).hom c with hX'
  have hmem : (groupCohomology.map (⊤ : Subgroup G).subtype (𝟙 (Rep.res (⊤ : Subgroup G).subtype B)) 2).hom X' ∈
      Submodule.span ℤ {(groupCohomology.map (⊤ : Subgroup G).subtype (𝟙 (Rep.res (⊤ : Subgroup G).subtype B)) 2).hom u} := by
    rw [hspan]; trivial
  obtain ⟨m₀, hm₀⟩ := Submodule.mem_span_singleton.mp hmem
  refine ⟨m₀, ?_⟩
  have hXu : X' = m₀ • u := by
    apply map_top_subtype_injective B
    rw [map_zsmul, ← hm₀]
    exact int_smul_eq_zsmul _ m₀ _
  calc c = (groupCohomology.map (MonoidHom.id G) θ 2).hom X' := (hback _).symm
    _ = m₀ • (groupCohomology.map (MonoidHom.id G) θ 2).hom u := by rw [hXu, map_zsmul]

theorem natCard_dvd_of_zsmul_map_eq_zero [Finite G] (hθθ' : θ ≫ θ' = 𝟙 B)
    (hcard : ∀ (S : Subgroup G) [Fintype S], Nat.card (groupCohomology (Rep.res S.subtype B) 2) = Fintype.card S)
    (hspan : Submodule.span ℤ {(groupCohomology.map (⊤ : Subgroup G).subtype (𝟙 (Rep.res (⊤ : Subgroup G).subtype B)) 2).hom u} = ⊤)
    (m : ℤ) (hm : m • (groupCohomology.map (MonoidHom.id G) θ 2).hom u = 0) : (Nat.card G : ℤ) ∣ m := by

  have hleft : ∀ y : groupCohomology B 2,
      (groupCohomology.map (MonoidHom.id G) θ' 2).hom ((groupCohomology.map (MonoidHom.id G) θ 2).hom y) = y := by
    intro y
    have hc' := congrArg (fun T => (ModuleCat.Hom.hom T) y) (groupCohomology.map_id_comp θ θ' 2)
    simp only [hθθ', groupCohomology.map_id, ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.comp_apply,
      LinearMap.id_apply] at hc'
    exact hc'.symm
  have hm' : m • u = 0 := by
    have h := congrArg ((groupCohomology.map (MonoidHom.id G) θ' 2).hom) hm
    rw [map_zsmul, map_zero, hleft] at h
    exact h

  haveI : Fintype (⊤ : Subgroup G) := Fintype.ofFinite _
  have hc := hcard ⊤
  haveI : Finite ↥(groupCohomology (Rep.res (⊤ : Subgroup G).subtype B) 2) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; exact Fintype.card_ne_zero)
  haveI : Fintype ↥(groupCohomology (Rep.res (⊤ : Subgroup G).subtype B) 2) := Fintype.ofFinite _
  set u₀ := (groupCohomology.map (⊤ : Subgroup G).subtype (𝟙 (Rep.res (⊤ : Subgroup G).subtype B)) 2).hom u with hu₀
  have hgen : ∀ y, y ∈ AddSubgroup.zmultiples u₀ := fun y => by
    have hy : y ∈ Submodule.span ℤ {u₀} := by rw [hspan]; trivial
    obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp hy
    exact ⟨k, (int_smul_eq_zsmul _ k u₀).symm.trans hk⟩
  have hordu : addOrderOf u₀ = Nat.card G := by
    rw [addOrderOf_eq_card_of_forall_mem_zmultiples hgen, hc, ← Nat.card_eq_fintype_card, Subgroup.card_top]
  have hm0 : m • u₀ = 0 := by
    rw [hu₀, ← map_zsmul, hm', map_zero]
  rw [← hordu]
  exact (addOrderOf_dvd_iff_zsmul_eq_zero).mpr hm0

end Cohomology

end M4aHerbrand.LocalSum

namespace M4aHerbrand
p2m_export "M4aHerbrand" "finPart repHomOfMulEquivariant repHomOfMulEquivariant_hom_apply IdeleGaloisDescent injective_and_finite_and_surjective_localCoordinates_groupCohomology_ideles exists_hom_res_decomp_ideles_adicCompletion_apply exists_hom_res_infPlaceDecomp_ideles_localUnits_apply"
namespace LocalSum
p2m_open "M4aHerbrand"

section Bridge

variable (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
  (w : HeightOneSpectrum (𝓞 F))

theorem exists_unitsTransport {q : ℕ} [Fact q.Prime] (L : IntermediateField ℚ_[q] (PadicAlgCl q))
    [MulSemiringAction ↥(NumberField.PlaceDecomp.decomp E F w) L] [MulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F w) (↥L)ˣ]
    (Φ : (w.adicCompletion F) ≃+* L)
    (hΦ₂ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (y : (↥L)ˣ), ((g • y : (↥L)ˣ) : L) = g • (y : L))
    (hΦ₃ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (y : (w.adicCompletion F)), Φ (g • y) = g • Φ y) :
    ∃ (θ : Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F w) (↥L)ˣ ⟶ Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F w) (w.adicCompletion F)ˣ)
      (θ' : Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F w) (w.adicCompletion F)ˣ ⟶ Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F w) (↥L)ˣ),
      (∀ y : (↥L)ˣ, ((Additive.toMul (θ.hom (Additive.ofMul y)) : (w.adicCompletion F)ˣ) : (w.adicCompletion F)) = Φ.symm (y : L)) ∧
      θ ≫ θ' = 𝟙 _ ∧ θ' ≫ θ = 𝟙 _ := by
  let ΨM : (↥L)ˣ →* (w.adicCompletion F)ˣ := Units.map Φ.symm.toRingHom.toMonoidHom
  have hΨM : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (y : (↥L)ˣ), ΨM (g • y) = g • ΨM y := by
    intro g y
    apply Units.ext
    show Φ.symm ((g • y : (↥L)ˣ) : ↥L) = ((g • ΨM y : (w.adicCompletion F)ˣ) : (w.adicCompletion F))
    rw [hΦ₂ g y, NumberField.PlaceDecomp.coe_smul_units]
    apply Φ.injective
    rw [hΦ₃ g, RingEquiv.apply_symm_apply]
    congr 1
    exact (Φ.apply_symm_apply _).symm
  let ΦM : (w.adicCompletion F)ˣ →* (↥L)ˣ := Units.map Φ.toRingHom.toMonoidHom
  have hΦM : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (m : (w.adicCompletion F)ˣ), ΦM (g • m) = g • ΦM m := by
    intro g m
    apply Units.ext
    rw [hΦ₂ g (ΦM m)]
    show Φ ((g • m : (w.adicCompletion F)ˣ) : (w.adicCompletion F)) = g • Φ (m : (w.adicCompletion F))
    rw [NumberField.PlaceDecomp.coe_smul_units, hΦ₃ g]
  refine ⟨M4aHerbrand.repHomOfMulEquivariant ΨM hΨM, M4aHerbrand.repHomOfMulEquivariant ΦM hΦM, fun y => rfl, ?_, ?_⟩
  · refine Rep.hom_ext ?_
    ext z
    rw [Rep.hom_comp, Rep.hom_id]
    show (M4aHerbrand.repHomOfMulEquivariant ΦM hΦM).hom ((M4aHerbrand.repHomOfMulEquivariant ΨM hΨM).hom z) = z
    rw [M4aHerbrand.repHomOfMulEquivariant_hom_apply, M4aHerbrand.repHomOfMulEquivariant_hom_apply]
    refine (congrArg Additive.ofMul ?_).trans (ofMul_toMul z)
    apply Units.ext
    exact Φ.apply_symm_apply _
  · refine Rep.hom_ext ?_
    ext z
    rw [Rep.hom_comp, Rep.hom_id]
    show (M4aHerbrand.repHomOfMulEquivariant ΨM hΨM).hom ((M4aHerbrand.repHomOfMulEquivariant ΦM hΦM).hom z) = z
    rw [M4aHerbrand.repHomOfMulEquivariant_hom_apply, M4aHerbrand.repHomOfMulEquivariant_hom_apply]
    refine (congrArg Additive.ofMul ?_).trans (ofMul_toMul z)
    apply Units.ext
    exact Φ.symm_apply_apply _

structure BridgeDatum where
  q : ℕ
  [hq : Fact q.Prime]
  L : IntermediateField ℚ_[q] (PadicAlgCl q)
  [fd : FiniteDimensional ℚ_[q] L]
  [sma : MulSemiringAction ↥(NumberField.PlaceDecomp.decomp E F w) L]
  [fs : FaithfulSMul ↥(NumberField.PlaceDecomp.decomp E F w) L]
  [mda : MulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F w) (↥L)ˣ]
  Φ : (w.adicCompletion F) ≃+* L
  h1 : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x
  h2 : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (y : (↥L)ˣ), ((g • y : (↥L)ˣ) : L) = g • (y : L)
  h3 : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (y : (w.adicCompletion F)), Φ (g • y) = g • Φ y
  hqw : ((q : ℕ) : 𝓞 F) ∈ w.asIdeal
  K₀ : IntermediateField ℚ_[q] (PadicAlgCl q)
  [fd₀ : FiniteDimensional ℚ_[q] K₀]
  base : ExtCitation.LocalLevel.IsBase q L ↥(NumberField.PlaceDecomp.decomp E F w) K₀
  θ : Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F w) (↥L)ˣ ⟶ Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F w) (w.adicCompletion F)ˣ
  θ' : Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F w) (w.adicCompletion F)ˣ ⟶ Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F w) (↥L)ˣ
  hθ : ∀ y : (↥L)ˣ, ((Additive.toMul (θ.hom (Additive.ofMul y)) : (w.adicCompletion F)ˣ) : (w.adicCompletion F)) = Φ.symm (y : L)
  hθθ' : θ ≫ θ' = 𝟙 _
  hθ'θ : θ' ≫ θ = 𝟙 _
  u : groupCohomology.H2 (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F w) (↥L)ˣ)
  hu : ExtCitation.LocalLevel.IsLocalFundamentalClass q L ↥(NumberField.PlaceDecomp.decomp E F w) K₀ u
  hcard : ∀ (S : Subgroup ↥(NumberField.PlaceDecomp.decomp E F w)) [Fintype S],
    Nat.card (groupCohomology (Rep.res S.subtype (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F w) (↥L)ˣ)) 2) = Fintype.card S
  hspan : ∀ S : Subgroup ↥(NumberField.PlaceDecomp.decomp E F w),
    Submodule.span ℤ {(groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F w) (↥L)ˣ))) 2).hom u} = ⊤

theorem exists_isBase (q : ℕ) [Fact q.Prime] (L : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L]
    (G : Type) [Group G] [MulSemiringAction G L]
    (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x) :
    ∃ (K : IntermediateField ℚ_[q] (PadicAlgCl q)) (_ : FiniteDimensional ℚ_[q] K), ExtCitation.LocalLevel.IsBase q L G K := by
  haveI : SMulCommClass G ℚ_[q] L := ⟨fun g c x => by rw [Algebra.smul_def, Algebra.smul_def, smul_mul', hG]⟩
  refine ⟨IntermediateField.lift (FixedPoints.intermediateField G : IntermediateField ℚ_[q] L), ?_, ?_⟩
  · exact FiniteDimensional.of_injective
      (IntermediateField.inclusion (IntermediateField.lift_le (FixedPoints.intermediateField G : IntermediateField ℚ_[q] L))).toLinearMap
      (fun a b h => (IntermediateField.inclusion
        (IntermediateField.lift_le (FixedPoints.intermediateField G : IntermediateField ℚ_[q] L))).toRingHom.injective h)
  · refine ⟨IntermediateField.lift_le _, fun x => ?_⟩
    rw [IntermediateField.mem_lift]
    exact Iff.rfl

theorem nonempty_bridgeDatum [IsCyclic (F ≃ₐ[E] F)] : Nonempty (BridgeDatum E F w) := by
  obtain ⟨q, hq, L, fd, sma, fs, mda, Φ, h1, h2, h3, hqw⟩ := NumberField.PlaceDecomp.exists_localLevel_ringEquiv_adicCompletion E F w
  obtain ⟨K₀, fd₀, base⟩ := exists_isBase q L ↥(NumberField.PlaceDecomp.decomp E F w) h1
  obtain ⟨θ, θ', hθ, hθθ', hθ'θ⟩ := exists_unitsTransport E F w L Φ h2 h3
  have hcomm : ∀ a b : F ≃ₐ[E] F, a * b = b * a := fun a b => by
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := F ≃ₐ[E] F)
    obtain ⟨i, rfl⟩ := hg a
    obtain ⟨j, rfl⟩ := hg b
    rw [← zpow_add, ← zpow_add, add_comm]
  have hsolv : Group.IsSolvable ↥(NumberField.PlaceDecomp.decomp E F w) :=
    Group.isSolvable_of_comm (fun g₁ g₂ => Subtype.ext (hcomm (g₁ : F ≃ₐ[E] F) (g₂ : F ≃ₐ[E] F)))
  obtain ⟨u, hu⟩ := (ExtCitation.LocalLevel.existsUnique_isLocalFundamentalClass q L ↥(NumberField.PlaceDecomp.decomp E F w) h1 h2 hsolv K₀ base).exists
  obtain ⟨-, hcard, hspan⟩ :=
    ExtCitation.LocalLevel.isZero_H1_and_natCard_H2_and_span_res_of_isLocalFundamentalClass q L ↥(NumberField.PlaceDecomp.decomp E F w) h1 h2 hsolv K₀ base u hu
  exact ⟨⟨q, L, Φ, h1, h2, h3, hqw, K₀, base, θ, θ', hθ, hθθ', hθ'θ, u, hu, hcard, hspan⟩⟩

end Bridge

section Chosen

variable (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F] [IsCyclic (F ≃ₐ[E] F)]
  (w : HeightOneSpectrum (𝓞 F))

noncomputable def bd : BridgeDatum E F w := Classical.choice (nonempty_bridgeDatum E F w)

noncomputable def gen : groupCohomology (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F w) (w.adicCompletion F)ˣ) 2 :=
  (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F w)) (bd E F w).θ 2).hom (bd E F w).u

theorem gen_generates (c : groupCohomology (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F w) (w.adicCompletion F)ˣ) 2) :
    ∃ m : ℤ, c = m • gen E F w :=
  exists_eq_zsmul_map_of_span (bd E F w).θ (bd E F w).θ' (bd E F w).u (bd E F w).hθ'θ ((bd E F w).hspan ⊤) c

theorem gen_order (m : ℤ) (hm : m • gen E F w = 0) : (Nat.card ↥(NumberField.PlaceDecomp.decomp E F w) : ℤ) ∣ m :=
  natCard_dvd_of_zsmul_map_eq_zero (bd E F w).θ (bd E F w).θ' (bd E F w).u (bd E F w).hθθ'
    (fun S => (bd E F w).hcard S) ((bd E F w).hspan ⊤) m hm

theorem exists_iota : ∃ ι : groupCohomology (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F w) (w.adicCompletion F)ˣ) 2 →+ AddCircle (1 : ℚ),
    ∀ (c : groupCohomology (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F w) (w.adicCompletion F)ˣ) 2) (m : ℤ), c = m • gen E F w →
      ι c = ((((m : ℚ) / (Nat.card ↥(NumberField.PlaceDecomp.decomp E F w) : ℚ) : ℚ)) : AddCircle (1 : ℚ)) :=
  exists_addMonoidHom_addCircle (gen E F w) (Nat.card ↥(NumberField.PlaceDecomp.decomp E F w)) Nat.card_pos (gen_generates E F w) (gen_order E F w)

noncomputable def iota : groupCohomology (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F w) (w.adicCompletion F)ˣ) 2 →+ AddCircle (1 : ℚ) :=
  Classical.choose (exists_iota E F w)

theorem iota_spec (c : groupCohomology (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F w) (w.adicCompletion F)ˣ) 2) (m : ℤ) (h : c = m • gen E F w) :
    iota E F w c = ((((m : ℚ) / (Nat.card ↥(NumberField.PlaceDecomp.decomp E F w) : ℚ) : ℚ)) : AddCircle (1 : ℚ)) :=
  Classical.choose_spec (exists_iota E F w) c m h

end Chosen

end M4aHerbrand.LocalSum

namespace M4aHerbrand
p2m_export "M4aHerbrand" "finPart repHomOfMulEquivariant repHomOfMulEquivariant_hom_apply IdeleGaloisDescent injective_and_finite_and_surjective_localCoordinates_groupCohomology_ideles exists_hom_res_decomp_ideles_adicCompletion_apply exists_hom_res_infPlaceDecomp_ideles_localUnits_apply"
namespace LocalSum
p2m_open "M4aHerbrand"

section Independence

variable (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F] [IsCyclic (F ≃ₐ[E] F)]
  (w : HeightOneSpectrum (𝓞 F))

theorem map_eq_gen {q₁ : ℕ} [Fact q₁.Prime] (L₁ : IntermediateField ℚ_[q₁] (PadicAlgCl q₁)) [FiniteDimensional ℚ_[q₁] L₁]
    [MulSemiringAction ↥(NumberField.PlaceDecomp.decomp E F w) L₁] [MulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F w) (↥L₁)ˣ]
    (Φ₁ : (w.adicCompletion F) ≃+* L₁)
    (h1 : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (y : ℚ_[q₁]), g • algebraMap ℚ_[q₁] L₁ y = algebraMap ℚ_[q₁] L₁ y)
    (h2 : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (y : (↥L₁)ˣ), ((g • y : (↥L₁)ˣ) : L₁) = g • (y : L₁))
    (h3 : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (y : (w.adicCompletion F)), Φ₁ (g • y) = g • Φ₁ y)
    (K₀₁ : IntermediateField ℚ_[q₁] (PadicAlgCl q₁)) [FiniteDimensional ℚ_[q₁] K₀₁]
    (base₁ : ExtCitation.LocalLevel.IsBase q₁ L₁ ↥(NumberField.PlaceDecomp.decomp E F w) K₀₁)
    (θ₁ : Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F w) (↥L₁)ˣ ⟶ Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F w) (w.adicCompletion F)ˣ)
    (hθ₁ : ∀ y : (↥L₁)ˣ, ((Additive.toMul (θ₁.hom (Additive.ofMul y)) : (w.adicCompletion F)ˣ) : (w.adicCompletion F)) = Φ₁.symm (y : L₁))
    (u₁ : groupCohomology.H2 (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F w) (↥L₁)ˣ))
    (hu₁ : ExtCitation.LocalLevel.IsLocalFundamentalClass q₁ L₁ ↥(NumberField.PlaceDecomp.decomp E F w) K₀₁ u₁) :
    (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F w)) θ₁ 2).hom u₁ = gen E F w := by
  haveI : FaithfulSMul ↥(NumberField.PlaceDecomp.decomp E F w) (w.adicCompletion F) := NumberField.PlaceDecomp.faithfulSMul_decomp E F w
  haveI : FaithfulSMul ↥(NumberField.PlaceDecomp.decomp E F w) L₁ := ⟨fun {g₁ g₂} h =>
    FaithfulSMul.eq_of_smul_eq_smul (α := (w.adicCompletion F)) fun y => Φ₁.injective (by rw [h3 g₁ y, h3 g₂ y]; exact h _)⟩
  obtain ⟨-, hqw₁⟩ :=
    NumberField.PlaceDecomp.mem_adicCompletionIntegers_iff_norm_le_one_and_natCast_mem_asIdeal_of_ringEquiv F w q₁ L₁ Φ₁
  haveI := (bd E F w).hq
  haveI := (bd E F w).fd
  letI := (bd E F w).sma
  haveI := (bd E F w).fs
  letI := (bd E F w).mda
  haveI := (bd E F w).fd₀
  exact NumberField.PlaceDecomp.map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion E F w
    q₁ hqw₁ L₁ Φ₁ h1 h2 h3 K₀₁ base₁ θ₁ hθ₁ u₁ hu₁
    (bd E F w).q (bd E F w).hqw (bd E F w).L (bd E F w).Φ (bd E F w).h1 (bd E F w).h2 (bd E F w).h3 (bd E F w).K₀ (bd E F w).base
    (bd E F w).θ (bd E F w).hθ (bd E F w).u (bd E F w).hu

end Independence

theorem above_injective (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] :
    Function.Injective (NumberField.PlaceAbove.above E F) := by
  intro v₁ v₂ h
  have h1 := NumberField.PlaceAbove.comap_above E F v₁
  have h2 := NumberField.PlaceAbove.comap_above E F v₂
  rw [h] at h1
  exact HeightOneSpectrum.ext (h1.symm.trans h2)

end M4aHerbrand.LocalSum

open M4aHerbrand.LocalSum in

theorem solution
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    [IsCyclic (F ≃ₐ[E] F)]
    (D : IdeleGaloisDescent (𝓞 F) E F)

    [MulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ]
    (hactI : ∀ (g : (F ≃ₐ[E] F)) (x : (AdeleRing (𝓞 F) F)ˣ), g • x = D.unitsAct g x)
    :
    ∃ Λ : ↥(groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) 2) →+ AddCircle (1 : ℚ),
      (∀

        (prG : ∀ w : HeightOneSpectrum (𝓞 F),
          Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) ⟶
            Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)
        (_ : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (AdeleRing (𝓞 F) F)ˣ), (prG w).hom (Additive.ofMul x) = Additive.ofMul (finPart w x))
        (x : ↥(groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) 2))

        (q : HeightOneSpectrum (𝓞 E) → ℕ) (_ : ∀ v, Fact (q v).Prime)
        (L' : ∀ v : HeightOneSpectrum (𝓞 E), IntermediateField ℚ_[q v] (PadicAlgCl (q v)))
        (_ : ∀ v, FiniteDimensional ℚ_[q v] (L' v))
        (_ : ∀ v : HeightOneSpectrum (𝓞 E), MulSemiringAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (L' v))
        (_ : ∀ v : HeightOneSpectrum (𝓞 E), MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (↥(L' v))ˣ)
        (Φ : ∀ v : HeightOneSpectrum (𝓞 E), (NumberField.PlaceAbove.above E F v).adicCompletion F ≃+* L' v)
        (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (g : ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (y : ℚ_[q v]), g • algebraMap ℚ_[q v] (L' v) y = algebraMap ℚ_[q v] (L' v) y)
        (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (g : ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (y : (↥(L' v))ˣ), ((g • y : (↥(L' v))ˣ) : L' v) = g • (y : L' v))
        (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (g : ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (y : (NumberField.PlaceAbove.above E F v).adicCompletion F), (Φ v) (g • y) = g • (Φ v) y)
        (K₀ : ∀ v : HeightOneSpectrum (𝓞 E), IntermediateField ℚ_[q v] (PadicAlgCl (q v)))
        (_ : ∀ v, FiniteDimensional ℚ_[q v] (K₀ v))
        (_ : ∀ v : HeightOneSpectrum (𝓞 E), ExtCitation.LocalLevel.IsBase (q v) (L' v) (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (K₀ v))
        (θ : ∀ v : HeightOneSpectrum (𝓞 E), Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (↥(L' v))ˣ ⟶
          Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) ((NumberField.PlaceAbove.above E F v).adicCompletion F)ˣ)
        (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (y : (↥(L' v))ˣ),
          ((Additive.toMul ((θ v).hom (Additive.ofMul y)) : ((NumberField.PlaceAbove.above E F v).adicCompletion F)ˣ) : (NumberField.PlaceAbove.above E F v).adicCompletion F) =
            (Φ v).symm (y : L' v))
        (u' : ∀ v : HeightOneSpectrum (𝓞 E), groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (↥(L' v))ˣ))
        (_ : ∀ v : HeightOneSpectrum (𝓞 E), ExtCitation.LocalLevel.IsLocalFundamentalClass (q v) (L' v) (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (K₀ v) (u' v))

        (n : HeightOneSpectrum (𝓞 E) → ℤ)
        (_ : ∀ v : HeightOneSpectrum (𝓞 E),
          (groupCohomology.map (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)).subtype (prG (NumberField.PlaceAbove.above E F v)) 2).hom x =
            n v • (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (θ v) 2).hom (u' v)),
        Λ x =
          ∑ᶠ v : HeightOneSpectrum (𝓞 E), ((((n v : ℚ) / (Nat.card ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)) : ℚ) : ℚ) : AddCircle (1 : ℚ)))) := by
  classical
  obtain ⟨prG₀, hprG₀⟩ := M4aHerbrand.exists_hom_res_decomp_ideles_adicCompletion_apply E F D hactI
  obtain ⟨prInf, hprInf⟩ := M4aHerbrand.exists_hom_res_infPlaceDecomp_ideles_localUnits_apply E F D hactI
  have hfin := (M4aHerbrand.injective_and_finite_and_surjective_localCoordinates_groupCohomology_ideles
    E F D hactI prG₀ hprG₀ prInf hprInf 1).2.1

  let cv : (v : HeightOneSpectrum (𝓞 E)) → ↥(groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) 2) →
      groupCohomology (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)) ((NumberField.PlaceAbove.above E F v).adicCompletion F)ˣ) 2 :=
    fun v x => (groupCohomology.map (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)).subtype (prG₀ (NumberField.PlaceAbove.above E F v)) 2).hom x
  let r : ↥(groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) 2) → HeightOneSpectrum (𝓞 E) → AddCircle (1 : ℚ) :=
    fun x v => iota E F (NumberField.PlaceAbove.above E F v) (cv v x)
  have hsupp : ∀ x, (Function.support (r x)).Finite := by
    intro x
    refine ((hfin x).preimage (above_injective E F).injOn).subset ?_
    intro v hv
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    intro h0
    apply hv
    show iota E F (NumberField.PlaceAbove.above E F v) (cv v x) = 0
    have : cv v x = 0 := h0
    rw [this, map_zero]
  refine ⟨{ toFun := fun x => ∑ᶠ v, r x v, map_zero' := ?_, map_add' := ?_ }, ?_⟩
  · show ∑ᶠ v, r 0 v = 0
    have : r 0 = fun _ => 0 := by
      funext v
      show iota E F (NumberField.PlaceAbove.above E F v) (cv v 0) = 0
      have : cv v 0 = 0 := map_zero _
      rw [this, map_zero]
    rw [this]
    exact finsum_zero
  · intro x y
    show ∑ᶠ v, r (x + y) v = ∑ᶠ v, r x v + ∑ᶠ v, r y v
    rw [← finsum_add_distrib (hsupp x) (hsupp y)]
    apply finsum_congr
    intro v
    show iota E F (NumberField.PlaceAbove.above E F v) (cv v (x + y)) = iota E F _ (cv v x) + iota E F _ (cv v y)
    have : cv v (x + y) = cv v x + cv v y := map_add _ _ _
    rw [this, map_add]
  · intro prG hpr x q hq L' hfd hsma hmda Φ hΦ1 hΦ2 hΦ3 K₀ hfd₀ hbase θ hθ u' hu' n hn
    have hprG : prG = prG₀ := by
      funext w
      refine Rep.hom_ext ?_
      ext z
      exact (hpr w (Additive.toMul z)).trans (hprG₀ w (Additive.toMul z)).symm
    subst hprG
    show ∑ᶠ v, r x v = _
    apply finsum_congr
    intro v
    haveI := hq v
    haveI := hfd v
    letI := hsma v
    letI := hmda v
    haveI := hfd₀ v
    have hg : (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (θ v) 2).hom (u' v) = gen E F (NumberField.PlaceAbove.above E F v) :=
      map_eq_gen E F (NumberField.PlaceAbove.above E F v) (L' v) (Φ v) (hΦ1 v) (hΦ2 v) (hΦ3 v) (K₀ v) (hbase v) (θ v) (hθ v) (u' v) (hu' v)
    show iota E F (NumberField.PlaceAbove.above E F v) (cv v x) = _
    apply iota_spec
    show (groupCohomology.map (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)).subtype (prG (NumberField.PlaceAbove.above E F v)) 2).hom x = _
    rw [hn v, hg]

end S_M4aHerbrand_exists_localSum_forall_eq_finsum_groupCohomology_ideles
end P2MW
export P2MW.S_M4aHerbrand_exists_localSum_forall_eq_finsum_groupCohomology_ideles (solution)
