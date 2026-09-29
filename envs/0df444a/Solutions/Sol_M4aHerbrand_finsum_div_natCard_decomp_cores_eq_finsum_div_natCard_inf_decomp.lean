-- Prove2me | solution 1 for M4aHerbrand.finsum_div_natCard_decomp_cores_eq_finsum_div_natCard_inf_decomp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/b8b6ca0a-c2bb-51d9-81af-152424b54447

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_NumberField_SIdeleModule
import Definitions.Def_NumberField_PlaceAbove
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import Definitions.Def_GroupCohomology_Corestriction2
import Theorems.Thm_NumberField_PlaceTransport_exists_bijective_doubleCoset_decomp_of_under_eq
import Theorems.Thm_groupCohomology_Cores_map_subtype_cores_eq_finsum_cores_map
import Theorems.Thm_Rep_exists_monoidHom_subgroupOf_conj_smul_and_hom_res_apply
import Theorems.Thm_groupCohomology_Cores_map_cores_eq_cores_map
import Theorems.Thm_NumberField_PlaceDecomp_exists_eq_zsmul_map_subtype_and_zsmul_eq_zero_iff_of_isLocalFundamentalClass
import Theorems.Thm_groupCohomology_Cores_cores_map_res_eq_index_smul
import Theorems.Thm_groupCohomology_bijective_map_top_subtype
import Theorems.Thm_M4aHerbrand_map_prG_map_eq_map_map_prH_of_smul_eq
import Theorems.Thm_NumberField_PlaceDecomp_exists_conj_subgroupOf_and_transport_repHom_of_smul_eq
import Theorems.Thm_M4aHerbrand_map_prH_eq_map_map_prH_of_smul_eq
import Theorems.Thm_NumberField_PlaceDecomp_exists_conj_and_transport_repHom_inf_decomp_of_smul_eq
import Theorems.Thm_NumberField_PlaceDecomp_exists_eq_zsmul_map_inclusion_and_zsmul_eq_zero_iff_of_isLocalFundamentalClass
import Theorems.Thm_ExtCitation_LocalLevel_isSolvable_of_faithfulSMul_of_padic
import Theorems.Thm_NumberField_PlaceDecomp_faithfulSMul_decomp
import Theorems.Thm_M4aHerbrand_injective_and_finite_and_surjective_localCoordinates_groupCohomology_res_ideles
import Theorems.Thm_M4aHerbrand_exists_hom_res_inf_infPlaceDecomp_ideles_completion_apply
import Theorems.Thm_NumberField_PlaceDecomp_map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion
import Theorems.Thm_NumberField_PlaceDecomp_mem_adicCompletionIntegers_iff_norm_le_one_and_natCast_mem_asIdeal_of_ringEquiv
import Theorems.Thm_NumberField_PlaceDecomp_exists_isLocalFundamentalClass_map_eq_map_of_smul_eq
import Theorems.Thm_NumberField_PlaceTransport_transport_trans_transport
import Theorems.Thm_NumberField_PlaceDecomp_exists_conj_and_transport_repHom_of_smul_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_M4aHerbrand_finsum_div_natCard_decomp_cores_eq_finsum_div_natCard_inf_decomp
p2m_attr_erase "instance" "FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing"
p2m_attr_erase "instance" "M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion NumberField.AdelicHaar.locallyCompactSpace_adeleRing NumberField.AdelicHaar.finite_residueField_adicCompletionIntegers NumberField.AdelicHaar.locallyCompactSpace_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_finiteAdeleRing NumberField.AdelicHaar.compactSpace_adicCompletionIntegers NumberField.AdelicHaar.t2Space_finiteAdeleRing NumberField.AdelicHaar.t2Space_matrix_adeleRing NumberField.AdelicHaar.t2Space_adeleRing NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers NumberField.AdelicHaar.t2Space_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_matrix_adeleRing NumberField.AdelicHaar.t2Space_infiniteAdeleRing NumberField.AdelicHaar.properSpace_adicCompletion M4aHerbrand.Bridge.instT2SpaceAdeleRing ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal"
p2m_attr_erase "simp" "IsLocalRing.principalUnits_zero M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq M4aHerbrand.Bridge.finiteConorm_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply"
p2m_attr_erase "simp" "IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply"
p2m_attr_erase "simp" "Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply"
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000
p2m_open "CategoryTheory NumberField IsDedekindDomain M4aHerbrand P2MW.S_M4aHerbrand_finsum_div_natCard_decomp_cores_eq_finsum_div_natCard_inf_decomp.M4aHerbrand"
open scoped NumberField.PlaceDecomp
open scoped Pointwise NumberField.PlaceTransport

namespace M4aHerbrand
p2m_export "M4aHerbrand" "finPart IdeleGaloisDescent map_prG_map_eq_map_map_prH_of_smul_eq map_prH_eq_map_map_prH_of_smul_eq injective_and_finite_and_surjective_localCoordinates_groupCohomology_res_ideles exists_hom_res_inf_infPlaceDecomp_ideles_completion_apply"
namespace CoresLocalProof
p2m_open "M4aHerbrand"

theorem map_eq_map_of_hom_eq {k G H : Type} [CommRing k] [Group G] [Group H] {A : Rep k H} {B : Rep k G}
    {f₁ f₂ : G →* H} (h : f₁ = f₂) (φ₁ : Rep.res f₁ A ⟶ B) (φ₂ : Rep.res f₂ A ⟶ B)
    (hφ : ∀ a : A, φ₁.hom a = φ₂.hom a) (n : ℕ) :
    groupCohomology.map f₁ φ₁ n = groupCohomology.map f₂ φ₂ n := by
  subst h
  obtain rfl : φ₁ = φ₂ := by
    ext a
    exact hφ a
  rfl

theorem map_eq_map_one_comp_map_id {k G H : Type} [CommRing k] [Group G] [Group H] {A : Rep k H} {B : Rep k G}
    (f : G →* H) (φ : Rep.res f A ⟶ B) (n : ℕ) (x : groupCohomology A n) :
    (groupCohomology.map f φ n).hom x
      = (groupCohomology.map (MonoidHom.id G) φ n).hom ((groupCohomology.map f (𝟙 (Rep.res f A)) n).hom x) := by
  have h1 := congrArg (fun T => T.hom x) (groupCohomology.map_comp f (MonoidHom.id G) (𝟙 (Rep.res f A)) φ n)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h1
  rw [← h1]
  exact congrArg (fun (T : groupCohomology A n ⟶ groupCohomology B n) => T.hom x)
    (map_eq_map_of_hom_eq (by ext; rfl) _ _ (fun a => rfl) n)

theorem map_map_map_eq_map_map {k G₀ G₁ G₂ G₃ H₁ : Type} [CommRing k] [Group G₀] [Group G₁] [Group G₂] [Group G₃] [Group H₁]
    {A₀ : Rep k G₀} {A₁ : Rep k G₁} {A₂ : Rep k G₂} {A₃ : Rep k G₃} {B₁ : Rep k H₁}
    (f₁ : G₁ →* G₀) (φ₁ : Rep.res f₁ A₀ ⟶ A₁) (f₂ : G₂ →* G₁) (φ₂ : Rep.res f₂ A₁ ⟶ A₂) (f₃ : G₃ →* G₂) (φ₃ : Rep.res f₃ A₂ ⟶ A₃)
    (g₁ : H₁ →* G₀) (ψ₁ : Rep.res g₁ A₀ ⟶ B₁) (g₂ : G₃ →* H₁) (ψ₂ : Rep.res g₂ B₁ ⟶ A₃)
    (hgrp : (f₁.comp f₂).comp f₃ = g₁.comp g₂) (hval : ∀ a : A₀, φ₃.hom (φ₂.hom (φ₁.hom a)) = ψ₂.hom (ψ₁.hom a))
    (n : ℕ) (x : groupCohomology A₀ n) :
    (groupCohomology.map f₃ φ₃ n).hom ((groupCohomology.map f₂ φ₂ n).hom ((groupCohomology.map f₁ φ₁ n).hom x))
      = (groupCohomology.map g₂ ψ₂ n).hom ((groupCohomology.map g₁ ψ₁ n).hom x) := by
  have h1 := congrArg (fun T => T.hom x) (groupCohomology.map_comp f₁ f₂ φ₁ φ₂ n)
  have h2 := congrArg (fun T => T.hom x) (groupCohomology.map_comp (f₁.comp f₂) f₃ ((Rep.resFunctor f₂).map φ₁ ≫ φ₂) φ₃ n)
  have h3 := congrArg (fun T => T.hom x) (groupCohomology.map_comp g₁ g₂ ψ₁ ψ₂ n)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h1 h2 h3
  rw [← h1, ← h2, ← h3]
  exact congrArg (fun (T : groupCohomology A₀ n ⟶ groupCohomology A₃ n) => T.hom x)
    (map_eq_map_of_hom_eq hgrp _ _ (fun a => hval a) n)

theorem coe_eq_coe_of_sub_eq_int {a b : ℚ} (z : ℤ) (h : a - b = z) : ((a : ℚ) : AddCircle (1 : ℚ)) = ((b : ℚ) : AddCircle (1 : ℚ)) := by
  rw [← sub_eq_zero, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff]
  exact ⟨z, by rw [h, zsmul_eq_mul, mul_one]⟩

theorem finsum_fiber_eq_finsum {α β M : Type} [AddCommMonoid M] (p : α → β) (f : α → M)
    (hf : (Function.support f).Finite) :
    ∑ᶠ b, ∑ᶠ a : {a // p a = b}, f a.1 = ∑ᶠ a, f a := by
  classical
  set S := hf.toFinset with hS
  have inner : ∀ b, ∑ᶠ a : {a // p a = b}, f a.1 = ∑ a ∈ S.filter (fun a => p a = b), f a := fun b => by
    have hs : (Function.support fun i : {a // p a = b} => f i.1) ⊆
        (((S.filter (fun a => p a = b)).subtype (fun a => p a = b) : Finset {a // p a = b}) : Set {a // p a = b}) := by
      intro i hi
      rw [Function.mem_support] at hi
      rw [Finset.mem_coe, Finset.mem_subtype, Finset.mem_filter]
      exact ⟨hf.mem_toFinset.2 hi, i.2⟩
    rw [finsum_eq_sum_of_support_subset _ hs]
    have := Finset.sum_map ((S.filter (fun a => p a = b)).subtype (fun a => p a = b)) (Function.Embedding.subtype _) f
    rw [Finset.subtype_map, Finset.filter_filter] at this
    simp only [and_self] at this
    exact this.symm
  simp_rw [inner]
  have hsupp : (Function.support fun b => ∑ a ∈ S.filter (fun a => p a = b), f a) ⊆ (S.image p : Set β) := by
    intro b hb
    rw [Function.mem_support] at hb
    obtain ⟨a, ha, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hb
    rw [Finset.mem_filter] at ha
    exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨a, ha.1, ha.2⟩)
  rw [finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_fiberwise_of_maps_to (fun a ha => Finset.mem_image_of_mem p ha),
    finsum_eq_sum_of_support_subset _ hf.coe_toFinset.symm.subset]

theorem coe_div_eq_zero_of_dvd (N : ℕ) (hN : 0 < N) (m : ℤ) (h : (N : ℤ) ∣ m) : ((((m : ℚ) / (N : ℚ) : ℚ)) : AddCircle (1 : ℚ)) = 0 := by
  obtain ⟨t, rfl⟩ := h
  rw [AddCircle.coe_eq_zero_iff]
  refine ⟨t, ?_⟩
  rw [zsmul_eq_mul, mul_one]
  have hN0 : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  push_cast
  field_simp

end M4aHerbrand.CoresLocalProof

theorem solution
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (D : IdeleGaloisDescent (𝓞 F) E F)

    [MulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ]
    (hactI : ∀ (g : (F ≃ₐ[E] F)) (x : (AdeleRing (𝓞 F) F)ˣ), g • x = D.unitsAct g x)
    (H : Subgroup (F ≃ₐ[E] F)) (τ : groupCohomology.Cores.Transversal H)
    (y : ↥(groupCohomology (Rep.res H.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ)) 2))

    (prG : ∀ w : HeightOneSpectrum (𝓞 F),
      Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)
    (_ : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (AdeleRing (𝓞 F) F)ˣ), (prG w).hom (Additive.ofMul x) = Additive.ofMul (finPart w x))

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
      (groupCohomology.map (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)).subtype (prG (NumberField.PlaceAbove.above E F v)) 2).hom (groupCohomology.Cores.cores (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) τ y) =
        n v • (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (θ v) 2).hom (u' v))

    (prH : ∀ w : HeightOneSpectrum (𝓞 F),
      Rep.res (Subgroup.inclusion (inf_le_left : H ⊓ (NumberField.PlaceDecomp.decomp E F w) ≤ H)) (Rep.res H.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ)) ⟶
        Rep.res (Subgroup.inclusion (inf_le_right : H ⊓ (NumberField.PlaceDecomp.decomp E F w) ≤ (NumberField.PlaceDecomp.decomp E F w)))
          (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ))
    (_ : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (AdeleRing (𝓞 F) F)ˣ), (prH w).hom (Additive.ofMul x) = Additive.ofMul (finPart w x))

    (qH : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)) → ℕ) (_ : ∀ v, Fact (qH v).Prime)
    (LH : ∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)), IntermediateField ℚ_[qH v] (PadicAlgCl (qH v)))
    (_ : ∀ v, FiniteDimensional ℚ_[qH v] (LH v))
    (_ : ∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)), MulSemiringAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))) (LH v))
    (_ : ∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)), MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))) (↥(LH v))ˣ)
    (ΦH : ∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)), (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v).adicCompletion F ≃+* LH v)
    (_ : ∀ (v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H))) (g : ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))) (y : ℚ_[qH v]), g • algebraMap ℚ_[qH v] (LH v) y = algebraMap ℚ_[qH v] (LH v) y)
    (_ : ∀ (v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H))) (g : ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))) (y : (↥(LH v))ˣ), ((g • y : (↥(LH v))ˣ) : LH v) = g • (y : LH v))
    (_ : ∀ (v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H))) (g : ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))) (y : (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v).adicCompletion F), (ΦH v) (g • y) = g • (ΦH v) y)
    (KH : ∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)), IntermediateField ℚ_[qH v] (PadicAlgCl (qH v)))
    (_ : ∀ v, FiniteDimensional ℚ_[qH v] (KH v))
    (_ : ∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)), ExtCitation.LocalLevel.IsBase (qH v) (LH v) (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))) (KH v))
    (θH : ∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)), Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))) (↥(LH v))ˣ ⟶
      Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))) ((NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v).adicCompletion F)ˣ)
    (_ : ∀ (v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H))) (y : (↥(LH v))ˣ),
      ((Additive.toMul ((θH v).hom (Additive.ofMul y)) : ((NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v).adicCompletion F)ˣ) : (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v).adicCompletion F) =
        (ΦH v).symm (y : LH v))
    (uH : ∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)), groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))) (↥(LH v))ˣ))
    (_ : ∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)), ExtCitation.LocalLevel.IsLocalFundamentalClass (qH v) (LH v) (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))) (KH v) (uH v))

    (m : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)) → ℤ)
    (_ : ∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)),
      (groupCohomology.map (Subgroup.inclusion (inf_le_left : H ⊓ (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v)) ≤ H)) (prH (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v)) 2).hom y =
        m v • (groupCohomology.map (Subgroup.inclusion (inf_le_right : H ⊓ (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v)) ≤ (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))))
          (𝟙 (Rep.res (Subgroup.inclusion (inf_le_right : H ⊓ (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v)) ≤ (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))))
            (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))) ((NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v).adicCompletion F)ˣ))) 2).hom
          ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))) (θH v) 2).hom (uH v))) :
    ∑ᶠ v : HeightOneSpectrum (𝓞 E), ((((n v : ℚ) / (Nat.card ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)) : ℚ) : ℚ) : AddCircle (1 : ℚ))) =
      ∑ᶠ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)), ((((m v : ℚ) / (Nat.card ↥(H ⊓ (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v))) : ℚ) : ℚ) : AddCircle (1 : ℚ))) := by
  open M4aHerbrand.CoresLocalProof in
  classical
  rename_i hprG hq hfL' aL' auL' hQ hU hΦ hfK₀ hB hθ hu' hn hprH hqH hfLH aLH auLH hQH hUH hΦH hfKH hBH hθH huH hm

  set f : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)) → AddCircle (1 : ℚ) := fun v' =>
    ((((m v' : ℚ) / (Nat.card ↥(H ⊓ (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v'))) : ℚ) : ℚ) : AddCircle (1 : ℚ)))
    with hf

  have hper : ∀ v : HeightOneSpectrum (𝓞 E),
      ((((n v : ℚ) / (Nat.card ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)) : ℚ) : ℚ) : AddCircle (1 : ℚ)))
        = ∑ᶠ i : {v' : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)) // v'.under (𝓞 E) = v}, f i.1 := by
    intro v

    have hunderw : (NumberField.PlaceAbove.above E F v).under (𝓞 E) = v := HeightOneSpectrum.ext (NumberField.PlaceAbove.comap_above E F v)
    obtain ⟨hfinι, g, hbij, ⟨i₀, -, hone⟩, hgunder, hconjH, hcard⟩ :=
      NumberField.PlaceTransport.exists_bijective_doubleCoset_decomp_of_under_eq E F H v (NumberField.PlaceAbove.above E F v) hunderw
    haveI := hfinι
    haveI : Fintype {v' : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)) // v'.under (𝓞 E) = v} := Fintype.ofFinite _

    have hCD := fun i => Rep.exists_monoidHom_subgroupOf_conj_smul_and_hom_res_apply
      (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) H (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)) (g i)
    choose c T hc hT using hCD
    let τD := fun i => Classical.choice (groupCohomology.Cores.Transversal.nonempty
      (H := (MulAut.conj (g i) • H).subgroupOf (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))))
    have hmac := groupCohomology.Cores.map_subtype_cores_eq_finsum_cores_map
      (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) H (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)) τ
      g hbij ⟨i₀, hone⟩ τD c hc T hT y

    haveI := hq v; haveI := hfL' v; letI := aL' v; letI := auL' v; haveI := hfK₀ v
    haveI : FaithfulSMul ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)) (L' v) := ⟨fun {g₁} {g₂} hg₁₂ => by
      haveI := NumberField.PlaceDecomp.faithfulSMul_decomp E F (NumberField.PlaceAbove.above E F v)
      refine FaithfulSMul.eq_of_smul_eq_smul (α := (NumberField.PlaceAbove.above E F v).adicCompletion F) fun yy => (Φ v).injective ?_
      rw [hΦ, hΦ, hg₁₂]⟩
    have hsolvD : Group.IsSolvable ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)) :=
      ExtCitation.LocalLevel.isSolvable_of_faithfulSMul_of_padic (q v) (L' v) _ (hQ v)

    have hcoordG := map_eq_map_one_comp_map_id (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)).subtype
      (prG (NumberField.PlaceAbove.above E F v)) 2 (groupCohomology.Cores.cores (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) τ y)
    set θu := (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (θ v) 2).hom (u' v) with hθu
    have hsum := hn v
    rw [hcoordG, hmac, finsum_eq_sum_of_fintype, map_sum] at hsum
    simp only [groupCohomology.Cores.map_cores_eq_cores_map] at hsum

    have hP2 := fun i => NumberField.PlaceDecomp.exists_eq_zsmul_map_subtype_and_zsmul_eq_zero_iff_of_isLocalFundamentalClass E F
      (NumberField.PlaceAbove.above E F v) hsolvD (q v) (L' v) (Φ v) (hQ v) (hU v) (hΦ v) (K₀ v) (hB v) (θ v) (hθ v) (u' v) (hu' v)
      ((MulAut.conj (g i) • H).subgroupOf (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)))
    have hk := fun i => (hP2 i).1 ((groupCohomology.map (MonoidHom.id _)
      ((Rep.resFunctor ((MulAut.conj (g i) • H).subgroupOf (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))).subtype).map
        (prG (NumberField.PlaceAbove.above E F v))) 2).hom ((groupCohomology.map (c i) (T i) 2).hom y))
    choose k hk using hk

    have hidx : ∀ i, groupCohomology.Cores.cores (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) ((NumberField.PlaceAbove.above E F v).adicCompletion F)ˣ) (τD i)
          ((groupCohomology.map (MonoidHom.id _)
            ((Rep.resFunctor ((MulAut.conj (g i) • H).subgroupOf (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))).subtype).map
              (prG (NumberField.PlaceAbove.above E F v))) 2).hom ((groupCohomology.map (c i) (T i) 2).hom y))
        = zmultiplesHom _ θu (k i * (((MulAut.conj (g i) • H).subgroupOf (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))).index : ℤ)) := fun i => by
      rw [hk i, map_zsmul, groupCohomology.Cores.cores_map_res_eq_index_smul, zmultiplesHom_apply, mul_zsmul, natCast_zsmul]
    simp only [hidx, ← map_sum] at hsum
    rw [zmultiplesHom_apply] at hsum

    have hP2top := (NumberField.PlaceDecomp.exists_eq_zsmul_map_subtype_and_zsmul_eq_zero_iff_of_isLocalFundamentalClass E F
      (NumberField.PlaceAbove.above E F v) hsolvD (q v) (L' v) (Φ v) (hQ v) (hU v) (hΦ v) (K₀ v) (hB v) (θ v) (hθ v) (u' v) (hu' v) ⊤).2
    have hdvd₀ : (Nat.card ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)) : ℤ) ∣
        n v - ∑ i, k i * (((MulAut.conj (g i) • H).subgroupOf (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))).index : ℤ) := by
      have h0 : (n v - ∑ i, k i * (((MulAut.conj (g i) • H).subgroupOf (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))).index : ℤ)) • θu = 0 := by rw [sub_zsmul, ← hsum, add_neg_cancel]
      have h1 := congrArg (groupCohomology.map (⊤ : Subgroup ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))).subtype
        (𝟙 (Rep.res (⊤ : Subgroup ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))).subtype
          (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) ((NumberField.PlaceAbove.above E F v).adicCompletion F)ˣ))) 2).hom h0
      rw [map_zsmul, map_zero] at h1
      rw [← Subgroup.card_top (G := ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))), ← hP2top]
      exact h1

    have hterm : ∀ i, (groupCohomology.map (MonoidHom.id _)
            ((Rep.resFunctor ((MulAut.conj (g i) • H).subgroupOf (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))).subtype).map
              (prG (NumberField.PlaceAbove.above E F v))) 2).hom ((groupCohomology.map (c i) (T i) 2).hom y)
        = m i.1 • (groupCohomology.map ((MulAut.conj (g i) • H).subgroupOf (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))).subtype
            (𝟙 (Rep.res ((MulAut.conj (g i) • H).subgroupOf (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))).subtype (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) ((NumberField.PlaceAbove.above E F v).adicCompletion F)ˣ))) 2).hom θu := by
      intro i

      have hg : (g i) • ((g i)⁻¹ • NumberField.PlaceAbove.above E F v) = NumberField.PlaceAbove.above E F v := smul_inv_smul _ _
      obtain ⟨-, c'', T'', -, hc'', hT''⟩ := NumberField.PlaceDecomp.exists_conj_subgroupOf_and_transport_repHom_of_smul_eq E F H
        (NumberField.PlaceAbove.above E F v) ((g i)⁻¹ • NumberField.PlaceAbove.above E F v) (g i) hg
      rw [M4aHerbrand.map_prG_map_eq_map_map_prH_of_smul_eq E F D hactI H prH hprH (NumberField.PlaceAbove.above E F v)
        (prG (NumberField.PlaceAbove.above E F v)) (hprG (NumberField.PlaceAbove.above E F v)) ((g i)⁻¹ • NumberField.PlaceAbove.above E F v)
        (g i) hg (c i) (hc i) (T i) (hT i) c'' hc'' T'' hT'' 2 y]
      obtain ⟨h, hh⟩ := hconjH i
      obtain ⟨-, ch, Th, -, hch, hTh⟩ := NumberField.PlaceDecomp.exists_conj_and_transport_repHom_inf_decomp_of_smul_eq E F H
        (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F i.1) ((g i)⁻¹ • NumberField.PlaceAbove.above E F v) h hh
      rw [M4aHerbrand.map_prH_eq_map_map_prH_of_smul_eq E F D hactI H prH hprH
        (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F i.1) ((g i)⁻¹ • NumberField.PlaceAbove.above E F v) h hh ch hch Th hTh 2 y,
        hm i.1, map_zsmul, map_zsmul]
      congr 1

      have hσ : ((g i) * (h : F ≃ₐ[E] F)) • (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F i.1) = NumberField.PlaceAbove.above E F v := by
        rw [mul_smul, hh, smul_inv_smul]
      obtain ⟨-, cσ, Tσ, -, hcσ, hTσ⟩ := NumberField.PlaceDecomp.exists_conj_and_transport_repHom_of_smul_eq E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F i.1) (NumberField.PlaceAbove.above E F v)
        ((g i) * (h : F ≃ₐ[E] F)) hσ

      have hfunc : (groupCohomology.map c'' T'' 2).hom ((groupCohomology.map ch Th 2).hom
            ((groupCohomology.map (Subgroup.inclusion (inf_le_right : H ⊓ (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F i.1)) ≤ (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F i.1))))
              (𝟙 (Rep.res (Subgroup.inclusion (inf_le_right : H ⊓ (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F i.1)) ≤ (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F i.1))))
                (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F i.1))) ((NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F i.1).adicCompletion F)ˣ))) 2).hom
              ((groupCohomology.map (MonoidHom.id _) (θH i.1) 2).hom (uH i.1))))
          = (groupCohomology.map ((MulAut.conj (g i) • H).subgroupOf (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))).subtype
              (𝟙 (Rep.res ((MulAut.conj (g i) • H).subgroupOf (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))).subtype (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) ((NumberField.PlaceAbove.above E F v).adicCompletion F)ˣ))) 2).hom
              ((groupCohomology.map cσ Tσ 2).hom ((groupCohomology.map (MonoidHom.id _) (θH i.1) 2).hom (uH i.1))) := by
        refine map_map_map_eq_map_map _ _ _ _ _ _ _ _ _ _ (MonoidHom.ext fun x => Subtype.ext ?_) (fun a => ?_) 2 _
        · change (((ch (c'' x) : ↥(H ⊓ (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F i.1)))) : F ≃ₐ[E] F))
            = ((cσ (((MulAut.conj (g i) • H).subgroupOf (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))).subtype x) : ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F i.1))) : F ≃ₐ[E] F)
          rw [hch, hc'', hcσ, mul_inv_rev]
          change _ = (h : F ≃ₐ[E] F)⁻¹ * (g i)⁻¹ * ((x : ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) : F ≃ₐ[E] F) * (g i * (h : F ≃ₐ[E] F))
          group
        · obtain ⟨x, rfl⟩ : ∃ x : ((NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F i.1).adicCompletion F)ˣ, Additive.ofMul x = a := ⟨Additive.toMul a, rfl⟩
          change T''.hom (Th.hom (Additive.ofMul x)) = Tσ.hom (Additive.ofMul x)
          apply (Additive.toMul : Additive ((NumberField.PlaceAbove.above E F v).adicCompletion F)ˣ ≃ ((NumberField.PlaceAbove.above E F v).adicCompletion F)ˣ).injective
          apply Units.ext
          refine (hT'' _).trans ?_
          refine Eq.trans ?_ (hTσ x).symm
          refine (congrArg (NumberField.PlaceTransport.transport (g i) hg) (hTh x)).trans ?_
          exact (RingEquiv.ext_iff.1 (NumberField.PlaceTransport.transport_trans_transport E F (g i) (h : F ≃ₐ[E] F) hh hg hσ) (x : (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F i.1).adicCompletion F))
      rw [hfunc]
      congr 1

      haveI := hqH i.1; haveI := hfLH i.1; letI := aLH i.1; letI := auLH i.1; haveI := hfKH i.1
      obtain ⟨-, act₁, actU₁, Φ₁, θ₁, u₁, hQ₁, hU₁, hΦ₁, hB₁, hθ₁, hu₁, hfund⟩ :=
        NumberField.PlaceDecomp.exists_isLocalFundamentalClass_map_eq_map_of_smul_eq E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F i.1) (NumberField.PlaceAbove.above E F v)
          ((g i) * (h : F ≃ₐ[E] F)) hσ cσ hcσ Tσ hTσ (qH i.1) (LH i.1) (ΦH i.1) (hQH i.1) (hUH i.1) (hΦH i.1) (KH i.1) (hBH i.1)
          (θH i.1) (hθH i.1) (uH i.1) (huH i.1)
      rw [hfund]

      letI := act₁; letI := actU₁
      haveI : FaithfulSMul ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)) (LH i.1) := ⟨fun {g₁} {g₂} hg₁₂ => by
        haveI := NumberField.PlaceDecomp.faithfulSMul_decomp E F (NumberField.PlaceAbove.above E F v)
        refine FaithfulSMul.eq_of_smul_eq_smul (α := (NumberField.PlaceAbove.above E F v).adicCompletion F) fun yy => Φ₁.injective ?_
        rw [hΦ₁, hΦ₁, hg₁₂]⟩
      exact NumberField.PlaceDecomp.map_eq_map_of_isLocalFundamentalClass_of_ringEquiv_adicCompletion E F (NumberField.PlaceAbove.above E F v)
        (qH i.1) (NumberField.PlaceDecomp.mem_adicCompletionIntegers_iff_norm_le_one_and_natCast_mem_asIdeal_of_ringEquiv F _ (qH i.1) (LH i.1) Φ₁).2
        (LH i.1) Φ₁ hQ₁ hU₁ hΦ₁ (KH i.1) hB₁ θ₁ hθ₁ u₁ hu₁
        (q v) (NumberField.PlaceDecomp.mem_adicCompletionIntegers_iff_norm_le_one_and_natCast_mem_asIdeal_of_ringEquiv F _ (q v) (L' v) (Φ v)).2
        (L' v) (Φ v) (hQ v) (hU v) (hΦ v) (K₀ v) (hB v) (θ v) (hθ v) (u' v) (hu' v)
    have hdvd : ∀ i, (Nat.card ↥((MulAut.conj (g i) • H).subgroupOf (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) : ℤ) ∣ k i - m i.1 := fun i => by
      rw [← (hP2 i).2]
      have e := (hk i).symm.trans (hterm i)
      rw [sub_zsmul, e]
      exact add_neg_cancel _

    have hN : ∀ i, Nat.card ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)) = Nat.card ↥((MulAut.conj (g i) • H).subgroupOf (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) * ((MulAut.conj (g i) • H).subgroupOf (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))).index :=
      fun i => (Subgroup.card_mul_index ((MulAut.conj (g i) • H).subgroupOf (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)))).symm
    have hNpos : (0 : ℚ) < Nat.card ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)) := by exact_mod_cast Nat.card_pos
    have hKpos : ∀ i, (0 : ℚ) < Nat.card ↥((MulAut.conj (g i) • H).subgroupOf (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) := fun i => by exact_mod_cast Nat.card_pos
    obtain ⟨z₀, hz₀⟩ := hdvd₀
    have hz := fun i => hdvd i
    choose z hz using hz
    rw [finsum_eq_sum_of_fintype]

    have e1 : ((((n v : ℚ) / (Nat.card ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)) : ℚ) : ℚ) : AddCircle (1 : ℚ)))
        = ((((∑ i, k i * (((MulAut.conj (g i) • H).subgroupOf (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))).index : ℤ) : ℤ) : ℚ) / (Nat.card ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)) : ℚ) : ℚ) : AddCircle (1 : ℚ)) := by
      apply coe_eq_coe_of_sub_eq_int z₀
      rw [← sub_div, div_eq_iff hNpos.ne', ← Int.cast_sub, hz₀]
      push_cast
      ring
    rw [e1]

    have e2 : (((∑ i, k i * (((MulAut.conj (g i) • H).subgroupOf (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))).index : ℤ) : ℤ) : ℚ) / (Nat.card ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)) : ℚ) : ℚ)
        = ∑ i, ((k i : ℚ) / (Nat.card ↥((MulAut.conj (g i) • H).subgroupOf (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) : ℚ)) := by
      push_cast
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hN i]
      push_cast
      have hI : (0 : ℚ) < ((MulAut.conj (g i) • H).subgroupOf (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))).index := by exact_mod_cast Nat.pos_of_ne_zero ((MulAut.conj (g i) • H).subgroupOf (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))).index_ne_zero_of_finite
      rw [div_eq_div_iff (ne_of_gt (mul_pos (hKpos i) hI)) (ne_of_gt (hKpos i))]
      ring
    rw [e2]

    have e3 : ((((∑ i, ((k i : ℚ) / (Nat.card ↥((MulAut.conj (g i) • H).subgroupOf (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) : ℚ))) : ℚ)) : AddCircle (1 : ℚ)) = ∑ i, ((((k i : ℚ) / (Nat.card ↥((MulAut.conj (g i) • H).subgroupOf (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) : ℚ)) : ℚ) : AddCircle (1 : ℚ)) :=
      map_sum (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℚ))) _ _
    rw [e3]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hf]
    dsimp only
    rw [← hcard i]
    apply coe_eq_coe_of_sub_eq_int (z i)
    rw [← sub_div, div_eq_iff (hKpos i).ne', ← Int.cast_sub, hz i]
    push_cast
    ring

  have hfsupp : (Function.support f).Finite := by
    obtain ⟨prInfH, hprInfH⟩ := M4aHerbrand.exists_hom_res_inf_infPlaceDecomp_ideles_completion_apply E F D hactI H
    have hFIN := (M4aHerbrand.injective_and_finite_and_surjective_localCoordinates_groupCohomology_res_ideles
      E F D hactI H prH hprH prInfH hprInfH 1).2.1 y
    have hinj : Set.InjOn (fun v' : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)) =>
        NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v')
        ((fun v' => NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v') ⁻¹'
          {w : HeightOneSpectrum (𝓞 F) | (groupCohomology.map (Subgroup.inclusion (inf_le_left : H ⊓ NumberField.PlaceDecomp.decomp E F w ≤ H)) (prH w) (1 + 1)).hom y ≠ 0}) := by
      intro a _ b _ hab
      have := congrArg (fun w : HeightOneSpectrum (𝓞 F) => w.under (𝓞 ↥(IntermediateField.fixedField H))) hab
      simpa only [HeightOneSpectrum.ext_iff, HeightOneSpectrum.under_asIdeal, NumberField.PlaceAbove.comap_above] using this
    refine (hFIN.preimage hinj).subset fun v' hv' => ?_
    rw [Function.mem_support] at hv'
    rw [Set.mem_preimage, Set.mem_setOf_eq, hm v']

    haveI := hqH v'; haveI := hfLH v'; letI := aLH v'; letI := auLH v'; haveI := hfKH v'
    haveI : FaithfulSMul ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v')) (LH v') :=
      ⟨fun {g₁} {g₂} hg₁₂ => by
        haveI := NumberField.PlaceDecomp.faithfulSMul_decomp E F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v')
        refine FaithfulSMul.eq_of_smul_eq_smul (α := (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v').adicCompletion F)
          fun yy => (ΦH v').injective ?_
        rw [hΦH, hΦH, hg₁₂]⟩
    have hsolv' := ExtCitation.LocalLevel.isSolvable_of_faithfulSMul_of_padic (qH v') (LH v') _ (hQH v')
    have hord := (NumberField.PlaceDecomp.exists_eq_zsmul_map_inclusion_and_zsmul_eq_zero_iff_of_isLocalFundamentalClass E F
      (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField H) F v') hsolv' (qH v') (LH v') (ΦH v') (hQH v') (hUH v') (hΦH v')
      (KH v') (hBH v') (θH v') (hθH v') (uH v') (huH v') H).2 (m v')
    intro h0
    apply hv'
    rw [hf]
    exact coe_div_eq_zero_of_dvd _ Nat.card_pos (m v') (hord.1 h0)
  calc ∑ᶠ v : HeightOneSpectrum (𝓞 E), ((((n v : ℚ) / (Nat.card ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)) : ℚ) : ℚ) : AddCircle (1 : ℚ)))
      = ∑ᶠ v : HeightOneSpectrum (𝓞 E), ∑ᶠ i : {v' : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)) // v'.under (𝓞 E) = v}, f i.1 :=
        finsum_congr hper
    _ = ∑ᶠ v', f v' := finsum_fiber_eq_finsum (fun v' : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)) => v'.under (𝓞 E)) f hfsupp
    _ = _ := by rw [hf]

end S_M4aHerbrand_finsum_div_natCard_decomp_cores_eq_finsum_div_natCard_inf_decomp
end P2MW
export P2MW.S_M4aHerbrand_finsum_div_natCard_decomp_cores_eq_finsum_div_natCard_inf_decomp (solution)
