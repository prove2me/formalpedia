-- Prove2me | solution 1 for NumberField.SIdele.exists_hom_classObj_ideleClassGroup_injective_range_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/cbe83186-7002-5d70-82a1-e3f3c39f77e1

import Mathlib
import Definitions.Def_NumberField_SIdeleModule
import Definitions.Def_IsDedekindDomain_FiniteUnitIdelesOutside
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Theorems.Thm_NumberField_SIdele_exists_addMonoidHom_obj_adeleRing_units
import Theorems.Thm_NumberField_AdeleRing_principalIdeles_inf_unitIdelesOutside_eq_map_unit
import Theorems.Thm_NumberField_SUnits_sUnits_eq_unit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_SIdele_exists_hom_classObj_ideleClassGroup_injective_range_eq
p2m_attr_erase "instance" "FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing"
p2m_attr_erase "instance" "M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion NumberField.AdelicHaar.locallyCompactSpace_adeleRing NumberField.AdelicHaar.finite_residueField_adicCompletionIntegers NumberField.AdelicHaar.locallyCompactSpace_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_finiteAdeleRing NumberField.AdelicHaar.compactSpace_adicCompletionIntegers NumberField.AdelicHaar.t2Space_finiteAdeleRing NumberField.AdelicHaar.t2Space_matrix_adeleRing NumberField.AdelicHaar.t2Space_adeleRing NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers NumberField.AdelicHaar.t2Space_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_matrix_adeleRing NumberField.AdelicHaar.t2Space_infiniteAdeleRing NumberField.AdelicHaar.properSpace_adicCompletion M4aHerbrand.Bridge.instT2SpaceAdeleRing"
p2m_attr_erase "simp" "M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq M4aHerbrand.Bridge.finiteConorm_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply"
p2m_attr_erase "simp" "AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe"
p2m_attr_erase "simp" "Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply"

set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace P2mS25E3

open IsDedekindDomain NumberField CategoryTheory

section generic

universe u

variable {k G : Type u} [CommRing k] [Group G]

theorem exists_hom_cokernel {X Y T : Rep.{u} k G} (f : X ⟶ Y) (g : Y →+ T)
    (hsmul : ∀ (c : k) (y : Y), g (c • y) = c • g y)
    (hcomm : ∀ (s : G) (y : Y), g (Y.ρ s y) = T.ρ s (g y))
    (hker : ∀ y : Y, g y = 0 ↔ y ∈ Set.range f.hom) :
    ∃ ι : GroupCohomology.RepCokernel.obj f ⟶ T,
      (∀ y : Y, ι.hom ((GroupCohomology.RepCokernel.π f).hom y) = g y) ∧ Function.Injective ι.hom ∧
      Set.range ι.hom = Set.range g := by
  let gl : Y →ₗ[k] T := { toFun := g, map_add' := g.map_add, map_smul' := hsmul }
  have hgl : ∀ y, gl y = g y := fun _ => rfl
  have hle : LinearMap.range f.hom.toLinearMap ≤ LinearMap.ker gl := by
    rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker, hgl]
    exact (hker _).2 ⟨x, rfl⟩
  let e : (Y ⧸ LinearMap.range f.hom.toLinearMap) →ₗ[k] T := Submodule.liftQ _ gl hle
  have he : ∀ y : Y, e (Submodule.Quotient.mk y) = g y := fun y => rfl
  refine ⟨Rep.ofHom (Representation.IntertwiningMap.mk e fun s => LinearMap.ext fun q => ?_), fun y => rfl, ?_, ?_⟩
  · obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [LinearMap.comp_apply, LinearMap.comp_apply, Representation.quotient_apply, Submodule.mapQ_apply]
    change e (Submodule.Quotient.mk (Y.ρ s y)) = T.ρ s (e (Submodule.Quotient.mk y))
    rw [he, he]
    exact hcomm s y
  ·
    intro q₁ q₂ h
    obtain ⟨y₁, rfl⟩ := Submodule.Quotient.mk_surjective _ q₁
    obtain ⟨y₂, rfl⟩ := Submodule.Quotient.mk_surjective _ q₂
    change e (Submodule.Quotient.mk y₁) = e (Submodule.Quotient.mk y₂) at h
    rw [he, he, ← sub_eq_zero, ← map_sub, hker] at h
    obtain ⟨x, hx⟩ := h
    rw [Submodule.Quotient.eq]
    exact ⟨x, hx⟩
  · ext t
    constructor
    · rintro ⟨q, rfl⟩
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      exact ⟨y, (he y).symm⟩
    · rintro ⟨y, rfl⟩
      exact ⟨Submodule.Quotient.mk y, he y⟩

end generic

variable {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]
variable {S : Finset (HeightOneSpectrum (𝓞 E))}

abbrev C (K : Type) [Field K] [NumberField K] : Type := M4aHerbrand.IdeleClassGroup (𝓞 K) K

noncomputable def ψ (Φ : NumberField.SIdele.obj E K S →+ Additive (AdeleRing (𝓞 K) K)ˣ) :
    NumberField.SIdele.obj E K S →+ Additive (C K) :=
  (MonoidHom.toAdditive (QuotientGroup.mk' (M4aHerbrand.principalIdeles (𝓞 K) K))).comp Φ

theorem toMul_ψ_apply (Φ : NumberField.SIdele.obj E K S →+ Additive (AdeleRing (𝓞 K) K)ˣ) (x : NumberField.SIdele.obj E K S) :
    Additive.toMul (ψ Φ x) = ((Additive.toMul (Φ x) : (AdeleRing (𝓞 K) K)ˣ) : C K) := rfl

theorem ψ_apply (Φ : NumberField.SIdele.obj E K S →+ Additive (AdeleRing (𝓞 K) K)ˣ) (x : NumberField.SIdele.obj E K S) :
    ψ Φ x = Additive.ofMul (QuotientGroup.mk (Additive.toMul (Φ x)) : C K) := rfl

section
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 K) E K)

omit [NumberField E] in
theorem classAct_mk (g : K ≃ₐ[E] K) (u : (AdeleRing (𝓞 K) K)ˣ) :
    D.classAct g (u : C K) = ((D.unitsAct g u : (AdeleRing (𝓞 K) K)ˣ) : C K) := rfl

variable [MulDistribMulAction (K ≃ₐ[E] K) (M4aHerbrand.IdeleClassGroup (𝓞 K) K)]

theorem ψ_rho (Φ : NumberField.SIdele.obj E K S →+ Additive (AdeleRing (𝓞 K) K)ˣ)
    (hequiv : ∀ (g : K ≃ₐ[E] K) (x : NumberField.SIdele.obj E K S),
      Φ ((NumberField.SIdele.obj E K S).ρ g x) = Additive.ofMul (D.unitsAct g (Additive.toMul (Φ x))))
    (hact : ∀ (g : K ≃ₐ[E] K) (c : M4aHerbrand.IdeleClassGroup (𝓞 K) K), g • c = D.classAct g c)
    (g : K ≃ₐ[E] K) (x : NumberField.SIdele.obj E K S) :
    ψ Φ ((NumberField.SIdele.obj E K S).ρ g x) =
      (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (C K)).ρ g (ψ Φ x) := by
  apply Additive.toMul.injective
  rw [toMul_ψ_apply, hequiv, toMul_ofMul, Rep.ofMulDistribMulAction_ρ_apply_apply, toMul_ofMul, toMul_ψ_apply, hact,
    classAct_mk]

end

theorem ψ_smul (Φ : NumberField.SIdele.obj E K S →+ Additive (AdeleRing (𝓞 K) K)ˣ)
    [MulDistribMulAction (K ≃ₐ[E] K) (M4aHerbrand.IdeleClassGroup (𝓞 K) K)] (c : ℤ) (y : NumberField.SIdele.obj E K S) :
    ψ Φ (@HSMul.hSMul ℤ _ _ (@instHSMul ℤ _ (NumberField.SIdele.obj E K S).hV2.toSMul) c y) =
      @HSMul.hSMul ℤ _ _ (@instHSMul ℤ _ (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (C K)).hV2.toSMul) c (ψ Φ y) :=
  (congrArg (ψ Φ) (int_smul_eq_zsmul (NumberField.SIdele.obj E K S).hV2 c y)).trans
    ((map_zsmul (ψ Φ) c y).trans (int_smul_eq_zsmul (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (C K)).hV2 c (ψ Φ y)).symm)

theorem ψ_eq_zero_iff (Φ : NumberField.SIdele.obj E K S →+ Additive (AdeleRing (𝓞 K) K)ˣ)
    (hinj : Function.Injective Φ)
    (hrange : Φ.range = (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K {w | w.under (𝓞 E) ∈ S}).toAddSubgroup)
    (hdiag : ∀ x : NumberField.SUnits.sUnitsRep E K S, Φ ((NumberField.SIdele.diag E K S).hom x) =
        Additive.ofMul (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) (NumberField.SUnits.val E K S x)))
    (x : NumberField.SIdele.obj E K S) :
    ψ Φ x = 0 ↔ x ∈ Set.range (NumberField.SIdele.diag E K S).hom := by
  constructor
  · intro h0
    have hP : (Additive.toMul (Φ x) : (AdeleRing (𝓞 K) K)ˣ) ∈ M4aHerbrand.principalIdeles (𝓞 K) K := by
      rw [← QuotientGroup.eq_one_iff]
      exact (toMul_ψ_apply Φ x).symm.trans (congrArg Additive.toMul h0)
    have hU : (Additive.toMul (Φ x) : (AdeleRing (𝓞 K) K)ˣ) ∈
        NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K {w | w.under (𝓞 E) ∈ S} := by
      have : Φ x ∈ Φ.range := ⟨x, rfl⟩
      rw [hrange] at this
      exact this
    have hPU : (Additive.toMul (Φ x) : (AdeleRing (𝓞 K) K)ˣ) ∈
        M4aHerbrand.principalIdeles (𝓞 K) K ⊓ NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K {w | w.under (𝓞 E) ∈ S} :=
      ⟨hP, hU⟩
    rw [NumberField.AdeleRing.principalIdeles_inf_unitIdelesOutside_eq_map_unit (𝓞 K) K {w | w.under (𝓞 E) ∈ S}] at hPU
    obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.1 hPU
    have ha' : a ∈ NumberField.SUnits.sUnits E K S := by
      rw [NumberField.SUnits.sUnits_eq_unit E K S]; exact ha
    refine ⟨⟨Additive.ofMul a, ha'⟩, hinj ?_⟩
    rw [hdiag]
    exact (congrArg Additive.ofMul hax).trans (ofMul_toMul (Φ x))
  · rintro ⟨a, rfl⟩
    apply Additive.toMul.injective
    rw [toMul_ψ_apply, hdiag, toMul_ofMul, toMul_zero, QuotientGroup.eq_one_iff]
    exact ⟨NumberField.SUnits.val E K S a, rfl⟩

theorem mem_range_ψ_iff (Φ : NumberField.SIdele.obj E K S →+ Additive (AdeleRing (𝓞 K) K)ˣ)
    (hrange : Φ.range = (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K {w | w.under (𝓞 E) ∈ S}).toAddSubgroup)
    (c : Additive (C K)) :
    c ∈ Set.range (ψ Φ) ↔ Additive.toMul c ∈
      (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K {w | w.under (𝓞 E) ∈ S}).map
        (QuotientGroup.mk' (M4aHerbrand.principalIdeles (𝓞 K) K)) := by
  constructor
  · rintro ⟨y, rfl⟩
    refine Subgroup.mem_map.2 ⟨Additive.toMul (Φ y), ?_, rfl⟩
    have : Φ y ∈ Φ.range := ⟨y, rfl⟩
    rw [hrange] at this
    exact this
  · intro hc
    obtain ⟨u, hu, huc⟩ := Subgroup.mem_map.1 hc
    have hu' : Additive.ofMul u ∈ Φ.range := by rw [hrange]; exact hu
    obtain ⟨y, hy⟩ := hu'
    refine ⟨y, Additive.toMul.injective ?_⟩
    rw [toMul_ψ_apply, hy, toMul_ofMul]
    exact huc

end P2mS25E3

open IsDedekindDomain NumberField CategoryTheory in
theorem solution (E K : Type) [Field E] [NumberField E]
    [Field K] [NumberField K] [Algebra E K] [IsGalois E K] (S : Finset (HeightOneSpectrum (𝓞 E)))
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 K) E K)
    [MulDistribMulAction (K ≃ₐ[E] K) (M4aHerbrand.IdeleClassGroup (𝓞 K) K)]
    (hact : ∀ (g : K ≃ₐ[E] K) (c : M4aHerbrand.IdeleClassGroup (𝓞 K) K), g • c = D.classAct g c) :
    ∃ (Φ : NumberField.SIdele.obj E K S →+ Additive (AdeleRing (𝓞 K) K)ˣ)
      (ι : NumberField.SIdele.classObj E K S ⟶ Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (M4aHerbrand.IdeleClassGroup (𝓞 K) K)),
      Function.Injective Φ ∧
      Φ.range = (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K {w | w.under (𝓞 E) ∈ S}).toAddSubgroup ∧
      (∀ (g : K ≃ₐ[E] K) (x : NumberField.SIdele.obj E K S),
        Φ ((NumberField.SIdele.obj E K S).ρ g x) = Additive.ofMul (D.unitsAct g (Additive.toMul (Φ x)))) ∧
      (∀ x : NumberField.SUnits.sUnitsRep E K S, Φ ((NumberField.SIdele.diag E K S).hom x) =
        Additive.ofMul (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) (NumberField.SUnits.val E K S x))) ∧
      (∀ y : NumberField.SIdele.obj E K S, ι.hom ((NumberField.SIdele.toClass E K S).hom y) =
        Additive.ofMul (QuotientGroup.mk (Additive.toMul (Φ y)) : M4aHerbrand.IdeleClassGroup (𝓞 K) K)) ∧
      Function.Injective ι.hom ∧
      (∀ c : Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (M4aHerbrand.IdeleClassGroup (𝓞 K) K),
        c ∈ Set.range ι.hom ↔ Additive.toMul c ∈
          (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K {w | w.under (𝓞 E) ∈ S}).map
            (QuotientGroup.mk' (M4aHerbrand.principalIdeles (𝓞 K) K))) := by
  obtain ⟨Φ, hinj, hrange, hequiv, hdiag⟩ := NumberField.SIdele.exists_addMonoidHom_obj_adeleRing_units E K S D
  obtain ⟨ι, hπ, hιinj, hιrange⟩ := P2mS25E3.exists_hom_cokernel (T := Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (M4aHerbrand.IdeleClassGroup (𝓞 K) K))
    (NumberField.SIdele.diag E K S) (P2mS25E3.ψ Φ) (P2mS25E3.ψ_smul Φ) (P2mS25E3.ψ_rho D Φ hequiv hact)
    (fun y => P2mS25E3.ψ_eq_zero_iff Φ hinj hrange hdiag y)
  refine ⟨Φ, ι, hinj, hrange, hequiv, hdiag, fun y => hπ y, hιinj, fun c => ?_⟩
  rw [hιrange]
  exact P2mS25E3.mem_range_ψ_iff Φ hrange c

end S_NumberField_SIdele_exists_hom_classObj_ideleClassGroup_injective_range_eq
end P2MW
export P2MW.S_NumberField_SIdele_exists_hom_classObj_ideleClassGroup_injective_range_eq (solution)
