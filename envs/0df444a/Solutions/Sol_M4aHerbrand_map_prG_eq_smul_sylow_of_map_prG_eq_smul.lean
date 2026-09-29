-- Prove2me | solution 1 for M4aHerbrand.map_prG_eq_smul_sylow_of_map_prG_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/d1f4c8c9-3435-515e-9135-7cc591fdd0d0

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_NumberField_SIdeleModule
import Definitions.Def_NumberField_PlaceAbove
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import Theorems.Thm_M4aHerbrand_map_prG_eq_smul_fixedField_of_map_prG_eq_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_M4aHerbrand_map_prG_eq_smul_sylow_of_map_prG_eq_smul
p2m_attr_erase "instance" "FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing"
p2m_attr_erase "instance" "M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion NumberField.AdelicHaar.locallyCompactSpace_adeleRing NumberField.AdelicHaar.finite_residueField_adicCompletionIntegers NumberField.AdelicHaar.locallyCompactSpace_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_finiteAdeleRing NumberField.AdelicHaar.compactSpace_adicCompletionIntegers NumberField.AdelicHaar.t2Space_finiteAdeleRing NumberField.AdelicHaar.t2Space_matrix_adeleRing NumberField.AdelicHaar.t2Space_adeleRing NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers NumberField.AdelicHaar.t2Space_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_matrix_adeleRing NumberField.AdelicHaar.t2Space_infiniteAdeleRing NumberField.AdelicHaar.properSpace_adicCompletion M4aHerbrand.Bridge.instT2SpaceAdeleRing ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal"
p2m_attr_erase "simp" "M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq M4aHerbrand.Bridge.finiteConorm_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply"
p2m_attr_erase "simp" "AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe"
p2m_attr_erase "simp" "Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply IsLocalRing.principalUnits_zero"
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000
open CategoryTheory NumberField IsDedekindDomain M4aHerbrand
open scoped NumberField.PlaceDecomp

theorem solution
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (p : ℕ) [Fact p.Prime] (P : Sylow p (F ≃ₐ[E] F))
    (D : IdeleGaloisDescent (𝓞 F) E F)
    [MulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ]
    (hactI : ∀ (g : (F ≃ₐ[E] F)) (x : (AdeleRing (𝓞 F) F)ˣ), g • x = D.unitsAct g x)
    (prG : ∀ w : HeightOneSpectrum (𝓞 F),
      Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)
    (hprG : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (AdeleRing (𝓞 F) F)ˣ), (prG w).hom (Additive.ofMul x) = Additive.ofMul (finPart w x))
    (D' : IdeleGaloisDescent (𝓞 F) ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))) F)
    [MulDistribMulAction (F ≃ₐ[↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F)))] F) (AdeleRing (𝓞 F) F)ˣ]
    (hactI' : ∀ (g : (F ≃ₐ[↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F)))] F)) (x : (AdeleRing (𝓞 F) F)ˣ), g • x = D'.unitsAct g x)
    (prG' : ∀ w : HeightOneSpectrum (𝓞 F),
      Rep.res (NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))) F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F)))] F) (AdeleRing (𝓞 F) F)ˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))) F w)) (w.adicCompletion F)ˣ)
    (hprG' : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (AdeleRing (𝓞 F) F)ˣ), (prG' w).hom (Additive.ofMul x) = Additive.ofMul (finPart w x))
    (Θ : ↥(P : Subgroup (F ≃ₐ[E] F)) ≃* (F ≃ₐ[↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F)))] F))
    (hΘ : ∀ (s : ↥(P : Subgroup (F ≃ₐ[E] F))) (y : F), Θ s y = (s : F ≃ₐ[E] F) y)
    (ψ : Rep.res Θ.toMonoidHom (Rep.ofMulDistribMulAction (F ≃ₐ[↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F)))] F) (AdeleRing (𝓞 F) F)ˣ) ⟶ Rep.res (P : Subgroup (F ≃ₐ[E] F)).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ))
    (hψ : ∀ y, ψ.hom y = y)
    (x : groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) 2)
    (x' : groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F)))] F) (AdeleRing (𝓞 F) F)ˣ) 2)
    (hx' : (groupCohomology.map Θ.toMonoidHom ψ 2).hom x' =
      (groupCohomology.map (P : Subgroup (F ≃ₐ[E] F)).subtype (𝟙 (Rep.res (P : Subgroup (F ≃ₐ[E] F)).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ))) 2).hom x)

    (q : HeightOneSpectrum (𝓞 E) → ℕ) (_ : ∀ v, Fact (q v).Prime)
    (L : ∀ v : HeightOneSpectrum (𝓞 E), IntermediateField ℚ_[q v] (PadicAlgCl (q v)))
    (_ : ∀ v, FiniteDimensional ℚ_[q v] (L v))
    (_ : ∀ v : HeightOneSpectrum (𝓞 E), MulSemiringAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (L v))
    (_ : ∀ v : HeightOneSpectrum (𝓞 E), MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (↥(L v))ˣ)
    (Φ : ∀ v : HeightOneSpectrum (𝓞 E), (NumberField.PlaceAbove.above E F v).adicCompletion F ≃+* L v)
    (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (g : ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (y : ℚ_[q v]), g • algebraMap ℚ_[q v] (L v) y = algebraMap ℚ_[q v] (L v) y)
    (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (g : ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (y : (↥(L v))ˣ), ((g • y : (↥(L v))ˣ) : L v) = g • (y : L v))
    (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (g : ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (y : (NumberField.PlaceAbove.above E F v).adicCompletion F), (Φ v) (g • y) = g • (Φ v) y)
    (K₀ : ∀ v : HeightOneSpectrum (𝓞 E), IntermediateField ℚ_[q v] (PadicAlgCl (q v)))
    (_ : ∀ v, FiniteDimensional ℚ_[q v] (K₀ v))
    (_ : ∀ v : HeightOneSpectrum (𝓞 E), ExtCitation.LocalLevel.IsBase (q v) (L v) (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (K₀ v))
    (θ : ∀ v : HeightOneSpectrum (𝓞 E), Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (↥(L v))ˣ ⟶
      Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) ((NumberField.PlaceAbove.above E F v).adicCompletion F)ˣ)
    (_ : ∀ (v : HeightOneSpectrum (𝓞 E)) (y : (↥(L v))ˣ),
      ((Additive.toMul ((θ v).hom (Additive.ofMul y)) : ((NumberField.PlaceAbove.above E F v).adicCompletion F)ˣ) : (NumberField.PlaceAbove.above E F v).adicCompletion F) =
        (Φ v).symm (y : L v))
    (u : ∀ v : HeightOneSpectrum (𝓞 E), groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (↥(L v))ˣ))
    (_ : ∀ v : HeightOneSpectrum (𝓞 E), ExtCitation.LocalLevel.IsLocalFundamentalClass (q v) (L v) (↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (K₀ v) (u v))
    (n : HeightOneSpectrum (𝓞 E) → ℤ)
    (hn : ∀ v : HeightOneSpectrum (𝓞 E),
      (groupCohomology.map (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)).subtype (prG (NumberField.PlaceAbove.above E F v)) 2).hom x =
        n v • (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v))) (θ v) 2).hom (u v))

    (q' : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F)))) → ℕ) (_ : ∀ v, Fact (q' v).Prime)
    (L' : ∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F)))), IntermediateField ℚ_[q' v] (PadicAlgCl (q' v)))
    (_ : ∀ v, FiniteDimensional ℚ_[q' v] (L' v))
    (_ : ∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F)))), MulSemiringAction (↥(NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))) F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))) F v))) (L' v))
    (_ : ∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F)))), MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))) F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))) F v))) (↥(L' v))ˣ)
    (Φ' : ∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F)))), (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))) F v).adicCompletion F ≃+* L' v)
    (_ : ∀ (v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))))) (g : ↥(NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))) F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))) F v))) (y : ℚ_[q' v]), g • algebraMap ℚ_[q' v] (L' v) y = algebraMap ℚ_[q' v] (L' v) y)
    (_ : ∀ (v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))))) (g : ↥(NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))) F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))) F v))) (y : (↥(L' v))ˣ), ((g • y : (↥(L' v))ˣ) : L' v) = g • (y : L' v))
    (_ : ∀ (v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))))) (g : ↥(NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))) F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))) F v))) (y : (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))) F v).adicCompletion F), (Φ' v) (g • y) = g • (Φ' v) y)
    (K₀' : ∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F)))), IntermediateField ℚ_[q' v] (PadicAlgCl (q' v)))
    (_ : ∀ v, FiniteDimensional ℚ_[q' v] (K₀' v))
    (_ : ∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F)))), ExtCitation.LocalLevel.IsBase (q' v) (L' v) (↥(NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))) F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))) F v))) (K₀' v))
    (θ' : ∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F)))), Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))) F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))) F v))) (↥(L' v))ˣ ⟶
      Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))) F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))) F v))) ((NumberField.PlaceAbove.above ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))) F v).adicCompletion F)ˣ)
    (_ : ∀ (v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))))) (y : (↥(L' v))ˣ),
      ((Additive.toMul ((θ' v).hom (Additive.ofMul y)) : ((NumberField.PlaceAbove.above ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))) F v).adicCompletion F)ˣ) : (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))) F v).adicCompletion F) =
        (Φ' v).symm (y : L' v))
    (u' : ∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F)))), groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))) F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))) F v))) (↥(L' v))ˣ))
    (_ : ∀ v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F)))), ExtCitation.LocalLevel.IsLocalFundamentalClass (q' v) (L' v) (↥(NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))) F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))) F v))) (K₀' v) (u' v)) :
    ∀ v' : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F)))),
      (groupCohomology.map (NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))) F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))) F v')).subtype (prG' (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))) F v')) 2).hom x' =
        n (v'.under (𝓞 E)) • (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))) F (NumberField.PlaceAbove.above ↥(IntermediateField.fixedField (P : Subgroup (F ≃ₐ[E] F))) F v'))) (θ' v') 2).hom (u' v') := by
  rename_i a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22
  exact M4aHerbrand.map_prG_eq_smul_fixedField_of_map_prG_eq_smul E F (P : Subgroup (F ≃ₐ[E] F)) D hactI prG hprG D' hactI' prG' hprG' Θ hΘ ψ hψ x x' hx' q a1 L a2 a3 a4 Φ a5 a6 a7 K₀ a8 a9 θ a10 u a11 n hn q' a12 L' a13 a14 a15 Φ' a16 a17 a18 K₀' a19 a20 θ' a21 u' a22

end S_M4aHerbrand_map_prG_eq_smul_sylow_of_map_prG_eq_smul
end P2MW
export P2MW.S_M4aHerbrand_map_prG_eq_smul_sylow_of_map_prG_eq_smul (solution)
