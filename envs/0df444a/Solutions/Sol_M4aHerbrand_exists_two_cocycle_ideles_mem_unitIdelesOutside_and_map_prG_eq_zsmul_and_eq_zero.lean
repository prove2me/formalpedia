-- Prove2me | solution 1 for M4aHerbrand.exists_two_cocycle_ideles_mem_unitIdelesOutside_and_map_prG_eq_zsmul_and_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/40136abd-1b93-533e-b1e9-ebd5874e6cfd

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_NumberField_SIdeleModule
import Definitions.Def_NumberField_PlaceAbove
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import Theorems.Thm_M4aHerbrand_exists_hom_coind_ideles_finPart_eq_and_eq_one
import Theorems.Thm_groupCohomology_exists_two_cocycle_coind_apply_one_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_M4aHerbrand_exists_two_cocycle_ideles_mem_unitIdelesOutside_and_map_prG_eq_zsmul_and_eq_zero
p2m_attr_erase "instance" "FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing"
p2m_attr_erase "instance" "M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion NumberField.AdelicHaar.locallyCompactSpace_adeleRing NumberField.AdelicHaar.finite_residueField_adicCompletionIntegers NumberField.AdelicHaar.locallyCompactSpace_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_finiteAdeleRing NumberField.AdelicHaar.compactSpace_adicCompletionIntegers NumberField.AdelicHaar.t2Space_finiteAdeleRing NumberField.AdelicHaar.t2Space_matrix_adeleRing NumberField.AdelicHaar.t2Space_adeleRing NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers NumberField.AdelicHaar.t2Space_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_matrix_adeleRing NumberField.AdelicHaar.t2Space_infiniteAdeleRing NumberField.AdelicHaar.properSpace_adicCompletion M4aHerbrand.Bridge.instT2SpaceAdeleRing"
p2m_attr_erase "simp" "M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq M4aHerbrand.Bridge.finiteConorm_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply"
p2m_attr_erase "simp" "AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe"
p2m_attr_erase "simp" "Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply"
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000
open CategoryTheory NumberField IsDedekindDomain M4aHerbrand
open scoped NumberField.PlaceDecomp

theorem solution
    (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]
    (D : IdeleGaloisDescent (𝓞 K) E K)
    [MulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ]
    (hactI : ∀ (g : (K ≃ₐ[E] K)) (x : (AdeleRing (𝓞 K) K)ˣ), g • x = D.unitsAct g x)

    (prG : ∀ w : HeightOneSpectrum (𝓞 K),
      Rep.res (NumberField.PlaceDecomp.decomp E K w).subtype (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (w.adicCompletion K)ˣ)
    (hprG : ∀ (w : HeightOneSpectrum (𝓞 K)) (x : (AdeleRing (𝓞 K) K)ˣ), (prG w).hom (Additive.ofMul x) = Additive.ofMul (finPart w x))

    (v₀ : HeightOneSpectrum (𝓞 E))
    (q : ℕ) [Fact q.Prime] (L' : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L']
    [MulSemiringAction ↥(NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v₀)) L'] [MulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v₀)) (↥L')ˣ]
    (Φ : (NumberField.PlaceAbove.above E K v₀).adicCompletion K ≃+* L')
    (hΦ₁ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v₀))) (y : ℚ_[q]), g • algebraMap ℚ_[q] L' y = algebraMap ℚ_[q] L' y)
    (hΦ₂ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v₀))) (y : (↥L')ˣ), ((g • y : (↥L')ˣ) : L') = g • (y : L'))
    (hΦ₃ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v₀))) (y : (NumberField.PlaceAbove.above E K v₀).adicCompletion K), Φ (g • y) = g • Φ y)
    (K₀ : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K₀]
    (hK₀ : ExtCitation.LocalLevel.IsBase q L' ↥(NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v₀)) K₀)
    (θ : Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v₀)) (↥L')ˣ ⟶ Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v₀)) ((NumberField.PlaceAbove.above E K v₀).adicCompletion K)ˣ)
    (hθ : ∀ y : (↥L')ˣ, ((Additive.toMul (θ.hom (Additive.ofMul y)) : ((NumberField.PlaceAbove.above E K v₀).adicCompletion K)ˣ) : (NumberField.PlaceAbove.above E K v₀).adicCompletion K) = Φ.symm (y : L'))
    (u' : groupCohomology.H2 (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v₀)) (↥L')ˣ))
    (hu' : ExtCitation.LocalLevel.IsLocalFundamentalClass q L' ↥(NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v₀)) K₀ u')

    (T : Set (HeightOneSpectrum (𝓞 K))) (hT : ∀ w : HeightOneSpectrum (𝓞 K), w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v₀.asIdeal → w ∈ T)
    (a : ℤ) :
    ∃ (ξ : (Fin 2 → (K ≃ₐ[E] K)) → (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ))
      (hξ : ((groupCohomology.inhomogeneousCochains (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ)).d 2 3).hom ξ = 0),
      (∀ g : Fin 2 → (K ≃ₐ[E] K), Additive.toMul (ξ g) ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K T) ∧
      (groupCohomology.map (NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v₀)).subtype (prG (NumberField.PlaceAbove.above E K v₀)) 2).hom
          (groupCohomology.π (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ) 2 (groupCohomology.cocyclesMk ξ hξ)) =
        a • (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v₀))) θ 2).hom u' ∧
      (∀ (w : HeightOneSpectrum (𝓞 K)) (g : Fin 2 → (K ≃ₐ[E] K)), w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) ≠ v₀.asIdeal →
        finPart w (Additive.toMul (ξ g)) = 1) := by
  classical

  set w₁ := NumberField.PlaceAbove.above E K v₀ with hw₁
  let Dw := NumberField.PlaceDecomp.decomp E K w₁
  let A : Rep ℤ ↥Dw := Rep.ofMulDistribMulAction ↥Dw (w₁.adicCompletion K)ˣ
  let M : Rep ℤ (K ≃ₐ[E] K) := Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ

  obtain ⟨Sh, hSh1, hSh2, hSh3⟩ :=
    M4aHerbrand.exists_hom_coind_ideles_finPart_eq_and_eq_one E K D hactI v₀

  let x : groupCohomology A 2 := a • (groupCohomology.map (MonoidHom.id ↥Dw) θ 2).hom u'
  obtain ⟨z, hz⟩ : ∃ z : groupCohomology.cocycles A 2, (groupCohomology.π A 2).hom z = x :=
    groupCohomology_induction_on (C := fun y => ∃ z : groupCohomology.cocycles A 2, (groupCohomology.π A 2).hom z = y)
      x (fun y => ⟨y, rfl⟩)
  let c : (Fin 2 → ↥Dw) → A := (groupCohomology.iCocycles A 2).hom z
  have hc : inhomogeneousCochains.d A 2 c = 0 := by
    have h := (groupCohomology.inhomogeneousCochains A).iCycles_d 2 3
    have h' := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h) z
    rw [← groupCohomology.inhomogeneousCochains.d_def]
    simpa using h'

  obtain ⟨F, hF, hF1⟩ := groupCohomology.exists_two_cocycle_coind_apply_one_eq Dw A c hc
  let ξ : (Fin 2 → (K ≃ₐ[E] K)) → M := fun g => Sh.hom (F g)
  have hξ : ((groupCohomology.inhomogeneousCochains M).d 2 3).hom ξ = 0 := by
    rw [groupCohomology.inhomogeneousCochains.d_def]
    funext g
    have hdF := congrFun hF g
    have key : (inhomogeneousCochains.d M 2).hom ξ g = Sh.hom ((inhomogeneousCochains.d (Rep.coind Dw.subtype A) 2).hom F g) := by
      rw [inhomogeneousCochains.d_hom_apply, inhomogeneousCochains.d_hom_apply, map_add, map_sum]
      congr 1
      · exact (Rep.hom_comm_apply Sh (g 0) _).symm
      · refine Finset.sum_congr rfl ?_
        intro j _
        rw [map_smul]
        rfl
    rw [key, hdF]
    exact map_zero _
  refine ⟨ξ, hξ, ?_, ?_, ?_⟩
  ·
    intro g
    apply (NumberField.AdeleRing.mem_unitIdelesOutside_iff T _).mpr
    apply (IsDedekindDomain.FiniteAdeleRing.mem_unitIdelesOutside_iff _ _).mpr
    intro w hw
    have hne : w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) ≠ v₀.asIdeal := fun h => hw (hT w h)
    have h1 : finPart w (Additive.toMul (ξ g)) = 1 := hSh2 (F g) w hne
    have h2 : finPart w (Additive.toMul (ξ g))⁻¹ = 1 := by rw [map_inv, h1, inv_one]
    have e1 := M4aHerbrand.coe_finPart_apply w (Additive.toMul (ξ g))
    have e2 := M4aHerbrand.coe_finPart_apply w (Additive.toMul (ξ g))⁻¹
    rw [h1, Units.val_one] at e1
    rw [h2, Units.val_one] at e2
    constructor
    · show ((Additive.toMul (ξ g) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 w ∈ _
      rw [← e1]; exact one_mem _
    · show (((Additive.toMul (ξ g))⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 w ∈ _
      rw [← e2]; exact one_mem _
  ·

    have hπ := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
      (groupCohomology.π_map Dw.subtype (prG w₁) 2)) (groupCohomology.cocyclesMk ξ hξ)
    simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at hπ
    rw [hπ]

    have hzz : groupCohomology.cocyclesMap Dw.subtype (prG w₁) 2 (groupCohomology.cocyclesMk ξ hξ) = z := by
      apply (ModuleCat.mono_iff_injective (groupCohomology.iCocycles A 2)).mp inferInstance
      have hi := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
        (HomologicalComplex.cyclesMap_i (groupCohomology.cochainsMap Dw.subtype (prG w₁)) 2))
        (groupCohomology.cocyclesMk ξ hξ)
      simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at hi
      show (groupCohomology.iCocycles A 2).hom (groupCohomology.cocyclesMap Dw.subtype (prG w₁) 2
        (groupCohomology.cocyclesMk ξ hξ)) = (groupCohomology.iCocycles A 2).hom z
      erw [hi, groupCohomology.iCocycles_mk]
      funext γ
      show (prG w₁).hom (ξ (fun i => (γ i : K ≃ₐ[E] K))) = c γ
      rw [← hF1 γ]
      show (prG w₁).hom (Sh.hom (F fun i => (γ i : K ≃ₐ[E] K))) = _
      have := hprG w₁ (Additive.toMul (Sh.hom (F fun i => (γ i : K ≃ₐ[E] K))))
      change (prG w₁).hom (Sh.hom (F fun i => (γ i : K ≃ₐ[E] K))) = _ at this
      rw [this, hSh1]
      rfl
    rw [hzz, hz]
  ·
    intro w g hne
    exact hSh2 (F g) w hne

end S_M4aHerbrand_exists_two_cocycle_ideles_mem_unitIdelesOutside_and_map_prG_eq_zsmul_and_eq_zero
end P2MW
export P2MW.S_M4aHerbrand_exists_two_cocycle_ideles_mem_unitIdelesOutside_and_map_prG_eq_zsmul_and_eq_zero (solution)
