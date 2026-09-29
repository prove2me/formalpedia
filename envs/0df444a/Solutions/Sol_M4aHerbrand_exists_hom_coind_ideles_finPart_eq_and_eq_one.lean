-- Prove2me | solution 1 for M4aHerbrand.exists_hom_coind_ideles_finPart_eq_and_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/8c34ef3e-274b-54be-a505-5a66e9b3f70f

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_NumberField_SIdeleModule
import Definitions.Def_NumberField_PlaceAbove
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import Definitions.Def_NumberField_PlaceTransport
import Definitions.Def_NumberField_InfinitePlaceTransport
import Definitions.Def_IsDedekindDomain_FiniteUnitIdelesOutside
import Theorems.Thm_NumberField_SIdele_exists_addMonoidHom_obj_adeleRing_units_apply
import Theorems.Thm_NumberField_PlaceTransport_transport_one
import Theorems.Thm_NumberField_PlaceTransport_orbit_eq_setOf_under_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_M4aHerbrand_exists_hom_coind_ideles_finPart_eq_and_eq_one
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

section Proof
open scoped NumberField.PlaceTransport

theorem solution
    (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]
    (D : IdeleGaloisDescent (𝓞 K) E K)
    [MulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ]
    (hactI : ∀ (g : (K ≃ₐ[E] K)) (x : (AdeleRing (𝓞 K) K)ˣ), g • x = D.unitsAct g x)
    (v₀ : HeightOneSpectrum (𝓞 E)) :
    ∃ Sh : Rep.coind (NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v₀)).subtype (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v₀)) ((NumberField.PlaceAbove.above E K v₀).adicCompletion K)ˣ) ⟶
        Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ,
      (∀ f : Rep.coind (NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v₀)).subtype (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v₀)) ((NumberField.PlaceAbove.above E K v₀).adicCompletion K)ˣ),
        finPart (NumberField.PlaceAbove.above E K v₀) (Additive.toMul (Sh.hom f)) = Additive.toMul (f.1 1)) ∧
      (∀ (f : Rep.coind (NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v₀)).subtype (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v₀)) ((NumberField.PlaceAbove.above E K v₀).adicCompletion K)ˣ))
        (w : HeightOneSpectrum (𝓞 K)), w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) ≠ v₀.asIdeal →
        finPart w (Additive.toMul (Sh.hom f)) = 1) ∧
      (∀ f : Rep.coind (NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v₀)).subtype (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v₀)) ((NumberField.PlaceAbove.above E K v₀).adicCompletion K)ˣ),
        infPart (Additive.toMul (Sh.hom f)) = 1)  := by
  classical
  have hvS : v₀ ∈ ({v₀} : Finset (HeightOneSpectrum (𝓞 E))) := Finset.mem_singleton_self v₀
  obtain ⟨Φ, -, -, hequiv, -, hval, hvalO, hvalI⟩ :=
    NumberField.SIdele.exists_addMonoidHom_obj_adeleRing_units_apply E K {v₀} D

  letI : Module ℤ (NumberField.SIdele.obj E K {v₀}) := (NumberField.SIdele.obj E K {v₀}).hV2
  let X : Rep ℤ (K ≃ₐ[E] K) := NumberField.SIdele.fibre E K {v₀} (Sum.inl (Sum.inl ⟨v₀, hvS⟩))
  letI : Module ℤ X := X.hV2

  let ΦR : NumberField.SIdele.obj E K {v₀} ⟶ Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ :=
    Rep.ofHom
      { toFun := Φ
        map_add' := map_add Φ
        map_smul' := fun n x => by
          have h := map_intCast_smul Φ ℤ ℤ n x
          simp only [Int.cast_id] at h
          rw [RingHom.id_apply]
          exact h
        isIntertwining' := fun g => LinearMap.ext fun x => by
          show Φ ((NumberField.SIdele.obj E K {v₀}).ρ g x) = Additive.ofMul (g • Additive.toMul (Φ x))
          rw [hequiv, hactI] }

  let sg : X → NumberField.SIdele.obj E K {v₀} := fun f =>
    Pi.single (M := fun i => (NumberField.SIdele.fibre E K {v₀} i)) (Sum.inl (Sum.inl ⟨v₀, hvS⟩)) f
  have hsg_same : ∀ f : X, sg f (Sum.inl (Sum.inl ⟨v₀, hvS⟩)) = f := fun f => Pi.single_eq_same _ _
  have hsg_ne : ∀ (f : X) (i : NumberField.SIdele.Index E {v₀}), i ≠ Sum.inl (Sum.inl ⟨v₀, hvS⟩) → sg f i = 0 :=
    fun f i hi => Pi.single_eq_of_ne hi _
  have hsg_add : ∀ f f' : X, sg (f + f') = sg f + sg f' := by
    intro f f'
    funext i
    by_cases hi : i = Sum.inl (Sum.inl ⟨v₀, hvS⟩)
    · subst hi; rw [Pi.add_apply, hsg_same, hsg_same, hsg_same]; try rfl
    · rw [Pi.add_apply, hsg_ne _ _ hi, hsg_ne _ _ hi, hsg_ne _ _ hi, add_zero]
  have hsg_zero : sg 0 = 0 := by
    funext i
    by_cases hi : i = Sum.inl (Sum.inl ⟨v₀, hvS⟩)
    · subst hi; rw [Pi.zero_apply, hsg_same]; try rfl
    · rw [Pi.zero_apply, hsg_ne _ _ hi]
  let sgA : X →+ NumberField.SIdele.obj E K {v₀} :=
    { toFun := sg
      map_zero' := hsg_zero
      map_add' := hsg_add }
  let incl : X ⟶ NumberField.SIdele.obj E K {v₀} :=
    Rep.ofHom
      { toFun := sg
        map_add' := hsg_add
        map_smul' := fun n f => by
          have h := map_intCast_smul sgA ℤ ℤ n f
          simp only [Int.cast_id] at h
          rw [RingHom.id_apply]
          exact h
        isIntertwining' := fun g => LinearMap.ext fun f => by
          funext i
          change sg (X.ρ g f) i = (NumberField.SIdele.fibre E K {v₀} i).ρ g (sg f i)
          by_cases hi : i = Sum.inl (Sum.inl ⟨v₀, hvS⟩)
          · subst hi; rw [hsg_same, hsg_same]; try rfl
          · rw [hsg_ne _ _ hi, hsg_ne _ _ hi, map_zero] }
  refine ⟨incl ≫ ΦR, ?_, ?_, ?_⟩
  ·
    intro f
    apply Units.ext
    change ((Additive.toMul (Φ (sg f)) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2
        (NumberField.PlaceAbove.above E K v₀) = _
    have h1 : (1 : K ≃ₐ[E] K) • NumberField.PlaceAbove.above E K v₀ = NumberField.PlaceAbove.above E K v₀ := one_smul _ _
    have key := hval (sg f) ⟨v₀, hvS⟩ (NumberField.PlaceAbove.above E K v₀) 1 h1
    rw [NumberField.PlaceTransport.transport_one E K _ h1, RingEquiv.refl_apply, hsg_same] at key
    exact key
  ·
    intro f w hw
    have hv : w.under (𝓞 E) ∉ ({v₀} : Finset (HeightOneSpectrum (𝓞 E))) := by
      rw [Finset.mem_singleton]
      intro h
      exact hw (congrArg HeightOneSpectrum.asIdeal h)
    have hmem : w ∈ MulAction.orbit (K ≃ₐ[E] K) (NumberField.PlaceAbove.above E K (w.under (𝓞 E))) := by
      rw [NumberField.PlaceTransport.orbit_eq_setOf_under_eq E K, Set.mem_setOf_eq, NumberField.SUnits.under_above]
    obtain ⟨y, hy⟩ := hmem
    have hy₀ : y • NumberField.PlaceAbove.above E K (w.under (𝓞 E)) = w := hy
    have hy' : y⁻¹ • w = NumberField.PlaceAbove.above E K (w.under (𝓞 E)) := inv_smul_eq_iff.mpr hy₀.symm
    have key := hvalO (sg f) ⟨w.under (𝓞 E), hv⟩ w y⁻¹ hy'
    rw [hsg_ne _ _ (by simp)] at key
    have key' : NumberField.PlaceTransport.transport y⁻¹ hy'
        (((Additive.toMul (Φ (sg f)) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 w) = 1 := key.trans rfl
    rw [map_eq_one_iff _ (RingEquiv.injective _)] at key'
    apply Units.ext
    change ((Additive.toMul (Φ (sg f)) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 w = _
    rw [Units.val_one]
    exact key'
  ·
    intro f
    apply Units.ext
    change ((Additive.toMul (Φ (sg f)) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 = _
    rw [Units.val_one]
    funext w
    obtain ⟨y, hy⟩ := NumberField.InfinitePlace.exists_smul_eq_of_comap_eq (k := E) (w := w)
      (w' := NumberField.ArchIdele.above E K (w.comap (algebraMap E K))) (by rw [NumberField.ArchIdele.comap_above])
    have key := hvalI (sg f) (w.comap (algebraMap E K)) w y hy
    rw [hsg_ne _ _ (by simp)] at key
    have key' : NumberField.InfinitePlaceTransport.transport y hy
        (((Additive.toMul (Φ (sg f)) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w) = 1 := key.trans rfl
    rw [map_eq_one_iff _ (RingEquiv.injective _)] at key'
    exact key'

end Proof

end S_M4aHerbrand_exists_hom_coind_ideles_finPart_eq_and_eq_one
end P2MW
export P2MW.S_M4aHerbrand_exists_hom_coind_ideles_finPart_eq_and_eq_one (solution)
