-- Prove2me | solution 1 for M4aHerbrand.injective_and_finite_and_surjective_localCoordinates_groupCohomology_ideles
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/d48f83d9-e3cf-590e-9241-9b999eb42042

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_NumberField_SIdeleModule
import Definitions.Def_NumberField_PlaceTransport
import Definitions.Def_NumberField_InfinitePlaceTransport
import Theorems.Thm_NumberField_SIdele_exists_addMonoidHom_obj_adeleRing_units_apply
import Theorems.Thm_groupCohomology_coindIso_hom_eq_map_subtype_comp_map_eval_one
import Theorems.Thm_NumberField_PlaceTransport_transport_one
import Theorems.Thm_NumberField_InfinitePlaceTransport_transport_one
import Theorems.Thm_groupCohomology_exists_map_eq_of_directed_of_injective
import Theorems.Thm_NumberField_exists_finset_forall_ramificationIdx_eq_one
import Theorems.Thm_NumberField_SIdele_bijective_groupCohomology_localCoordinates_of_ramificationIdx_eq_one
import Theorems.Thm_NumberField_PlaceTransport_orbit_eq_setOf_under_eq
import Theorems.Thm_NumberField_PlaceDecomp_subsingleton_tateCohomology_integerUnits_of_ramificationIdx_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_M4aHerbrand_injective_and_finite_and_surjective_localCoordinates_groupCohomology_ideles
p2m_attr_erase "instance" "FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing"
p2m_attr_erase "instance" "M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion NumberField.AdelicHaar.locallyCompactSpace_adeleRing NumberField.AdelicHaar.finite_residueField_adicCompletionIntegers NumberField.AdelicHaar.locallyCompactSpace_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_finiteAdeleRing NumberField.AdelicHaar.compactSpace_adicCompletionIntegers NumberField.AdelicHaar.t2Space_finiteAdeleRing NumberField.AdelicHaar.t2Space_matrix_adeleRing NumberField.AdelicHaar.t2Space_adeleRing NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers NumberField.AdelicHaar.t2Space_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_matrix_adeleRing NumberField.AdelicHaar.t2Space_infiniteAdeleRing NumberField.AdelicHaar.properSpace_adicCompletion M4aHerbrand.Bridge.instT2SpaceAdeleRing"
p2m_attr_erase "simp" "M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq M4aHerbrand.Bridge.finiteConorm_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply"
p2m_attr_erase "simp" "AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe"
p2m_attr_erase "simp" "Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory NumberField IsDedekindDomain M4aHerbrand
open scoped NumberField.PlaceDecomp NumberField.InfPlaceDecomp NumberField.PlaceTransport

namespace ShapiroH2

variable (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]

theorem exists_hom_sIdele_ideles (D : IdeleGaloisDescent (𝓞 F) E F)
    [MulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ]
    (hactI : ∀ (g : (F ≃ₐ[E] F)) (x : (AdeleRing (𝓞 F) F)ˣ), g • x = D.unitsAct g x)
    (S : Finset (HeightOneSpectrum (𝓞 E))) :
    ∃ ι : NumberField.SIdele.obj E F S ⟶ Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ,
      Function.Injective ι.hom ∧
      (∀ x : NumberField.SIdele.obj E F S, Additive.toMul (ι.hom x) ∈
        NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F {w | w.under (𝓞 E) ∈ S}) ∧
      (∀ u : (AdeleRing (𝓞 F) F)ˣ, u ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F {w | w.under (𝓞 E) ∈ S} →
        ∃ x : NumberField.SIdele.obj E F S, ι.hom x = Additive.ofMul u) ∧

      (∀ (x : NumberField.SIdele.obj E F S) (v : {v // v ∈ S}),
        finPart (NumberField.PlaceAbove.above E F v.1) (Additive.toMul (ι.hom x)) =
          Additive.toMul ((x (Sum.inl (Sum.inl v))).1 1)) ∧
      (∀ (x : NumberField.SIdele.obj E F S) (v : InfinitePlace E),
        Units.map (Pi.evalMonoidHom (fun u : InfinitePlace F => u.Completion) (NumberField.ArchIdele.above E F v))
            (infPart (Additive.toMul (ι.hom x))) =
          Additive.toMul ((x (Sum.inr v)).1 1)) ∧

      (∀ (x : NumberField.SIdele.obj E F S) (v : {v // v ∈ S}) (w : HeightOneSpectrum (𝓞 F)) (y : (F ≃ₐ[E] F))
        (hy : y • w = NumberField.PlaceAbove.above E F v.1),
        NumberField.PlaceTransport.transport y hy (((Additive.toMul (ι.hom x) : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 w) =
          ((Additive.toMul ((x (Sum.inl (Sum.inl v))).1 y) :
            ((NumberField.PlaceAbove.above E F v.1).adicCompletion F)ˣ) : (NumberField.PlaceAbove.above E F v.1).adicCompletion F)) ∧
      (∀ (x : NumberField.SIdele.obj E F S) (v : {v // v ∉ S}) (w : HeightOneSpectrum (𝓞 F)) (y : (F ≃ₐ[E] F))
        (hy : y • w = NumberField.PlaceAbove.above E F v.1),
        NumberField.PlaceTransport.transport y hy (((Additive.toMul (ι.hom x) : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 w) =
          (((Additive.toMul ((x (Sum.inl (Sum.inr v))).1 y) :
            ((NumberField.PlaceAbove.above E F v.1).adicCompletionIntegers F)ˣ) :
              (NumberField.PlaceAbove.above E F v.1).adicCompletionIntegers F) : (NumberField.PlaceAbove.above E F v.1).adicCompletion F)) ∧
      (∀ (x : NumberField.SIdele.obj E F S) (v : InfinitePlace E) (w : InfinitePlace F) (y : (F ≃ₐ[E] F))
        (hy : y • w = NumberField.ArchIdele.above E F v),
        NumberField.InfinitePlaceTransport.transport y hy (((Additive.toMul (ι.hom x) : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w) =
          ((Additive.toMul ((x (Sum.inr v)).1 y) : ((NumberField.ArchIdele.above E F v).Completion)ˣ) :
            (NumberField.ArchIdele.above E F v).Completion)) := by
  obtain ⟨Φ, hinj, hrange, hequiv, -, hvS, hvI, hvA⟩ :=
    NumberField.SIdele.exists_addMonoidHom_obj_adeleRing_units_apply E F S D

  let ι : NumberField.SIdele.obj E F S ⟶ Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ :=
    @Rep.ofHom ℤ (F ≃ₐ[E] F) _ _ _ _ _ _ (_) (_) (NumberField.SIdele.obj E F S).ρ (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ).ρ
      (@Representation.IntertwiningMap.mk _ _ _ _ _ _ _ _ (_) (_) _ _
        (@LinearMap.mk ℤ ℤ _ _ (RingHom.id ℤ) _ _ _ _ (_) (_) ⟨fun x => Φ x, fun x y => map_add Φ x y⟩
          (fun n x => by
            have h := @map_intCast_smul _ _ _ _ _ _ _ Φ ℤ ℤ _ _ (NumberField.SIdele.obj E F S).hV2 (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ).hV2 n x
            simp only [Int.cast_id] at h
            exact h))
        (fun g => @LinearMap.ext _ _ _ _ _ _ _ _ (_) (_) _ _ _ fun x => by
          show Φ ((NumberField.SIdele.obj E F S).ρ g x) = (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ).ρ g (Φ x)
          rw [hequiv g x, Rep.ofMulDistribMulAction_ρ_apply_apply, hactI]))
  have hι : ∀ x, ι.hom x = Φ x := fun x => rfl
  refine ⟨ι, hinj, fun x => ?_, fun u hu => ?_, fun x v => ?_, fun x v => ?_, hvS, hvI, hvA⟩
  · have : Φ x ∈ Φ.range := ⟨x, rfl⟩
    rw [hrange] at this
    exact this
  · have : Additive.ofMul u ∈ Φ.range := by rw [hrange]; exact hu
    obtain ⟨x, hx⟩ := this
    exact ⟨x, hx⟩
  · apply Units.ext
    have h1 : (1 : (F ≃ₐ[E] F)) • NumberField.PlaceAbove.above E F v.1 = NumberField.PlaceAbove.above E F v.1 := one_smul _ _
    have := hvS x v (NumberField.PlaceAbove.above E F v.1) 1 h1
    rw [NumberField.PlaceTransport.transport_one E F _ h1, RingEquiv.refl_apply] at this
    exact this
  · apply Units.ext
    have h1 : (1 : (F ≃ₐ[E] F)) • NumberField.ArchIdele.above E F v = NumberField.ArchIdele.above E F v := one_smul _ _
    have := hvA x v (NumberField.ArchIdele.above E F v) 1 h1
    rw [NumberField.InfinitePlaceTransport.transport_one E F _ h1, RingEquiv.refl_apply] at this
    exact this

theorem map_id_comp_map_subtype_comp_map_id {k G : Type} [CommRing k] [Group G] (T : Subgroup G)
    {X Y : Rep k G} {Z : Rep k T} (φ : X ⟶ Y) (ψ : Rep.res T.subtype Y ⟶ Z) (n : ℕ) :
    groupCohomology.map (MonoidHom.id G) φ n ≫ groupCohomology.map T.subtype (𝟙 (Rep.res T.subtype Y)) n ≫
        groupCohomology.map (MonoidHom.id T) ψ n =
      groupCohomology.map T.subtype ((Rep.resFunctor T.subtype).map φ ≫ ψ) n := by
  rw [← Category.assoc, ← groupCohomology.map_comp, ← groupCohomology.map_comp]
  rfl

omit [IsGalois E F] in
set_option maxHeartbeats 3200000 in

theorem coordinate_above_eq_coindIso
    [MulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ]
    (S : Finset (HeightOneSpectrum (𝓞 E)))
    (ι : NumberField.SIdele.obj E F S ⟶ Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ)
    (hιv : ∀ (x : NumberField.SIdele.obj E F S) (v : {v // v ∈ S}),
      finPart (NumberField.PlaceAbove.above E F v.1) (Additive.toMul (ι.hom x)) =
        Additive.toMul ((x (Sum.inl (Sum.inl v))).1 1))
    (v : {v // v ∈ S})
    (pr : Rep.res (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v.1)).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) ⟶
      Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v.1)) ((NumberField.PlaceAbove.above E F v.1).adicCompletion F)ˣ)
    (hpr : ∀ x : (AdeleRing (𝓞 F) F)ˣ, pr.hom (Additive.ofMul x) = Additive.ofMul (finPart (NumberField.PlaceAbove.above E F v.1) x))
    (n : ℕ) (x : groupCohomology (NumberField.SIdele.obj E F S) (n + 1)) :
    (groupCohomology.map (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v.1)).subtype (𝟙 (Rep.res (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v.1)).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ))) (n + 1) ≫
        groupCohomology.map (MonoidHom.id _) pr (n + 1)).hom
      ((groupCohomology.map (MonoidHom.id (F ≃ₐ[E] F)) ι (n + 1)).hom x) =
    (groupCohomology.map (MonoidHom.id (F ≃ₐ[E] F))
        (GroupCohomology.RepPi.proj (NumberField.SIdele.fibre E F S) (Sum.inl (Sum.inl v))) (n + 1) ≫
      (groupCohomology.coindIso (NumberField.FiniteSIdele.localUnits E F v.1) (n + 1)).hom).hom x := by

  let ev : Rep.res (NumberField.FiniteSIdele.D E F v.1).subtype
      (Rep.coind (NumberField.FiniteSIdele.D E F v.1).subtype (NumberField.FiniteSIdele.localUnits E F v.1)) ⟶ NumberField.FiniteSIdele.localUnits E F v.1 :=
    (Rep.resCoindHomEquiv (NumberField.FiniteSIdele.D E F v.1).subtype
      (Rep.coind (NumberField.FiniteSIdele.D E F v.1).subtype (NumberField.FiniteSIdele.localUnits E F v.1)) (NumberField.FiniteSIdele.localUnits E F v.1)).symm (𝟙 _)
  have hev : ∀ f : Rep.res (NumberField.FiniteSIdele.D E F v.1).subtype
      (Rep.coind (NumberField.FiniteSIdele.D E F v.1).subtype (NumberField.FiniteSIdele.localUnits E F v.1)),
      ev.hom f = (f : (F ≃ₐ[E] F) → NumberField.FiniteSIdele.localUnits E F v.1) 1 := fun f => rfl
  rw [groupCohomology.coindIso_hom_eq_map_subtype_comp_map_eval_one (NumberField.FiniteSIdele.localUnits E F v.1) (n + 1) ev hev]
  show (groupCohomology.map (MonoidHom.id (F ≃ₐ[E] F)) ι (n + 1) ≫
      groupCohomology.map (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v.1)).subtype (𝟙 _) (n + 1) ≫ groupCohomology.map (MonoidHom.id _) pr (n + 1)).hom x =
    (groupCohomology.map (MonoidHom.id (F ≃ₐ[E] F))
        (GroupCohomology.RepPi.proj (NumberField.SIdele.fibre E F S) (Sum.inl (Sum.inl v))) (n + 1) ≫
      groupCohomology.map (NumberField.FiniteSIdele.D E F v.1).subtype (𝟙 _) (n + 1) ≫
        groupCohomology.map (MonoidHom.id _) ev (n + 1)).hom x
  rw [map_id_comp_map_subtype_comp_map_id, map_id_comp_map_subtype_comp_map_id]
  congr 3

  refine Rep.hom_ext (@Representation.IntertwiningMap.ext _ _ _ _ _ _ _ _ (_) (_) _ _ _ _
    (@LinearMap.ext _ _ _ _ _ _ _ _ (_) (_) _ _ _ fun y => ?_))
  show pr.hom (ι.hom y) = ev.hom ((GroupCohomology.RepPi.proj (NumberField.SIdele.fibre E F S) (Sum.inl (Sum.inl v))).hom y)
  rw [hev, GroupCohomology.RepPi.proj_hom_apply]
  have h1 : ι.hom y = Additive.ofMul (Additive.toMul (ι.hom y)) := rfl
  rw [h1, hpr]
  exact congrArg Additive.ofMul (hιv y v)

omit [IsGalois E F] in
set_option maxHeartbeats 3200000 in

theorem coordinate_above_eq_coindIso_inf
    [MulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ]
    (S : Finset (HeightOneSpectrum (𝓞 E)))
    (ι : NumberField.SIdele.obj E F S ⟶ Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ)
    (hιv : ∀ (x : NumberField.SIdele.obj E F S) (v : InfinitePlace E),
      Units.map (Pi.evalMonoidHom (fun u : InfinitePlace F => u.Completion) (NumberField.ArchIdele.above E F v))
          (infPart (Additive.toMul (ι.hom x))) =
        Additive.toMul ((x (Sum.inr v)).1 1))
    (v : InfinitePlace E)
    (prInf : Rep.res (NumberField.InfPlaceDecomp.decomp E F (NumberField.ArchIdele.above E F v)).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) ⟶ NumberField.InfPlaceDecomp.localUnits E F (NumberField.ArchIdele.above E F v))
    (hprInf : ∀ x : (AdeleRing (𝓞 F) F)ˣ, prInf.hom (Additive.ofMul x) =
      Additive.ofMul (Units.map (Pi.evalMonoidHom (fun u : InfinitePlace F => u.Completion) (NumberField.ArchIdele.above E F v)) (infPart x)))
    (n : ℕ) (x : groupCohomology (NumberField.SIdele.obj E F S) (n + 1)) :
    (groupCohomology.map (NumberField.InfPlaceDecomp.decomp E F (NumberField.ArchIdele.above E F v)).subtype (𝟙 (Rep.res (NumberField.InfPlaceDecomp.decomp E F (NumberField.ArchIdele.above E F v)).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ))) (n + 1) ≫
        groupCohomology.map (MonoidHom.id _) prInf (n + 1)).hom
      ((groupCohomology.map (MonoidHom.id (F ≃ₐ[E] F)) ι (n + 1)).hom x) =
    (groupCohomology.map (MonoidHom.id (F ≃ₐ[E] F))
        (GroupCohomology.RepPi.proj (NumberField.SIdele.fibre E F S) (Sum.inr v)) (n + 1) ≫
      (groupCohomology.coindIso (NumberField.InfPlaceDecomp.localUnits E F (NumberField.ArchIdele.above E F v)) (n + 1)).hom).hom x := by
  let ev : Rep.res (NumberField.InfPlaceDecomp.decomp E F (NumberField.ArchIdele.above E F v)).subtype (Rep.coind (NumberField.InfPlaceDecomp.decomp E F (NumberField.ArchIdele.above E F v)).subtype (NumberField.InfPlaceDecomp.localUnits E F (NumberField.ArchIdele.above E F v))) ⟶ NumberField.InfPlaceDecomp.localUnits E F (NumberField.ArchIdele.above E F v) :=
    (Rep.resCoindHomEquiv (NumberField.InfPlaceDecomp.decomp E F (NumberField.ArchIdele.above E F v)).subtype (Rep.coind (NumberField.InfPlaceDecomp.decomp E F (NumberField.ArchIdele.above E F v)).subtype (NumberField.InfPlaceDecomp.localUnits E F (NumberField.ArchIdele.above E F v))) (NumberField.InfPlaceDecomp.localUnits E F (NumberField.ArchIdele.above E F v))).symm (𝟙 _)
  have hev : ∀ f : Rep.res (NumberField.InfPlaceDecomp.decomp E F (NumberField.ArchIdele.above E F v)).subtype (Rep.coind (NumberField.InfPlaceDecomp.decomp E F (NumberField.ArchIdele.above E F v)).subtype (NumberField.InfPlaceDecomp.localUnits E F (NumberField.ArchIdele.above E F v))),
      ev.hom f = (f : (F ≃ₐ[E] F) → NumberField.InfPlaceDecomp.localUnits E F (NumberField.ArchIdele.above E F v)) 1 := fun f => rfl
  rw [groupCohomology.coindIso_hom_eq_map_subtype_comp_map_eval_one (NumberField.InfPlaceDecomp.localUnits E F (NumberField.ArchIdele.above E F v)) (n + 1) ev hev]
  show (groupCohomology.map (MonoidHom.id (F ≃ₐ[E] F)) ι (n + 1) ≫
      groupCohomology.map (NumberField.InfPlaceDecomp.decomp E F (NumberField.ArchIdele.above E F v)).subtype (𝟙 _) (n + 1) ≫ groupCohomology.map (MonoidHom.id _) prInf (n + 1)).hom x =
    (groupCohomology.map (MonoidHom.id (F ≃ₐ[E] F))
        (GroupCohomology.RepPi.proj (NumberField.SIdele.fibre E F S) (Sum.inr v)) (n + 1) ≫
      groupCohomology.map (NumberField.InfPlaceDecomp.decomp E F (NumberField.ArchIdele.above E F v)).subtype (𝟙 _) (n + 1) ≫
        groupCohomology.map (MonoidHom.id _) ev (n + 1)).hom x
  rw [map_id_comp_map_subtype_comp_map_id, map_id_comp_map_subtype_comp_map_id]
  congr 3
  refine Rep.hom_ext (@Representation.IntertwiningMap.ext _ _ _ _ _ _ _ _ (_) (_) _ _ _ _
    (@LinearMap.ext _ _ _ _ _ _ _ _ (_) (_) _ _ _ fun y => ?_))
  show prInf.hom (ι.hom y) = ev.hom ((GroupCohomology.RepPi.proj (NumberField.SIdele.fibre E F S) (Sum.inr v)).hom y)
  rw [hev, GroupCohomology.RepPi.proj_hom_apply]
  have h1 : ι.hom y = Additive.ofMul (Additive.toMul (ι.hom y)) := rfl
  rw [h1, hprInf]
  exact congrArg Additive.ofMul (hιv y v)

theorem exists_lift_of_injective {k G : Type} [CommRing k] [Group G] {X Y Z : Rep k G}
    (ψ : X ⟶ Z) (i : Y ⟶ Z) (hi : Function.Injective i.hom) (h : ∀ x : X, ∃ y : Y, i.hom y = ψ.hom x) :
    ∃ θ : X ⟶ Y, θ ≫ i = ψ := by
  classical
  choose t ht using h
  have hadd : ∀ x x', t (x + x') = t x + t x' := fun x x' =>
    hi (by rw [map_add, ht, ht, ht, map_add])
  have hsmul : ∀ (c : k) x, t (c • x) = c • t x := fun c x =>
    hi (by rw [map_smul, ht, ht, map_smul])
  let θl : X →ₗ[k] Y := { toFun := t, map_add' := hadd, map_smul' := hsmul }
  refine ⟨Rep.ofHom ⟨θl, fun g => LinearMap.ext fun x => hi ?_⟩, ?_⟩
  · show i.hom (t (X.ρ g x)) = i.hom (Y.ρ g (t x))
    rw [ht, Rep.hom_comm_apply, Rep.hom_comm_apply, ht]
  · exact Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun x => ht x))

set_option maxHeartbeats 3200000 in

theorem coordinate_eq_zero_of_under_notMem
    [MulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ]
    (S : Finset (HeightOneSpectrum (𝓞 E)))
    (ι : NumberField.SIdele.obj E F S ⟶ Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ)
    (hιmem : ∀ x : NumberField.SIdele.obj E F S, Additive.toMul (ι.hom x) ∈
      NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F {w | w.under (𝓞 E) ∈ S})
    (w : HeightOneSpectrum (𝓞 F)) (hw : w.under (𝓞 E) ∉ S)
    (hunr : (w.under (𝓞 E)).asIdeal.ramificationIdx' w.asIdeal = 1)
    (pr : Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) ⟶ Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F w) ((w.adicCompletion F)ˣ))
    (hpr : ∀ x : (AdeleRing (𝓞 F) F)ˣ, pr.hom (Additive.ofMul x) = Additive.ofMul (finPart w x))
    (n : ℕ) (x : groupCohomology (NumberField.SIdele.obj E F S) (n + 1)) :
    (groupCohomology.map (NumberField.PlaceDecomp.decomp E F w).subtype (𝟙 (Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ))) (n + 1) ≫
        groupCohomology.map (MonoidHom.id _) pr (n + 1)).hom
      ((groupCohomology.map (MonoidHom.id (F ≃ₐ[E] F)) ι (n + 1)).hom x) = 0 := by
  classical

  let incl : Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F w) ((w.adicCompletionIntegers F)ˣ) ⟶ Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F w) ((w.adicCompletion F)ˣ) :=
    Rep.ofHom ⟨(Units.map (w.adicCompletionIntegers F).subtype.toMonoidHom).toAdditive.toIntLinearMap, fun _ => rfl⟩
  have hincl : ∀ u : (w.adicCompletionIntegers F)ˣ,
      incl.hom (Additive.ofMul u) = Additive.ofMul (Units.map (w.adicCompletionIntegers F).subtype.toMonoidHom u) :=
    fun u => rfl
  have hinj : Function.Injective incl.hom := by
    intro a b hab
    have hab' : Units.map (w.adicCompletionIntegers F).subtype.toMonoidHom (Additive.toMul a) =
        Units.map (w.adicCompletionIntegers F).subtype.toMonoidHom (Additive.toMul b) := hab
    have : Additive.toMul a = Additive.toMul b :=
      Units.ext (Subtype.ext (congrArg (fun u : (w.adicCompletion F)ˣ => (u : w.adicCompletion F)) hab'))
    exact congrArg Additive.ofMul this

  have hlift : ∀ y : Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (NumberField.SIdele.obj E F S), ∃ u : Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F w) ((w.adicCompletionIntegers F)ˣ),
      incl.hom u = ((Rep.resFunctor (NumberField.PlaceDecomp.decomp E F w).subtype).map ι ≫ pr).hom y := by
    intro y
    obtain ⟨h1, h2⟩ := hιmem y w hw
    refine ⟨Additive.ofMul
      ⟨⟨(finPart w (Additive.toMul (ι.hom y)) : (w.adicCompletion F)), h1⟩,
       ⟨(((finPart w (Additive.toMul (ι.hom y)))⁻¹ : (w.adicCompletion F)ˣ) : (w.adicCompletion F)), h2⟩,
       Subtype.ext (Units.mul_inv _), Subtype.ext (Units.inv_mul _)⟩, ?_⟩
    rw [hincl]
    show _ = pr.hom (ι.hom y)
    conv_rhs => rw [show ι.hom y = Additive.ofMul (Additive.toMul (ι.hom y)) from rfl, hpr]
    congr 1

  obtain ⟨θ, hθ⟩ := exists_lift_of_injective _ incl hinj hlift

  letI : Fintype (NumberField.PlaceDecomp.decomp E F w) := Fintype.ofFinite _
  have hsub := NumberField.PlaceDecomp.subsingleton_tateCohomology_integerUnits_of_ramificationIdx_eq_one E F w
    hunr ((n + 1 : ℕ) : ℤ)
  rw [Rep.tateCohomology_ofNat_succ] at hsub

  show (groupCohomology.map (MonoidHom.id (F ≃ₐ[E] F)) ι (n + 1) ≫
      groupCohomology.map (NumberField.PlaceDecomp.decomp E F w).subtype (𝟙 _) (n + 1) ≫ groupCohomology.map (MonoidHom.id _) pr (n + 1)).hom x = 0
  rw [map_id_comp_map_subtype_comp_map_id, ← hθ]
  have hsplit : groupCohomology.map (NumberField.PlaceDecomp.decomp E F w).subtype (θ ≫ incl) (n + 1) =
      groupCohomology.map (NumberField.PlaceDecomp.decomp E F w).subtype θ (n + 1) ≫ groupCohomology.map (MonoidHom.id _) incl (n + 1) := by
    rw [← groupCohomology.map_comp]
    rfl
  rw [hsplit]
  show (groupCohomology.map (MonoidHom.id _) incl (n + 1)).hom
      ((groupCohomology.map (NumberField.PlaceDecomp.decomp E F w).subtype θ (n + 1)).hom x) = 0
  rw [Subsingleton.elim ((groupCohomology.map (NumberField.PlaceDecomp.decomp E F w).subtype θ (n + 1)).hom x) 0, map_zero]

set_option maxHeartbeats 6400000 in

theorem injective_and_finite_and_surjective_localCoordinates
    (D : IdeleGaloisDescent (𝓞 F) E F)
    [MulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ]
    (hactI : ∀ (g : (F ≃ₐ[E] F)) (x : (AdeleRing (𝓞 F) F)ˣ), g • x = D.unitsAct g x)
    (pr : ∀ w : HeightOneSpectrum (𝓞 F), Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) ⟶
        Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F w) ((w).adicCompletion F)ˣ)
    (hpr : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (AdeleRing (𝓞 F) F)ˣ), (pr w).hom (Additive.ofMul x) = Additive.ofMul (finPart w x))
    (prInf : ∀ v : InfinitePlace F,
      Rep.res (NumberField.InfPlaceDecomp.decomp E F v).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) ⟶ NumberField.InfPlaceDecomp.localUnits E F v)
    (hprInf : ∀ (v : InfinitePlace F) (x : (AdeleRing (𝓞 F) F)ˣ), (prInf v).hom (Additive.ofMul x) =
      Additive.ofMul (Units.map (Pi.evalMonoidHom (fun u : InfinitePlace F => u.Completion) v) (infPart x)))
    (n : ℕ) :
    (∀ x : groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) (n + 1),
      (∀ w : HeightOneSpectrum (𝓞 F), (groupCohomology.map (NumberField.PlaceDecomp.decomp E F w).subtype (pr w) (n + 1)).hom x = 0) →
      (∀ v : InfinitePlace F, (groupCohomology.map (NumberField.InfPlaceDecomp.decomp E F v).subtype (prInf v) (n + 1)).hom x = 0) → x = 0) ∧
    (∀ x : groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) (n + 1),
      {w : HeightOneSpectrum (𝓞 F) | (groupCohomology.map (NumberField.PlaceDecomp.decomp E F w).subtype (pr w) (n + 1)).hom x ≠ 0}.Finite) ∧
    (∀ (T : Finset (HeightOneSpectrum (𝓞 E)))
      (y : ∀ v : HeightOneSpectrum (𝓞 E), groupCohomology
        (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)) (((NumberField.PlaceAbove.above E F v)).adicCompletion F)ˣ) (n + 1))
      (yinf : ∀ v : InfinitePlace E, groupCohomology (NumberField.InfPlaceDecomp.localUnits E F (NumberField.ArchIdele.above E F v)) (n + 1)),
      ∃ x : groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) (n + 1),
        (∀ v ∈ T, (groupCohomology.map (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)).subtype (pr (NumberField.PlaceAbove.above E F v)) (n + 1)).hom x = y v) ∧
        (∀ v ∉ T, (groupCohomology.map (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)).subtype (pr (NumberField.PlaceAbove.above E F v)) (n + 1)).hom x = 0) ∧
        (∀ v : InfinitePlace E, (groupCohomology.map (NumberField.InfPlaceDecomp.decomp E F (NumberField.ArchIdele.above E F v)).subtype (prInf (NumberField.ArchIdele.above E F v)) (n + 1)).hom x = yinf v)) := by
  classical
  obtain ⟨S₀, hS₀⟩ := NumberField.exists_finset_forall_ramificationIdx_eq_one E F

  have hι := fun S : Finset (HeightOneSpectrum (𝓞 E)) => exists_hom_sIdele_ideles E F D hactI S
  choose ι hιinj hιmem hιsurj hιvf hιvi hιtf hιti hιta using hι

  have bridge : ∀ (T : Subgroup (F ≃ₐ[E] F)) {Z : Rep ℤ T} (ψ : Rep.res T.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) ⟶ Z),
      groupCohomology.map T.subtype ψ (n + 1) =
        groupCohomology.map T.subtype (𝟙 (Rep.res T.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ))) (n + 1) ≫
          groupCohomology.map (MonoidHom.id T) ψ (n + 1) := by
    intro T Z ψ
    rw [← groupCohomology.map_comp]
    rfl

  have hmonoU : ∀ {A B : Set (HeightOneSpectrum (𝓞 F))}, A ⊆ B →
      NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F A ≤ NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F B :=
    fun hAB u hu => IsDedekindDomain.FiniteAdeleRing.unitIdelesOutside_mono (𝓞 F) F hAB hu
  have hmono : ∀ S T : Finset (HeightOneSpectrum (𝓞 E)), S ≤ T →
      Set.range (ι S).hom ⊆ Set.range (ι T).hom := by
    rintro S T hST _ ⟨z, rfl⟩
    have hmem : Additive.toMul ((ι S).hom z) ∈
        NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F {w | w.under (𝓞 E) ∈ T} :=
      hmonoU (fun w (hw : w.under (𝓞 E) ∈ S) => hST hw) (hιmem S z)
    obtain ⟨z', hz'⟩ := hιsurj T _ hmem
    exact ⟨z', hz'⟩
  have hcov : ∀ b : Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ, ∃ S : Finset (HeightOneSpectrum (𝓞 E)), b ∈ Set.range (ι S).hom := by
    intro b

    set u : (AdeleRing (𝓞 F) F)ˣ := Additive.toMul b with hu
    set δ : (FiniteAdeleRing (𝓞 F) F)ˣ :=
      Units.map (RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)).toMonoidHom u with hδ
    have h1 : ∀ᶠ w in Filter.cofinite, (δ : FiniteAdeleRing (𝓞 F) F) w ∈ w.adicCompletionIntegers F := (δ : FiniteAdeleRing (𝓞 F) F).2
    have h2 : ∀ᶠ w in Filter.cofinite, ((δ⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) w ∈
        w.adicCompletionIntegers F := ((δ⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F).2
    have hfin := (h1.and h2)
    rw [Filter.eventually_cofinite] at hfin
    refine ⟨hfin.toFinset.image (fun w => w.under (𝓞 E)), ?_⟩
    have hmem : u ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F
        {w | w.under (𝓞 E) ∈ hfin.toFinset.image (fun w => w.under (𝓞 E))} := by
      intro w hw
      by_contra hcon
      apply hw
      show w.under (𝓞 E) ∈ hfin.toFinset.image (fun w => w.under (𝓞 E))
      rw [Finset.mem_image]
      exact ⟨w, by rw [Set.Finite.mem_toFinset]; exact hcon, rfl⟩
    obtain ⟨z, hz⟩ := hιsurj _ u hmem
    exact ⟨z, hz⟩

  have hlift : ∀ (x : groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) (n + 1)) (S₁ : Finset (HeightOneSpectrum (𝓞 E))),
      ∃ S, S₁ ≤ S ∧ ∃ xS : groupCohomology (NumberField.SIdele.obj E F S) (n + 1),
        (groupCohomology.map (MonoidHom.id _) (ι S) (n + 1)).hom xS = x :=
    fun x S₁ => groupCohomology.exists_map_eq_of_directed_of_injective
      (fun S => NumberField.SIdele.obj E F S) ι hιinj hmono hcov (n + 1) x S₁

  have hfinabove : ∀ S : Finset (HeightOneSpectrum (𝓞 E)), {w : HeightOneSpectrum (𝓞 F) | w.under (𝓞 E) ∈ S}.Finite := by
    intro S
    have : {w : HeightOneSpectrum (𝓞 F) | w.under (𝓞 E) ∈ S} =
        ⋃ v ∈ (S : Set (HeightOneSpectrum (𝓞 E))), {w | w.under (𝓞 E) = v} := by
      ext w; simp
    rw [this]
    refine Set.Finite.biUnion S.finite_toSet fun v _ => ?_
    have h := NumberField.PlaceTransport.orbit_eq_setOf_under_eq E F (NumberField.PlaceAbove.above E F v)
    rw [NumberField.SUnits.under_above] at h
    rw [← h]
    exact Set.finite_range _
  refine ⟨fun x hx0 hxi => ?_, fun x => ?_, fun T y yinf => ?_⟩
  ·
    obtain ⟨S, hS, xS, rfl⟩ := hlift x S₀
    have hunr : ∀ w : HeightOneSpectrum (𝓞 F), w.under (𝓞 E) ∉ S →
        (w.under (𝓞 E)).asIdeal.ramificationIdx' w.asIdeal = 1 := fun w hw => hS₀ w fun h => hw (hS h)
    have hbij := NumberField.SIdele.bijective_groupCohomology_localCoordinates_of_ramificationIdx_eq_one E F S hunr n
    suffices h0 : xS = 0 by rw [h0, map_zero]
    apply hbij.1
    simp only [map_zero, Prod.mk.injEq]
    constructor
    · funext v
      rw [← coordinate_above_eq_coindIso E F S (ι S) (hιvf S) v (pr _) (hpr _) n xS, ← LinearMap.comp_apply,
        ← ModuleCat.hom_comp, ← bridge]
      exact hx0 _
    · funext v
      rw [← coordinate_above_eq_coindIso_inf E F S (ι S) (hιvi S) v (prInf _) (hprInf _) n xS,
        ← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← bridge]
      exact hxi _
  ·
    obtain ⟨S, hS, xS, rfl⟩ := hlift x S₀
    refine (hfinabove S).subset fun w hw => ?_
    by_contra hwS
    apply hw
    have hunr : (w.under (𝓞 E)).asIdeal.ramificationIdx' w.asIdeal = 1 := hS₀ w fun h => hwS (hS h)
    rw [bridge]
    exact coordinate_eq_zero_of_under_notMem E F S (ι S) (hιmem S) w hwS hunr (pr w) (hpr w) n xS
  ·
    set S := S₀ ∪ T with hSdef
    have hunr : ∀ w : HeightOneSpectrum (𝓞 F), w.under (𝓞 E) ∉ S →
        (w.under (𝓞 E)).asIdeal.ramificationIdx' w.asIdeal = 1 :=
      fun w hw => hS₀ w fun h => hw (Finset.mem_union_left _ h)
    have hbij := NumberField.SIdele.bijective_groupCohomology_localCoordinates_of_ramificationIdx_eq_one E F S hunr n
    obtain ⟨xS, hxS⟩ := hbij.2
      ((fun v : {v // v ∈ S} => if v.1 ∈ T then y v.1 else 0), (fun v => yinf v))
    refine ⟨(groupCohomology.map (MonoidHom.id _) (ι S) (n + 1)).hom xS, fun v hv => ?_, fun v hv => ?_, fun v => ?_⟩
    · have hvS : v ∈ S := Finset.mem_union_right _ hv
      have h := congrArg (fun p => p.1 ⟨v, hvS⟩) hxS
      simp only [if_pos hv] at h
      have hβ := coordinate_above_eq_coindIso E F S (ι S) (hιvf S) ⟨v, hvS⟩ (pr _) (hpr _) n xS
      dsimp only at hβ
      rw [bridge, hβ]
      exact h
    · by_cases hvS : v ∈ S
      · have h := congrArg (fun p => p.1 ⟨v, hvS⟩) hxS
        simp only [if_neg hv] at h
        have hβ := coordinate_above_eq_coindIso E F S (ι S) (hιvf S) ⟨v, hvS⟩ (pr _) (hpr _) n xS
        dsimp only at hβ
        rw [bridge, hβ]
        exact h
      · have hw : (NumberField.PlaceAbove.above E F v).under (𝓞 E) ∉ S := by
          rw [NumberField.SUnits.under_above]; exact hvS
        rw [bridge]
        exact coordinate_eq_zero_of_under_notMem E F S (ι S) (hιmem S) _ hw (hunr _ hw) (pr _) (hpr _) n xS
    · have h := congrArg (fun p => p.2 v) hxS
      simp only at h
      rw [bridge, coordinate_above_eq_coindIso_inf E F S (ι S) (hιvi S) v (prInf _) (hprInf _) n xS]
      exact h

end ShapiroH2

open CategoryTheory NumberField IsDedekindDomain M4aHerbrand in
open scoped NumberField.PlaceDecomp NumberField.InfPlaceDecomp in
theorem solution
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (D : IdeleGaloisDescent (𝓞 F) E F)
    [MulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ]
    (hactI : ∀ (g : (F ≃ₐ[E] F)) (x : (AdeleRing (𝓞 F) F)ˣ), g • x = D.unitsAct g x)
    (pr : ∀ w : HeightOneSpectrum (𝓞 F), Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) ⟶
        Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F w) ((w).adicCompletion F)ˣ)
    (hpr : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (AdeleRing (𝓞 F) F)ˣ), (pr w).hom (Additive.ofMul x) = Additive.ofMul (finPart w x))
    (prInf : ∀ v : InfinitePlace F,
      Rep.res (NumberField.InfPlaceDecomp.decomp E F v).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) ⟶ NumberField.InfPlaceDecomp.localUnits E F v)
    (hprInf : ∀ (v : InfinitePlace F) (x : (AdeleRing (𝓞 F) F)ˣ), (prInf v).hom (Additive.ofMul x) =
      Additive.ofMul (Units.map (Pi.evalMonoidHom (fun u : InfinitePlace F => u.Completion) v) (infPart x)))
    (n : ℕ) :
    (∀ x : groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) (n + 1),
      (∀ w : HeightOneSpectrum (𝓞 F), (groupCohomology.map (NumberField.PlaceDecomp.decomp E F w).subtype (pr w) (n + 1)).hom x = 0) →
      (∀ v : InfinitePlace F, (groupCohomology.map (NumberField.InfPlaceDecomp.decomp E F v).subtype (prInf v) (n + 1)).hom x = 0) → x = 0) ∧
    (∀ x : groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) (n + 1),
      {w : HeightOneSpectrum (𝓞 F) | (groupCohomology.map (NumberField.PlaceDecomp.decomp E F w).subtype (pr w) (n + 1)).hom x ≠ 0}.Finite) ∧
    (∀ (T : Finset (HeightOneSpectrum (𝓞 E)))
      (y : ∀ v : HeightOneSpectrum (𝓞 E), groupCohomology
        (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)) (((NumberField.PlaceAbove.above E F v)).adicCompletion F)ˣ) (n + 1))
      (yinf : ∀ v : InfinitePlace E, groupCohomology (NumberField.InfPlaceDecomp.localUnits E F (NumberField.ArchIdele.above E F v)) (n + 1)),
      ∃ x : groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (AdeleRing (𝓞 F) F)ˣ) (n + 1),
        (∀ v ∈ T, (groupCohomology.map (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)).subtype (pr (NumberField.PlaceAbove.above E F v)) (n + 1)).hom x = y v) ∧
        (∀ v ∉ T, (groupCohomology.map (NumberField.PlaceDecomp.decomp E F (NumberField.PlaceAbove.above E F v)).subtype (pr (NumberField.PlaceAbove.above E F v)) (n + 1)).hom x = 0) ∧
        (∀ v : InfinitePlace E, (groupCohomology.map (NumberField.InfPlaceDecomp.decomp E F (NumberField.ArchIdele.above E F v)).subtype (prInf (NumberField.ArchIdele.above E F v)) (n + 1)).hom x = yinf v)) :=
  ShapiroH2.injective_and_finite_and_surjective_localCoordinates E F D hactI pr hpr prInf hprInf n

end S_M4aHerbrand_injective_and_finite_and_surjective_localCoordinates_groupCohomology_ideles
end P2MW
export P2MW.S_M4aHerbrand_injective_and_finite_and_surjective_localCoordinates_groupCohomology_ideles (solution)
