-- Prove2me | solution 1 for NumberField.LevelArith.exists_hasBrauerLocalInvAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/b6e0a439-c8bc-5099-a5a4-af0966d81021

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_NumberField_SUnitsMax
import Definitions.Def_NumberField_IdeleLocalInvariant
import Definitions.Def_NumberField_BrauerLocalInvariantPresentation
import Definitions.Def_NumberField_SUnitsModule
import Theorems.Thm_groupCohomology_exists_continuousH2SrInflation_eq_of_nsmul_eq_zero
import Theorems.Thm_NumberField_LevelArith_exists_monoidHom_levelGal_exists_hom_res_quotientToInvariants_sUnitsRep_bijective
import Theorems.Thm_M4aHerbrand_nonempty_ideleGaloisDescent
import Theorems.Thm_NumberField_IdeleLocalInv_exists_hasLocalInv
import Theorems.Thm_groupCohomology_continuousH2SrInflation_H2pi_eq_of_le
import Theorems.Thm_IntermediateField_exists_normal_isUnramifiedOutside_of_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_LevelArith_exists_hasBrauerLocalInvAt
p2m_attr_erase "instance" "AlgebraicClosure.Rat.isGalois NumberField.LevelArith.instCommGroupUnitsModPow FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed"
p2m_attr_erase "instance" "RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap NumberField.AdelicHaar.locallyCompactSpace_adeleRing NumberField.AdelicHaar.finite_residueField_adicCompletionIntegers NumberField.AdelicHaar.locallyCompactSpace_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_finiteAdeleRing NumberField.AdelicHaar.compactSpace_adicCompletionIntegers NumberField.AdelicHaar.t2Space_finiteAdeleRing NumberField.AdelicHaar.t2Space_matrix_adeleRing NumberField.AdelicHaar.t2Space_adeleRing NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers NumberField.AdelicHaar.t2Space_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_matrix_adeleRing NumberField.AdelicHaar.t2Space_infiniteAdeleRing NumberField.AdelicHaar.properSpace_adicCompletion ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing"
p2m_attr_erase "simp" "groupCohomology.coe_continuousH1SrMap_apply groupCohomology.continuousH2SrMap_continuousH2Srπ groupCohomology.coe_levelCocyclesSr₂Map NumberField.LevelArith.smul_mk NumberField.LevelArith.selmerRepInt_ρ_apply NumberField.LevelArith.selmerRepField_ρ_apply NumberField.LevelArith.unitsModPowMap_mk M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply"
p2m_attr_erase "simp" "IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply"
p2m_attr_erase "simp" "Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl IsLocalRing.principalUnits_zero groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply M4aHerbrand.Bridge.finiteConorm_apply M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply"

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 1600000
p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module CategoryTheory.Limits CategoryTheory.MonoidalCategory.Limits groupCohomology ExtCitation NumberField.LevelArith P2MW.S_NumberField_LevelArith_exists_hasBrauerLocalInvAt.NumberField.LevelArith"
p2m_open_scoped "Classical NumberField.LevelArith P2MW.S_NumberField_LevelArith_exists_hasBrauerLocalInvAt.NumberField.LevelArith TensorProduct Pointwise"

p2m_open_scoped "NumberField P2MW.S_NumberField_LevelArith_exists_hasBrauerLocalInvAt.NumberField"

namespace NumberField
p2m_export "NumberField" "mk place AdeleRing SUnits.toUnitsRep SUnits.val placesOverPrimes LevelArith.exists_monoidHom_levelGal_exists_hom_res_quotientToInvariants_sUnitsRep_bijective IdeleLocalInv.exists_hasLocalInv"
namespace LevelArith
p2m_export "NumberField.LevelArith" "levelField levelFieldEquiv coe_levelFieldEquiv placesOverPrimes placesOverPrimesFinset sUnitsMax mem_sUnitsMax_iff sUnitsMaxStable_le sUnitsMaxRep sUnitsMaxRep.val sUnitsMaxRep.val_ρ HasBrauerLocalInvAt exists_monoidHom_levelGal_exists_hom_res_quotientToInvariants_sUnitsRep_bijective"
namespace ValueExists
p2m_open "NumberField.LevelArith NumberField"

section LevelInstances

variable (L F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF : L ≤ F)

noncomputable def levelFieldAlgEquiv : ↥F ≃ₐ[ℚ] ↥(levelField L F hLF) :=
  AlgEquiv.ofRingEquiv (f := levelFieldEquiv L F hLF) (fun r => by
    apply Subtype.ext
    rw [coe_levelFieldEquiv]
    rfl)

theorem normal_levelField [Normal ℚ ↥F] : Normal ℚ ↥(levelField L F hLF) :=
  Normal.of_algEquiv (levelFieldAlgEquiv L F hLF)

theorem isGalois_levelField [Normal ℚ ↥F] : IsGalois ↥L ↥(levelField L F hLF) := by
  haveI := normal_levelField L F hLF
  haveI : IsGalois ℚ ↥(levelField L F hLF) := IsGalois.mk
  exact IsGalois.tower_top_of_isGalois ℚ ↥L ↥(levelField L F hLF)

end LevelInstances

theorem sUnitsMaxRep_smooth (S : Finset Nat.Primes) (L : IntermediateField ℚ (AlgebraicClosure ℚ)) (m : sUnitsMaxRep S L) :
    ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧
      ∀ s : ↥L.fixingSubgroup, L.fixingSubgroup.subtype s ∈ F.fixingSubgroup → (sUnitsMaxRep S L).ρ s m = m := by
  have hm : sUnitsMaxRep.val S L m ∈ sUnitsMax S := sUnitsMaxStable_le S L m.2
  obtain ⟨⟨F, hF, hxF⟩, -⟩ := (mem_sUnitsMax_iff S _).mp hm
  refine ⟨F, hF, fun s hs => ?_⟩
  apply Subtype.ext
  apply Additive.toMul.injective
  show sUnitsMaxRep.val S L ((sUnitsMaxRep S L).ρ s m) = sUnitsMaxRep.val S L m
  rw [sUnitsMaxRep.val_ρ]
  apply Units.ext
  rw [IntermediateField.mem_fixingSubgroup_iff] at hs
  exact hs _ hxF

end NumberField.LevelArith.ValueExists

set_option maxHeartbeats 6400000 in
open NumberField.LevelArith.ValueExists in
open scoped _root_.NumberField _root_.P2MW.S_NumberField_LevelArith_exists_hasBrauerLocalInvAt.NumberField in

theorem solution
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hL : L.IsUnramifiedOutside S) [FiniteDimensional ℚ ↥L]
    (h4 : p = 2 → ∃ i ∈ L, i ^ 2 = -1)
    (a : ↥(Submodule.torsion' ℤ (continuousH2Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L)) (Submonoid.powers (p : ℤ)))) (v : ↥(placesOverPrimes ↥L (S : Set Nat.Primes))) :
    ∃ t : AddCircle (1 : ℚ), HasBrauerLocalInvAt p S L a v t := by

  obtain ⟨⟨c, hc⟩, hca⟩ := (Submodule.mem_torsion'_iff (Submonoid.powers (p : ℤ))
    (a : continuousH2Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L))).mp a.2
  obtain ⟨k, rfl⟩ := hc
  have ha0 : (p ^ k : ℕ) • (a : continuousH2Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L)) = 0 := by
    rw [← natCast_zsmul]
    push_cast
    exact hca

  obtain ⟨F₀, hF₀, hgal₀, y₀, -, hy₀⟩ := groupCohomology.exists_continuousH2SrInflation_eq_of_nsmul_eq_zero
    L.fixingSubgroup.subtype S (sUnitsMaxRep S L) (sUnitsMaxRep_smooth S L) (p ^ k) _ ha0

  obtain ⟨F₁, hLF₁, hF₁, hnorm₁⟩ := IntermediateField.exists_normal_isUnramifiedOutside_of_le S L hL
  haveI : Normal ℚ ↥F₀ := hgal₀.to_normal
  haveI := hnorm₁
  haveI : Normal ℚ ↥(F₀ ⊔ F₁) := @IntermediateField.normal_sup ℚ (AlgebraicClosure ℚ) _ _ _ F₀ F₁ hgal₀.to_normal hnorm₁
  have hF : (F₀ ⊔ F₁).IsUnramifiedOutside S := hF₀.sup hF₁

  generalize hFdef : F₀ ⊔ F₁ = F at hF
  haveI : Normal ℚ ↥F := by rw [← hFdef]; infer_instance
  haveI : FiniteDimensional ℚ ↥F := hF.1
  have hLF : L ≤ F := by rw [← hFdef]; exact hLF₁.trans le_sup_right
  have hF₀F : F₀ ≤ F := by rw [← hFdef]; exact le_sup_left
  haveI : IsGalois ↥L ↥(levelField L F hLF) := isGalois_levelField L F hLF

  obtain ⟨f₀, hf₀⟩ : ∃ f₀ : cocycles₂ ((sUnitsMaxRep S L).quotientToInvariants (F₀.fixingSubgroup.comap L.fixingSubgroup.subtype)),
      H2π _ f₀ = y₀ := H2_induction_on (C := fun x => ∃ f₀, H2π _ f₀ = x) y₀ (fun f => ⟨f, rfl⟩)
  have hU : F.fixingSubgroup.comap L.fixingSubgroup.subtype ≤ F₀.fixingSubgroup.comap L.fixingSubgroup.subtype :=
    Subgroup.comap_mono (IntermediateField.fixingSubgroup_antitone hF₀F)
  let π : ↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype →*
      ↥L.fixingSubgroup ⧸ F₀.fixingSubgroup.comap L.fixingSubgroup.subtype :=
    QuotientGroup.map _ _ (MonoidHom.id _) hU
  have hinv : Representation.invariants ((sUnitsMaxRep S L).ρ.comp (F₀.fixingSubgroup.comap L.fixingSubgroup.subtype).subtype) ≤
      Representation.invariants ((sUnitsMaxRep S L).ρ.comp (F.fixingSubgroup.comap L.fixingSubgroup.subtype).subtype) := by
    intro m hm u
    exact hm ⟨u.1, hU u.2⟩
  let ψ : Rep.res π ((sUnitsMaxRep S L).quotientToInvariants (F₀.fixingSubgroup.comap L.fixingSubgroup.subtype)) ⟶
      (sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype) :=
    Rep.ofHom ⟨Submodule.inclusion hinv, fun g => by
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
      refine LinearMap.ext fun z => Subtype.ext ?_
      rfl⟩
  let f : cocycles₂ ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)) := mapCocycles₂ π ψ f₀
  have hff : ∀ g h : ↥L.fixingSubgroup,
      ((f ((g : ↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype), (h : ↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype)) :
        (sUnitsMaxRep S L).quotientToInvariants _) : sUnitsMaxRep S L)
      = ((f₀ ((g : ↥L.fixingSubgroup ⧸ F₀.fixingSubgroup.comap L.fixingSubgroup.subtype), (h : ↥L.fixingSubgroup ⧸ F₀.fixingSubgroup.comap L.fixingSubgroup.subtype)) :
        (sUnitsMaxRep S L).quotientToInvariants _) : sUnitsMaxRep S L) := by
    intro g h
    show (((mapCocycles₂ π ψ f₀ : cocycles₂ _) : _ → _) ((g : ↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype), (h : _)) : (sUnitsMaxRep S L).quotientToInvariants _).1 = _
    rw [coe_mapCocycles₂]
    rfl
  have ha : (a : continuousH2Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L)) =
      continuousH2SrInflation L.fixingSubgroup.subtype S (sUnitsMaxRep S L) F hF (H2π _ f) := by
    rw [groupCohomology.continuousH2SrInflation_H2pi_eq_of_le L.fixingSubgroup.subtype S (sUnitsMaxRep S L) F₀ F hF₀ hF f₀ f hff,
      hf₀, hy₀]

  obtain ⟨ι, hι, φ, hbij, hval⟩ :=
    NumberField.LevelArith.exists_monoidHom_levelGal_exists_hom_res_quotientToInvariants_sUnitsRep_bijective S L F hLF hF
  obtain ⟨D⟩ := M4aHerbrand.nonempty_ideleGaloisDescent ↥L ↥(levelField L F hLF)
  letI instI : MulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (NumberField.AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ := MulDistribMulAction.compHom _ D.unitsAct
  have hactI : ∀ (g : (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF))) (y : (NumberField.AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ), g • y = D.unitsAct g y := fun _ _ => rfl
  let jK : Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (↥(levelField L F hLF))ˣ ⟶ Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (NumberField.AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ :=
    M4aHerbrand.repHomOfMulEquivariant (Units.map (algebraMap ↥(levelField L F hLF) (NumberField.AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF)) : ↥(levelField L F hLF) →* (NumberField.AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF)))) (fun g u => by
      apply Units.ext
      show algebraMap ↥(levelField L F hLF) (NumberField.AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF)) (g • (u : ↥(levelField L F hLF))) = D.act g (algebraMap ↥(levelField L F hLF) (NumberField.AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF)) (u : ↥(levelField L F hLF)))
      rw [D.compat]
      rfl)
  let j := NumberField.SUnits.toUnitsRep ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S) ≫ jK
  have hj : ∀ y, Additive.toMul (j.hom y) =
      Units.map (algebraMap ↥(levelField L F hLF) (NumberField.AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF)) : ↥(levelField L F hLF) →* (NumberField.AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))) (NumberField.SUnits.val ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S) y) :=
    fun y => rfl

  obtain ⟨t, ht⟩ := NumberField.IdeleLocalInv.exists_hasLocalInv ↥L ↥(levelField L F hLF) D hactI ((groupCohomology.map ι (φ ≫ j) 2) (H2π _ f)) v.1
  exact ⟨t, F, hLF, inferInstance, inferInstance, inferInstance, hF, ι, hι, φ, hbij, hval, D, instI, hactI, j, hj, f, ha, ht⟩

end S_NumberField_LevelArith_exists_hasBrauerLocalInvAt
end P2MW
export P2MW.S_NumberField_LevelArith_exists_hasBrauerLocalInvAt (solution)
