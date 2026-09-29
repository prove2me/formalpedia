-- Prove2me | solution 1 for NumberField.LevelArith.eq_of_hasBrauerLocalInvAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/901a4704-e5f3-5111-9a73-244de3d28d81

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_NumberField_SUnitsMax
import Definitions.Def_NumberField_IdeleLocalInvariant
import Definitions.Def_NumberField_BrauerLocalInvariantPresentation
import Definitions.Def_NumberField_SUnitsModule
import Theorems.Thm_NumberField_LevelArith_hasLocalInv_of_hasLocalInv_of_le
import Theorems.Thm_NumberField_IdeleLocalInv_eq_of_hasLocalInv
import Theorems.Thm_NumberField_LevelArith_exists_level_sub_eq_coboundary_of_continuousH2SrInflation_eq
import Theorems.Thm_groupCohomology_continuousH2SrInflation_H2pi_eq_of_le
import Theorems.Thm_IntermediateField_exists_normal_isUnramifiedOutside_of_le
import Theorems.Thm_NumberField_LevelArith_exists_monoidHom_levelGal_exists_hom_res_quotientToInvariants_sUnitsRep_bijective
import Theorems.Thm_M4aHerbrand_nonempty_ideleGaloisDescent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_LevelArith_eq_of_hasBrauerLocalInvAt
p2m_attr_erase "instance" "FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing"
p2m_attr_erase "instance" "M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion NumberField.AdelicHaar.locallyCompactSpace_adeleRing NumberField.AdelicHaar.finite_residueField_adicCompletionIntegers NumberField.AdelicHaar.locallyCompactSpace_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_finiteAdeleRing NumberField.AdelicHaar.compactSpace_adicCompletionIntegers NumberField.AdelicHaar.t2Space_finiteAdeleRing NumberField.AdelicHaar.t2Space_matrix_adeleRing NumberField.AdelicHaar.t2Space_adeleRing NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers NumberField.AdelicHaar.t2Space_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_matrix_adeleRing NumberField.AdelicHaar.t2Space_infiniteAdeleRing NumberField.AdelicHaar.properSpace_adicCompletion M4aHerbrand.Bridge.instT2SpaceAdeleRing ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal AlgebraicClosure.Rat.isGalois NumberField.LevelArith.instCommGroupUnitsModPow"
p2m_attr_erase "simp" "GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq M4aHerbrand.Bridge.finiteConorm_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply"
p2m_attr_erase "simp" "SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply"
p2m_attr_erase "simp" "RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply IsLocalRing.principalUnits_zero groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq groupCohomology.coe_continuousH1SrMap_apply groupCohomology.continuousH2SrMap_continuousH2Srπ groupCohomology.coe_levelCocyclesSr₂Map NumberField.LevelArith.smul_mk NumberField.LevelArith.selmerRepInt_ρ_apply NumberField.LevelArith.selmerRepField_ρ_apply NumberField.LevelArith.unitsModPowMap_mk"

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000
p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module CategoryTheory.Limits CategoryTheory.MonoidalCategory.Limits groupCohomology ExtCitation NumberField.LevelArith P2MW.S_NumberField_LevelArith_eq_of_hasBrauerLocalInvAt.NumberField.LevelArith"
p2m_open_scoped "Classical NumberField.LevelArith P2MW.S_NumberField_LevelArith_eq_of_hasBrauerLocalInvAt.NumberField.LevelArith TensorProduct Pointwise"
p2m_open_scoped "NumberField P2MW.S_NumberField_LevelArith_eq_of_hasBrauerLocalInvAt.NumberField"

namespace NumberField
p2m_export "NumberField" "mk AdeleRing SUnits.toUnitsRep SUnits.val placesOverPrimes LevelArith.hasLocalInv_of_hasLocalInv_of_le IdeleLocalInv.eq_of_hasLocalInv LevelArith.exists_level_sub_eq_coboundary_of_continuousH2SrInflation_eq LevelArith.exists_monoidHom_levelGal_exists_hom_res_quotientToInvariants_sUnitsRep_bijective"
namespace LevelArith
p2m_export "NumberField.LevelArith" "levelField levelFieldEquiv coe_levelFieldEquiv placesOverPrimes placesOverPrimesFinset sUnitsMaxRep HasBrauerLocalInvAt hasLocalInv_of_hasLocalInv_of_le exists_level_sub_eq_coboundary_of_continuousH2SrInflation_eq exists_monoidHom_levelGal_exists_hom_res_quotientToInvariants_sUnitsRep_bijective"
namespace ValueUnique
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

theorem exists_pullback (S : Finset Nat.Primes) (L F F' : IntermediateField ℚ (AlgebraicClosure ℚ)) [Normal ℚ ↥F] [Normal ℚ ↥F'] (hFF' : F ≤ F')
    (f : cocycles₂ ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype))) :
    ∃ f' : cocycles₂ ((sUnitsMaxRep S L).quotientToInvariants (F'.fixingSubgroup.comap L.fixingSubgroup.subtype)),
      ∀ g h : ↥L.fixingSubgroup,
        ((f' ((g : ↥L.fixingSubgroup ⧸ F'.fixingSubgroup.comap L.fixingSubgroup.subtype),
              (h : ↥L.fixingSubgroup ⧸ F'.fixingSubgroup.comap L.fixingSubgroup.subtype)) :
            (sUnitsMaxRep S L).quotientToInvariants _) : sUnitsMaxRep S L)
          = ((f ((g : ↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype),
                 (h : ↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype)) :
            (sUnitsMaxRep S L).quotientToInvariants _) : sUnitsMaxRep S L) := by
  have hU : F'.fixingSubgroup.comap L.fixingSubgroup.subtype ≤ F.fixingSubgroup.comap L.fixingSubgroup.subtype :=
    Subgroup.comap_mono (IntermediateField.fixingSubgroup_antitone hFF')
  let π : ↥L.fixingSubgroup ⧸ F'.fixingSubgroup.comap L.fixingSubgroup.subtype →*
      ↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype :=
    QuotientGroup.map _ _ (MonoidHom.id _) hU
  have hinv : Representation.invariants ((sUnitsMaxRep S L).ρ.comp (F.fixingSubgroup.comap L.fixingSubgroup.subtype).subtype) ≤
      Representation.invariants ((sUnitsMaxRep S L).ρ.comp (F'.fixingSubgroup.comap L.fixingSubgroup.subtype).subtype) := by
    intro m hm u
    exact hm ⟨u.1, hU u.2⟩
  let ψ : Rep.res π ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)) ⟶
      (sUnitsMaxRep S L).quotientToInvariants (F'.fixingSubgroup.comap L.fixingSubgroup.subtype) :=
    Rep.ofHom ⟨Submodule.inclusion hinv, fun g => by
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
      refine LinearMap.ext fun z => Subtype.ext ?_
      rfl⟩
  refine ⟨mapCocycles₂ π ψ f, fun g h => ?_⟩
  show (((mapCocycles₂ π ψ f : cocycles₂ _) : _ → _)
    ((g : ↥L.fixingSubgroup ⧸ F'.fixingSubgroup.comap L.fixingSubgroup.subtype), (h : _)) : (sUnitsMaxRep S L).quotientToInvariants _).1 = _
  rw [coe_mapCocycles₂]
  rfl

theorem H2π_eq_of_forall_sub_eq (S : Finset Nat.Primes) (L F : IntermediateField ℚ (AlgebraicClosure ℚ)) [Normal ℚ ↥F]
    (f₁ f₂ : cocycles₂ ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)))
    (b : (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype) →
      ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)))
    (hb : ∀ g h : ↥L.fixingSubgroup,
        ((f₁ ((g : (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype)), (h : (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))) : ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype))) : sUnitsMaxRep S L)
          - ((f₂ ((g : (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype)), (h : (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))) : ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype))) : sUnitsMaxRep S L)
          = (((d₁₂ ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype))).hom b ((g : (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype)), (h : (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))) : ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype))) : sUnitsMaxRep S L)) :
    H2π _ f₁ = H2π _ f₂ := by
  rw [← sub_eq_zero, ← map_sub, H2π_eq_zero_iff]
  refine ⟨b, ?_⟩
  funext pq
  obtain ⟨p, q⟩ := pq
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective p
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective q
  apply Subtype.ext
  exact (hb g h).symm

end NumberField.LevelArith.ValueUnique

open NumberField.LevelArith.ValueUnique in

theorem solution
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hL : L.IsUnramifiedOutside S) [FiniteDimensional ℚ ↥L]
    (h4 : p = 2 → ∃ i ∈ L, i ^ 2 = -1)
    (a : ↥(Submodule.torsion' ℤ (continuousH2Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L)) (Submonoid.powers (p : ℤ)))) (v : ↥(placesOverPrimes ↥L (S : Set Nat.Primes))) (t₁ t₂ : AddCircle (1 : ℚ))
    (h₁ : HasBrauerLocalInvAt p S L a v t₁) (h₂ : HasBrauerLocalInvAt p S L a v t₂) : t₁ = t₂ := by

  obtain ⟨F₁, hLF₁, fd₁, nrm₁, gal₁, hF₁, ι₁, hι₁, φ₁, hbij₁, hval₁, D₁, inst₁, hactI₁, j₁, hj₁, f₁, ha₁, read₁⟩ := h₁
  obtain ⟨F₂, hLF₂, fd₂, nrm₂, gal₂, hF₂, ι₂, hι₂, φ₂, hbij₂, hval₂, D₂, inst₂, hactI₂, j₂, hj₂, f₂, ha₂, read₂⟩ := h₂

  obtain ⟨F, hF12, hF, hnormF⟩ := IntermediateField.exists_normal_isUnramifiedOutside_of_le S (F₁ ⊔ F₂) (hF₁.sup hF₂)
  haveI := hnormF
  have hF₁F : F₁ ≤ F := le_sup_left.trans hF12
  have hF₂F : F₂ ≤ F := le_sup_right.trans hF12
  have hLF : L ≤ F := hLF₁.trans hF₁F
  haveI : FiniteDimensional ℚ ↥F := hF.1

  obtain ⟨f₁', hf₁'⟩ := exists_pullback S L F₁ F hF₁F f₁
  obtain ⟨f₂', hf₂'⟩ := exists_pullback S L F₂ F hF₂F f₂
  have hinfl : continuousH2SrInflation L.fixingSubgroup.subtype S (sUnitsMaxRep S L) F hF (H2π _ f₁')
      = continuousH2SrInflation L.fixingSubgroup.subtype S (sUnitsMaxRep S L) F hF (H2π _ f₂') := by
    rw [groupCohomology.continuousH2SrInflation_H2pi_eq_of_le L.fixingSubgroup.subtype S (sUnitsMaxRep S L) F₁ F hF₁ hF f₁ f₁' hf₁',
      groupCohomology.continuousH2SrInflation_H2pi_eq_of_le L.fixingSubgroup.subtype S (sUnitsMaxRep S L) F₂ F hF₂ hF f₂ f₂' hf₂',
      ← ha₁, ← ha₂]

  obtain ⟨F', hF', galF', hFF', b, hb⟩ :=
    NumberField.LevelArith.exists_level_sub_eq_coboundary_of_continuousH2SrInflation_eq S L hL F hLF hF f₁' f₂' hinfl
  haveI := galF'
  haveI : Normal ℚ ↥F' := galF'.to_normal
  haveI : FiniteDimensional ℚ ↥F' := hF'.1
  have hLF' : L ≤ F' := hLF.trans hFF'
  haveI : IsGalois ↥L ↥(levelField L F' hLF') := isGalois_levelField L F' hLF'
  obtain ⟨f₁'', hf₁''⟩ := exists_pullback S L F F' hFF' f₁'
  obtain ⟨f₂'', hf₂''⟩ := exists_pullback S L F F' hFF' f₂'
  have hclass : H2π _ f₁'' = H2π _ f₂'' := by
    apply H2π_eq_of_forall_sub_eq S L F' f₁'' f₂'' b
    intro g h
    rw [hf₁'', hf₂'']
    exact hb g h

  obtain ⟨ι', hι', φ', hbij', hval'⟩ :=
    NumberField.LevelArith.exists_monoidHom_levelGal_exists_hom_res_quotientToInvariants_sUnitsRep_bijective S L F' hLF' hF'
  obtain ⟨D'⟩ := M4aHerbrand.nonempty_ideleGaloisDescent ↥L ↥(levelField L F' hLF')
  letI instI' : MulDistribMulAction (↥(levelField L F' hLF') ≃ₐ[↥L] ↥(levelField L F' hLF')) (NumberField.AdeleRing (𝓞 ↥(levelField L F' hLF')) ↥(levelField L F' hLF'))ˣ := MulDistribMulAction.compHom _ D'.unitsAct
  have hactI' : ∀ (g : (↥(levelField L F' hLF') ≃ₐ[↥L] ↥(levelField L F' hLF'))) (y : (NumberField.AdeleRing (𝓞 ↥(levelField L F' hLF')) ↥(levelField L F' hLF'))ˣ), g • y = D'.unitsAct g y := fun _ _ => rfl
  let jK : Rep.ofMulDistribMulAction (↥(levelField L F' hLF') ≃ₐ[↥L] ↥(levelField L F' hLF')) (↥(levelField L F' hLF'))ˣ ⟶ Rep.ofMulDistribMulAction (↥(levelField L F' hLF') ≃ₐ[↥L] ↥(levelField L F' hLF')) (NumberField.AdeleRing (𝓞 ↥(levelField L F' hLF')) ↥(levelField L F' hLF'))ˣ :=
    M4aHerbrand.repHomOfMulEquivariant (Units.map (algebraMap ↥(levelField L F' hLF') (NumberField.AdeleRing (𝓞 ↥(levelField L F' hLF')) ↥(levelField L F' hLF')) : ↥(levelField L F' hLF') →* (NumberField.AdeleRing (𝓞 ↥(levelField L F' hLF')) ↥(levelField L F' hLF')))) (fun g u => by
      apply Units.ext
      show algebraMap ↥(levelField L F' hLF') (NumberField.AdeleRing (𝓞 ↥(levelField L F' hLF')) ↥(levelField L F' hLF')) (g • (u : ↥(levelField L F' hLF'))) = D'.act g (algebraMap ↥(levelField L F' hLF') (NumberField.AdeleRing (𝓞 ↥(levelField L F' hLF')) ↥(levelField L F' hLF')) (u : ↥(levelField L F' hLF')))
      rw [D'.compat]
      rfl)
  let j' := NumberField.SUnits.toUnitsRep ↥L ↥(levelField L F' hLF') (placesOverPrimesFinset ↥L S) ≫ jK
  have hj' : ∀ y, Additive.toMul (j'.hom y) =
      Units.map (algebraMap ↥(levelField L F' hLF') (NumberField.AdeleRing (𝓞 ↥(levelField L F' hLF')) ↥(levelField L F' hLF')) : ↥(levelField L F' hLF') →* (NumberField.AdeleRing (𝓞 ↥(levelField L F' hLF')) ↥(levelField L F' hLF'))) (NumberField.SUnits.val ↥L ↥(levelField L F' hLF') (placesOverPrimesFinset ↥L S) y) :=
    fun y => rfl

  have hff₁ : ∀ g h : ↥L.fixingSubgroup,
      ((f₁'' ((g : ↥L.fixingSubgroup ⧸ F'.fixingSubgroup.comap L.fixingSubgroup.subtype), (h : ↥L.fixingSubgroup ⧸ F'.fixingSubgroup.comap L.fixingSubgroup.subtype)) :
          (sUnitsMaxRep S L).quotientToInvariants _) : sUnitsMaxRep S L)
        = ((f₁ ((g : ↥L.fixingSubgroup ⧸ F₁.fixingSubgroup.comap L.fixingSubgroup.subtype), (h : ↥L.fixingSubgroup ⧸ F₁.fixingSubgroup.comap L.fixingSubgroup.subtype)) :
          (sUnitsMaxRep S L).quotientToInvariants _) : sUnitsMaxRep S L) := fun g h => by rw [hf₁'', hf₁']
  have hff₂ : ∀ g h : ↥L.fixingSubgroup,
      ((f₂'' ((g : ↥L.fixingSubgroup ⧸ F'.fixingSubgroup.comap L.fixingSubgroup.subtype), (h : ↥L.fixingSubgroup ⧸ F'.fixingSubgroup.comap L.fixingSubgroup.subtype)) :
          (sUnitsMaxRep S L).quotientToInvariants _) : sUnitsMaxRep S L)
        = ((f₂ ((g : ↥L.fixingSubgroup ⧸ F₂.fixingSubgroup.comap L.fixingSubgroup.subtype), (h : ↥L.fixingSubgroup ⧸ F₂.fixingSubgroup.comap L.fixingSubgroup.subtype)) :
          (sUnitsMaxRep S L).quotientToInvariants _) : sUnitsMaxRep S L) := fun g h => by rw [hf₂'', hf₂']
  have r₁ := NumberField.LevelArith.hasLocalInv_of_hasLocalInv_of_le S L F₁ hLF₁ hF₁ F' hLF' hF' (hF₁F.trans hFF')
    ι₁ hι₁ φ₁ hbij₁ hval₁ ι' hι' φ' hbij' hval' D₁ hactI₁ j₁ hj₁ D' hactI' j' hj' f₁ f₁'' hff₁ v.1 t₁ read₁
  have r₂ := NumberField.LevelArith.hasLocalInv_of_hasLocalInv_of_le S L F₂ hLF₂ hF₂ F' hLF' hF' (hF₂F.trans hFF')
    ι₂ hι₂ φ₂ hbij₂ hval₂ ι' hι' φ' hbij' hval' D₂ hactI₂ j₂ hj₂ D' hactI' j' hj' f₂ f₂'' hff₂ v.1 t₂ read₂

  rw [hclass] at r₁
  exact NumberField.IdeleLocalInv.eq_of_hasLocalInv ↥L ↥(levelField L F' hLF') D' hactI' _ v.1 t₁ t₂ r₁ r₂

end S_NumberField_LevelArith_eq_of_hasBrauerLocalInvAt
end P2MW
export P2MW.S_NumberField_LevelArith_eq_of_hasBrauerLocalInvAt (solution)
