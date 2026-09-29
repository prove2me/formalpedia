-- Prove2me | solution 1 for LanglandsTunnell.not_agreesAwayFromFinite_formalBaseChange_sylowH_eisensteinTableOf_of_quatH
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/faf88843-f821-55b8-91d5-5e6df0a07f0e

import Mathlib
import Definitions.Def_LanglandsTunnell_QuatH
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_LanglandsTunnell_ConverseData
import Theorems.Thm_AutomorphicForm_formalBaseChange_formalBaseChange
import Theorems.Thm_AutomorphicForm_not_agreesAwayFromFinite_eisensteinTableOf_of_isArithGenuineCuspRealizable_of_coversModCentre
import Theorems.Thm_AutomorphicForm_exists_agreesAwayFromFinite_formalBaseChange_eisensteinTableOf
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_not_agreesAwayFromFinite_formalBaseChange_sylowH_eisensteinTableOf_of_quatH
p2m_attr_erase "instance" "RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension"
p2m_attr_erase "instance" "IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers"
p2m_attr_erase "simp" "AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply"
p2m_attr_erase "simp" "RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply"
p2m_attr_erase "simp" "IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq M4aHerbrand.Bridge.finiteConorm_apply M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul"
p2m_attr_erase "simp" "M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply"

set_option autoImplicit false

p2m_open "IsDedekindDomain NumberField AutomorphicForm P2MW.S_LanglandsTunnell_not_agreesAwayFromFinite_formalBaseChange_sylowH_eisensteinTableOf_of_quatH.AutomorphicForm"
open NumberField.AdelicLevel NumberField.AdelicBox NumberField.TateGlobal
open AutomorphicForm.WindowedSiegel
open LanglandsTunnell LanglandsTunnell.Converse
open NumberField.AdelicHaar AutomorphicForm.SiegelCovering

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "formalBaseChange formalBaseChange_a formalBaseChange_b HeckeEigensystem HeckeEigensystem.AgreesAwayFromFinite IsArithGenuineCuspRealizable WindowedSiegel.centreCutSiegelSet productionPinsOf AdelicGL2 IsIdeleClassChar finiteAdelicGL2Subgroup SiegelCovering.CoversModCentre formalBaseChange_formalBaseChange not_agreesAwayFromFinite_eisensteinTableOf_of_isArithGenuineCuspRealizable_of_coversModCentre exists_agreesAwayFromFinite_formalBaseChange_eisensteinTableOf"
namespace HeckeEigensystem
p2m_export "AutomorphicForm.HeckeEigensystem" "AgreesAwayFromFinite level_ne_bot level a"
p2m_open "AutomorphicForm.HeckeEigensystem AutomorphicForm"
variable {F : Type*} [Field F] [NumberField F] {R : Type*} [CommRing R]

p2m_open_scoped "AutomorphicForm.HeckeEigensystem.AgreesAwayFromFinite" in
theorem AgreesAwayFromFinite.refl' (Φ : HeckeEigensystem F R) : Φ.AgreesAwayFromFinite Φ :=
  ⟨∅, fun _ _ => ⟨rfl, rfl⟩⟩

namespace AgreesAwayFromFinite
p2m_open_scoped "AutomorphicForm.HeckeEigensystem.AgreesAwayFromFinite" in
private theorem _root_.AutomorphicForm.HeckeEigensystem.AgreesAwayFromFinite.symm' {Φ Φ' : HeckeEigensystem F R} (h : Φ.AgreesAwayFromFinite Φ') :
    Φ'.AgreesAwayFromFinite Φ := by
  obtain ⟨S, hS⟩ := h
  exact ⟨S, fun v hv => ⟨(hS v hv).1.symm, (hS v hv).2.symm⟩⟩

end AgreesAwayFromFinite
p2m_export "AutomorphicForm.HeckeEigensystem" "AgreesAwayFromFinite.symm'"
namespace AgreesAwayFromFinite
p2m_open_scoped "AutomorphicForm.HeckeEigensystem.AgreesAwayFromFinite" in
private theorem _root_.AutomorphicForm.HeckeEigensystem.AgreesAwayFromFinite.trans' {Φ Φ' Φ'' : HeckeEigensystem F R} (h : Φ.AgreesAwayFromFinite Φ')
    (h' : Φ'.AgreesAwayFromFinite Φ'') : Φ.AgreesAwayFromFinite Φ'' := by
  classical
  obtain ⟨S, hS⟩ := h
  obtain ⟨S', hS'⟩ := h'
  refine ⟨S ∪ S', fun v hv => ?_⟩
  rw [Finset.mem_union, not_or] at hv
  exact ⟨(hS v hv.1).1.trans (hS' v hv.2).1, (hS v hv.1).2.trans (hS' v hv.2).2⟩

end AgreesAwayFromFinite
p2m_export "AutomorphicForm.HeckeEigensystem" "AgreesAwayFromFinite.trans'"
end AutomorphicForm.HeckeEigensystem

theorem eisensteinTableOf_agrees_of_level (K : Type) [Field K] [NumberField K]
    (N N' : Ideal (𝓞 K)) (hN : N ≠ ⊥) (hN' : N' ≠ ⊥) (μ₁ μ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) :
    (eisensteinTableOf K N hN μ₁ μ₂).AgreesAwayFromFinite (eisensteinTableOf K N' hN' μ₁ μ₂) :=
  ⟨∅, fun _ _ => ⟨rfl, rfl⟩⟩

theorem HOLE_BC_CONGR (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M]
    [Algebra (𝓞 K) (𝓞 M)] [Algebra.IsIntegral (𝓞 K) (𝓞 M)] [Module.IsTorsionFree (𝓞 K) (𝓞 M)]
    {Φ Φ' : HeckeEigensystem K ℂ} (h : Φ.AgreesAwayFromFinite Φ') :
    (formalBaseChange K M Φ).AgreesAwayFromFinite (formalBaseChange K M Φ') := by
  classical
  obtain ⟨S, hS⟩ := h

  have hfin : {𝔓 : HeightOneSpectrum (𝓞 M) | 𝔓.under (𝓞 K) ∈ S}.Finite := by
    have : {𝔓 : HeightOneSpectrum (𝓞 M) | 𝔓.under (𝓞 K) ∈ S}
        ⊆ ⋃ v ∈ S, (fun 𝔓 : HeightOneSpectrum (𝓞 M) => 𝔓.asIdeal) ⁻¹' ((v.asIdeal).primesOver (𝓞 M)) := by
      intro 𝔓 h𝔓
      simp only [Set.mem_iUnion, Set.mem_preimage]
      refine ⟨𝔓.under (𝓞 K), h𝔓, 𝔓.isPrime, ⟨rfl⟩⟩
    refine Set.Finite.subset ?_ this
    refine Set.Finite.biUnion S.finite_toSet fun v _ => ?_
    haveI := v.isMaximal
    exact (IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 M)).preimage (fun _ _ _ _ h => HeightOneSpectrum.ext h)
  refine ⟨hfin.toFinset, fun 𝔓 h𝔓 => ?_⟩
  rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at h𝔓
  obtain ⟨ha, hb⟩ := hS _ h𝔓
  simp only [formalBaseChange_a, formalBaseChange_b, ha, hb, and_self]

theorem HOLE_TRANS {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) (Φ : HeckeEigensystem ℚ ℂ) :
    (formalBaseChange ↥(fixFld (sylowH e)) ↥(fixFld (quatH e)) (formalBaseChange ℚ ↥(fixFld (sylowH e)) Φ)).AgreesAwayFromFinite
      (formalBaseChange ℚ ↥(fixFld (quatH e)) Φ) := by
  rw [AutomorphicForm.formalBaseChange_formalBaseChange ℚ ↥(fixFld (sylowH e)) ↥(fixFld (quatH e)) Φ]
  exact AutomorphicForm.HeckeEigensystem.AgreesAwayFromFinite.refl' _

theorem solution
    {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (Φ : AutomorphicForm.HeckeEigensystem ℚ ℂ)
    (c₆ u₆ d₁₆ d₂₆ : ℝ)
    (T₆ : Finset (AutomorphicForm.AdelicGL2
      (NumberField.RingOfIntegers ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e)))
      ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e))))
    (hd₆ : d₁₆ < d₂₆)
    (Φ₆ : AutomorphicForm.HeckeEigensystem ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e)) ℂ)
    (h₆ : (AutomorphicForm.formalBaseChange ℚ ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e))
      Φ).AgreesAwayFromFinite Φ₆)
    (hΦ₆ : AutomorphicForm.IsArithGenuineCuspRealizable
      ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e))
      (AutomorphicForm.productionPinsOf ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e))
        (⋃ x ∈ T₆, (· * x) ''
          AutomorphicForm.WindowedSiegel.centreCutSiegelSet
            ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e)) c₆ u₆ d₁₆ d₂₆)
        (fun N =>
          NumberField.AdelicLevel.levelOne
              (NumberField.RingOfIntegers ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e)))
              ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e)) N ⊓
            AutomorphicForm.finiteAdelicGL2Subgroup
              ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e)))
        (fun v =>
          NumberField.AdelicLevel.heckeGen
            (NumberField.RingOfIntegers ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e)))
            ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e)) v)
        (NumberField.AdelicBox.adelicBox ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e)))) Φ₆)
    (hcov₆ : AutomorphicForm.SiegelCovering.CoversModCentre
      ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e))
      (⋃ x ∈ T₆, (· * x) ''
        AutomorphicForm.WindowedSiegel.centreCutSiegelSet
          ↥(LanglandsTunnell.fixFld (LanglandsTunnell.quatH e)) c₆ u₆ d₁₆ d₂₆)) :
    ∀ (μ₁ μ₂ : (AdeleRing (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.sylowH e))) ↥(LanglandsTunnell.fixFld (LanglandsTunnell.sylowH e)))ˣ →* ℂˣ),
      IsIdeleClassChar (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.sylowH e))) ↥(LanglandsTunnell.fixFld (LanglandsTunnell.sylowH e)) μ₁ → IsIdeleClassChar (𝓞 ↥(LanglandsTunnell.fixFld (LanglandsTunnell.sylowH e))) ↥(LanglandsTunnell.fixFld (LanglandsTunnell.sylowH e)) μ₂ →
      Continuous μ₁ → Continuous μ₂ →
      ¬ HeckeEigensystem.AgreesAwayFromFinite (AutomorphicForm.formalBaseChange ℚ ↥(LanglandsTunnell.fixFld (LanglandsTunnell.sylowH e)) Φ)
          (eisensteinTableOf ↥(LanglandsTunnell.fixFld (LanglandsTunnell.sylowH e)) (AutomorphicForm.formalBaseChange ℚ ↥(LanglandsTunnell.fixFld (LanglandsTunnell.sylowH e)) Φ).level (AutomorphicForm.formalBaseChange ℚ ↥(LanglandsTunnell.fixFld (LanglandsTunnell.sylowH e)) Φ).level_ne_bot μ₁ μ₂) := by
  intro μ₁ μ₂ h₁ h₂ hc₁ hc₂ hagree

  have hδ := HOLE_BC_CONGR ↥(fixFld (sylowH e)) ↥(fixFld (quatH e)) hagree
  obtain ⟨ν₁, ν₂, N', hN', hν₁, hν₂, hcν₁, hcν₂, hγ⟩ :=
    AutomorphicForm.exists_agreesAwayFromFinite_formalBaseChange_eisensteinTableOf ↥(fixFld (sylowH e)) ↥(fixFld (quatH e)) _ _ μ₁ μ₂ h₁ h₂ hc₁ hc₂
  have hT := HOLE_TRANS e Φ

  have hΦ₆eis : Φ₆.AgreesAwayFromFinite (eisensteinTableOf ↥(fixFld (quatH e)) Φ₆.level Φ₆.level_ne_bot ν₁ ν₂) :=
    ((h₆.symm'.trans' (hT.symm'.trans' (hδ.trans' hγ))).trans'
      (eisensteinTableOf_agrees_of_level _ N' Φ₆.level hN' Φ₆.level_ne_bot ν₁ ν₂))
  exact AutomorphicForm.not_agreesAwayFromFinite_eisensteinTableOf_of_isArithGenuineCuspRealizable_of_coversModCentre ↥(fixFld (quatH e)) c₆ u₆ d₁₆ d₂₆ T₆ hd₆ hcov₆ Φ₆ hΦ₆ ν₁ ν₂ hν₁ hν₂ hcν₁ hcν₂ hΦ₆eis

end

end S_LanglandsTunnell_not_agreesAwayFromFinite_formalBaseChange_sylowH_eisensteinTableOf_of_quatH
end P2MW
export P2MW.S_LanglandsTunnell_not_agreesAwayFromFinite_formalBaseChange_sylowH_eisensteinTableOf_of_quatH (solution)
