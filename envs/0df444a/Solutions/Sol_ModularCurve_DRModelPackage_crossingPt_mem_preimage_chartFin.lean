-- Prove2me | solution 1 for ModularCurve.DRModelPackage.crossingPt_mem_preimage_chartFin
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/e881cb9b-504c-5c9d-9f8e-2c698155db06

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageCrossingFrame
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModelCharts
import Theorems.Thm_ModularCurve_DRModelPackage_compl_jNeLocus_inter_range_comp_eq_singleton
import Theorems.Thm_ModularCurve_DRModel_exists_ne_and_notMem_chartFin_pFibre
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackage_crossingPt_mem_preimage_chartFin
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.qExpandAlgHomC_apply ModularCurve.jqNModC_one ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero"
p2m_attr_erase "simp" "ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd"
p2m_attr_erase "simp" "ModularCurve.eisensteinSystem_of_not_dvd NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow"
p2m_attr_erase "simp" "ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve AlgebraicCurve

namespace L1PREP

variable (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p)
  (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ]

theorem fst_mem_of_mem_range_compInf_of_mem_range_compZero (hp : 5 ≤ p)
    (x : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ)))))
    (hinf : x ∈ Set.range (𝔛.compInf κ).base) (hzero : x ∈ Set.range (𝔛.compZero κ).base) :
    (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ)))).base x ∈
      ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤) := by
  by_contra hx

  obtain ⟨-, a, ha⟩ := ModularCurve.DRModelPackage.compl_jNeLocus_inter_range_comp_eq_singleton p 𝔛 κ (𝔛.compInf κ)
    (Or.inl rfl)
  obtain ⟨-, b, hb⟩ := ModularCurve.DRModelPackage.compl_jNeLocus_inter_range_comp_eq_singleton p 𝔛 κ (𝔛.compZero κ)
    (Or.inr rfl)

  have hmem : ∀ y : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ)))),
      y ∈ ((TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ :
          (TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ).Opens) :
        Set ↥(TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ)) ↔
      (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ)))).base y ∈
        ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤) := by
    intro y
    change (TwoChartIntegralModel.baseChangeι ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ).base y ∈
        TwoChartIntegralModel.chartFinOpen ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) ↔ _
    rw [← TwoChartIntegralModel.TwoChartsAux.U_eq]
    exact Iff.rfl

  have hxa : x = (𝔛.compInf κ).base a.1 := by
    have : x ∈ ((TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ :
          (TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ).Opens) :
        Set ↥(TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ))ᶜ ∩
        Set.range (𝔛.compInf κ).base := ⟨fun h => hx ((hmem x).mp h), hinf⟩
    rw [ha] at this
    exact this
  have hxb : x = (𝔛.compZero κ).base b.1 := by
    have : x ∈ ((TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ :
          (TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ).Opens) :
        Set ↥(TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ))ᶜ ∩
        Set.range (𝔛.compZero κ).base := ⟨fun h => hx ((hmem x).mp h), hzero⟩
    rw [hb] at this
    exact this

  obtain ⟨y₁, y₂, hne, hy₁, hy₂⟩ := ModularCurve.DRModel.exists_ne_and_notMem_chartFin_pFibre p hp κ
  have key : ∀ y : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ)))),
      (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ)))).base y ∉
        ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤) → y = x := by
    intro y hy
    rcases 𝔛.comp_jointly_surjective κ y with h | h
    · have : y ∈ ((TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ :
            (TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ).Opens) :
          Set ↥(TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ))ᶜ ∩
          Set.range (𝔛.compInf κ).base := ⟨fun h' => hy ((hmem y).mp h'), h⟩
      rw [ha] at this
      rw [hxa]; exact this
    · have : y ∈ ((TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ :
            (TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ).Opens) :
          Set ↥(TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ))ᶜ ∩
          Set.range (𝔛.compZero κ).base := ⟨fun h' => hy ((hmem y).mp h'), h⟩
      rw [hb] at this
      rw [hxb]; exact this
  exact hne ((key y₁ hy₁).trans (key y₂ hy₂).symm)

theorem main (hp : 5 ≤ p) (O : Type) [CommRing O] (toκ : O →+* κ)
    (n : ↥(pullback (𝔛.compInf κ) (𝔛.compZero κ))) :
    (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).base (𝔛.crossingPt O κ toκ n) ∈
      ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤) := by

  have hfst : DRModel.baseChangeMap toκ ≫ pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))
      = pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ))) := by
    rw [DRModel.baseChangeMap, pullback.lift_fst, Category.comp_id]
  have : (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).base (𝔛.crossingPt O κ toκ n)
      = (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ)))).base
          ((𝔛.compInf κ).base ((pullback.fst (𝔛.compInf κ) (𝔛.compZero κ)).base n)) := by
    change ((pullback.fst (𝔛.compInf κ) (𝔛.compZero κ) ≫ 𝔛.compInf κ ≫ DRModel.baseChangeMap toκ) ≫
      pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).base n = _
    rw [Category.assoc, Category.assoc, hfst, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
  rw [this]
  refine fst_mem_of_mem_range_compInf_of_mem_range_compZero p 𝔛 κ hp _ ⟨_, rfl⟩ ⟨(pullback.snd (𝔛.compInf κ) (𝔛.compZero κ)).base n, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]

end L1PREP

theorem solution
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (𝔛 : DRModelPackage p)
    (O : Type) [CommRing O] (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] (toκ : O →+* κ)
    (n : ↥(pullback (𝔛.compInf κ) (𝔛.compZero κ))) :
    𝔛.crossingPt O κ toκ n ∈ (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
      ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤) :=
  L1PREP.main p 𝔛 κ hp O toκ n

end S_ModularCurve_DRModelPackage_crossingPt_mem_preimage_chartFin
end P2MW
export P2MW.S_ModularCurve_DRModelPackage_crossingPt_mem_preimage_chartFin (solution)
