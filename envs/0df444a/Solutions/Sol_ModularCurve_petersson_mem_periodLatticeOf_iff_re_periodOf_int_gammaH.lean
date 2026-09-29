-- Prove2me | solution 1 for ModularCurve.petersson_mem_periodLatticeOf_iff_re_periodOf_int_gammaH
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/5c04089c-bf76-56e5-b8e2-3badc5c45268

import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_PeriodOf
import Definitions.Def_AutomorphicForm_Gamma0FundamentalSet
import Theorems.Thm_ModularCurve_petersson_mem_periodLatticeOf_iff_re_periodOf_int
import Theorems.Thm_ModularCurve_exists_linearEquiv_cuspForm_sup_zpowers_neg_one_dualMap_periodOf
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_petersson_mem_periodLatticeOf_iff_re_periodOf_int_gammaH
p2m_attr_erase "instance" "HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField"
p2m_attr_erase "instance" "AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "simp" "HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.LevelN.coe_jGen PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X"
p2m_attr_erase "simp" "ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule"

set_option autoImplicit false

open UpperHalfPlane MeasureTheory
open scoped MatrixGroups Topology

namespace ModularCurve
p2m_export "ModularCurve" "Gamma1_le_GammaH periodOf periodLatticeOf petersson_mem_periodLatticeOf_iff_re_periodOf_int exists_linearEquiv_cuspForm_sup_zpowers_neg_one_dualMap_periodOf"
namespace PetLatTransport
p2m_open "ModularCurve"

theorem neg_one_zpow_eq_or (k : ℤ) : (-1 : SL(2, ℤ)) ^ k = 1 ∨ (-1 : SL(2, ℤ)) ^ k = -1 := by
  rcases Int.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · left
    rw [← two_mul, zpow_mul, zpow_ofNat, neg_one_sq, one_zpow]
  · right
    rw [zpow_add, zpow_mul, zpow_ofNat, neg_one_sq, one_zpow, one_mul, zpow_one]

scoped instance zpowers_neg_one_normal : (Subgroup.zpowers (-1 : SL(2, ℤ))).Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
  rcases neg_one_zpow_eq_or k with h | h
  · rw [h, mul_one, mul_inv_cancel]
    exact Subgroup.one_mem _
  · rw [h, mul_neg_one, neg_mul, mul_inv_cancel]
    exact Subgroup.mem_zpowers _

theorem mem_or_neg_mem_of_mem_sup {Γ : Subgroup SL(2, ℤ)} {x : SL(2, ℤ)}
    (hx : x ∈ Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))) : x ∈ Γ ∨ -x ∈ Γ := by
  rw [Subgroup.mem_sup_of_normal_right] at hx
  obtain ⟨y, hy, z, hz, rfl⟩ := hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  rcases neg_one_zpow_eq_or k with h | h
  · exact Or.inl (by rw [h, mul_one]; exact hy)
  · exact Or.inr (by rw [h, mul_neg_one, neg_neg]; exact hy)

theorem transport (Γ Γ' : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    (hΓ' : Γ' = Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)))
    (hcong : CongruenceSubgroup.IsCongruenceSubgroup Γ')
    (f : CuspForm Γ 2) :
    (∃ Λ ∈ ModularCurve.periodLatticeOf Γ, ∀ g : CuspForm Γ 2,
        Complex.I * (∫ τ in FLT.Gamma0FundamentalSet.gammaFundamentalSet Γ',
          UpperHalfPlane.petersson 2 ⇑f ⇑g τ) = Λ g) ↔
      ∀ γ : Γ, ∃ m : ℤ, (ModularCurve.periodOf Γ γ f).re = m := by
  classical
  subst hΓ'
  haveI : ((Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) : Subgroup SL(2, ℤ))).FiniteIndex :=
    Subgroup.finiteIndex_of_le (le_sup_left : Γ ≤ Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)))
  have hneg : (-1 : SL(2, ℤ)) ∈ Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  obtain ⟨e, he, hesymm, -, heper, hnegper, hlat⟩ :=
    ModularCurve.exists_linearEquiv_cuspForm_sup_zpowers_neg_one_dualMap_periodOf Γ
  have key := ModularCurve.petersson_mem_periodLatticeOf_iff_re_periodOf_int
    (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))) hcong hneg (e.symm f)
  have hcoe_f : (⇑(e.symm f) : ℍ → ℂ) = ⇑f := funext (hesymm f)
  have hper : ∀ γ : Γ, ModularCurve.periodOf Γ γ f =
      ModularCurve.periodOf (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))) ⟨γ, Subgroup.mem_sup_left γ.2⟩ (e.symm f) := by
    intro γ
    have h := congrArg (fun φ => φ (e.symm f)) (heper γ)
    simpa [LinearMap.dualMap_apply] using h
  constructor
  · rintro ⟨Λ, hΛ, hval⟩
    have hL := key.mp ⟨e.toLinearMap.dualMap Λ, (hlat Λ).mp hΛ, fun g' => by
      rw [LinearMap.dualMap_apply, LinearEquiv.coe_coe, ← hval (e g'), hcoe_f,
        show (⇑(e g') : ℍ → ℂ) = ⇑g' from funext (he g')]⟩
    intro γ
    obtain ⟨m, hm⟩ := hL ⟨γ, Subgroup.mem_sup_left γ.2⟩
    exact ⟨m, by rw [hper]; exact hm⟩
  · intro hint
    have hint' : ∀ γ' : ↥(Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))), ∃ m : ℤ,
        (ModularCurve.periodOf (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))) γ' (e.symm f)).re = m := by
      intro γ'
      rcases mem_or_neg_mem_of_mem_sup γ'.2 with h | h
      · obtain ⟨m, hm⟩ := hint ⟨γ', h⟩
        refine ⟨m, ?_⟩
        rw [hper] at hm
        convert hm using 3
      · obtain ⟨m, hm⟩ := hint ⟨-(γ' : SL(2, ℤ)), h⟩
        refine ⟨m, ?_⟩
        rw [hper] at hm
        have h2 := hnegper (γ' : SL(2, ℤ)) γ'.2 (Subgroup.mem_sup_left h)
        have h2' := congrArg (fun φ => (φ (e.symm f)).re) h2
        simp only [Subtype.coe_eta] at h2'
        rw [← h2']
        convert hm using 3
    obtain ⟨Λ', hΛ', hval'⟩ := key.mpr hint'
    refine ⟨e.symm.toLinearMap.dualMap Λ', ?_, fun g => ?_⟩
    · rw [hlat]
      convert hΛ' using 1
      ext g'
      simp [LinearMap.dualMap_apply]
    · rw [LinearMap.dualMap_apply, LinearEquiv.coe_coe, ← hval' (e.symm g), hcoe_f,
        show (⇑(e.symm g) : ℍ → ℂ) = ⇑g from funext (hesymm g)]

end ModularCurve.PetLatTransport
p2m_reactivate "P2MW.S_ModularCurve_petersson_mem_periodLatticeOf_iff_re_periodOf_int_gammaH.ModularCurve P2MW.S_ModularCurve_petersson_mem_periodLatticeOf_iff_re_periodOf_int_gammaH.ModularCurve.PetLatTransport"
p2m_reactivate "P2MW.S_ModularCurve_petersson_mem_periodLatticeOf_iff_re_periodOf_int_gammaH.ModularCurve"

open ModularCurve.PetLatTransport in
theorem solution
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (f : CuspForm (CohCarrier.GammaH M H) 2) :
    (∃ Λ ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H), ∀ g : CuspForm (CohCarrier.GammaH M H) 2,
        Complex.I * (∫ τ in FLT.Gamma0FundamentalSet.gammaFundamentalSet
          (CohCarrier.GammaH M H ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))), UpperHalfPlane.petersson 2 ⇑f ⇑g τ) = Λ g) ↔
      ∀ γ : CohCarrier.GammaH M H, ∃ m : ℤ, (ModularCurve.periodOf (CohCarrier.GammaH M H) γ f).re = m := by
  haveI : (CohCarrier.GammaH M H).FiniteIndex :=
    Subgroup.finiteIndex_of_le (ModularCurve.Gamma1_le_GammaH M H)
  exact transport (CohCarrier.GammaH M H) _ rfl
    (CongruenceSubgroup.isCongruenceSubgroup_trans _ _ le_sup_left
      (CongruenceSubgroup.isCongruenceSubgroup_trans _ _ (ModularCurve.Gamma1_le_GammaH M H)
        (CongruenceSubgroup.Gamma1_is_congruence M))) f

end S_ModularCurve_petersson_mem_periodLatticeOf_iff_re_periodOf_int_gammaH
end P2MW
export P2MW.S_ModularCurve_petersson_mem_periodLatticeOf_iff_re_periodOf_int_gammaH (solution)
