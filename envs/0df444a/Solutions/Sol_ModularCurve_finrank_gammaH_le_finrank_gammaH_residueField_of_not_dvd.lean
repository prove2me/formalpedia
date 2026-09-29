-- Prove2me | solution 1 for ModularCurve.finrank_gammaH_le_finrank_gammaH_residueField_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/fd991a04-af98-5c46-af69-da4d95cec628

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_CohCarrier_Level
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_ModularCurve_XH
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_le_index
import Theorems.Thm_ModularCurve_index_gammaH_le_finrank_adjoin_jqModC_qExpFunctionFieldC_residueField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_finrank_gammaH_le_finrank_gammaH_residueField_of_not_dvd
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.qExpandAlgHomC_apply CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.ProjectiveLine.map_mk"

set_option autoImplicit false

namespace FGamHGlue

open CohCarrier CongruenceSubgroup
open scoped MatrixGroups

variable {M : ℕ}

theorem mem_sup_zpowers_neg_one_iff (H : Subgroup (ZMod M)ˣ) (u : (ZMod M)ˣ) :
    u ∈ H ⊔ Subgroup.zpowers (-1) ↔ u ∈ H ∨ -u ∈ H := by
  constructor
  · intro hu
    rw [Subgroup.mem_sup] at hu
    obtain ⟨y, hy, z, hz, rfl⟩ := hu
    rw [Subgroup.mem_zpowers_iff] at hz
    obtain ⟨n, rfl⟩ := hz
    rcases Int.even_or_odd n with hn | hn
    · left; rw [hn.neg_one_zpow, mul_one]; exact hy
    · right; rw [hn.neg_one_zpow, mul_neg_one, neg_neg]; exact hy
  · rintro (h | h)
    · exact Subgroup.mem_sup_left h
    · have : u = -u * -1 := by rw [mul_neg_one, neg_neg]
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h)
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))

theorem GammaH_mono {H H' : Subgroup (ZMod M)ˣ} (h : H ≤ H') : GammaH M H ≤ GammaH M H' := by
  intro A hA
  obtain ⟨hA0, hAH⟩ := mem_GammaH_iff.mp hA
  exact mem_GammaH_iff.mpr ⟨hA0, h hAH⟩

theorem neg_mem_Gamma0 {γ : SL(2, ℤ)} (h : γ ∈ Gamma0 M) : -γ ∈ Gamma0 M := by
  rw [Gamma0_mem] at h ⊢
  simp [h]

theorem gamma0Units_neg (γ : SL(2, ℤ)) (h : γ ∈ Gamma0 M) :
    gamma0Units M ⟨-γ, neg_mem_Gamma0 h⟩ = -gamma0Units M ⟨γ, h⟩ := by
  ext
  simp [Gamma0Map]

theorem mem_or_neg_mem_of_mem_GammaH_sup (H : Subgroup (ZMod M)ˣ) (γ : SL(2, ℤ))
    (hγ : γ ∈ GammaH M (H ⊔ Subgroup.zpowers (-1))) : γ ∈ GammaH M H ∨ -γ ∈ GammaH M H := by
  obtain ⟨hγ0, hγH⟩ := mem_GammaH_iff.mp hγ
  rcases (mem_sup_zpowers_neg_one_iff H _).mp hγH with h | h
  · exact Or.inl (mem_GammaH_iff.mpr ⟨hγ0, h⟩)
  · refine Or.inr (mem_GammaH_iff.mpr ⟨neg_mem_Gamma0 hγ0, ?_⟩)
    rw [gamma0Units_neg]
    exact h

end FGamHGlue

open FGamHGlue in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution (M : ℕ) [NeZero M]
    (H : Subgroup (ZMod M)ˣ) {ℓ : ℕ} [Fact ℓ.Prime] (hℓM : ¬ ℓ ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    (x : ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField A) (CohCarrier.GammaH M H))
    (y : ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
      (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))
    (hx : (x : LaurentSeries (IsLocalRing.ResidueField A)) =
      ModularCurve.jqModC (IsLocalRing.ResidueField A))
    (hy : (y : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.jqModC (AlgebraicClosure ℚ)) :
    Module.finrank
        (IntermediateField.adjoin (AlgebraicClosure ℚ)
          ({y} : Set (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
            (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))))
        (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
          (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) ≤
      Module.finrank
        (IntermediateField.adjoin (IsLocalRing.ResidueField A)
          ({x} : Set (ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField A)
            (CohCarrier.GammaH M H))))
        (ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField A) (CohCarrier.GammaH M H)) := by
  haveI : (CohCarrier.GammaH M H).FiniteIndex :=
    Subgroup.finiteIndex_of_le (ModularCurve.Gamma1_le_GammaH M H)
  have hT : ModularGroup.T ∈ CohCarrier.GammaH M H := ModularCurve.translation_mem_GammaH M H
  refine le_trans
    (ModularCurve.finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_le_index
      (AlgebraicClosure ℚ) (CohCarrier.GammaH M H) hT
      (CohCarrier.GammaH M (H ⊔ Subgroup.zpowers (-1))) (GammaH_mono le_sup_left)
      (mem_or_neg_mem_of_mem_GammaH_sup H) y hy) ?_
  exact ModularCurve.index_gammaH_le_finrank_adjoin_jqModC_qExpFunctionFieldC_residueField
    M H hℓM A hA x hx

end S_ModularCurve_finrank_gammaH_le_finrank_gammaH_residueField_of_not_dvd
end P2MW
export P2MW.S_ModularCurve_finrank_gammaH_le_finrank_gammaH_residueField_of_not_dvd (solution)
