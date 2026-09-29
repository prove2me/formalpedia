-- Prove2me | solution 1 for ModularCurve.isFinite_and_flat_schemeNsmul_of_schemeHomOver_iso_of_jZeroC_points
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/89c3dfbd-156b-5e77-bc98-1b07681d00b0

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Theorems.Thm_ModularCurve_isFinite_and_flat_schemeNsmul_pow_of_jZeroC_points
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isFinite_and_flat_schemeNsmul_of_isUnit
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_schemeNsmul_comp_eq_comp_schemeNsmul_of_hom
import Theorems.Thm_GaloisRep_isDiscreteValuationRing_ratLocalizedAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_isFinite_and_flat_schemeNsmul_of_schemeHomOver_iso_of_jZeroC_points
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue kmfloorsGlue_int_three_isPrime kmfloorsGlue_int_bot_isPrime instTopologicallyFGOfFiniteType AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicCurve.KwCfx.kw_cfx_tau_coe AlgebraicCurve.kw_hwcd_dlog_zero AlgebraicCurve.kw_hwcd_mem_regularDifferentials_iff AlgebraicCurve.kw_hwcd_dlog_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk"
p2m_attr_erase "simp" "ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve IsLocalRing

namespace C5L

universe u

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

theorem nsmul_eq_pow (G : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (n : ℕ) (x : SchemeHomOver t f) :
    letI := G.pointGroup t
    G.nsmul t n x = x ^ n := by
  letI := G.pointGroup t
  induction n with
  | zero => rfl
  | succ n ih => rw [RelativeGroupLaw.nsmul_succ, pow_succ, ← ih]; rfl

theorem nsmul_mul (G : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (a b : ℕ) (x : SchemeHomOver t f) :
    G.nsmul t (a * b) x = G.nsmul t b (G.nsmul t a x) := by
  letI := G.pointGroup t
  rw [nsmul_eq_pow, nsmul_eq_pow, nsmul_eq_pow]
  exact pow_mul x a b

theorem schemeNsmul_mul (G : RelativeGroupLaw R f) (a b : ℕ) :
    G.schemeNsmul (a * b) = G.schemeNsmul a ≫ G.schemeNsmul b := by
  have hnat := G.nsmul_natural f f (G.schemeNsmul a) (G.schemeNsmul_over a) b RelativeGroupLaw.idPoint

  have hid : schemeHomOverComp (G.schemeNsmul a) (G.schemeNsmul_over a)
      (RelativeGroupLaw.idPoint : SchemeHomOver f f) = G.nsmul f a RelativeGroupLaw.idPoint := by
    apply Subtype.ext
    show G.schemeNsmul a ≫ 𝟙 A = (G.nsmul f a RelativeGroupLaw.idPoint).1
    rw [Category.comp_id]
    rfl
  rw [hid, ← nsmul_mul] at hnat

  have := congrArg Subtype.val hnat

  exact this.symm

end C5L

open C5L

theorem solution
    (p : ℕ) [NeZero p] (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ¬ ℓ ∣ p)
    {J : Scheme.{0}} {f : J ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ))}
    (L : RelativeGroupLaw ↥(GaloisRep.ratLocalizedAt ℓ) f)
    (hJ : AbelianSchemePropertyBundle ↥(GaloisRep.ratLocalizedAt ℓ) f)
    (hcomm : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ)))
      (x y : SchemeHomOver t f), L.mul t x y = L.mul t y x)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    (σA : Spec (CommRingCat.of ↥A) ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ)))
    (ptsSp : JZeroC (ResidueField ↥A) p ≃
      SchemeHomOver (Spec.map (CommRingCat.ofHom (residue ↥A)) ≫ σA) f)
    (hadd : ∀ u v : JZeroC (ResidueField ↥A) p, ptsSp (u + v) = L.mul _ (ptsSp u) (ptsSp v))
    {B : Scheme.{0}} {g : B ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ))}
    (LB : RelativeGroupLaw ↥(GaloisRep.ratLocalizedAt ℓ) g)
    (u : SchemeHomOver g f) (v : SchemeHomOver f g)
    (huv : u.1 ≫ v.1 = 𝟙 B) (hvu : v.1 ≫ u.1 = 𝟙 J)
    (hu : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ))) (x y : SchemeHomOver t g),
      NeronModelInfra.schemeHomOverComp (LB.mul t x y) u =
        L.mul t (NeronModelInfra.schemeHomOverComp x u) (NeronModelInfra.schemeHomOverComp y u))
    (n : ℕ) (hn : 0 < n) :
    IsFinite (LB.schemeNsmul n) ∧ Flat (LB.schemeNsmul n) := by
  haveI hdvr : IsDiscreteValuationRing ↥(GaloisRep.ratLocalizedAt ℓ) :=
    GaloisRep.isDiscreteValuationRing_ratLocalizedAt ℓ Fact.out
  haveI : IsNoetherianRing ↥(GaloisRep.ratLocalizedAt ℓ) := inferInstance

  have hℓ : ℓ.Prime := Fact.out
  obtain ⟨k, m, hm, hnkm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' ℓ hℓ.ne_one

  obtain ⟨hfin₁, hflat₁⟩ := ModularCurve.isFinite_and_flat_schemeNsmul_pow_of_jZeroC_points p ℓ hℓp L hJ
    (fun t x y => hcomm t x y) A hA σA ptsSp hadd k
  have hmunit : IsUnit ((m : ℕ) : ↥(GaloisRep.ratLocalizedAt ℓ)) := by
    have hm0 : m ≠ 0 := by rintro rfl; simp at hnkm; exact hn.ne' hnkm
    have hcop : m.Coprime ℓ := (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hm))
    have hmem : ((m : ℚ)⁻¹) ∈ GaloisRep.ratLocalizedAt ℓ := by
      show ((m : ℚ)⁻¹).den.Coprime ℓ
      rw [Rat.inv_natCast_den, if_neg hm0]
      exact hcop
    refine ⟨⟨(m : ↥(GaloisRep.ratLocalizedAt ℓ)), ⟨(m : ℚ)⁻¹, hmem⟩, ?_, ?_⟩, rfl⟩
    · apply Subtype.ext
      show (m : ℚ) * (m : ℚ)⁻¹ = 1
      exact mul_inv_cancel₀ (by exact_mod_cast hm0)
    · apply Subtype.ext
      show (m : ℚ)⁻¹ * (m : ℚ) = 1
      exact inv_mul_cancel₀ (by exact_mod_cast hm0)
  obtain ⟨hfin₂, hflat₂⟩ := GoodReductionJacobian.RelativeGroupLaw.isFinite_and_flat_schemeNsmul_of_isUnit L hJ
    (fun t x y => hcomm t x y) m hmunit

  have hJn : L.schemeNsmul n = L.schemeNsmul (ℓ ^ k) ≫ L.schemeNsmul m := by rw [hnkm]; exact schemeNsmul_mul L _ _
  haveI := hfin₁; haveI := hfin₂; haveI := hflat₁; haveI := hflat₂
  have hfinJ : IsFinite (L.schemeNsmul n) := by rw [hJn]; infer_instance
  have hflatJ : Flat (L.schemeNsmul n) := by rw [hJn]; infer_instance

  obtain ⟨-, -, hcomp⟩ := GoodReductionJacobian.RelativeGroupLaw.schemeNsmul_comp_eq_comp_schemeNsmul_of_hom LB L u
    (fun t x y => hu t x y)
  have hB : LB.schemeNsmul n = u.1 ≫ L.schemeNsmul n ≫ v.1 := by
    rw [← Category.assoc, ← hcomp n, Category.assoc, huv, Category.comp_id]
  haveI : IsIso u.1 := ⟨⟨v.1, huv, hvu⟩⟩
  haveI : IsIso v.1 := ⟨⟨u.1, hvu, huv⟩⟩
  haveI := hfinJ; haveI := hflatJ
  refine ⟨?_, ?_⟩
  · rw [hB]; infer_instance
  · rw [hB]; infer_instance

end S_ModularCurve_isFinite_and_flat_schemeNsmul_of_schemeHomOver_iso_of_jZeroC_points
end P2MW
export P2MW.S_ModularCurve_isFinite_and_flat_schemeNsmul_of_schemeHomOver_iso_of_jZeroC_points (solution)
