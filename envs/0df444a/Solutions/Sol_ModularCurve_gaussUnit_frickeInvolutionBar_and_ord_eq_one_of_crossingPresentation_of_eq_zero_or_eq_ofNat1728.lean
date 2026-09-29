-- Prove2me | solution 1 for ModularCurve.gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/a2ddc6c7-1ff0-5746-92b9-bd6e761e3d7f

import Mathlib
import Theorems.Thm_ModularCurve_CharPReduction_modularRedLocHom_mem
import Theorems.Thm_ModularCurve_NodeLocalized_exists_hasValue_nodeCoord_of_centred
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_modularEval_kroneckerRemainder
import Theorems.Thm_ModularCurve_eval_kroneckerRemainder_ne_zero_of_mem_ssJSet
import Theorems.Thm_ModularCurve_frickeInvolutionBar_coeffEmb_qExpand
import Theorems.Thm_ModularCurve_exists_isFrickeAutFull_of_neZero
import Theorems.Thm_ModularCurve_qExpand_jqModC_eq_pow_unconditional
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_kroneckerCongruence
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_pow_mem_ssJSet_iff_of_perfectField
import Definitions.Def_ModularCurve_NodeDescent
import Definitions.Def_ModularCurve_NodeLocalized
import Definitions.Def_ModularCurve_JWidth
import Definitions.Def_ModularCurve_CharPReduction
import Definitions.Def_ModularCurve_CuspidalClass
import Definitions.Def_ModularCurve_AtkinLehner
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_SupersingularNodes
import Definitions.Def_ModularCurve_SpecializeModuli
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_StandardAnnulus
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd"
p2m_attr_erase "simp" "ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero"
p2m_attr_erase "simp" "compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"
set_option synthInstance.maxHeartbeats 1600000
set_option autoImplicit false
set_option Elab.async false

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.AlgebraicCurve IsLocalRing ModularCurve~coeffEmb_jq P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.ModularCurve"

noncomputable section

namespace Ws23
namespace NodePlaceAPI

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.AlgebraicCurve IsLocalRing Polynomial"

section PlaceLemmas

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem hasValue_add {v : Place K F} {g g' : F} {a a' : K} (h : v.HasValue g a) (h' : v.HasValue g' a') :
    v.HasValue (g + g') (a + a') := by
  obtain ⟨hg, hr⟩ := h
  obtain ⟨hg', hr'⟩ := h'
  refine ⟨add_mem hg hg', ?_⟩
  have hx : (⟨g + g', add_mem hg hg'⟩ : v.toValuationSubring) = ⟨g, hg⟩ + ⟨g', hg'⟩ := rfl
  rw [hx, map_add, hr, hr', map_add]

theorem hasValue_of_ord_sub_pos {v : Place K F} {g : F} {c : K}
    (h : 0 < v.ord (g - algebraMap K F c)) : v.HasValue g c := by
  have hne : g - algebraMap K F c ≠ 0 := by
    intro h0
    rw [h0, Place.ord_zero] at h
    exact lt_irrefl _ h
  have hmem : g - algebraMap K F c ∈ v.toValuationSubring :=
    v.mem_toValuationSubring_of_ord_nonneg_alt hne h.le
  have hnu : ¬ IsUnit (⟨g - algebraMap K F c, hmem⟩ : v.toValuationSubring) := by
    intro hu
    have h0 := v.ord_coe_unit hu.unit
    rw [IsUnit.unit_spec] at h0
    have h0' : v.ord (g - algebraMap K F c) = 0 := h0
    rw [h0'] at h
    exact lt_irrefl _ h
  have hmax : (⟨g - algebraMap K F c, hmem⟩ : v.toValuationSubring) ∈ maximalIdeal v.toValuationSubring := by
    rw [mem_maximalIdeal, mem_nonunits_iff]
    exact hnu
  have hres0 : residue v.toValuationSubring ⟨g - algebraMap K F c, hmem⟩ = algebraMap K v.ResidueField 0 := by
    rw [map_zero]
    exact (residue_eq_zero_iff _).mpr hmax
  have hd := hasValue_add (⟨hmem, hres0⟩ : v.HasValue (g - algebraMap K F c) 0) (v.hasValue_algebraMap c)
  rwa [sub_add_cancel, zero_add] at hd

theorem hasValue_congrRingEquiv {F' : Type*} [Field F'] [Algebra K F'] (e : F ≃+* F')
    (he : ∀ a : K, e (algebraMap K F a) = algebraMap K F' a) (v : Place K F) {g : F} {c : K}
    (h : v.HasValue g c) : (Place.congrRingEquiv e he v).HasValue (e g) c := by
  obtain ⟨hg, hr⟩ := h
  let φ := Place.comapSymmRingEquiv e v.toValuationSubring
  have hg' : e g ∈ (Place.congrRingEquiv e he v).toValuationSubring := (φ ⟨g, hg⟩).2
  refine ⟨hg', ?_⟩
  have h1 : (⟨e g, hg'⟩ : (Place.congrRingEquiv e he v).toValuationSubring) = φ ⟨g, hg⟩ := rfl
  have h3 : φ (algebraMap K v.toValuationSubring c)
      = algebraMap K (Place.congrRingEquiv e he v).toValuationSubring c := by
    ext
    rw [Place.coe_comapSymmRingEquiv_apply, Place.coe_algebraMap, Place.coe_algebraMap]
    exact he c
  rw [h1, ← Place.residue_algebraMap, ← h3]
  have key : ∀ z : v.toValuationSubring,
      residue _ (φ z) = IsLocalRing.ResidueField.mapEquiv φ (residue _ z) := fun z => by
    rw [IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
    rfl
  show residue _ (φ ⟨g, hg⟩) = residue _ (φ (algebraMap K v.toValuationSubring c))
  rw [key, key, hr, Place.residue_algebraMap]

theorem hasValue_placeOfPoint (a : K) (p : K[X]) :
    (RationalFunctionField.placeOfPoint K a).HasValue (algebraMap K[X] (RatFunc K) p) (p.eval a) := by
  let w := RationalFunctionField.heightOneSpectrumOfIrreducible K (irreducible_X_sub_C a)
  have hmem : algebraMap K[X] (RatFunc K) p ∈ (RationalFunctionField.placeOfPoint K a).toValuationSubring :=
    RationalFunctionField.algebraMap_mem_ofHeightOneSpectrum K w p
  refine ⟨hmem, ?_⟩
  have hker : p - C (p.eval a) ∈ RingHom.ker (RationalFunctionField.residueOfHeightOneSpectrum K w) := by
    rw [RationalFunctionField.ker_residueOfHeightOneSpectrum,
      RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal, Ideal.mem_span_singleton, dvd_iff_isRoot]
    simp [IsRoot]
  rw [RingHom.mem_ker, map_sub, sub_eq_zero, RationalFunctionField.residueOfHeightOneSpectrum_apply,
    RationalFunctionField.residueOfHeightOneSpectrum_apply] at hker
  have hC : (⟨algebraMap K[X] (RatFunc K) (C (p.eval a)), RationalFunctionField.algebraMap_mem_ofHeightOneSpectrum K w _⟩ :
        (RationalFunctionField.placeOfPoint K a).toValuationSubring)
      = algebraMap K (RationalFunctionField.placeOfPoint K a).toValuationSubring (p.eval a) := by
    ext
    rw [Place.coe_algebraMap, IsScalarTower.algebraMap_apply K K[X] (RatFunc K), Polynomial.algebraMap_eq]
  have hker' : residue (RationalFunctionField.placeOfPoint K a).toValuationSubring ⟨_, hmem⟩
      = residue (RationalFunctionField.placeOfPoint K a).toValuationSubring
          ⟨algebraMap K[X] (RatFunc K) (C (p.eval a)), RationalFunctionField.algebraMap_mem_ofHeightOneSpectrum K w _⟩ :=
    hker
  rw [hker', hC, Place.residue_algebraMap]

end PlaceLemmas

end Ws23.NodePlaceAPI

namespace Ws23
namespace NodePlaceAPI

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.AlgebraicCurve IsLocalRing Polynomial ModularCurve~coeffEmb_jq P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.ModularCurve"

section PlaceLemmas2

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem evalAt_eq_of_hasValue' {v : Place K F} {g : F} {a : K} (h : v.HasValue g a) : v.evalAt g = a := by
  rw [v.evalAt_of_mem h.mem, h.residue_eq, v.residueInv_algebraMap]

theorem hasValue_pow {v : Place K F} {g : F} {a : K} (h : v.HasValue g a) (n : ℕ) :
    v.HasValue (g ^ n) (a ^ n) := by
  induction n with
  | zero =>
      rw [pow_zero, pow_zero]
      exact v.hasValue_one
  | succ n ih =>
      rw [pow_succ, pow_succ]
      exact ih.mul h

end PlaceLemmas2

section JLine

variable (K : Type*) [Field K]

noncomputable def jC1 : ↥(modularFunctionFieldC K 1) := ⟨jqModC K, jqModC_mem K 1⟩

@[scoped simp] theorem coe_jC1 : ((jC1 K : ↥(modularFunctionFieldC K 1)) : LaurentSeries K) = jqModC K := rfl

theorem ratFuncEquivCharLOneC_X :
    ratFuncEquivCharLOneC K (algebraMap K[X] (RatFunc K) X) = jC1 K := by
  apply Subtype.ext
  rw [RatFunc.algebraMap_X, ratFuncEquivCharLOneC, AlgEquiv.trans_apply]
  exact RatFunc.algEquivOfTranscendental_X (jqModC K) (transcendental_jqModC K)

theorem ratFuncEquivCharLOneC_polynomial (p : K[X]) :
    ratFuncEquivCharLOneC K (algebraMap K[X] (RatFunc K) p) = Polynomial.aeval (jC1 K) p := by
  have hfun : ((ratFuncEquivCharLOneC K : RatFunc K →ₐ[K] ↥(modularFunctionFieldC K 1)).comp
      (IsScalarTower.toAlgHom K K[X] (RatFunc K))) = Polynomial.aeval (jC1 K) := by
    apply Polynomial.algHom_ext
    rw [AlgHom.comp_apply, IsScalarTower.toAlgHom_apply, Polynomial.aeval_X]
    exact ratFuncEquivCharLOneC_X K
  exact AlgHom.congr_fun hfun p

theorem hasValue_charLGeomPlaceOfPoint_aeval (a : K) (p : K[X]) :
    (charLGeomPlaceOfPoint K a).HasValue (Polynomial.aeval (jC1 K) p) (p.eval a) := by
  have h := hasValue_congrRingEquiv (K := K) (ratFuncEquivCharLOneC K).toRingEquiv
    (fun c => (ratFuncEquivCharLOneC K).commutes c) (RationalFunctionField.placeOfPoint K a)
    (hasValue_placeOfPoint a p)
  rw [← ratFuncEquivCharLOneC_polynomial]
  exact h

theorem hasValue_charLGeomPlaceOfPoint_jC1 (a : K) :
    (charLGeomPlaceOfPoint K a).HasValue (jC1 K) a := by
  simpa using hasValue_charLGeomPlaceOfPoint_aeval K a X

end JLine

end Ws23.NodePlaceAPI
p2m_reactivate "P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.Ws23 P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.Ws23.NodePlaceAPI"
p2m_reactivate "P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.Ws23"

namespace Ws23
namespace NodePlaceAPI

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.AlgebraicCurve AlgebraicCurve.RationalFunctionField IsLocalRing Polynomial ModularCurve~coeffEmb_jq P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.ModularCurve"

section Orders

variable {K : Type*} [Field K]

theorem ord_placeOfPoint_algebraMap_eq_mul (a : K) {q : K[X]} (hq : q ≠ 0) :
    (placeOfPoint K a).ord (algebraMap K[X] (RatFunc K) q)
      = (rootMultiplicity a q : ℤ)
          * (placeOfPoint K a).ord (algebraMap K[X] (RatFunc K) (X - C a)) := by
  obtain ⟨r, hr⟩ := pow_rootMultiplicity_dvd q a
  set m : ℕ := rootMultiplicity a q with hm
  have hXa : (X : K[X]) - C a ≠ 0 := X_sub_C_ne_zero a
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact hq (by simpa using hr)
  have hndvd : ¬((X : K[X]) - C a) ∣ r := by
    intro ⟨s, hs⟩
    have : (X - C a) ^ (m + 1) ∣ q := ⟨s, by rw [hr, hs]; ring⟩
    have := (le_rootMultiplicity_iff hq).mpr this
    omega
  have hinj := IsFractionRing.injective K[X] (RatFunc K)
  have hr0' : algebraMap K[X] (RatFunc K) r ≠ 0 := (map_ne_zero_iff _ hinj).mpr hr0
  have hpow' : algebraMap K[X] (RatFunc K) ((X - C a) ^ m) ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr (pow_ne_zero m hXa)
  have hordr : (placeOfPoint K a).ord (algebraMap K[X] (RatFunc K) r) = 0 := by
    by_contra hcon
    apply hndvd
    have hmem := (Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K)
      (heightOneSpectrumOfIrreducible K (irreducible_X_sub_C a)) hr0).mp hcon
    rw [heightOneSpectrumOfIrreducible_asIdeal, Ideal.mem_span_singleton] at hmem
    exact hmem
  calc (placeOfPoint K a).ord (algebraMap K[X] (RatFunc K) q)
      = (placeOfPoint K a).ord (algebraMap K[X] (RatFunc K) ((X - C a) ^ m)
          * algebraMap K[X] (RatFunc K) r) := by rw [← map_mul, ← hr]
    _ = (placeOfPoint K a).ord (algebraMap K[X] (RatFunc K) ((X - C a) ^ m))
          + (placeOfPoint K a).ord (algebraMap K[X] (RatFunc K) r) :=
        (placeOfPoint K a).ord_mul hpow' hr0'
    _ = (placeOfPoint K a).ord ((algebraMap K[X] (RatFunc K) (X - C a)) ^ (m : ℤ)) := by
        rw [hordr, add_zero, map_pow, ← zpow_natCast]
    _ = (m : ℤ) * (placeOfPoint K a).ord (algebraMap K[X] (RatFunc K) (X - C a)) :=
        (placeOfPoint K a).ord_zpow _ _

theorem ord_placeOfPoint_algebraMap (a : K) {q : K[X]} (hq : q ≠ 0) :
    (placeOfPoint K a).ord (algebraMap K[X] (RatFunc K) q) = (rootMultiplicity a q : ℤ) := by
  rw [ord_placeOfPoint_algebraMap_eq_mul a hq, StandardAnnulus.ord_placeOfPoint_X_sub_C_self a, mul_one]

theorem ord_placeOfPoint_algebraMap' (a : K) (q : K[X]) :
    (placeOfPoint K a).ord (algebraMap K[X] (RatFunc K) q) = (rootMultiplicity a q : ℤ) := by
  by_cases hq : q = 0
  · rw [hq, map_zero, Place.ord_zero, rootMultiplicity_zero, Nat.cast_zero]
  · exact ord_placeOfPoint_algebraMap a hq

variable (K)

theorem ord_charLGeomPlaceOfPoint_ratFuncEquiv (a : K) (f : RatFunc K) :
    (charLGeomPlaceOfPoint K a).ord (ratFuncEquivCharLOneC K f) = (placeOfPoint K a).ord f :=
  Place.ord_congrRingEquiv (ratFuncEquivCharLOneC K).toRingEquiv
    (fun c => (ratFuncEquivCharLOneC K).commutes c) (placeOfPoint K a) f

theorem ord_charLGeomPlaceOfPoint_aeval (a : K) (p : K[X]) :
    (charLGeomPlaceOfPoint K a).ord (Polynomial.aeval (jC1 K) p) = (rootMultiplicity a p : ℤ) := by
  rw [← ratFuncEquivCharLOneC_polynomial, ord_charLGeomPlaceOfPoint_ratFuncEquiv, ord_placeOfPoint_algebraMap']

end Orders
p2m_reactivate "P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.Ws23 P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.Ws23.NodePlaceAPI"

end Ws23.NodePlaceAPI
p2m_reactivate "P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.Ws23 P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.Ws23.NodePlaceAPI"
p2m_reactivate "P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.Ws23 P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.Ws23.NodePlaceAPI"

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.AlgebraicCurve IsLocalRing ModularCurve~coeffEmb_jq P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "CharPReduction.modularRedLocHom_mem CharPReduction.coeffRed_coeff CharPReduction.redRes CharPReduction.redRes_apply CharPReduction.redKer CharPReduction.notMem_redKer_iff CharPReduction.subring_le_localizedAtKer CharPReduction.redLoc CharPReduction.redLoc_spec CharPReduction.redLoc_coe CharPReduction.constSeries CharPReduction.modularRing CharPReduction.jqModC_mem_modularRing CharPReduction.jqNModC_mem_modularRing CharPReduction.constSeries_mem_modularRing CharPReduction.jqModC_mem_integralCoeffs CharPReduction.modularRing_le_integralCoeffs CharPReduction.modularLocalized CharPReduction.modularRedLocHom coeffEmb coeffEmb_coeff coeffEmb_mem_laurentBaseChange jqModC jqNModC jqModC_rat map_jqModC jqModC_eq_map_intCast modularFunctionFieldC jqModC_mem modularFunctionFieldC_one qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_one_apply jq ModularPolynomialData jq_mem jqd_mem_full modularFunctionField_le_full NodeLocalized.exists_hasValue_nodeCoord_of_centred frickeInvolutionBar IsFrickeAutFull frickeInvolutionFull isFrickeAutFull_frickeInvolutionFull modularFunctionFieldBar ssJSet deg_eq_one_modularFunctionFieldBar modularEval_kroneckerRemainder ratFuncEquivCharLOneC charLGeomPlaceOfPoint transcendental_jqModC eval_kroneckerRemainder_ne_zero_of_mem_ssJSet frickeInvolutionBar_coeffEmb_qExpand exists_isFrickeAutFull_of_neZero qExpand_jqModC_eq_pow_unconditional kroneckerCongruence reduceModBivar reduceModBivar_X reduceModBivar_C_X KroneckerCongruence nonempty_modularPolynomialData jWidth"
namespace CharPReduction
p2m_export "ModularCurve.CharPReduction" "modularRedLocHom_mem coeffRed_coeff redRes redRes_apply redKer notMem_redKer_iff mem_localizedAtKer subring_le_localizedAtKer redLoc redRes_ne_zero_of_notMem redLoc_spec redLoc_coe constSeries modularRing jqModC_mem_modularRing jqNModC_mem_modularRing constSeries_mem_modularRing jqModC_mem_integralCoeffs modularRing_le_integralCoeffs modularLocalized modularRedLocHom"
p2m_open "ModularCurve.CharPReduction ModularCurve~coeffEmb_jq"

variable (N : ℕ) [NeZero N] {L : Type*} [Field L] (A : Subring L) {k : Type*} [Field k] (red : A →+* k)

theorem gaussUnit_congr {x y : LaurentSeries L} (hxy : x = y)
    (h : ∃ hx : x ∈ modularLocalized N A red, modularRedLocHom N A red ⟨x, hx⟩ ≠ 0) :
    ∃ hy : y ∈ modularLocalized N A red, modularRedLocHom N A red ⟨y, hy⟩ ≠ 0 := by
  subst hxy
  exact h

theorem gaussUnit_one :
    ∃ h : (1 : LaurentSeries L) ∈ modularLocalized N A red, modularRedLocHom N A red ⟨1, h⟩ ≠ 0 := by
  refine ⟨one_mem _, ?_⟩
  have h1 : (⟨1, one_mem _⟩ : modularLocalized N A red) = 1 := rfl
  rw [h1, map_one]
  exact one_ne_zero

theorem gaussUnit_mul {x y : LaurentSeries L}
    (hx : ∃ h : x ∈ modularLocalized N A red, modularRedLocHom N A red ⟨x, h⟩ ≠ 0)
    (hy : ∃ h : y ∈ modularLocalized N A red, modularRedLocHom N A red ⟨y, h⟩ ≠ 0) :
    ∃ h : x * y ∈ modularLocalized N A red, modularRedLocHom N A red ⟨x * y, h⟩ ≠ 0 := by
  obtain ⟨hx, hx0⟩ := hx
  obtain ⟨hy, hy0⟩ := hy
  refine ⟨mul_mem hx hy, ?_⟩
  have hxy : (⟨x * y, mul_mem hx hy⟩ : modularLocalized N A red) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
  rw [hxy, map_mul]
  exact mul_ne_zero hx0 hy0

theorem gaussUnit_inv {x : LaurentSeries L}
    (hx : ∃ h : x ∈ modularLocalized N A red, modularRedLocHom N A red ⟨x, h⟩ ≠ 0) :
    ∃ h : x⁻¹ ∈ modularLocalized N A red, modularRedLocHom N A red ⟨x⁻¹, h⟩ ≠ 0 := by
  obtain ⟨hx, hx0⟩ := hx
  obtain ⟨r, s, hs, hxs⟩ :=
    (mem_localizedAtKer A red (modularRing N A) (modularRing_le_integralCoeffs N A)).mp hx
  have hsne := redRes_ne_zero_of_notMem (A := A) (red := red) (R := modularRing N A)
    (hR := modularRing_le_integralCoeffs N A) hs
  have hspec := redLoc_spec (A := A) (red := red) (R := modularRing N A)
    (hR := modularRing_le_integralCoeffs N A) ⟨x, hx⟩ hxs
  have hx0' : redLoc (A := A) (red := red) (R := modularRing N A)
      (hR := modularRing_le_integralCoeffs N A) ⟨x, hx⟩ ≠ 0 := hx0
  have hrne : redRes A red (modularRing N A) (modularRing_le_integralCoeffs N A) r ≠ 0 := by
    rw [← hspec]
    exact mul_ne_zero hx0' hsne
  have hr : r ∉ redKer A red (modularRing N A) (modularRing_le_integralCoeffs N A) :=
    (notMem_redKer_iff A red (modularRing N A) (modularRing_le_integralCoeffs N A)).mpr hrne
  have hxne : x ≠ 0 := by
    intro hx0
    apply hrne
    have hr0 : r = 0 := by
      apply Subtype.ext
      rw [← hxs, hx0, zero_mul]
      rfl
    rw [hr0, map_zero]
  have hinv : x⁻¹ * r = s := by
    rw [← hxs, ← mul_assoc, inv_mul_cancel₀ hxne, one_mul]
  have hmem : x⁻¹ ∈ modularLocalized N A red :=
    (mem_localizedAtKer A red (modularRing N A) (modularRing_le_integralCoeffs N A)).mpr ⟨s, r, hr, hinv⟩
  refine ⟨hmem, ?_⟩
  have hspec' := redLoc_spec (A := A) (red := red) (R := modularRing N A)
    (hR := modularRing_le_integralCoeffs N A) ⟨x⁻¹, hmem⟩ hinv
  intro hzero
  apply hsne
  have hzero' : redLoc (A := A) (red := red) (R := modularRing N A)
      (hR := modularRing_le_integralCoeffs N A) ⟨x⁻¹, hmem⟩ = 0 := hzero
  rw [← hspec', hzero', zero_mul]

theorem gaussUnit_pow {x : LaurentSeries L}
    (hx : ∃ h : x ∈ modularLocalized N A red, modularRedLocHom N A red ⟨x, h⟩ ≠ 0) (n : ℕ) :
    ∃ h : x ^ n ∈ modularLocalized N A red, modularRedLocHom N A red ⟨x ^ n, h⟩ ≠ 0 := by
  induction n with
  | zero =>
      rw [pow_zero]
      exact gaussUnit_one N A red
  | succ n ih =>
      rw [pow_succ]
      exact gaussUnit_mul N A red ih hx

theorem gaussUnit_zpow {x : LaurentSeries L}
    (hx : ∃ h : x ∈ modularLocalized N A red, modularRedLocHom N A red ⟨x, h⟩ ≠ 0) (n : ℤ) :
    ∃ h : x ^ n ∈ modularLocalized N A red, modularRedLocHom N A red ⟨x ^ n, h⟩ ≠ 0 := by
  cases n with
  | ofNat n =>
      rw [Int.ofNat_eq_natCast, zpow_natCast]
      exact gaussUnit_pow N A red hx n
  | negSucc n =>
      rw [zpow_negSucc]
      exact gaussUnit_inv N A red (gaussUnit_pow N A red hx (n + 1))

end ModularCurve.CharPReduction
p2m_reactivate "P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.Ws23 P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.Ws23.NodePlaceAPI"
p2m_reactivate "P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.Ws23 P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.Ws23.NodePlaceAPI"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.coe_algebraMap Place.deg Place.ord_zero Place.ord_mul Place.smulRingEquiv Place.coe_smulRingEquiv_apply Place.smul_toValuationSubring Place.ord_smul Place.smulResidueAlgEquiv Place.residue_algebraMap GluedPic0 Place.ord_ofHeightOneSpectrum_ne_zero_iff RationalFunctionField.heightOneSpectrumOfIrreducible RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal RationalFunctionField.algebraMap_mem_ofHeightOneSpectrum RationalFunctionField.residueOfHeightOneSpectrum RationalFunctionField.residueOfHeightOneSpectrum_apply RationalFunctionField.ker_residueOfHeightOneSpectrum RationalFunctionField.placeOfPoint Place.comapSymmRingEquiv Place.coe_comapSymmRingEquiv_apply Place.congrRingEquiv Place.ord_congrRingEquiv Place.evalAt GaussReduction.ord_nonneg_of_mem_gen StandardAnnulus.ord_placeOfPoint_X_sub_C_self Place.mem_smul_iff' Place.hasValue_smul Place.isRational_smul Place.evalAt_smul"
namespace Place
p2m_export "AlgebraicCurve.Place" "ext coe_algebraMap ResidueField deg ord ord_zero ord_mul ord_coe_unit ord_zpow smulRingEquiv coe_smulRingEquiv_apply smul_toValuationSubring ord_smul smulResidueAlgEquiv toValuationSubring residue_algebraMap HasValue hasValue_one hasValue_algebraMap ord_ofHeightOneSpectrum_ne_zero_iff comapSymmRingEquiv coe_comapSymmRingEquiv_apply congrRingEquiv ord_congrRingEquiv IsRational residueInv_algebraMap evalAt evalAt_of_mem algebraMap_evalAt mem_toValuationSubring_of_ord_nonneg_alt mem_smul_iff' hasValue_smul isRational_smul evalAt_smul"
p2m_open "AlgebraicCurve.Place AlgebraicCurve"

variable {K F : Type*} [Field K] [Field F] [Algebra K F] {v : Place K F}

theorem evalAt_eq_of_hasValue' {g : F} {a : K} (h : v.HasValue g a) : v.evalAt g = a := by
  rw [v.evalAt_of_mem h.mem, h.residue_eq, v.residueInv_algebraMap]

theorem hasValue_pow_of_hasValue {g : F} {a : K} (h : v.HasValue g a) (n : ℕ) : v.HasValue (g ^ n) (a ^ n) := by
  induction n with
  | zero =>
      rw [pow_zero, pow_zero]
      exact v.hasValue_one
  | succ n ih =>
      rw [pow_succ, pow_succ]
      exact ih.mul h

theorem hasValue_zpow_of_hasValue {g : F} {a : K} (h : v.HasValue g a) (ha : a ≠ 0) (n : ℤ) :
    v.HasValue (g ^ n) (a ^ n) := by
  cases n with
  | ofNat n =>
      rw [Int.ofNat_eq_natCast, zpow_natCast, zpow_natCast]
      exact hasValue_pow_of_hasValue h n
  | negSucc n =>
      rw [zpow_negSucc, zpow_negSucc]
      exact (hasValue_pow_of_hasValue h (n + 1)).inv (pow_ne_zero _ ha)

end AlgebraicCurve.Place
p2m_reactivate "P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.Ws23 P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.Ws23.NodePlaceAPI"
p2m_reactivate "P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.Ws23 P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.Ws23.NodePlaceAPI"

namespace ModularCurve
p2m_export "ModularCurve" "CharPReduction.modularRedLocHom_mem CharPReduction.coeffRed_coeff CharPReduction.redRes CharPReduction.redRes_apply CharPReduction.redKer CharPReduction.notMem_redKer_iff CharPReduction.subring_le_localizedAtKer CharPReduction.redLoc CharPReduction.redLoc_spec CharPReduction.redLoc_coe CharPReduction.constSeries CharPReduction.modularRing CharPReduction.jqModC_mem_modularRing CharPReduction.jqNModC_mem_modularRing CharPReduction.constSeries_mem_modularRing CharPReduction.jqModC_mem_integralCoeffs CharPReduction.modularRing_le_integralCoeffs CharPReduction.modularLocalized CharPReduction.modularRedLocHom coeffEmb coeffEmb_coeff coeffEmb_mem_laurentBaseChange jqModC jqNModC jqModC_rat map_jqModC jqModC_eq_map_intCast modularFunctionFieldC jqModC_mem modularFunctionFieldC_one qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_one_apply jq ModularPolynomialData jq_mem jqd_mem_full modularFunctionField_le_full NodeLocalized.exists_hasValue_nodeCoord_of_centred frickeInvolutionBar IsFrickeAutFull frickeInvolutionFull isFrickeAutFull_frickeInvolutionFull modularFunctionFieldBar ssJSet deg_eq_one_modularFunctionFieldBar modularEval_kroneckerRemainder ratFuncEquivCharLOneC charLGeomPlaceOfPoint transcendental_jqModC eval_kroneckerRemainder_ne_zero_of_mem_ssJSet frickeInvolutionBar_coeffEmb_qExpand exists_isFrickeAutFull_of_neZero qExpand_jqModC_eq_pow_unconditional kroneckerCongruence reduceModBivar reduceModBivar_X reduceModBivar_C_X KroneckerCongruence nonempty_modularPolynomialData jWidth"
namespace NodeLocalized
p2m_export "ModularCurve.NodeLocalized" "exists_hasValue_nodeCoord_of_centred modularEval pointEval modularLocalizedAtPoint modularEval_mem_modularLocalizedAtPoint coeffSubring redRestrict"
p2m_open "ModularCurve.NodeLocalized ModularCurve~coeffEmb_jq"

theorem correction_identity {K : Type*} [Field K] (a c q w : K) (m : ℤ) :
    a * (c⁻¹ * q ^ (-m))⁻¹ * w ^ (-m) = c * a * (q * w⁻¹) ^ m := by
  rw [mul_zpow, inv_zpow', mul_inv, inv_inv, zpow_neg q m, inv_inv]
  ring

theorem isFrickeAutFull_one_mul (q : ℕ) [Fact q.Prime] :
    IsFrickeAutFull (1 * q) (frickeInvolutionFull (1 * q)) :=
  isFrickeAutFull_frickeInvolutionFull (1 * q) (exists_isFrickeAutFull_of_neZero (1 * q))

theorem frickeInvolutionBar_jElt (q : ℕ) [Fact q.Prime] :
    frickeInvolutionBar (1 * q)
        (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
          (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q))
      = ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ := by
  have h := frickeInvolutionBar_coeffEmb_qExpand (1 * q) (isFrickeAutFull_one_mul q) 1 (1 * q) (one_mul _)
  have hj : (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
        (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q))
      = ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ 1 jq), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
          (jqd_mem_full (1 * q) (Dvd.intro (1 * q) (one_mul _)))⟩ :=
    Subtype.ext (congrArg (coeffEmb (AlgebraicClosure ℚ)) (qExpand_one_apply jq).symm)
  rw [hj, h]

theorem frickeInvolutionBar_jqElt (q : ℕ) [Fact q.Prime] :
    frickeInvolutionBar (1 * q)
        (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ :
          modularFunctionFieldBar (1 * q))
      = ⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
          (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ := by
  have h := frickeInvolutionBar_coeffEmb_qExpand (1 * q) (isFrickeAutFull_one_mul q) (1 * q) 1 (mul_one _)
  have hjq : (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ :
        modularFunctionFieldBar (1 * q))
      = ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
          (jqd_mem_full (1 * q) (Dvd.intro 1 (mul_one _)))⟩ := Subtype.ext rfl
  have hj : (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ 1 jq), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
        (jqd_mem_full (1 * q) (Dvd.intro_left (1 * q) (mul_one _)))⟩ : modularFunctionFieldBar (1 * q))
      = ⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
          (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ :=
    Subtype.ext (congrArg (coeffEmb (AlgebraicClosure ℚ)) (qExpand_one_apply jq))
  rw [hjq, h, hj]

theorem qExpand_one_mul {K : Type*} [CommRing K] (q : ℕ) [NeZero q] (x : LaurentSeries K) :
    qExpand K (1 * q) x = qExpand K q x := by
  ext n
  by_cases h : (q : ℤ) ∣ n
  · obtain ⟨m, rfl⟩ := h
    have e : ((1 * q : ℕ) : ℤ) * m = (q : ℤ) * m := by rw [one_mul]
    rw [qExpand_coeff_mul]
    conv_lhs => rw [← e]
    rw [qExpand_coeff_mul]
  · have h' : ¬ ((1 * q : ℕ) : ℤ) ∣ n := by rwa [one_mul]
    rw [qExpand_coeff_of_not_dvd _ _ h', qExpand_coeff_of_not_dvd _ _ h]

theorem jqNModC_one_mul_eq_pow (K : Type*) [CommRing K] (q : ℕ) [Fact q.Prime] [CharP K q] :
    jqNModC K (1 * q) = jqModC K ^ q := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  rw [jqNModC, qExpand_one_mul, qExpand_jqModC_eq_pow_unconditional K]

theorem coeffEmb_jq : coeffEmb (AlgebraicClosure ℚ) jq = jqModC (AlgebraicClosure ℚ) := by
  rw [← jqModC_rat]
  exact map_jqModC (algebraMap ℚ (AlgebraicClosure ℚ))

theorem coeffEmb_qExpand_jq (N : ℕ) [NeZero N] :
    coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq) = jqNModC (AlgebraicClosure ℚ) N := by
  rw [jqNModC, ← coeffEmb_jq]
  ext n
  by_cases h : (N : ℤ) ∣ n
  · obtain ⟨m, rfl⟩ := h
    rw [coeffEmb_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffEmb_coeff]
  · rw [coeffEmb_coeff, qExpand_coeff_of_not_dvd _ _ h, qExpand_coeff_of_not_dvd _ _ h, map_zero]

theorem algebraMap_eq_single' {K : Type*} [CommRing K] (c : K) :
    algebraMap K (LaurentSeries K) c = HahnSeries.single 0 c := by
  rw [HahnSeries.algebraMap_apply', show algebraMap K (PowerSeries K) c = PowerSeries.C c from by simp,
    HahnSeries.ofPowerSeries_C]
  rfl

section Red

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] (red : A →+* k)

theorem red_coeff_jqModC (n : ℤ) (h : (jqModC (AlgebraicClosure ℚ)).coeff n ∈ A.toSubring) :
    red ⟨(jqModC (AlgebraicClosure ℚ)).coeff n, h⟩ = (jqModC k).coeff n := by
  have hz : (⟨(jqModC (AlgebraicClosure ℚ)).coeff n, h⟩ : ↥A.toSubring)
      = ((jqModC ℤ).coeff n : ↥A.toSubring) := by
    apply Subtype.ext
    show (jqModC (AlgebraicClosure ℚ)).coeff n = (((jqModC ℤ).coeff n : ↥A.toSubring) : AlgebraicClosure ℚ)
    rw [jqModC_eq_map_intCast (K := AlgebraicClosure ℚ), HahnSeries.map_coeff, eq_intCast, SubringClass.coe_intCast]
  rw [hz, map_intCast, jqModC_eq_map_intCast (K := k), HahnSeries.map_coeff, eq_intCast]

theorem redRes_jqModC :
    CharPReduction.redRes A.toSubring red (CharPReduction.modularRing (1 * q) A.toSubring)
        (CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring)
        ⟨jqModC (AlgebraicClosure ℚ), CharPReduction.jqModC_mem_modularRing (1 * q) A.toSubring⟩
      = jqModC k := by
  ext n
  rw [CharPReduction.redRes_apply, CharPReduction.coeffRed_coeff]
  exact red_coeff_jqModC red n _

theorem redRes_jqNModC :
    CharPReduction.redRes A.toSubring red (CharPReduction.modularRing (1 * q) A.toSubring)
        (CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring)
        ⟨jqNModC (AlgebraicClosure ℚ) (1 * q), CharPReduction.jqNModC_mem_modularRing (1 * q) A.toSubring⟩
      = jqNModC k (1 * q) := by
  ext n
  rw [CharPReduction.redRes_apply, CharPReduction.coeffRed_coeff]
  show red ⟨(jqNModC (AlgebraicClosure ℚ) (1 * q)).coeff n, _⟩ = (jqNModC k (1 * q)).coeff n
  by_cases h : ((1 * q : ℕ) : ℤ) ∣ n
  · obtain ⟨m, rfl⟩ := h
    have hm : (jqModC (AlgebraicClosure ℚ)).coeff m ∈ A.toSubring := CharPReduction.jqModC_mem_integralCoeffs A.toSubring m
    have hx : (⟨(jqNModC (AlgebraicClosure ℚ) (1 * q)).coeff ((1 * q : ℕ) * m), CharPReduction.modularRing_le_integralCoeffs
          (1 * q) A.toSubring (CharPReduction.jqNModC_mem_modularRing (1 * q) A.toSubring) _⟩ : ↥A.toSubring)
        = ⟨(jqModC (AlgebraicClosure ℚ)).coeff m, hm⟩ :=
      Subtype.ext (by show (jqNModC (AlgebraicClosure ℚ) (1 * q)).coeff _ = _; rw [jqNModC, qExpand_coeff_mul])
    rw [hx, red_coeff_jqModC red m hm, jqNModC, qExpand_coeff_mul]
  · have hx : (⟨(jqNModC (AlgebraicClosure ℚ) (1 * q)).coeff n, CharPReduction.modularRing_le_integralCoeffs
          (1 * q) A.toSubring (CharPReduction.jqNModC_mem_modularRing (1 * q) A.toSubring) _⟩ : ↥A.toSubring) = 0 :=
      Subtype.ext (by show (jqNModC (AlgebraicClosure ℚ) (1 * q)).coeff n = ((0 : ↥A.toSubring) : AlgebraicClosure ℚ)
                      rw [jqNModC, qExpand_coeff_of_not_dvd _ _ h]; rfl)
    rw [hx, map_zero, jqNModC, qExpand_coeff_of_not_dvd _ _ h]

theorem modularEval_mem_modularRing (N : ℕ) [NeZero N] (P : MvPolynomial (Fin 2) ↥A.toSubring) :
    modularEval N A.toSubring P ∈ CharPReduction.modularRing N A.toSubring := by
  induction P using MvPolynomial.induction_on with
  | C c =>
      rw [modularEval, MvPolynomial.eval₂Hom_C]
      exact CharPReduction.constSeries_mem_modularRing N A.toSubring c
  | add p r hp hr => rw [map_add]; exact add_mem hp hr
  | mul_X p i hp =>
      rw [map_mul]
      refine mul_mem hp ?_
      rw [modularEval, MvPolynomial.eval₂Hom_X']
      revert i
      refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
      · exact CharPReduction.jqModC_mem_modularRing N A.toSubring
      · exact CharPReduction.jqNModC_mem_modularRing N A.toSubring

theorem redRes_modularEval [CharP k q] (P : MvPolynomial (Fin 2) ↥A.toSubring) :
    CharPReduction.redRes A.toSubring red (CharPReduction.modularRing (1 * q) A.toSubring)
        (CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring)
        ⟨modularEval (1 * q) A.toSubring P, modularEval_mem_modularRing (1 * q) P⟩
      = Polynomial.aeval (jqModC k)
          (MvPolynomial.eval₂Hom (Polynomial.C.comp red) ![Polynomial.X, Polynomial.X ^ q] P) := by

  let φ : MvPolynomial (Fin 2) ↥A.toSubring →+* LaurentSeries k :=
    (CharPReduction.redRes A.toSubring red (CharPReduction.modularRing (1 * q) A.toSubring)
        (CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring)).comp
      ((modularEval (1 * q) A.toSubring).codRestrict (CharPReduction.modularRing (1 * q) A.toSubring)
        (modularEval_mem_modularRing (1 * q)))
  let ψ : MvPolynomial (Fin 2) ↥A.toSubring →+* LaurentSeries k :=
    (Polynomial.aeval (jqModC k)).toRingHom.comp
      (MvPolynomial.eval₂Hom (Polynomial.C.comp red) ![Polynomial.X, Polynomial.X ^ q])
  have hφψ : φ = ψ := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)
    ·
      have hC : (⟨modularEval (1 * q) A.toSubring (MvPolynomial.C c), modularEval_mem_modularRing (1 * q) _⟩ :
            ↥(CharPReduction.modularRing (1 * q) A.toSubring))
          = ⟨CharPReduction.constSeries A.toSubring c, CharPReduction.constSeries_mem_modularRing (1 * q) _ c⟩ :=
        Subtype.ext (MvPolynomial.eval₂Hom_C _ _ c)
      show CharPReduction.redRes A.toSubring red _ _ ⟨modularEval (1 * q) A.toSubring (MvPolynomial.C c), _⟩
        = Polynomial.aeval (jqModC k) (MvPolynomial.eval₂Hom (Polynomial.C.comp red) ![Polynomial.X, Polynomial.X ^ q]
            (MvPolynomial.C c))
      rw [hC, MvPolynomial.eval₂Hom_C, RingHom.comp_apply, Polynomial.aeval_C, algebraMap_eq_single' (red c)]
      ext n
      rw [CharPReduction.redRes_apply, CharPReduction.coeffRed_coeff, HahnSeries.coeff_single]
      show red ⟨(CharPReduction.constSeries A.toSubring c).coeff n, _⟩ = _
      have hcs : ∀ m : ℤ, (CharPReduction.constSeries A.toSubring c).coeff m = if m = 0 then (c : AlgebraicClosure ℚ) else 0 := by
        intro m
        show (algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (c : AlgebraicClosure ℚ)).coeff m = _
        rw [algebraMap_eq_single', HahnSeries.coeff_single]
        split_ifs <;> rfl
      by_cases hn : n = 0
      · subst hn
        have hx : (⟨(CharPReduction.constSeries A.toSubring c).coeff 0, CharPReduction.modularRing_le_integralCoeffs (1 * q)
            A.toSubring (CharPReduction.constSeries_mem_modularRing (1 * q) _ c) 0⟩ : ↥A.toSubring) = c :=
          Subtype.ext (by show (CharPReduction.constSeries A.toSubring c).coeff 0 = c; rw [hcs, if_pos rfl])
        rw [hx, if_pos rfl]
      · have hx : (⟨(CharPReduction.constSeries A.toSubring c).coeff n, CharPReduction.modularRing_le_integralCoeffs (1 * q)
            A.toSubring (CharPReduction.constSeries_mem_modularRing (1 * q) _ c) n⟩ : ↥A.toSubring) = 0 :=
          Subtype.ext (by show (CharPReduction.constSeries A.toSubring c).coeff n = ((0 : ↥A.toSubring) : AlgebraicClosure ℚ);
                          rw [hcs, if_neg hn]; rfl)
        rw [hx, map_zero, if_neg hn]
    ·
      have hX : (⟨modularEval (1 * q) A.toSubring (MvPolynomial.X 0), modularEval_mem_modularRing (1 * q) _⟩ :
            ↥(CharPReduction.modularRing (1 * q) A.toSubring))
          = ⟨jqModC (AlgebraicClosure ℚ), CharPReduction.jqModC_mem_modularRing (1 * q) A.toSubring⟩ :=
        Subtype.ext (MvPolynomial.eval₂Hom_X' _ _ 0)
      show CharPReduction.redRes A.toSubring red _ _ ⟨modularEval (1 * q) A.toSubring (MvPolynomial.X 0), _⟩
        = Polynomial.aeval (jqModC k) (MvPolynomial.eval₂Hom (Polynomial.C.comp red) ![Polynomial.X, Polynomial.X ^ q]
            (MvPolynomial.X 0))
      rw [hX, redRes_jqModC, MvPolynomial.eval₂Hom_X', Matrix.cons_val_zero, Polynomial.aeval_X]
    ·
      have hX : (⟨modularEval (1 * q) A.toSubring (MvPolynomial.X 1), modularEval_mem_modularRing (1 * q) _⟩ :
            ↥(CharPReduction.modularRing (1 * q) A.toSubring))
          = ⟨jqNModC (AlgebraicClosure ℚ) (1 * q), CharPReduction.jqNModC_mem_modularRing (1 * q) A.toSubring⟩ :=
        Subtype.ext (MvPolynomial.eval₂Hom_X' _ _ 1)
      show CharPReduction.redRes A.toSubring red _ _ ⟨modularEval (1 * q) A.toSubring (MvPolynomial.X 1), _⟩
        = Polynomial.aeval (jqModC k) (MvPolynomial.eval₂Hom (Polynomial.C.comp red) ![Polynomial.X, Polynomial.X ^ q]
            (MvPolynomial.X 1))
      rw [hX, redRes_jqNModC, jqNModC_one_mul_eq_pow, MvPolynomial.eval₂Hom_X', Matrix.cons_val_one, Matrix.cons_val_zero,
        map_pow, Polynomial.aeval_X]
  exact RingHom.congr_fun hφψ P

omit [Fact q.Prime] in

theorem eval_graphReduce (a : k) (P : MvPolynomial (Fin 2) ↥A.toSubring) :
    Polynomial.eval a (MvPolynomial.eval₂Hom (Polynomial.C.comp red) ![Polynomial.X, Polynomial.X ^ q] P)
      = MvPolynomial.eval₂Hom red ![a, a ^ q] P := by
  let φ : MvPolynomial (Fin 2) ↥A.toSubring →+* k :=
    (Polynomial.evalRingHom a).comp (MvPolynomial.eval₂Hom (Polynomial.C.comp red) ![Polynomial.X, Polynomial.X ^ q])
  have hφ : φ = MvPolynomial.eval₂Hom red ![a, a ^ q] := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)
    · show Polynomial.eval a (MvPolynomial.eval₂Hom _ _ (MvPolynomial.C c)) = _
      rw [MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C, RingHom.comp_apply, Polynomial.eval_C]
    · show Polynomial.eval a (MvPolynomial.eval₂Hom _ _ (MvPolynomial.X 0)) = _
      rw [MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X', Matrix.cons_val_zero, Matrix.cons_val_zero, Polynomial.eval_X]
    · show Polynomial.eval a (MvPolynomial.eval₂Hom _ _ (MvPolynomial.X 1)) = _
      rw [MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X', Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_zero, Polynomial.eval_pow, Polynomial.eval_X]
  exact RingHom.congr_fun hφ P

omit [Fact q.Prime] in

theorem eval₂Hom_kroneckerPolynomial (a : k) (R : Polynomial (Polynomial ℤ)) :
    MvPolynomial.eval₂Hom red ![a, a ^ q]
        (Polynomial.eval₂ (Polynomial.eval₂RingHom (MvPolynomial.C.comp (Int.castRingHom ↥A.toSubring)) (MvPolynomial.X 0))
          (MvPolynomial.X 1) R : MvPolynomial (Fin 2) ↥A.toSubring)
      = ((R.map (Polynomial.mapRingHom (Int.castRingHom k))).eval (Polynomial.C (a ^ q))).eval a := by
  set E : MvPolynomial (Fin 2) ↥A.toSubring →+* k := MvPolynomial.eval₂Hom red ![a, a ^ q] with hE
  set g : Polynomial ℤ →+* MvPolynomial (Fin 2) ↥A.toSubring :=
    Polynomial.eval₂RingHom (MvPolynomial.C.comp (Int.castRingHom ↥A.toSubring)) (MvPolynomial.X 0) with hg
  have h1 : E (Polynomial.eval₂ g (MvPolynomial.X 1) R) = R.eval₂ (E.comp g) (E (MvPolynomial.X 1)) :=
    Polynomial.hom_eval₂ R g E (MvPolynomial.X 1)
  have hEg : E.comp g = Polynomial.eval₂RingHom (Int.castRingHom k) a := by
    refine Polynomial.ringHom_ext (fun z => ?_) ?_
    · rw [RingHom.comp_apply, hg, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, RingHom.comp_apply, hE,
        MvPolynomial.eval₂Hom_C, eq_intCast, map_intCast, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, eq_intCast]
    · rw [RingHom.comp_apply, hg, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, hE, MvPolynomial.eval₂Hom_X',
        Matrix.cons_val_zero, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
  have hEX : E (MvPolynomial.X 1) = a ^ q := by
    rw [hE, MvPolynomial.eval₂Hom_X', Matrix.cons_val_one, Matrix.cons_val_zero]
  rw [h1, hEg, hEX]

  have h2 : ((R.map (Polynomial.mapRingHom (Int.castRingHom k))).eval (Polynomial.C (a ^ q))).eval a
      = R.eval₂ ((Polynomial.evalRingHom a).comp (Polynomial.mapRingHom (Int.castRingHom k))) (Polynomial.eval a (Polynomial.C (a ^ q))) := by
    rw [Polynomial.eval_map, ← Polynomial.coe_evalRingHom, Polynomial.hom_eval₂]
  have h3 : (Polynomial.evalRingHom a).comp (Polynomial.mapRingHom (Int.castRingHom k)) = Polynomial.eval₂RingHom (Int.castRingHom k) a := by
    refine Polynomial.ringHom_ext (fun z => ?_) ?_
    · rw [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_C, Polynomial.coe_evalRingHom, Polynomial.eval_C,
        Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
    · rw [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_X, Polynomial.coe_evalRingHom, Polynomial.eval_X,
        Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
  rw [h2, h3, Polynomial.eval_C]

end Red
p2m_reactivate "P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.Ws23 P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.Ws23.NodePlaceAPI"

theorem exists_kroneckerRemainder (q : ℕ) [Fact q.Prime] (data : ModularPolynomialData q) :
    ∃ R : Polynomial (Polynomial ℤ),
      data.Φ = (Polynomial.C Polynomial.X ^ q - Polynomial.X) * (Polynomial.C Polynomial.X - Polynomial.X ^ q)
        + Polynomial.C (Polynomial.C (q : ℤ)) * R := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hKr : KroneckerCongruence q data := kroneckerCongruence q data
  have hdvd : Polynomial.C (Polynomial.C (q : ℤ)) ∣
      data.Φ - (Polynomial.C Polynomial.X ^ q - Polynomial.X) * (Polynomial.C Polynomial.X - Polynomial.X ^ q) := by
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro n
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro m
    have h := congrArg (fun S : Polynomial (Polynomial (ZMod q)) => (S.coeff n).coeff m) hKr
    have hprod : reduceModBivar q ((Polynomial.C Polynomial.X ^ q - Polynomial.X) * (Polynomial.C Polynomial.X - Polynomial.X ^ q))
        = (Polynomial.C Polynomial.X ^ q - Polynomial.X) * (Polynomial.C Polynomial.X - Polynomial.X ^ q) := by
      simp only [map_mul, map_sub, map_pow, reduceModBivar_X, reduceModBivar_C_X]
    rw [← hprod] at h
    simp only [reduceModBivar, Polynomial.coe_mapRingHom, Polynomial.coeff_map, eq_intCast] at h
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Polynomial.coeff_sub, Polynomial.coeff_sub, Int.cast_sub, sub_eq_zero]
    exact h
  obtain ⟨R, hR⟩ := hdvd
  exact ⟨R, by rw [← hR]; ring⟩

section Gauss

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] (red : A →+* k)

theorem gaussUnit_of_mem_modularRing {x : LaurentSeries (AlgebraicClosure ℚ)}
    (hx : x ∈ CharPReduction.modularRing (1 * q) A.toSubring)
    (hred : CharPReduction.redRes A.toSubring red (CharPReduction.modularRing (1 * q) A.toSubring)
        (CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring) ⟨x, hx⟩ ≠ 0) :
    ∃ h : x ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red,
      CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨x, h⟩ ≠ 0 := by
  refine ⟨CharPReduction.subring_le_localizedAtKer A.toSubring red _ _ hx, ?_⟩
  show CharPReduction.redLoc _ ≠ 0
  have h := CharPReduction.redLoc_coe (A := A.toSubring) (red := red) (R := CharPReduction.modularRing (1 * q) A.toSubring)
    (hR := CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring) ⟨x, hx⟩
  intro h0
  apply hred
  rw [← h]
  exact h0

theorem gaussUnit_of_mem_modularRing_div {r s : LaurentSeries (AlgebraicClosure ℚ)}
    (hr : r ∈ CharPReduction.modularRing (1 * q) A.toSubring) (hs : s ∈ CharPReduction.modularRing (1 * q) A.toSubring)
    (hrred : CharPReduction.redRes A.toSubring red (CharPReduction.modularRing (1 * q) A.toSubring)
        (CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring) ⟨r, hr⟩ ≠ 0)
    (hsred : CharPReduction.redRes A.toSubring red (CharPReduction.modularRing (1 * q) A.toSubring)
        (CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring) ⟨s, hs⟩ ≠ 0) :
    ∃ h : r * s⁻¹ ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red,
      CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨r * s⁻¹, h⟩ ≠ 0 := by
  have hs0 : s ≠ 0 := by
    intro h0
    apply hsred
    have : (⟨s, hs⟩ : ↥(CharPReduction.modularRing (1 * q) A.toSubring)) = 0 := Subtype.ext h0
    rw [this, map_zero]
  have hnot : (⟨s, hs⟩ : ↥(CharPReduction.modularRing (1 * q) A.toSubring)) ∉ CharPReduction.redKer A.toSubring red
      (CharPReduction.modularRing (1 * q) A.toSubring) (CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring) :=
    (CharPReduction.notMem_redKer_iff _ _ _ _).mpr hsred
  have hpres : r * s⁻¹ * s = r := by rw [mul_assoc, inv_mul_cancel₀ hs0, mul_one]
  have hmem : r * s⁻¹ ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red := ⟨⟨r, hr⟩, ⟨s, hs⟩, hnot, hpres⟩
  refine ⟨hmem, ?_⟩
  show CharPReduction.redLoc _ ≠ 0
  have hspec := CharPReduction.redLoc_spec (A := A.toSubring) (red := red) (R := CharPReduction.modularRing (1 * q) A.toSubring)
    (hR := CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring) ⟨r * s⁻¹, hmem⟩ (r := ⟨r, hr⟩) (s := ⟨s, hs⟩) hpres
  exact left_ne_zero_of_mul (ne_of_eq_of_ne hspec hrred)

end Gauss
p2m_reactivate "P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.Ws23 P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.Ws23.NodePlaceAPI"

end ModularCurve.NodeLocalized
p2m_reactivate "P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.Ws23 P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.Ws23.NodePlaceAPI"
p2m_reactivate "P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.Ws23 P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.Ws23.NodePlaceAPI"

namespace E4b80310

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.AlgebraicCurve IsLocalRing ModularCurve~coeffEmb_jq P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.ModularCurve ModularCurve.NodeLocalized P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.ModularCurve.NodeLocalized P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.Ws23.NodePlaceAPI"

section WSide

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}

private def _root_.E4b80310.jE (q : ℕ) [Fact q.Prime] : ↥(modularFunctionFieldBar (1 * q)) :=
  ⟨coeffEmb (AlgebraicClosure ℚ) jq,
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
      (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩

p2m_export "E4b80310" "jE"

private def _root_.E4b80310.jqE (q : ℕ) [Fact q.Prime] : ↥(modularFunctionFieldBar (1 * q)) :=
  ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
      (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩

p2m_export "E4b80310" "jqE"
variable (A) in

def evalF (q : ℕ) [Fact q.Prime] : MvPolynomial (Fin 2) ↥A.toSubring →+* ↥(modularFunctionFieldBar (1 * q)) :=
  MvPolynomial.eval₂Hom
    ((algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))).comp A.toSubring.subtype) ![jE q, jqE q]

theorem coe_evalF (P : MvPolynomial (Fin 2) ↥A.toSubring) :
    ((evalF A q P : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ))
      = modularEval (1 * q) A.toSubring P := by
  let φ : MvPolynomial (Fin 2) ↥A.toSubring →+* LaurentSeries (AlgebraicClosure ℚ) :=
    (algebraMap ↥(modularFunctionFieldBar (1 * q)) (LaurentSeries (AlgebraicClosure ℚ))).comp (evalF A q)
  have hφ : φ = modularEval (1 * q) A.toSubring := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)
    · show algebraMap _ _ (evalF A q (MvPolynomial.C c)) = modularEval (1 * q) A.toSubring (MvPolynomial.C c)
      rw [evalF, MvPolynomial.eval₂Hom_C, modularEval, MvPolynomial.eval₂Hom_C, RingHom.comp_apply,
        ← IsScalarTower.algebraMap_apply]
      rfl
    · show algebraMap _ _ (evalF A q (MvPolynomial.X 0)) = modularEval (1 * q) A.toSubring (MvPolynomial.X 0)
      rw [evalF, MvPolynomial.eval₂Hom_X', modularEval, MvPolynomial.eval₂Hom_X', Matrix.cons_val_zero,
        Matrix.cons_val_zero, IntermediateField.algebraMap_apply]
      exact coeffEmb_jq
    · show algebraMap _ _ (evalF A q (MvPolynomial.X 1)) = modularEval (1 * q) A.toSubring (MvPolynomial.X 1)
      rw [evalF, MvPolynomial.eval₂Hom_X', modularEval, MvPolynomial.eval₂Hom_X', Matrix.cons_val_one,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_zero, IntermediateField.algebraMap_apply]
      exact coeffEmb_qExpand_jq (1 * q)
  have := RingHom.congr_fun hφ P
  rw [← this]
  rfl

theorem hasValue_evalF (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    {x y : ↥A.toSubring} (hx : W.HasValue (jE q) (x : AlgebraicClosure ℚ))
    (hy : W.HasValue (jqE q) (y : AlgebraicClosure ℚ)) (P : MvPolynomial (Fin 2) ↥A.toSubring) :
    W.HasValue (evalF A q P) ((MvPolynomial.eval ![x, y] P : ↥A.toSubring) : AlgebraicClosure ℚ) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
      rw [evalF, MvPolynomial.eval₂Hom_C, MvPolynomial.eval_C, RingHom.comp_apply]
      exact W.hasValue_algebraMap _
  | add p r hp hr =>
      rw [map_add, map_add, Subring.coe_add]
      exact hasValue_add hp hr
  | mul_X p i hp =>
      rw [map_mul, map_mul, Subring.coe_mul]
      refine hp.mul ?_
      rw [evalF, MvPolynomial.eval₂Hom_X', MvPolynomial.eval_X]
      revert i
      refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
      · simpa using hx
      · simpa using hy

theorem red_eval {k : Type*} [Field k] (red : A →+* k) (x y : ↥A.toSubring) (P : MvPolynomial (Fin 2) ↥A.toSubring) :
    red (MvPolynomial.eval ![x, y] P) = pointEval A.toSubring red (red x) (red y) P := by
  have h : (red : ↥A.toSubring →+* k).comp (MvPolynomial.eval ![x, y]) = pointEval A.toSubring red (red x) (red y) := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)
    · rw [RingHom.comp_apply, MvPolynomial.eval_C, pointEval, MvPolynomial.eval₂Hom_C]
    · rw [RingHom.comp_apply, MvPolynomial.eval_X, pointEval, MvPolynomial.eval₂Hom_X', Matrix.cons_val_zero,
        Matrix.cons_val_zero]
    · rw [RingHom.comp_apply, MvPolynomial.eval_X, pointEval, MvPolynomial.eval₂Hom_X', Matrix.cons_val_one,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_zero]
  exact RingHom.congr_fun h P

end WSide
p2m_reactivate "P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.Ws23 P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.Ws23.NodePlaceAPI"

end E4b80310
p2m_reactivate "P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.Ws23 P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.Ws23.NodePlaceAPI"

namespace E4b80310

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.AlgebraicCurve IsLocalRing ModularCurve~coeffEmb_jq P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.ModularCurve ModularCurve.NodeLocalized P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.ModularCurve.NodeLocalized"

section NodeSide

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k] [CharP k q]

theorem modularRedLocHom_modularEval (red : A →+* k) (P : MvPolynomial (Fin 2) ↥A.toSubring) :
    CharPReduction.modularRedLocHom (1 * q) A.toSubring red
        ⟨modularEval (1 * q) A.toSubring P, CharPReduction.subring_le_localizedAtKer _ _ _ _
          (modularEval_mem_modularRing (A := A) (1 * q) P)⟩
      = Polynomial.aeval (jqModC k)
          (MvPolynomial.eval₂Hom (Polynomial.C.comp red) ![Polynomial.X, Polynomial.X ^ q] P) := by
  rw [← redRes_modularEval red P]
  exact CharPReduction.redLoc_coe (A := A.toSubring) (red := red) (R := CharPReduction.modularRing (1 * q) A.toSubring)
    (hR := CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring)
    ⟨modularEval (1 * q) A.toSubring P, modularEval_mem_modularRing (A := A) (1 * q) P⟩

theorem coe_aeval_jC1 (p : Polynomial k) :
    ((Polynomial.aeval (Ws23.NodePlaceAPI.jC1 k) p : ↥(modularFunctionFieldC k 1)) : LaurentSeries k) = Polynomial.aeval (jqModC k) p := by
  rw [← Ws23.NodePlaceAPI.coe_jC1 k, ← IntermediateField.algebraMap_apply, ← IntermediateField.algebraMap_apply,
    Polynomial.aeval_algebraMap_apply]

end NodeSide
p2m_reactivate "P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.Ws23 P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.Ws23.NodePlaceAPI"

end E4b80310
p2m_reactivate "P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.Ws23 P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.Ws23.NodePlaceAPI"

namespace Ws23
namespace CentredSigma

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.AlgebraicCurve IsLocalRing ModularCurve~coeffEmb_jq P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.ModularCurve"

section Generic

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (σ : F ≃ₐ[K] F) (v : Place K F)

private theorem _root_.AlgebraicCurve.Place.mem_smul_iff' (g : F) :
    σ g ∈ (σ • v).toValuationSubring ↔ g ∈ v.toValuationSubring := by
  rw [Place.smul_toValuationSubring, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def,
    AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]

p2m_alias "P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.AlgebraicCurve.Place.mem_smul_iff'" "AlgebraicCurve.Place.mem_smul_iff'"

private theorem _root_.AlgebraicCurve.Place.hasValue_smul {g : F} {c : K} (h : v.HasValue g c) :
    (σ • v).HasValue (σ g) c := by
  obtain ⟨hg, hr⟩ := h
  let φ := Place.smulRingEquiv σ v.toValuationSubring
  have hg' : σ g ∈ (σ • v).toValuationSubring := (φ ⟨g, hg⟩).2
  refine ⟨hg', ?_⟩
  have h1 : (⟨σ g, hg'⟩ : (σ • v).toValuationSubring) = φ ⟨g, hg⟩ := rfl
  have h3 : φ (algebraMap K v.toValuationSubring c) = algebraMap K (σ • v).toValuationSubring c := by
    ext
    rw [Place.coe_smulRingEquiv_apply, Place.coe_algebraMap, σ.commutes]
    rfl
  rw [h1, ← Place.residue_algebraMap, ← h3]
  have key : ∀ z : v.toValuationSubring,
      residue _ (φ z) = IsLocalRing.ResidueField.mapEquiv φ (residue _ z) := fun z => by
    rw [IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
    rfl
  show residue _ (φ ⟨g, hg⟩) = residue _ (φ (algebraMap K v.toValuationSubring c))
  rw [key, key, hr, Place.residue_algebraMap]

p2m_alias "P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.AlgebraicCurve.Place.hasValue_smul" "AlgebraicCurve.Place.hasValue_smul"

private theorem _root_.AlgebraicCurve.Place.isRational_smul (hv : v.IsRational) : (σ • v).IsRational := by
  intro z
  obtain ⟨w, hw⟩ := (Place.smulResidueAlgEquiv σ v).surjective z
  obtain ⟨c, hc⟩ := hv w
  refine ⟨c, ?_⟩
  rw [← hw, ← hc]
  exact ((Place.smulResidueAlgEquiv σ v).commutes c).symm

p2m_alias "P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.AlgebraicCurve.Place.isRational_smul" "AlgebraicCurve.Place.isRational_smul"

private theorem _root_.AlgebraicCurve.Place.evalAt_smul (hv : v.IsRational) (g : F) :
    (σ • v).evalAt (σ g) = v.evalAt g := by
  by_cases hg : g ∈ v.toValuationSubring
  · have h1 : v.HasValue g (v.evalAt g) := ⟨hg, (v.algebraMap_evalAt hv hg).symm⟩
    have h2 := Place.hasValue_smul σ v h1
    rw [(σ • v).evalAt_of_mem h2.mem, h2.residue_eq, (σ • v).residueInv_algebraMap]
  · have hg' : σ g ∉ (σ • v).toValuationSubring := fun h => hg ((Place.mem_smul_iff' σ v g).mp h)
    rw [Place.evalAt, Place.evalAt, dif_neg hg, dif_neg hg']

p2m_alias "P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.AlgebraicCurve.Place.evalAt_smul" "AlgebraicCurve.Place.evalAt_smul"
end Generic
p2m_reactivate "P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.Ws23 P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.Ws23.NodePlaceAPI"

section Modular

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k]

noncomputable def jE (q : ℕ) [Fact q.Prime] : ↥(modularFunctionFieldBar (1 * q)) :=
  ⟨coeffEmb (AlgebraicClosure ℚ) jq,
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
      (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩

noncomputable def jqE (q : ℕ) [Fact q.Prime] : ↥(modularFunctionFieldBar (1 * q)) :=
  ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
      (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩

theorem isFrickeAutFull_one_mul (q : ℕ) [Fact q.Prime] :
    IsFrickeAutFull (1 * q) (frickeInvolutionFull (1 * q)) :=
  isFrickeAutFull_frickeInvolutionFull (1 * q) (exists_isFrickeAutFull_of_neZero (1 * q))

theorem frickeInvolutionBar_jE (q : ℕ) [Fact q.Prime] : frickeInvolutionBar (1 * q) (jE q) = jqE q := by
  have h := frickeInvolutionBar_coeffEmb_qExpand (1 * q) (isFrickeAutFull_one_mul q) 1 (1 * q) (one_mul _)
  have hj : jE q = ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ 1 jq), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
          (jqd_mem_full (1 * q) (Dvd.intro (1 * q) (one_mul _)))⟩ :=
    Subtype.ext (congrArg (coeffEmb (AlgebraicClosure ℚ)) (qExpand_one_apply jq).symm)
  rw [hj, h]
  rfl

theorem frickeInvolutionBar_jqE (q : ℕ) [Fact q.Prime] : frickeInvolutionBar (1 * q) (jqE q) = jE q := by
  have h := frickeInvolutionBar_coeffEmb_qExpand (1 * q) (isFrickeAutFull_one_mul q) (1 * q) 1 (mul_one _)
  have hjq : jqE q = ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
          (jqd_mem_full (1 * q) (Dvd.intro 1 (mul_one _)))⟩ := Subtype.ext rfl
  have hj : (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ 1 jq), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
        (jqd_mem_full (1 * q) (Dvd.intro_left (1 * q) (mul_one _)))⟩ : modularFunctionFieldBar (1 * q)) = jE q :=
    Subtype.ext (congrArg (coeffEmb (AlgebraicClosure ℚ)) (qExpand_one_apply jq))
  rw [hjq, h, hj]

theorem frickeInvolutionBar_symm_jE (q : ℕ) [Fact q.Prime] : (frickeInvolutionBar (1 * q)).symm (jE q) = jqE q := by
  rw [AlgEquiv.symm_apply_eq]
  exact (frickeInvolutionBar_jqE q).symm

theorem frickeInvolutionBar_symm_jqE (q : ℕ) [Fact q.Prime] : (frickeInvolutionBar (1 * q)).symm (jqE q) = jE q := by
  rw [AlgEquiv.symm_apply_eq]
  exact (frickeInvolutionBar_jE q).symm

theorem frickeInvolutionBar_smul' (c : AlgebraicClosure ℚ) (x : ↥(modularFunctionFieldBar (1 * q))) :
    frickeInvolutionBar (1 * q) (c • x) = c • frickeInvolutionBar (1 * q) x := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, AlgEquiv.commutes]

variable (red : A →+* k)

def Centred (a : k) (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) : Prop :=
  (∃ x : A, red x = a ∧
      0 < W.ord (jE q - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
  (∃ y : A, red y = a ^ q ∧
      0 < W.ord (jqE q - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ)))

theorem centred_smul {a : k} (ha2 : a ^ (q ^ 2) = a) {W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))}
    (hW : Centred red a W) : Centred red (a ^ q) (frickeInvolutionBar (1 * q) • W) := by
  obtain ⟨⟨x, hxa, hx⟩, ⟨y, hya, hy⟩⟩ := hW
  refine ⟨⟨y, hya, ?_⟩, ⟨x, ?_, ?_⟩⟩
  · rw [← frickeInvolutionBar_jqE q, ← (frickeInvolutionBar (1 * q)).commutes (y : AlgebraicClosure ℚ), ← map_sub,
      Place.ord_smul]
    exact hy
  · rw [hxa, ← pow_mul, ← pow_two, ha2]
  · rw [← frickeInvolutionBar_jE q, ← (frickeInvolutionBar (1 * q)).commutes (x : AlgebraicClosure ℚ), ← map_sub,
      Place.ord_smul]
    exact hx

theorem centred_of_centred_smul {a : k} (ha2 : a ^ (q ^ 2) = a)
    {W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))}
    (hW : Centred red (a ^ q) (frickeInvolutionBar (1 * q) • W)) : Centred red a W := by
  obtain ⟨⟨x, hxa, hx⟩, ⟨y, hya, hy⟩⟩ := hW
  refine ⟨⟨y, ?_, ?_⟩, ⟨x, hxa, ?_⟩⟩
  · rw [hya, ← pow_mul, ← pow_two, ha2]
  · rw [← Place.ord_smul (frickeInvolutionBar (1 * q)) W, map_sub, frickeInvolutionBar_jE, AlgEquiv.commutes]
    exact hy
  · rw [← Place.ord_smul (frickeInvolutionBar (1 * q)) W, map_sub, frickeInvolutionBar_jqE, AlgEquiv.commutes]
    exact hx

theorem centred_smul_iff {a : k} (ha2 : a ^ (q ^ 2) = a) (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) :
    Centred red (a ^ q) (frickeInvolutionBar (1 * q) • W) ↔ Centred red a W :=
  ⟨centred_of_centred_smul red ha2, centred_smul red ha2⟩

theorem forall_centred_ord_smul_eq_zero {a : k} (ha2 : a ^ (q ^ 2) = a) {f : ↥(modularFunctionFieldBar (1 * q))}
    (hford : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), Centred red a W → W.ord f = 0)
    (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (hW : Centred red (a ^ q) W) :
    W.ord (frickeInvolutionBar (1 * q) f) = 0 := by
  have hW' : Centred red (a ^ q) (frickeInvolutionBar (1 * q) • ((frickeInvolutionBar (1 * q))⁻¹ • W)) := by
    rwa [smul_inv_smul]
  have h := hford _ (centred_of_centred_smul red ha2 hW')
  rwa [← Place.ord_smul (frickeInvolutionBar (1 * q)), smul_inv_smul] at h

end Modular
p2m_reactivate "P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.Ws23 P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.Ws23.NodePlaceAPI"

end Ws23.CentredSigma
p2m_reactivate "P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.Ws23 P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.Ws23.NodePlaceAPI"
p2m_reactivate "P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.Ws23 P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.Ws23.NodePlaceAPI"

namespace Ws23
namespace SlopeLaw0

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.AlgebraicCurve IsLocalRing ModularCurve~coeffEmb_jq P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.ModularCurve ModularCurve.NodeLocalized P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.ModularCurve.NodeLocalized P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.Ws23.NodePlaceAPI P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.Ws23.CentredSigma"

section Small

set_option synthInstance.maxHeartbeats 1600000

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k]

theorem not_isUnit_natCast_zpow [CharP k q] (red : A →+* k)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A) {n : ℤ} (hn : n ≠ 0)
    (h : ((q : AlgebraicClosure ℚ)) ^ n ∈ A) : ¬ IsUnit (⟨_, h⟩ : A) := by
  have hqmem : ((q : ℕ) : A) ∈ IsLocalRing.maximalIdeal A :=
    (hker _).mp (by rw [map_natCast]; exact CharP.cast_eq_zero k q)
  have hqnu : ¬ IsUnit ((q : ℕ) : A) := by
    rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hqmem
  have hq0 : ((q : AlgebraicClosure ℚ)) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  have hcoe : ∀ m : ℕ, ((((q : ℕ) : A) ^ m : A) : AlgebraicClosure ℚ) = ((q : AlgebraicClosure ℚ)) ^ (m : ℤ) := by
    intro m
    rw [zpow_natCast]
    push_cast
    rfl
  intro hu
  apply hqnu
  rcases lt_or_gt_of_ne hn with hlt | hgt
  ·
    obtain ⟨m, hm⟩ : ∃ m : ℕ, n = -((m : ℤ) + 1) := ⟨(-n - 1).toNat, by omega⟩
    subst hm
    have hprod : ((q : ℕ) : A) ^ (m + 1) * (⟨_, h⟩ : A) = 1 := by
      apply Subtype.ext
      show ((((q : ℕ) : A) ^ (m + 1) : A) : AlgebraicClosure ℚ) * ((q : AlgebraicClosure ℚ)) ^ (-((m : ℤ) + 1))
        = (1 : AlgebraicClosure ℚ)
      rw [hcoe, zpow_neg, ← Nat.cast_succ, mul_inv_cancel₀ (zpow_ne_zero _ hq0)]
    have hu2 : IsUnit (((q : ℕ) : A) ^ (m + 1)) := ⟨⟨_, _, hprod, by rwa [mul_comm] at hprod⟩, rfl⟩
    exact (isUnit_pow_iff (Nat.succ_ne_zero m)).mp hu2
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, n = (m : ℤ) + 1 := ⟨(n - 1).toNat, by omega⟩
    subst hm
    have heq : (⟨_, h⟩ : A) = ((q : ℕ) : A) ^ (m + 1) := by
      apply Subtype.ext
      show ((q : AlgebraicClosure ℚ)) ^ ((m : ℤ) + 1) = (((q : ℕ) : A) ^ (m + 1) : A)
      rw [hcoe, Nat.cast_succ]
    rw [heq] at hu
    exact (isUnit_pow_iff (Nat.succ_ne_zero m)).mp hu

omit [Fact q.Prime] in

theorem pow_pow_sq_eq {a : k} (ha2 : a ^ (q ^ 2) = a) : (a ^ q) ^ (q ^ 2) = a ^ q := by
  rw [← pow_mul, mul_comm, pow_mul, ha2]

theorem pow_ne_1728 [CharP k q] {a : k} (ha2 : a ^ (q ^ 2) = a) (h1728 : a ≠ 1728) : a ^ q ≠ 1728 := by
  intro h
  apply h1728
  have h2 : (a ^ q) ^ q = (1728 : k) ^ q := by rw [h]
  rw [← pow_mul, ← pow_two, ha2] at h2
  rw [h2]
  have h3 : frobenius k q ((1728 : ℕ) : k) = ((1728 : ℕ) : k) := map_natCast (frobenius k q) 1728
  rw [frobenius_def] at h3
  exact_mod_cast h3

theorem ord_algebraMap_mul {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {c : K} (hc : c ≠ 0)
    {g : F} (hg : g ≠ 0) : v.ord (algebraMap K F c * g) = v.ord g := by
  rw [v.ord_mul ((map_ne_zero _).mpr hc) hg, (v.hasValue_algebraMap c).ord_eq_zero hc, zero_add]

theorem coe_algebraMap_eq_constSeries (c : A) :
    ((algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (c : AlgebraicClosure ℚ) :
        ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ))
      = CharPReduction.constSeries A.toSubring ⟨(c : AlgebraicClosure ℚ), c.2⟩ := rfl

theorem algebraMap_mem_modularLocalized (red : A →+* k) (c : A) :
    ((algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (c : AlgebraicClosure ℚ) :
        ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈
      CharPReduction.modularLocalized (1 * q) A.toSubring red := by
  rw [coe_algebraMap_eq_constSeries]
  exact CharPReduction.subring_le_localizedAtKer _ _ _ _
    (CharPReduction.constSeries_mem_modularRing (1 * q) A.toSubring ⟨(c : AlgebraicClosure ℚ), c.2⟩)

theorem modularRedLocHom_algebraMap [CharP k q] (red : A →+* k) (c : A)
    (h : ((algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (c : AlgebraicClosure ℚ) :
        ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈
      CharPReduction.modularLocalized (1 * q) A.toSubring red) :
    CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h⟩ = algebraMap k (LaurentSeries k) (red c) := by
  have hm : modularEval (1 * q) A.toSubring (MvPolynomial.C ⟨(c : AlgebraicClosure ℚ), c.2⟩)
      = ((algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (c : AlgebraicClosure ℚ) :
        ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) := by
    rw [modularEval, MvPolynomial.eval₂Hom_C, coe_algebraMap_eq_constSeries]
  have key := E4b80310.modularRedLocHom_modularEval (q := q) (A := A) red (MvPolynomial.C ⟨(c : AlgebraicClosure ℚ), c.2⟩)
  rw [MvPolynomial.eval₂Hom_C, RingHom.comp_apply, Polynomial.aeval_C] at key
  have hsub : (⟨modularEval (1 * q) A.toSubring (MvPolynomial.C ⟨(c : AlgebraicClosure ℚ), c.2⟩),
        CharPReduction.subring_le_localizedAtKer _ _ _ _
          (ModularCurve.NodeLocalized.modularEval_mem_modularRing (A := A) (1 * q) _)⟩ : ↥(CharPReduction.modularLocalized (1 * q) A.toSubring red))
      = ⟨_, h⟩ := Subtype.ext hm
  rw [hsub] at key
  exact key

theorem coe_smul_eq (c : A) (g : ↥(modularFunctionFieldBar (1 * q))) :
    (((c : AlgebraicClosure ℚ) • g : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ))
      = ((algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (c : AlgebraicClosure ℚ) :
          ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) * (g : LaurentSeries (AlgebraicClosure ℚ)) := by
  rw [Algebra.smul_def]
  rfl

theorem smul_mem_modularLocalized (red : A →+* k) (c : A) {g : ↥(modularFunctionFieldBar (1 * q))}
    (hg : (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red) :
    (((c : AlgebraicClosure ℚ) • g : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈
      CharPReduction.modularLocalized (1 * q) A.toSubring red := by
  rw [coe_smul_eq]
  exact mul_mem (algebraMap_mem_modularLocalized red c) hg

theorem modularRedLocHom_smul [CharP k q] (red : A →+* k) (c : A) {g : ↥(modularFunctionFieldBar (1 * q))}
    (hg : (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red)
    (hcg : (((c : AlgebraicClosure ℚ) • g : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈
      CharPReduction.modularLocalized (1 * q) A.toSubring red) :
    CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, hcg⟩
      = algebraMap k (LaurentSeries k) (red c) * CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, hg⟩ := by
  have hprod : (⟨_, hcg⟩ : ↥(CharPReduction.modularLocalized (1 * q) A.toSubring red))
      = ⟨_, algebraMap_mem_modularLocalized red c⟩ * ⟨_, hg⟩ := Subtype.ext (coe_smul_eq c g)
  rw [hprod, map_mul, modularRedLocHom_algebraMap]

theorem nodeCoord_mem_and_evalAt_ne_zero [CharP k q] [IsAlgClosed k] [DecidableEq k] (red : A →+* k)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (hq : 5 ≤ q) (a : k) (ha : a ∈ ssJSet q k) (ha2 : a ^ (q ^ 2) = a) (h0 : a ≠ 0) (h1728 : a ≠ 1728)
    (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (hW : Centred red a W) :
    (jqE q - jE q ^ q) ∈ W.toValuationSubring ∧ W.evalAt (jqE q - jE q ^ q) ≠ 0 := by
  obtain ⟨c, -, ⟨d, -, hcd⟩, hV⟩ :=
    ModularCurve.NodeLocalized.exists_hasValue_nodeCoord_of_centred red hker hq a ha ha2 h0 h1728 W hW
  have hV' : W.HasValue (jqE q - jE q ^ q) (c : AlgebraicClosure ℚ) := hV
  refine ⟨hV'.mem, ?_⟩
  rw [evalAt_eq_of_hasValue' hV']
  intro hc0
  have hq0 : ((q : ℕ) : A) ≠ 0 := by
    intro h
    have : ((q : ℕ) : AlgebraicClosure ℚ) = 0 := by exact_mod_cast congrArg Subtype.val h
    exact (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero) this
  apply hq0
  rw [← hcd, show c = 0 from Subtype.ext hc0, zero_mul]

theorem modularFunctionFieldC_one_mul (K : Type*) [Field K] (q : ℕ) [Fact q.Prime] [CharP K q] :
    modularFunctionFieldC K (1 * q) = modularFunctionFieldC K 1 := by
  rw [modularFunctionFieldC_one, modularFunctionFieldC, ModularCurve.NodeLocalized.jqNModC_one_mul_eq_pow]
  refine le_antisymm ?_ (IntermediateField.adjoin.mono K _ _ (Set.singleton_subset_iff.mpr (Set.mem_insert _ _)))
  refine IntermediateField.adjoin_le_iff.mpr ?_
  rintro x (rfl | rfl)
  · exact IntermediateField.subset_adjoin K _ (Set.mem_singleton _)
  · exact pow_mem (IntermediateField.subset_adjoin K _ (Set.mem_singleton (jqModC K))) q

theorem modularRedLocHom_mem_one [CharP k q] (red : A →+* k)
    (g : ↥(CharPReduction.modularLocalized (1 * q) A.toSubring red)) :
    CharPReduction.modularRedLocHom (1 * q) A.toSubring red g ∈ modularFunctionFieldC k 1 := by
  rw [← modularFunctionFieldC_one_mul k q]
  exact CharPReduction.modularRedLocHom_mem A.toSubring red (1 * q) g

end Small
p2m_reactivate "P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.Ws23 P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.Ws23.NodePlaceAPI"

end Ws23.SlopeLaw0
p2m_reactivate "P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.Ws23 P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.Ws23.NodePlaceAPI"
p2m_reactivate "P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.Ws23 P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.Ws23.NodePlaceAPI"

namespace Ws23
namespace Jump

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.AlgebraicCurve IsLocalRing ModularCurve~coeffEmb_jq P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.ModularCurve ModularCurve.NodeLocalized P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.ModularCurve.NodeLocalized P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.Ws23.NodePlaceAPI P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.Ws23.CentredSigma"

section PlaceGeneric

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem ord_one' : v.ord (1 : F) = 0 := (v.hasValue_one).ord_eq_zero one_ne_zero

theorem ord_pow' {f : F} (hf : f ≠ 0) (n : ℕ) : v.ord (f ^ n) = n * v.ord f := by
  induction n with
  | zero => rw [pow_zero, ord_one', Nat.cast_zero, zero_mul]
  | succ n ih => rw [pow_succ, v.ord_mul (pow_ne_zero _ hf) hf, ih]; push_cast; ring

theorem ord_inv' {f : F} (hf : f ≠ 0) : v.ord f⁻¹ = - v.ord f := by
  have h := v.ord_mul hf (inv_ne_zero hf)
  rw [mul_inv_cancel₀ hf, ord_one'] at h
  omega

theorem ord_zpow' {f : F} (hf : f ≠ 0) (n : ℤ) : v.ord (f ^ n) = n * v.ord f := by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · rw [zpow_natCast, ord_pow' v hf]
  · rw [zpow_neg, zpow_natCast, ord_inv' v (pow_ne_zero _ hf), ord_pow' v hf]; ring

theorem ord_nonneg_of_mem' {g : F} (hm : g ∈ v.toValuationSubring) : 0 ≤ v.ord g := by
  by_cases hg : g = 0
  · rw [hg, Place.ord_zero]
  · exact GaussReduction.ord_nonneg_of_mem_gen v hm hg

theorem hasValue_ne_zero_of_inv {y : F} (hy : y ≠ 0) {c c' : K} (h : v.HasValue y c) (h' : v.HasValue y⁻¹ c') :
    c ≠ 0 := by
  have hprod := h.mul h'
  rw [mul_inv_cancel₀ hy] at hprod
  have h1 : c * c' = 1 := hprod.unique v.hasValue_one
  exact left_ne_zero_of_mul_eq_one h1

theorem coe_zpow' {L : Type*} [Field L] [Algebra K L] (S : IntermediateField K L) (x : ↥S) (m : ℤ) :
    ((x ^ m : ↥S) : L) = (x : L) ^ m := by
  cases m with
  | ofNat n => rw [Int.ofNat_eq_natCast, zpow_natCast, zpow_natCast, SubmonoidClass.coe_pow]
  | negSucc n => rw [zpow_negSucc, zpow_negSucc, IntermediateField.coe_inv, SubmonoidClass.coe_pow]

theorem zpow_mem_of_mem_of_inv_mem {f : F} (hf : f ∈ v.toValuationSubring) (hfi : f⁻¹ ∈ v.toValuationSubring) (m : ℤ) :
    f ^ m ∈ v.toValuationSubring := by
  cases m with
  | ofNat n => rw [Int.ofNat_eq_natCast, zpow_natCast]; exact pow_mem hf n
  | negSucc n => rw [zpow_negSucc, ← inv_pow]; exact pow_mem hfi _

theorem isRational_W {q : ℕ} [Fact q.Prime] (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) : W.IsRational := by
  intro z
  have h : W.deg = 1 := deg_eq_one_modularFunctionFieldBar (1 * q) W
  unfold Place.deg at h
  have hbt : (⊥ : Subalgebra (AlgebraicClosure ℚ) W.ResidueField) = ⊤ := Subalgebra.bot_eq_top_of_finrank_eq_one h
  have hz : z ∈ (⊥ : Subalgebra (AlgebraicClosure ℚ) W.ResidueField) := by rw [hbt]; exact Algebra.mem_top
  exact Algebra.mem_bot.mp hz

end PlaceGeneric
p2m_reactivate "P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.Ws23 P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.Ws23.NodePlaceAPI"

section RL

set_option synthInstance.maxHeartbeats 1600000

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k] [CharP k q]
  (red : A →+* k)

noncomputable def rlHom : ↥(CharPReduction.modularLocalized (1 * q) A.toSubring red) →+* ↥(modularFunctionFieldC k 1) :=
  (CharPReduction.modularRedLocHom (1 * q) A.toSubring red).codRestrict (modularFunctionFieldC k 1)
    (fun x => Ws23.SlopeLaw0.modularRedLocHom_mem_one red x)

theorem coe_rlHom (x : ↥(CharPReduction.modularLocalized (1 * q) A.toSubring red)) :
    ((rlHom red x : ↥(modularFunctionFieldC k 1)) : LaurentSeries k) = CharPReduction.modularRedLocHom (1 * q) A.toSubring red x :=
  rfl

theorem rlHom_eq (x : LaurentSeries (AlgebraicClosure ℚ)) (hx : x ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red)
    (hF : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨x, hx⟩ ∈ modularFunctionFieldC k 1) :
    (⟨_, hF⟩ : ↥(modularFunctionFieldC k 1)) = rlHom red ⟨x, hx⟩ := Subtype.ext rfl

theorem rlHom_ne_zero_iff (x : ↥(CharPReduction.modularLocalized (1 * q) A.toSubring red)) :
    rlHom red x ≠ 0 ↔ CharPReduction.modularRedLocHom (1 * q) A.toSubring red x ≠ 0 := by
  rw [not_iff_not]
  constructor
  · intro h; have := congrArg Subtype.val h; exact this
  · intro h; exact Subtype.ext h

theorem rlHom_zpow {x : LaurentSeries (AlgebraicClosure ℚ)}
    (hx : ∃ h : x ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red, CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨x, h⟩ ≠ 0)
    (m : ℤ) (hm : x ^ m ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red) :
    rlHom red ⟨x ^ m, hm⟩ = (rlHom red ⟨x, hx.1⟩) ^ m := by
  obtain ⟨hxm, hx0⟩ := hx
  have hne : rlHom red ⟨x, hxm⟩ ≠ 0 := (rlHom_ne_zero_iff red _).mpr hx0
  have hxne : x ≠ 0 := by
    intro h0; apply hx0
    have : (⟨x, hxm⟩ : ↥(CharPReduction.modularLocalized (1 * q) A.toSubring red)) = 0 := Subtype.ext h0
    rw [this, map_zero]

  suffices key : ∀ (y : LaurentSeries (AlgebraicClosure ℚ)) (hy : y ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red),
      y = x ^ m → rlHom red ⟨y, hy⟩ = (rlHom red ⟨x, hxm⟩) ^ m from key _ hm rfl
  intro y hy hyx
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg m
  · have : (⟨y, hy⟩ : ↥(CharPReduction.modularLocalized (1 * q) A.toSubring red)) = ⟨x, hxm⟩ ^ n :=
      Subtype.ext (show y = (((⟨x, hxm⟩ ^ n : ↥(CharPReduction.modularLocalized (1 * q) A.toSubring red))) : LaurentSeries (AlgebraicClosure ℚ)) by
        rw [SubmonoidClass.coe_pow, hyx]; exact zpow_natCast x n)
    rw [this, map_pow, zpow_natCast]
  · have hprod : (⟨y, hy⟩ : ↥(CharPReduction.modularLocalized (1 * q) A.toSubring red)) * ⟨x, hxm⟩ ^ n = 1 := by
      apply Subtype.ext
      show y * x ^ n = 1
      rw [hyx, zpow_neg, zpow_natCast, inv_mul_cancel₀ (pow_ne_zero _ hxne)]
    have h2 := congrArg (rlHom red) hprod
    rw [map_mul, map_pow, map_one] at h2
    rw [zpow_neg, zpow_natCast]
    exact eq_inv_of_mul_eq_one_left h2

theorem rlHom_inv {x : LaurentSeries (AlgebraicClosure ℚ)}
    (hx : ∃ h : x ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red, CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨x, h⟩ ≠ 0)
    (hm : x⁻¹ ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red) :
    rlHom red ⟨x⁻¹, hm⟩ = (rlHom red ⟨x, hx.1⟩)⁻¹ := by
  obtain ⟨hxm, hx0⟩ := hx
  have hxne : x ≠ 0 := by
    intro h0; apply hx0
    have : (⟨x, hxm⟩ : ↥(CharPReduction.modularLocalized (1 * q) A.toSubring red)) = 0 := Subtype.ext h0
    rw [this, map_zero]
  have hprod : (⟨x⁻¹, hm⟩ : ↥(CharPReduction.modularLocalized (1 * q) A.toSubring red)) * ⟨x, hxm⟩ = 1 :=
    Subtype.ext (show x⁻¹ * x = 1 from inv_mul_cancel₀ hxne)
  have h2 := congrArg (rlHom red) hprod
  rw [map_mul, map_one] at h2
  exact eq_inv_of_mul_eq_one_left h2

theorem ord_rlHom_smul (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (v : Place k ↥(modularFunctionFieldC k 1)) (c : A) (hc : IsUnit c)
    {g : ↥(modularFunctionFieldBar (1 * q))}
    (hg : (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red)
    (hg0 : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, hg⟩ ≠ 0)
    (hcg : (((c : AlgebraicClosure ℚ) • g : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈
      CharPReduction.modularLocalized (1 * q) A.toSubring red) :
    v.ord (rlHom red ⟨_, hcg⟩) = v.ord (rlHom red ⟨_, hg⟩) := by
  have hredc : red c ≠ 0 := by
    intro h
    have := (hker _).mp h
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at this
    exact this hc
  have heq : rlHom red ⟨_, hcg⟩ = algebraMap k (modularFunctionFieldC k 1) (red c) * rlHom red ⟨_, hg⟩ := by
    apply Subtype.ext
    rw [MulMemClass.coe_mul, coe_rlHom, coe_rlHom]
    exact Ws23.SlopeLaw0.modularRedLocHom_smul red c hg hcg
  have hne : rlHom red ⟨_, hg⟩ ≠ 0 := (rlHom_ne_zero_iff red _).mpr hg0
  rw [heq, Ws23.SlopeLaw0.ord_algebraMap_mul v hredc hne]

end RL
p2m_reactivate "P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.Ws23 P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.Ws23.NodePlaceAPI"

section Calibrator

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k] [CharP k q]
  [IsAlgClosed k] [DecidableEq k] (red : A →+* k)

theorem rootMultiplicity_X_sub_X_pow_sq_eq_one {b : k} (hb : b ^ (q ^ 2) = b) :
    (Polynomial.X - Polynomial.X ^ (q ^ 2) : Polynomial k).rootMultiplicity b = 1 := by
  have hq1 : 1 < q ^ 2 := Nat.one_lt_pow two_ne_zero (Fact.out : q.Prime).one_lt
  have hne : (Polynomial.X - Polynomial.X ^ (q ^ 2) : Polynomial k) ≠ 0 := by
    intro h
    have := congrArg Polynomial.natDegree (sub_eq_zero.mp h)
    rw [Polynomial.natDegree_X, Polynomial.natDegree_X_pow] at this
    omega
  have hroot : (Polynomial.X - Polynomial.X ^ (q ^ 2) : Polynomial k).IsRoot b := by
    rw [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_pow, Polynomial.eval_X, hb, sub_self]
  have hderiv : Polynomial.derivative (Polynomial.X - Polynomial.X ^ (q ^ 2) : Polynomial k) = 1 := by
    rw [Polynomial.derivative_sub, Polynomial.derivative_X, Polynomial.derivative_X_pow]
    have : ((q ^ 2 : ℕ) : Polynomial k) = 0 := by
      rw [pow_two, Nat.cast_mul]
      have hq : ((q : ℕ) : Polynomial k) = 0 := by
        rw [← Polynomial.C_eq_natCast, CharP.cast_eq_zero k q, map_zero]
      rw [hq, zero_mul]
    rw [Polynomial.C_eq_natCast, this, zero_mul, sub_zero]
  have hnot : ¬ (Polynomial.derivative (Polynomial.X - Polynomial.X ^ (q ^ 2) : Polynomial k)).IsRoot b := by
    rw [hderiv, Polynomial.IsRoot, Polynomial.eval_one]; exact one_ne_zero
  have hle := (Polynomial.one_lt_rootMultiplicity_iff_isRoot (p := (Polynomial.X - Polynomial.X ^ (q ^ 2) : Polynomial k)) hne).not.mpr
    (fun h => hnot h.2)
  have hge : 1 ≤ (Polynomial.X - Polynomial.X ^ (q ^ 2) : Polynomial k).rootMultiplicity b :=
    (Polynomial.rootMultiplicity_pos hne).mpr hroot
  omega

theorem exists_gaussUnit_calibrator_ord_eq_one (hq : 5 ≤ q) (a : k) (ha : a ∈ ssJSet q k) (ha2 : a ^ (q ^ 2) = a)
    (h0 : a ≠ 0) (h1728 : a ≠ 1728) :
    ∃ (hz : ((algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (q : AlgebraicClosure ℚ) * (jqE q - jE q ^ q)⁻¹ :
        ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red),
      CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, hz⟩ ≠ 0 ∧
      (charLGeomPlaceOfPoint k a).ord (rlHom red ⟨_, hz⟩) = 1 := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩

  obtain ⟨J, hJ⟩ : ∃ J : ↥(modularFunctionFieldBar (1 * q)), J = ⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ := ⟨_, rfl⟩
  obtain ⟨JQ, hJQ⟩ : ∃ JQ : ↥(modularFunctionFieldBar (1 * q)), JQ = ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ := ⟨_, rfl⟩
  have hJser : (J : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) := by rw [hJ]; exact coeffEmb_jq
  have hJQser : (JQ : LaurentSeries (AlgebraicClosure ℚ)) = jqNModC (AlgebraicClosure ℚ) (1 * q) := by
    rw [hJQ]; exact coeffEmb_qExpand_jq (1 * q)

  have hGser : ((JQ - J ^ q : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ))
      = modularEval (1 * q) A.toSubring (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q) := by
    rw [AddSubgroupClass.coe_sub, SubmonoidClass.coe_pow, hJser, hJQser]
    simp only [modularEval, map_sub, map_pow, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X, Matrix.cons_val_one,
      Matrix.cons_val_zero]
  have hHser : ((J - JQ ^ q : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ))
      = modularEval (1 * q) A.toSubring (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q) := by
    rw [AddSubgroupClass.coe_sub, SubmonoidClass.coe_pow, hJser, hJQser]
    simp only [modularEval, map_sub, map_pow, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X, Matrix.cons_val_one,
      Matrix.cons_val_zero]

  have hHred : CharPReduction.redRes A.toSubring red (CharPReduction.modularRing (1 * q) A.toSubring)
      (CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring)
      ⟨modularEval (1 * q) A.toSubring (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q), modularEval_mem_modularRing (1 * q) _⟩ ≠ 0 := by
    rw [redRes_modularEval]
    intro hzero
    have hQ : (MvPolynomial.eval₂Hom (Polynomial.C.comp red) ![Polynomial.X, Polynomial.X ^ q]
        (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q : MvPolynomial (Fin 2) ↥A.toSubring)) ≠ 0 := by
      rw [map_sub, map_pow, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_zero]
      intro h
      have hdeg := congrArg Polynomial.natDegree (sub_eq_zero.mp h)
      rw [Polynomial.natDegree_X, ← pow_mul, Polynomial.natDegree_X_pow] at hdeg
      have h25 : 25 ≤ q * q := Nat.mul_le_mul hq hq
      rw [← hdeg] at h25
      exact absurd h25 (by norm_num)
    exact transcendental_jqModC k ⟨_, hQ, hzero⟩

  obtain ⟨data⟩ := nonempty_modularPolynomialData q
  obtain ⟨R, hR⟩ := exists_kroneckerRemainder q data
  have hRne := eval_kroneckerRemainder_ne_zero_of_mem_ssJSet hq data R hR a ha h0 h1728
  have hEval := modularEval_kroneckerRemainder A data R hR
  rw [← hJ, ← hJQ] at hEval

  obtain ⟨Rser, hRser⟩ : ∃ Rser : LaurentSeries (AlgebraicClosure ℚ), Rser = modularEval (1 * q) A.toSubring
      (Polynomial.eval₂ (Polynomial.eval₂RingHom (MvPolynomial.C.comp (Int.castRingHom ↥A.toSubring)) (MvPolynomial.X 0))
        (MvPolynomial.X 1) R : MvPolynomial (Fin 2) ↥A.toSubring) := ⟨_, rfl⟩
  rw [← hRser] at hEval
  have hRmem : Rser ∈ CharPReduction.modularRing (1 * q) A.toSubring := by rw [hRser]; exact modularEval_mem_modularRing (1 * q) _
  have hRred' : CharPReduction.redRes A.toSubring red (CharPReduction.modularRing (1 * q) A.toSubring)
      (CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring) ⟨Rser, hRmem⟩ ≠ 0 := by
    have hx : (⟨Rser, hRmem⟩ : ↥(CharPReduction.modularRing (1 * q) A.toSubring)) = ⟨modularEval (1 * q) A.toSubring
        (Polynomial.eval₂ (Polynomial.eval₂RingHom (MvPolynomial.C.comp (Int.castRingHom ↥A.toSubring)) (MvPolynomial.X 0))
          (MvPolynomial.X 1) R : MvPolynomial (Fin 2) ↥A.toSubring), modularEval_mem_modularRing (1 * q) _⟩ := Subtype.ext hRser
    rw [hx, redRes_modularEval]
    intro hzero
    have hQ : (MvPolynomial.eval₂Hom (Polynomial.C.comp red) ![Polynomial.X, Polynomial.X ^ q]
        (Polynomial.eval₂ (Polynomial.eval₂RingHom (MvPolynomial.C.comp (Int.castRingHom ↥A.toSubring)) (MvPolynomial.X 0))
          (MvPolynomial.X 1) R : MvPolynomial (Fin 2) ↥A.toSubring)) ≠ 0 := by
      intro h
      apply hRne
      rw [← eval₂Hom_kroneckerPolynomial red a R, ← eval_graphReduce red a, h, Polynomial.eval_zero]
    exact transcendental_jqModC k ⟨_, hQ, hzero⟩
  have hHmem : ((J - JQ ^ q : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ))
      ∈ CharPReduction.modularRing (1 * q) A.toSubring := by rw [hHser]; exact modularEval_mem_modularRing (1 * q) _
  have hHred' : CharPReduction.redRes A.toSubring red (CharPReduction.modularRing (1 * q) A.toSubring)
      (CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring) ⟨_, hHmem⟩ ≠ 0 := by
    have hx : (⟨_, hHmem⟩ : ↥(CharPReduction.modularRing (1 * q) A.toSubring))
        = ⟨modularEval (1 * q) A.toSubring (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q), modularEval_mem_modularRing (1 * q) _⟩ :=
      Subtype.ext hHser
    rw [hx]; exact hHred
  have hH0 : (J - JQ ^ q : ↥(modularFunctionFieldBar (1 * q))) ≠ 0 := by
    intro h
    apply hHred'
    have hx : (⟨_, hHmem⟩ : ↥(CharPReduction.modularRing (1 * q) A.toSubring)) = 0 :=
      Subtype.ext (by
        show ((J - JQ ^ q : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ))
          = ((0 : ↥(CharPReduction.modularRing (1 * q) A.toSubring)) : LaurentSeries (AlgebraicClosure ℚ))
        rw [h]; rfl)
    rw [hx, map_zero]
  have hq0 : ((q : ℕ) : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero

  have hjE : jE q = J := by rw [hJ]; rfl
  have hjqE : jqE q = JQ := by rw [hJQ]; rfl
  have hident : algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (q : AlgebraicClosure ℚ) * (JQ - J ^ q)⁻¹
      = (J - JQ ^ q) * ((algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (q : AlgebraicClosure ℚ))⁻¹
          * ((JQ - J ^ q) * (J - JQ ^ q)))⁻¹ := by
    have h : (J - JQ ^ q) * ((algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (q : AlgebraicClosure ℚ))⁻¹
          * ((JQ - J ^ q) * (J - JQ ^ q)))⁻¹
        = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (q : AlgebraicClosure ℚ) * (JQ - J ^ q)⁻¹
          * ((J - JQ ^ q) * (J - JQ ^ q)⁻¹) := by
      rw [mul_inv, inv_inv, mul_inv]; ring
    rw [h, mul_inv_cancel₀ hH0, mul_one]
  have hcoe : (((J - JQ ^ q) * ((algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (q : AlgebraicClosure ℚ))⁻¹
          * ((JQ - J ^ q) * (J - JQ ^ q)))⁻¹ : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ))
      = ((J - JQ ^ q : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) * Rser⁻¹ := by
    rw [MulMemClass.coe_mul, IntermediateField.coe_inv, MulMemClass.coe_mul, IntermediateField.coe_inv, MulMemClass.coe_mul,
      hEval, AddSubgroupClass.coe_sub, AddSubgroupClass.coe_sub, SubmonoidClass.coe_pow, SubmonoidClass.coe_pow, map_natCast,
      map_natCast, show (((q : ℕ) : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ))
        = (modularFunctionFieldBar (1 * q)).val (q : ↥(modularFunctionFieldBar (1 * q))) from rfl, map_natCast]
  have hzser : ((algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (q : AlgebraicClosure ℚ) * (jqE q - jE q ^ q)⁻¹ :
        ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ))
      = ((J - JQ ^ q : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) * Rser⁻¹ := by
    rw [hjE, hjqE, hident, hcoe]
  obtain ⟨hz, hz0⟩ := CharPReduction.gaussUnit_congr (1 * q) A.toSubring red hzser.symm
    (gaussUnit_of_mem_modularRing_div red hHmem hRmem hHred' hRred')
  refine ⟨hz, hz0, ?_⟩

  have hRser0 : Rser ≠ 0 := by
    intro h0; apply hRred'
    have : (⟨Rser, hRmem⟩ : ↥(CharPReduction.modularRing (1 * q) A.toSubring)) = 0 := Subtype.ext h0
    rw [this, map_zero]
  have hRloc := CharPReduction.subring_le_localizedAtKer A.toSubring red _ (CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring) hRmem
  have hHloc := CharPReduction.subring_le_localizedAtKer A.toSubring red _ (CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring) hHmem
  have hprodML : (⟨_, hz⟩ : ↥(CharPReduction.modularLocalized (1 * q) A.toSubring red)) * ⟨Rser, hRloc⟩ = ⟨_, hHloc⟩ := by
    apply Subtype.ext
    show ((algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (q : AlgebraicClosure ℚ) * (jqE q - jE q ^ q)⁻¹ :
        ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) * Rser = _
    rw [hzser, mul_assoc, inv_mul_cancel₀ hRser0, mul_one]
  have hprodF := congrArg (rlHom red) hprodML
  rw [map_mul] at hprodF

  have hRl : rlHom red ⟨Rser, hRloc⟩ = Polynomial.aeval (jC1 k)
      (MvPolynomial.eval₂Hom (Polynomial.C.comp red) ![Polynomial.X, Polynomial.X ^ q]
        (Polynomial.eval₂ (Polynomial.eval₂RingHom (MvPolynomial.C.comp (Int.castRingHom ↥A.toSubring)) (MvPolynomial.X 0))
          (MvPolynomial.X 1) R : MvPolynomial (Fin 2) ↥A.toSubring)) := by
    apply Subtype.ext
    rw [coe_rlHom, E4b80310.coe_aeval_jC1]
    have hx : (⟨Rser, hRloc⟩ : ↥(CharPReduction.modularLocalized (1 * q) A.toSubring red)) = ⟨modularEval (1 * q) A.toSubring _,
        CharPReduction.subring_le_localizedAtKer _ _ _ _ (ModularCurve.NodeLocalized.modularEval_mem_modularRing (A := A) (1 * q) _)⟩ := Subtype.ext hRser
    rw [hx]
    exact E4b80310.modularRedLocHom_modularEval red _
  have hHl : rlHom red ⟨_, hHloc⟩ = Polynomial.aeval (jC1 k) (Polynomial.X - Polynomial.X ^ (q ^ 2) : Polynomial k) := by
    apply Subtype.ext
    rw [coe_rlHom, E4b80310.coe_aeval_jC1]
    have hx : (⟨_, hHloc⟩ : ↥(CharPReduction.modularLocalized (1 * q) A.toSubring red)) = ⟨modularEval (1 * q) A.toSubring (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q),
        CharPReduction.subring_le_localizedAtKer _ _ _ _ (ModularCurve.NodeLocalized.modularEval_mem_modularRing (A := A) (1 * q) _)⟩ := Subtype.ext hHser
    rw [hx, E4b80310.modularRedLocHom_modularEval red]
    congr 1
    rw [map_sub, map_pow, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_zero, ← pow_mul, pow_two]

  have hordR : (charLGeomPlaceOfPoint k a).ord (rlHom red ⟨Rser, hRloc⟩) = 0 := by
    rw [hRl, Ws23.NodePlaceAPI.ord_charLGeomPlaceOfPoint_aeval]
    have : Polynomial.rootMultiplicity a (MvPolynomial.eval₂Hom (Polynomial.C.comp red) ![Polynomial.X, Polynomial.X ^ q]
        (Polynomial.eval₂ (Polynomial.eval₂RingHom (MvPolynomial.C.comp (Int.castRingHom ↥A.toSubring)) (MvPolynomial.X 0))
          (MvPolynomial.X 1) R : MvPolynomial (Fin 2) ↥A.toSubring)) = 0 := by
      rw [Polynomial.rootMultiplicity_eq_zero_iff]
      intro hroot
      exfalso
      apply hRne
      rw [← eval₂Hom_kroneckerPolynomial red a R, ← eval_graphReduce red a]
      exact hroot
    rw [this]; rfl
  have hordH : (charLGeomPlaceOfPoint k a).ord (rlHom red ⟨_, hHloc⟩) = 1 := by
    rw [hHl, Ws23.NodePlaceAPI.ord_charLGeomPlaceOfPoint_aeval, rootMultiplicity_X_sub_X_pow_sq_eq_one ha2]; rfl
  have hz0' : rlHom red ⟨_, hz⟩ ≠ 0 := (rlHom_ne_zero_iff red _).mpr hz0
  have hR0' : rlHom red ⟨Rser, hRloc⟩ ≠ 0 := by
    intro h; rw [h, mul_zero] at hprodF
    have := hordH; rw [← hprodF, Place.ord_zero] at this; exact zero_ne_one this
  have hsum := congrArg (charLGeomPlaceOfPoint k a).ord hprodF
  rw [Place.ord_mul _ hz0' hR0', hordR, hordH, add_zero] at hsum
  exact hsum

end Calibrator
p2m_reactivate "P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.Ws23 P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.Ws23.NodePlaceAPI"

end Ws23.Jump
p2m_reactivate "P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.Ws23 P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.Ws23.NodePlaceAPI"
p2m_reactivate "P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.Ws23 P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.Ws23.NodePlaceAPI"

namespace P7b57522e
p2m_open "AlgebraicCurve P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.AlgebraicCurve IsLocalRing ModularCurve~coeffEmb_jq P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.ModularCurve ModularCurve.NodeLocalized P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.ModularCurve.NodeLocalized"
theorem modularEval_map_inclusion (N : ℕ) [NeZero N] (A : ValuationSubring (AlgebraicClosure ℚ))
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (P : MvPolynomial (Fin 2) ↥(coeffSubring A K)) :
    modularEval N A.toSubring (MvPolynomial.map (Subring.inclusion (inf_le_left : coeffSubring A K ≤ A.toSubring)) P)
      = modularEval N (coeffSubring A K) P := by
  rw [modularEval, MvPolynomial.eval₂Hom_map_hom]
  rfl

theorem pointEval_map_inclusion {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k]
    (red : A →+* k) (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (a b : k)
    (P : MvPolynomial (Fin 2) ↥(coeffSubring A K)) :
    pointEval A.toSubring red a b (MvPolynomial.map (Subring.inclusion (inf_le_left : coeffSubring A K ≤ A.toSubring)) P)
      = pointEval (coeffSubring A K) (redRestrict red K) a b P := by
  rw [pointEval, MvPolynomial.eval₂Hom_map_hom]
  rfl

end P7b57522e
p2m_reactivate "P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.Ws23 P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.Ws23.NodePlaceAPI"

namespace Ws23
namespace WParam

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.AlgebraicCurve IsLocalRing ModularCurve~coeffEmb_jq P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.ModularCurve ModularCurve.NodeLocalized P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.ModularCurve.NodeLocalized P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.Ws23.NodePlaceAPI P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.Ws23.Jump"

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k] [CharP k q]

theorem frickeInvolutionBar_evalF (P : MvPolynomial (Fin 2) ↥A.toSubring) :
    frickeInvolutionBar (1 * q) (E4b80310.evalF A q P)
      = E4b80310.evalF A q (MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1) P) := by
  let φ : MvPolynomial (Fin 2) ↥A.toSubring →+* ↥(modularFunctionFieldBar (1 * q)) :=
    ((frickeInvolutionBar (1 * q) : ↥(modularFunctionFieldBar (1 * q)) ≃ₐ[AlgebraicClosure ℚ] _) : _ →+* _).comp (E4b80310.evalF A q)
  let ψ : MvPolynomial (Fin 2) ↥A.toSubring →+* ↥(modularFunctionFieldBar (1 * q)) :=
    (E4b80310.evalF A q).comp (MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1) : MvPolynomial (Fin 2) ↥A.toSubring →ₐ[↥A.toSubring] _).toRingHom
  have hφψ : φ = ψ := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)
    · show frickeInvolutionBar (1 * q) (E4b80310.evalF A q (MvPolynomial.C c)) = E4b80310.evalF A q (MvPolynomial.rename _ (MvPolynomial.C c))
      rw [MvPolynomial.rename_C, E4b80310.evalF, MvPolynomial.eval₂Hom_C, RingHom.comp_apply, AlgEquiv.commutes]
    · show frickeInvolutionBar (1 * q) (E4b80310.evalF A q (MvPolynomial.X 0)) = E4b80310.evalF A q (MvPolynomial.rename _ (MvPolynomial.X 0))
      rw [MvPolynomial.rename_X, Equiv.swap_apply_left, E4b80310.evalF, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_zero]
      exact ModularCurve.NodeLocalized.frickeInvolutionBar_jElt q
    · show frickeInvolutionBar (1 * q) (E4b80310.evalF A q (MvPolynomial.X 1)) = E4b80310.evalF A q (MvPolynomial.rename _ (MvPolynomial.X 1))
      rw [MvPolynomial.rename_X, Equiv.swap_apply_right, E4b80310.evalF, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_zero]
      exact ModularCurve.NodeLocalized.frickeInvolutionBar_jqElt q
  exact RingHom.congr_fun hφψ P

theorem pointEval_rename_swap (red : ↥A.toSubring →+* k) (c d : k) (P : MvPolynomial (Fin 2) ↥A.toSubring) :
    pointEval A.toSubring red c d (MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1) P) = pointEval A.toSubring red d c P := by
  rw [pointEval, pointEval, MvPolynomial.eval₂Hom_rename]
  have : ((![c, d] : Fin 2 → k) ∘ ⇑(Equiv.swap (0 : Fin 2) 1)) = ![d, c] := by
    funext i; fin_cases i <;> simp [Equiv.swap_apply_left, Equiv.swap_apply_right]
  rw [this]

noncomputable def gr (q : ℕ) (red : ↥A →+* k) (P : MvPolynomial (Fin 2) ↥A.toSubring) : Polynomial k :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp red) ![Polynomial.X, Polynomial.X ^ q] P

theorem eval_gr (red : ↥A →+* k) (c : k) (P : MvPolynomial (Fin 2) ↥A.toSubring) :
    Polynomial.eval c (gr q red P) = pointEval A.toSubring red c (c ^ q) P := by
  rw [gr, eval_graphReduce red c P]; rfl

theorem gr_ne_zero_of_pointEval_ne_zero (red : ↥A →+* k) {c : k} {P : MvPolynomial (Fin 2) ↥A.toSubring}
    (h : pointEval A.toSubring red c (c ^ q) P ≠ 0) : gr q red P ≠ 0 := by
  intro h0; apply h; rw [← eval_gr, h0, Polynomial.eval_zero]

theorem redRes_modularEval_eq_aeval_gr (red : ↥A →+* k) (P : MvPolynomial (Fin 2) ↥A.toSubring) :
    CharPReduction.redRes A.toSubring red (CharPReduction.modularRing (1 * q) A.toSubring)
        (CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring)
        ⟨modularEval (1 * q) A.toSubring P, modularEval_mem_modularRing (1 * q) P⟩
      = Polynomial.aeval (jqModC k) (gr q red P) :=
  redRes_modularEval red P

theorem modularEval_ne_zero_of_gr_ne_zero (red : ↥A →+* k) {P : MvPolynomial (Fin 2) ↥A.toSubring} (h : gr q red P ≠ 0) :
    modularEval (1 * q) A.toSubring P ≠ 0 := by
  intro h0
  apply transcendental_jqModC k
  refine ⟨gr q red P, h, ?_⟩
  rw [← redRes_modularEval_eq_aeval_gr red P]
  have : (⟨modularEval (1 * q) A.toSubring P, modularEval_mem_modularRing (1 * q) P⟩ :
      ↥(CharPReduction.modularRing (1 * q) A.toSubring)) = 0 := Subtype.ext h0
  rw [this, map_zero]

theorem exists_mem_rlHom_mul_eq (red : ↥A →+* k) (g : ↥(modularFunctionFieldBar (1 * q)))
    (r s : MvPolynomial (Fin 2) ↥A.toSubring)
    (hgs : ((g : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) * modularEval (1 * q) A.toSubring s
      = modularEval (1 * q) A.toSubring r)
    (hs : gr q red s ≠ 0) :
    ∃ hg : ((g : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red,
      rlHom red ⟨_, hg⟩ * Polynomial.aeval (jC1 k) (gr q red s) = Polynomial.aeval (jC1 k) (gr q red r) := by
  have hsred : CharPReduction.redRes A.toSubring red (CharPReduction.modularRing (1 * q) A.toSubring)
      (CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring)
      ⟨modularEval (1 * q) A.toSubring s, modularEval_mem_modularRing (1 * q) s⟩ ≠ 0 := by
    rw [redRes_modularEval_eq_aeval_gr]
    intro h0; exact transcendental_jqModC k ⟨gr q red s, hs, h0⟩
  have hnot := (CharPReduction.notMem_redKer_iff A.toSubring red (CharPReduction.modularRing (1 * q) A.toSubring)
    (CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring)).mpr hsred
  have hg : ((g : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red :=
    ⟨⟨_, modularEval_mem_modularRing (1 * q) r⟩, ⟨_, modularEval_mem_modularRing (1 * q) s⟩, hnot, hgs⟩
  refine ⟨hg, ?_⟩
  have hspec := CharPReduction.redLoc_spec (A := A.toSubring) (red := red) (R := CharPReduction.modularRing (1 * q) A.toSubring)
    (hR := CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring) ⟨_, hg⟩
    (r := ⟨_, modularEval_mem_modularRing (1 * q) r⟩) (s := ⟨_, modularEval_mem_modularRing (1 * q) s⟩) hgs
  apply Subtype.ext
  rw [MulMemClass.coe_mul, coe_rlHom, E4b80310.coe_aeval_jC1, E4b80310.coe_aeval_jC1, ← redRes_modularEval_eq_aeval_gr red s,
    ← redRes_modularEval_eq_aeval_gr red r]
  exact hspec

theorem ord_aeval_gr (red : ↥A →+* k) [DecidableEq k] (c : k) (P : MvPolynomial (Fin 2) ↥A.toSubring) :
    (charLGeomPlaceOfPoint k c).ord (Polynomial.aeval (jC1 k) (gr q red P)) = ((gr q red P).rootMultiplicity c : ℤ) := by
  rw [Ws23.NodePlaceAPI.ord_charLGeomPlaceOfPoint_aeval]

theorem ord_aeval_gr_eq_zero (red : ↥A →+* k) [DecidableEq k] {c : k} {P : MvPolynomial (Fin 2) ↥A.toSubring}
    (h : pointEval A.toSubring red c (c ^ q) P ≠ 0) :
    (charLGeomPlaceOfPoint k c).ord (Polynomial.aeval (jC1 k) (gr q red P)) = 0 := by
  rw [ord_aeval_gr, Polynomial.rootMultiplicity_eq_zero]
  · rfl
  · intro hroot; exfalso; apply h; rw [← eval_gr]; exact hroot

theorem aeval_gr_ne_zero (red : ↥A →+* k) {P : MvPolynomial (Fin 2) ↥A.toSubring} (h : gr q red P ≠ 0) :
    Polynomial.aeval (jC1 k) (gr q red P) ≠ 0 := by
  intro h0
  apply transcendental_jqModC k
  refine ⟨gr q red P, h, ?_⟩
  have := congrArg (fun t : ↥(modularFunctionFieldC k 1) => (t : LaurentSeries k)) h0
  simp only [E4b80310.coe_aeval_jC1] at this
  exact this

theorem exists_mem_ord_nonneg (red : ↥A →+* k) [DecidableEq k] (c : k) (g : ↥(modularFunctionFieldBar (1 * q)))
    (r s : MvPolynomial (Fin 2) ↥A.toSubring)
    (hgs : ((g : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) * modularEval (1 * q) A.toSubring s
      = modularEval (1 * q) A.toSubring r)
    (hsc : pointEval A.toSubring red c (c ^ q) s ≠ 0) :
    ∃ hg : ((g : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red,
      (rlHom red ⟨_, hg⟩ ≠ 0 → 0 ≤ (charLGeomPlaceOfPoint k c).ord (rlHom red ⟨_, hg⟩)) := by
  have hs0 := gr_ne_zero_of_pointEval_ne_zero red hsc
  obtain ⟨hg, hmul⟩ := exists_mem_rlHom_mul_eq red g r s hgs hs0
  refine ⟨hg, fun hne => ?_⟩
  have hsne := aeval_gr_ne_zero red hs0 (k := k)
  have hrne : Polynomial.aeval (jC1 k) (gr q red r) ≠ 0 := by rw [← hmul]; exact mul_ne_zero hne hsne
  have hord := congrArg (charLGeomPlaceOfPoint k c).ord hmul
  rw [Place.ord_mul _ hne hsne, ord_aeval_gr_eq_zero red hsc, add_zero, ord_aeval_gr] at hord
  rw [hord]; exact Int.natCast_nonneg _

end Ws23.WParam
p2m_reactivate "P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.Ws23 P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.Ws23.NodePlaceAPI"
p2m_reactivate "P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.Ws23 P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.Ws23.NodePlaceAPI"

namespace Ws23
namespace WParam

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.AlgebraicCurve IsLocalRing ModularCurve~coeffEmb_jq P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.ModularCurve ModularCurve.NodeLocalized P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.ModularCurve.NodeLocalized P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.Ws23.NodePlaceAPI P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.Ws23.Jump"

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k] [CharP k q]
  [IsAlgClosed k] [DecidableEq k]

theorem exists_rep (red : ↥A →+* k) (a : k) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (x : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) :
    ∃ (g : ↥(modularFunctionFieldBar (1 * q))) (r s : MvPolynomial (Fin 2) ↥A.toSubring),
      ((g : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) = (x : LaurentSeries (AlgebraicClosure ℚ)) ∧
      ((g : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) * modularEval (1 * q) A.toSubring s
        = modularEval (1 * q) A.toSubring r ∧
      pointEval A.toSubring red a (a ^ q) s ≠ 0 := by
  obtain ⟨rK, sK, hsK, hx⟩ := x.2
  set r := MvPolynomial.map (Subring.inclusion (inf_le_left : coeffSubring A K ≤ A.toSubring)) rK with hr
  set s := MvPolynomial.map (Subring.inclusion (inf_le_left : coeffSubring A K ≤ A.toSubring)) sK with hs
  have hsA : pointEval A.toSubring red a (a ^ q) s ≠ 0 := by rw [hs, P7b57522e.pointEval_map_inclusion]; exact hsK
  have hxA : (x : LaurentSeries (AlgebraicClosure ℚ)) * modularEval (1 * q) A.toSubring s = modularEval (1 * q) A.toSubring r := by
    rw [hr, hs, P7b57522e.modularEval_map_inclusion, P7b57522e.modularEval_map_inclusion]; exact hx
  have hs0 : modularEval (1 * q) A.toSubring s ≠ 0 :=
    modularEval_ne_zero_of_gr_ne_zero red (gr_ne_zero_of_pointEval_ne_zero red hsA)
  refine ⟨E4b80310.evalF A q r * (E4b80310.evalF A q s)⁻¹, r, s, ?_, ?_, hsA⟩
  · rw [MulMemClass.coe_mul, IntermediateField.coe_inv, E4b80310.coe_evalF, E4b80310.coe_evalF, ← hxA, mul_assoc,
      mul_inv_cancel₀ hs0, mul_one]
  · rw [MulMemClass.coe_mul, IntermediateField.coe_inv, E4b80310.coe_evalF, E4b80310.coe_evalF, mul_assoc,
      inv_mul_cancel₀ hs0, mul_one]

theorem presentation_frickeInvolutionBar (red : ↥A →+* k) {a : k} (ha2 : a ^ (q ^ 2) = a)
    (g : ↥(modularFunctionFieldBar (1 * q))) (r s : MvPolynomial (Fin 2) ↥A.toSubring)
    (hgs : ((g : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) * modularEval (1 * q) A.toSubring s
      = modularEval (1 * q) A.toSubring r)
    (hsa : pointEval A.toSubring red a (a ^ q) s ≠ 0) :
    ((frickeInvolutionBar (1 * q) g : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ))
        * modularEval (1 * q) A.toSubring (MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1) s)
      = modularEval (1 * q) A.toSubring (MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1) r) ∧
    pointEval A.toSubring red (a ^ q) ((a ^ q) ^ q) (MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1) s) ≠ 0 := by
  constructor
  · have hF : g * E4b80310.evalF A q s = E4b80310.evalF A q r := by
      apply Subtype.ext
      rw [MulMemClass.coe_mul, E4b80310.coe_evalF, E4b80310.coe_evalF]; exact hgs
    have h2 := congrArg (frickeInvolutionBar (1 * q)) hF
    rw [map_mul, frickeInvolutionBar_evalF, frickeInvolutionBar_evalF] at h2
    have h3 := congrArg (fun t : ↥(modularFunctionFieldBar (1 * q)) => (t : LaurentSeries (AlgebraicClosure ℚ))) h2
    simp only [MulMemClass.coe_mul, E4b80310.coe_evalF] at h3
    exact h3
  · rw [pointEval_rename_swap, ← pow_mul, ← sq, ha2]; exact hsa

end Ws23.WParam
p2m_reactivate "P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.Ws23 P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.Ws23.NodePlaceAPI"
p2m_reactivate "P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.Ws23 P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.Ws23.NodePlaceAPI"

p2m_open "ModularCurve~coeffEmb_jq" in open Ws23.WParam Ws23.Jump Ws23.SlopeLaw0 Ws23.NodePlaceAPI _root_.AlgebraicCurve _root_.P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.AlgebraicCurve IsLocalRing _root_.P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.ModularCurve _root_.ModularCurve.NodeLocalized _root_.P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728.ModularCurve.NodeLocalized in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 12800000 in
theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] (red : A →+* k)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (hq : 5 ≤ q) (a : k) (ha : a ∈ ssJSet q k) (ha2 : a ^ (q ^ 2) = a) (h01728 : a = 0 ∨ a = 1728)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (ϖ : ↥(coeffSubring A K)) (hϖ : ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d)
    (eK : ℕ) (ε : ↥(coeffSubring A K)) (hε : IsUnit ε)
    (hqϖ : ((q : ℕ) : ↥(coeffSubring A K)) = ϖ ^ eK * ε)
    (G' H' w : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))
    (hw : IsUnit w)
    (hGH : G' * H' = (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) ^ (jWidth a * eK) * w)
    (hmax : ∀ [IsLocalRing ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))],
      IsLocalRing.maximalIdeal ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) =
        Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), G', H'})
    (heK1 : 1 ≤ eK)
    (hpr1 : (Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), G'}).IsPrime)
    (hpr2 : (Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), H'}).IsPrime)
    (hnm1 : H' ∉ Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), G'})
    (hnm2 : G' ∉ Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), H'})
    (hsp1 : Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), G'} = Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))})
    (hsp2 : Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), H'} = Ideal.span {(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))}) :
    (∀ g : ↥(modularFunctionFieldBar (1 * q)),
        ((g : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) = (G' : LaurentSeries (AlgebraicClosure ℚ)) →
        ∃ (h : ((frickeInvolutionBar (1 * q) g : modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ)) ∈
              CharPReduction.modularLocalized (1 * q) A.toSubring red)
          (hF : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h⟩ ∈ modularFunctionFieldC k 1),
          CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h⟩ ≠ 0 ∧
          (charLGeomPlaceOfPoint k (a ^ q)).ord (⟨_, hF⟩ : ↥(modularFunctionFieldC k 1)) = 1) ∧
    (∀ g g' : ↥(modularFunctionFieldBar (1 * q)),
        ((g : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) = (G' : LaurentSeries (AlgebraicClosure ℚ)) →
        g' * g = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (((q : ℕ) : AlgebraicClosure ℚ) ^ jWidth a) →
        ∃ (h : ((g' : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈
              CharPReduction.modularLocalized (1 * q) A.toSubring red)
          (hF : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h⟩ ∈ modularFunctionFieldC k 1),
          CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h⟩ ≠ 0 ∧
          (charLGeomPlaceOfPoint k a).ord (⟨_, hF⟩ : ↥(modularFunctionFieldC k 1)) = 1) := by
  classical
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩

  obtain ⟨ϖF, hϖF⟩ : ∃ x : ↥(modularFunctionFieldBar (1 * q)), x = algebraMap (AlgebraicClosure ℚ) _ ((ϖ : ↥(coeffSubring A K)) : AlgebraicClosure ℚ) := ⟨_, rfl⟩
  obtain ⟨GF, hGF⟩ : ∃ x : ↥(modularFunctionFieldBar (1 * q)), x = Ws23.CentredSigma.jqE q - Ws23.CentredSigma.jE q ^ q := ⟨_, rfl⟩
  obtain ⟨HF, hHF⟩ : ∃ x : ↥(modularFunctionFieldBar (1 * q)), x = Ws23.CentredSigma.jE q - Ws23.CentredSigma.jqE q ^ q := ⟨_, rfl⟩
  have hϖmemA : ((ϖ : ↥(coeffSubring A K)) : AlgebraicClosure ℚ) ∈ A := (Subring.inclusion (inf_le_left : coeffSubring A K ≤ A.toSubring) ϖ).2
  have hredϖ : red ⟨_, hϖmemA⟩ = 0 := by
    have : redRestrict red K ϖ = 0 := (hϖ ϖ).mpr ⟨1, (mul_one ϖ).symm⟩
    exact this

  have hϖser : ((⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) : LaurentSeries (AlgebraicClosure ℚ)) = ((ϖF : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) := by
    rw [hϖF, coe_algebraMap_eq_constSeries ⟨_, hϖmemA⟩]
    show modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ) = _
    rw [modularEval, MvPolynomial.eval₂Hom_C]
    rfl
  have hGser : ((⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) : LaurentSeries (AlgebraicClosure ℚ)) = ((GF : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) := by
    show modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q) = _
    rw [hGF, AddSubgroupClass.coe_sub, SubmonoidClass.coe_pow]
    simp only [modularEval, map_sub, map_pow, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X, Matrix.cons_val_one,
      Matrix.cons_val_zero]
    show _ = coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq) - (coeffEmb (AlgebraicClosure ℚ) jq) ^ q
    rw [coeffEmb_jq, coeffEmb_qExpand_jq]
  have hHser : ((⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) : LaurentSeries (AlgebraicClosure ℚ)) = ((HF : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) := by
    show modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q) = _
    rw [hHF, AddSubgroupClass.coe_sub, SubmonoidClass.coe_pow]
    simp only [modularEval, map_sub, map_pow, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X, Matrix.cons_val_one,
      Matrix.cons_val_zero]
    show _ = coeffEmb (AlgebraicClosure ℚ) jq - (coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq)) ^ q
    rw [coeffEmb_jq, coeffEmb_qExpand_jq]
  have hσG : frickeInvolutionBar (1 * q) GF = HF := by
    rw [hGF, hHF, map_sub, map_pow, Ws23.CentredSigma.frickeInvolutionBar_jqE, Ws23.CentredSigma.frickeInvolutionBar_jE]

  have hHpres : ((HF : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) * modularEval (1 * q) A.toSubring 1
      = modularEval (1 * q) A.toSubring (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q) := by
    rw [map_one, mul_one, ← E4b80310.coe_evalF]
    congr 1
    rw [hHF, map_sub, map_pow, E4b80310.evalF, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_zero]
    rfl

  obtain ⟨hHmem, hHmul⟩ := exists_mem_rlHom_mul_eq red HF (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q) 1 hHpres
    (by rw [gr, map_one]; exact one_ne_zero)
  have hHval : rlHom red ⟨_, hHmem⟩ = Polynomial.aeval (jC1 k) (Polynomial.X - Polynomial.X ^ (q ^ 2) : Polynomial k) := by
    rw [gr, map_one, map_one, mul_one] at hHmul
    rw [hHmul, gr]
    congr 1
    rw [map_sub, map_pow, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_zero, ← pow_mul, pow_two]
  have hH0 : rlHom red ⟨_, hHmem⟩ ≠ 0 := by
    rw [hHval]
    intro h0
    have := congrArg (fun t : ↥(modularFunctionFieldC k 1) => (t : LaurentSeries k)) h0
    simp only [E4b80310.coe_aeval_jC1, ZeroMemClass.coe_zero] at this
    apply transcendental_jqModC k
    refine ⟨_, ?_, this⟩
    intro h
    have hdeg := congrArg Polynomial.natDegree (sub_eq_zero.mp h)
    rw [Polynomial.natDegree_X, Polynomial.natDegree_X_pow] at hdeg
    have : 1 < q ^ 2 := Nat.one_lt_pow two_ne_zero (Fact.out : q.Prime).one_lt
    omega
  have hordH : ∀ c : k, c ^ (q ^ 2) = c → (charLGeomPlaceOfPoint k c).ord (rlHom red ⟨_, hHmem⟩) = 1 := by
    intro c hc
    rw [hHval, Ws23.NodePlaceAPI.ord_charLGeomPlaceOfPoint_aeval, rootMultiplicity_X_sub_X_pow_sq_eq_one hc]; rfl
  have haq2 : (a ^ q) ^ (q ^ 2) = a ^ q := by rw [← pow_mul, mul_comm, pow_mul, ha2]

  have hϖmem : ((ϖF : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red := by
    simpa only [hϖF] using algebraMap_mem_modularLocalized red ⟨_, hϖmemA⟩ (q := q)
  have hϖ0 : rlHom red ⟨_, hϖmem⟩ = 0 := by
    have hmem' := algebraMap_mem_modularLocalized red ⟨_, hϖmemA⟩ (q := q)
    have heq : (⟨_, hϖmem⟩ : ↥(CharPReduction.modularLocalized (1 * q) A.toSubring red)) = ⟨_, hmem'⟩ :=
      Subtype.ext (by show ((ϖF : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) = _; rw [hϖF])
    apply Subtype.ext
    rw [heq, coe_rlHom, ZeroMemClass.coe_zero, modularRedLocHom_algebraMap red ⟨_, hϖmemA⟩, hredϖ, map_zero]
  have hσϖ : frickeInvolutionBar (1 * q) ϖF = ϖF := by rw [hϖF]; exact AlgEquiv.commutes _ _

  have sandwich : ∀ (c : k) (y yβ yδ yH : ↥(modularFunctionFieldC k 1)),
      y = yβ * yH → yH = yδ * y → yH ≠ 0 → (charLGeomPlaceOfPoint k c).ord yH = 1 →
      (yβ ≠ 0 → 0 ≤ (charLGeomPlaceOfPoint k c).ord yβ) → (yδ ≠ 0 → 0 ≤ (charLGeomPlaceOfPoint k c).ord yδ) →
      y ≠ 0 ∧ (charLGeomPlaceOfPoint k c).ord y = 1 := by
    intro c y yβ yδ yH h1 h2 hH0' hH1 hβ hδ
    have hy0 : y ≠ 0 := by intro h; rw [h, mul_zero] at h2; exact hH0' h2
    have hδ0 : yδ ≠ 0 := by intro h; rw [h, zero_mul] at h2; exact hH0' h2
    have hβ0 : yβ ≠ 0 := by intro h; rw [h, zero_mul] at h1; exact hy0 h1
    have e1 := congrArg (charLGeomPlaceOfPoint k c).ord h1
    have e2 := congrArg (charLGeomPlaceOfPoint k c).ord h2
    rw [Place.ord_mul _ hβ0 hH0', hH1] at e1
    rw [Place.ord_mul _ hδ0 hy0, hH1] at e2
    have := hβ hβ0; have := hδ hδ0
    exact ⟨hy0, by omega⟩
  refine ⟨?_, ?_⟩

  · intro g hg

    have hG'mem : (G' : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) ∈ Ideal.span ({(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))} : Set ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) := by
      rw [← hsp1]; exact Ideal.subset_span (by simp)
    have hGmem : (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) ∈ Ideal.span ({(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), G'} : Set ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) := by
      rw [hsp1]; exact Ideal.subset_span (by simp)
    obtain ⟨α, β, hαβ⟩ := Ideal.mem_span_pair.mp hG'mem
    obtain ⟨γ, δ, hγδ⟩ := Ideal.mem_span_pair.mp hGmem
    obtain ⟨gα, rα, sα, hgα, hpα, hsα⟩ := exists_rep red a K α
    obtain ⟨gβ, rβ, sβ, hgβ, hpβ, hsβ⟩ := exists_rep red a K β
    obtain ⟨gγ, rγ, sγ, hgγ, hpγ, hsγ⟩ := exists_rep red a K γ
    obtain ⟨gδ, rδ, sδ, hgδ, hpδ, hsδ⟩ := exists_rep red a K δ
    obtain ⟨g₀, r₀, s₀, hg₀, hp₀, hs₀⟩ := exists_rep red a K G'
    have hgg₀ : g = g₀ := Subtype.ext (hg.trans hg₀.symm)
    subst hgg₀

    have eqF1 : g = gα * ϖF + gβ * GF := by
      apply Subtype.ext
      rw [AddMemClass.coe_add, MulMemClass.coe_mul, MulMemClass.coe_mul, hg, hgα, hgβ, ← hϖser, ← hGser]
      have := congrArg Subtype.val hαβ; push_cast at this; exact this.symm
    have eqF2 : GF = gγ * ϖF + gδ * g := by
      apply Subtype.ext
      rw [AddMemClass.coe_add, MulMemClass.coe_mul, MulMemClass.coe_mul, hg, hgγ, hgδ, ← hϖser, ← hGser]
      have := congrArg Subtype.val hγδ; push_cast at this; exact this.symm
    have eqσ1 : frickeInvolutionBar (1 * q) g = frickeInvolutionBar (1 * q) gα * ϖF + frickeInvolutionBar (1 * q) gβ * HF := by
      conv_lhs => rw [eqF1]
      rw [map_add, map_mul, map_mul, hσϖ, hσG]
    have eqσ2 : HF = frickeInvolutionBar (1 * q) gγ * ϖF + frickeInvolutionBar (1 * q) gδ * frickeInvolutionBar (1 * q) g := by
      conv_lhs => rw [← hσG, eqF2]
      rw [map_add, map_mul, map_mul, hσϖ]

    obtain ⟨hmg, -⟩ := exists_mem_ord_nonneg red (a ^ q) (frickeInvolutionBar (1 * q) g) _ _
      (presentation_frickeInvolutionBar red ha2 g r₀ s₀ hp₀ hs₀).1 (presentation_frickeInvolutionBar red ha2 g r₀ s₀ hp₀ hs₀).2
    obtain ⟨hmα, -⟩ := exists_mem_ord_nonneg red (a ^ q) (frickeInvolutionBar (1 * q) gα) _ _
      (presentation_frickeInvolutionBar red ha2 gα rα sα hpα hsα).1 (presentation_frickeInvolutionBar red ha2 gα rα sα hpα hsα).2
    obtain ⟨hmβ, hoβ⟩ := exists_mem_ord_nonneg red (a ^ q) (frickeInvolutionBar (1 * q) gβ) _ _
      (presentation_frickeInvolutionBar red ha2 gβ rβ sβ hpβ hsβ).1 (presentation_frickeInvolutionBar red ha2 gβ rβ sβ hpβ hsβ).2
    obtain ⟨hmγ, -⟩ := exists_mem_ord_nonneg red (a ^ q) (frickeInvolutionBar (1 * q) gγ) _ _
      (presentation_frickeInvolutionBar red ha2 gγ rγ sγ hpγ hsγ).1 (presentation_frickeInvolutionBar red ha2 gγ rγ sγ hpγ hsγ).2
    obtain ⟨hmδ, hoδ⟩ := exists_mem_ord_nonneg red (a ^ q) (frickeInvolutionBar (1 * q) gδ) _ _
      (presentation_frickeInvolutionBar red ha2 gδ rδ sδ hpδ hsδ).1 (presentation_frickeInvolutionBar red ha2 gδ rδ sδ hpδ hsδ).2

    have eqM1 : (⟨_, hmg⟩ : ↥(CharPReduction.modularLocalized (1 * q) A.toSubring red)) = ⟨_, hmα⟩ * ⟨_, hϖmem⟩ + ⟨_, hmβ⟩ * ⟨_, hHmem⟩ :=
      Subtype.ext (by
        show ((frickeInvolutionBar (1 * q) g : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) = _
        rw [eqσ1]; rfl)
    have eqM2 : (⟨_, hHmem⟩ : ↥(CharPReduction.modularLocalized (1 * q) A.toSubring red)) = ⟨_, hmγ⟩ * ⟨_, hϖmem⟩ + ⟨_, hmδ⟩ * ⟨_, hmg⟩ :=
      Subtype.ext (by
        show ((HF : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) = _
        conv_lhs => rw [eqσ2]
        rfl)
    have e1 := congrArg (rlHom red) eqM1
    have e2 := congrArg (rlHom red) eqM2
    rw [map_add, map_mul, map_mul, hϖ0, mul_zero, zero_add] at e1 e2
    obtain ⟨hy0, hy1⟩ := sandwich (a ^ q) _ _ _ _ e1 e2 hH0 (hordH _ haq2) hoβ hoδ
    refine ⟨hmg, Ws23.SlopeLaw0.modularRedLocHom_mem_one red ⟨_, hmg⟩, (rlHom_ne_zero_iff red _).mp hy0, ?_⟩
    rw [rlHom_eq red]; exact hy1

  · intro g g' hg hgg'
    have hH'mem : (H' : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) ∈ Ideal.span ({(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))} : Set ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) := by
      rw [← hsp2]; exact Ideal.subset_span (by simp)
    have hHtmem : (⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) ∈ Ideal.span ({(⟨modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C ϖ),
          modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) _⟩ :
          ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))), H'} : Set ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))) := by
      rw [hsp2]; exact Ideal.subset_span (by simp)
    obtain ⟨c₁, d₁, hcd₁⟩ := Ideal.mem_span_pair.mp hH'mem
    obtain ⟨c₂, d₂, hcd₂⟩ := Ideal.mem_span_pair.mp hHtmem
    obtain ⟨gc₁, rc₁, sc₁, hgc₁, hpc₁, hsc₁⟩ := exists_rep red a K c₁
    obtain ⟨gd₁, rd₁, sd₁, hgd₁, hpd₁, hsd₁⟩ := exists_rep red a K d₁
    obtain ⟨gc₂, rc₂, sc₂, hgc₂, hpc₂, hsc₂⟩ := exists_rep red a K c₂
    obtain ⟨gd₂, rd₂, sd₂, hgd₂, hpd₂, hsd₂⟩ := exists_rep red a K d₂
    obtain ⟨gH, rH, sH, hgH, hpH, hsH⟩ := exists_rep red a K H'
    obtain ⟨gw, rw_, sw, hgw, hpw, hsw⟩ := exists_rep red a K w
    obtain ⟨gwi, rwi, swi, hgwi, hpwi, hswi⟩ := exists_rep red a K (↑(hw.unit⁻¹) : ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))
    obtain ⟨g₀, r₀, s₀, hg₀, hp₀, hs₀⟩ := exists_rep red a K G'
    have hgg₀ : g = g₀ := Subtype.ext (hg.trans hg₀.symm)
    subst hgg₀

    have eqF1 : gH = gc₁ * ϖF + gd₁ * HF := by
      apply Subtype.ext
      rw [AddMemClass.coe_add, MulMemClass.coe_mul, MulMemClass.coe_mul, hgH, hgc₁, hgd₁, ← hϖser, ← hHser]
      have := congrArg Subtype.val hcd₁; push_cast at this; exact this.symm
    have eqF2 : HF = gc₂ * ϖF + gd₂ * gH := by
      apply Subtype.ext
      rw [AddMemClass.coe_add, MulMemClass.coe_mul, MulMemClass.coe_mul, hgH, hgc₂, hgd₂, ← hϖser, ← hHser]
      have := congrArg Subtype.val hcd₂; push_cast at this; exact this.symm
    have eqFw : gw * gwi = 1 := by
      apply Subtype.ext
      rw [MulMemClass.coe_mul, OneMemClass.coe_one, hgw, hgwi, ← Subring.coe_mul, hw.mul_val_inv]; rfl
    have eqFGH : g * gH = ϖF ^ (jWidth a * eK) * gw := by
      apply Subtype.ext
      rw [MulMemClass.coe_mul, MulMemClass.coe_mul, SubmonoidClass.coe_pow, hg, hgH, hgw, ← hϖser]
      have := congrArg Subtype.val hGH; push_cast at this; exact this

    obtain ⟨hmH, -⟩ := exists_mem_ord_nonneg red a gH _ _ hpH hsH
    obtain ⟨hmc₁, -⟩ := exists_mem_ord_nonneg red a gc₁ _ _ hpc₁ hsc₁
    obtain ⟨hmd₁, hod₁⟩ := exists_mem_ord_nonneg red a gd₁ _ _ hpd₁ hsd₁
    obtain ⟨hmc₂, -⟩ := exists_mem_ord_nonneg red a gc₂ _ _ hpc₂ hsc₂
    obtain ⟨hmd₂, hod₂⟩ := exists_mem_ord_nonneg red a gd₂ _ _ hpd₂ hsd₂
    obtain ⟨hmw, how⟩ := exists_mem_ord_nonneg red a gw _ _ hpw hsw
    obtain ⟨hmwi, howi⟩ := exists_mem_ord_nonneg red a gwi _ _ hpwi hswi
    have eqM1 : (⟨_, hmH⟩ : ↥(CharPReduction.modularLocalized (1 * q) A.toSubring red)) = ⟨_, hmc₁⟩ * ⟨_, hϖmem⟩ + ⟨_, hmd₁⟩ * ⟨_, hHmem⟩ :=
      Subtype.ext (by
        show ((gH : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) = _
        rw [eqF1]; rfl)
    have eqM2 : (⟨_, hHmem⟩ : ↥(CharPReduction.modularLocalized (1 * q) A.toSubring red)) = ⟨_, hmc₂⟩ * ⟨_, hϖmem⟩ + ⟨_, hmd₂⟩ * ⟨_, hmH⟩ :=
      Subtype.ext (by
        show ((HF : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) = _
        conv_lhs => rw [eqF2]
        rfl)
    have e1 := congrArg (rlHom red) eqM1
    have e2 := congrArg (rlHom red) eqM2
    rw [map_add, map_mul, map_mul, hϖ0, mul_zero, zero_add] at e1 e2
    obtain ⟨hz0, hz1⟩ := sandwich a _ _ _ _ e1 e2 hH0 (hordH _ ha2) hod₁ hod₂

    have eqMw : (⟨_, hmw⟩ : ↥(CharPReduction.modularLocalized (1 * q) A.toSubring red)) * ⟨_, hmwi⟩ = 1 :=
      Subtype.ext (by
        show ((gw : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) * ((gwi : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) = 1
        rw [← MulMemClass.coe_mul, eqFw]; rfl)
    have ew := congrArg (rlHom red) eqMw
    rw [map_mul, map_one] at ew
    have hw0 : rlHom red ⟨_, hmw⟩ ≠ 0 := left_ne_zero_of_mul_eq_one ew
    have hwi0 : rlHom red ⟨_, hmwi⟩ ≠ 0 := right_ne_zero_of_mul_eq_one ew
    have hordw : (charLGeomPlaceOfPoint k a).ord (rlHom red ⟨_, hmw⟩) = 0 := by
      have := congrArg (charLGeomPlaceOfPoint k a).ord ew
      rw [Place.ord_mul _ hw0 hwi0, ord_one'] at this
      have h1 := how hw0; have h2 := howi hwi0
      omega

    have hεmemA : ((ε : ↥(coeffSubring A K)) : AlgebraicClosure ℚ) ∈ A := (Subring.inclusion (inf_le_left : coeffSubring A K ≤ A.toSubring) ε).2
    have hredε : red ⟨_, hεmemA⟩ ≠ 0 := by
      intro h0
      have h1 : redRestrict red K ε = 0 := h0
      obtain ⟨d, hd⟩ := (hϖ ε).mp h1
      have hϖunit : IsUnit ϖ := isUnit_of_mul_isUnit_left (hd ▸ hε)
      have h2 : redRestrict red K 1 = 0 := (hϖ 1).mpr ⟨↑(hϖunit.unit⁻¹), by rw [IsUnit.mul_val_inv]⟩
      rw [map_one] at h2
      exact one_ne_zero h2
    have hq0 : ((q : AlgebraicClosure ℚ)) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
    have hϖF0 : ϖF ≠ 0 := by
      rw [hϖF, map_ne_zero]
      intro h0
      apply hq0
      have := congrArg (fun t : ↥(coeffSubring A K) => (t : AlgebraicClosure ℚ)) hqϖ
      simp only [Subring.coe_mul, Subring.coe_pow, Subring.coe_natCast] at this
      rw [this, h0, zero_pow (by omega : eK ≠ 0), zero_mul]
    have hgw0 : gw ≠ 0 := left_ne_zero_of_mul_eq_one eqFw
    have hg0 : g ≠ 0 := by
      intro h0; rw [h0, zero_mul] at eqFGH
      exact (mul_ne_zero (pow_ne_zero _ hϖF0) hgw0) eqFGH.symm
    set εA : ↥A := ⟨_, hεmemA⟩ with hεA
    have key : g' = ((εA : AlgebraicClosure ℚ) ^ jWidth a) • (gH * gw⁻¹) := by
      have hqe : algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (((q : ℕ) : AlgebraicClosure ℚ) ^ jWidth a)
          = ϖF ^ (jWidth a * eK) * algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (((εA : AlgebraicClosure ℚ)) ^ jWidth a) := by
        have := congrArg (fun t : ↥(coeffSubring A K) => (t : AlgebraicClosure ℚ)) hqϖ
        simp only [Subring.coe_mul, Subring.coe_pow, Subring.coe_natCast] at this
        rw [this, hϖF, mul_pow, ← pow_mul, map_mul, map_pow, map_pow, mul_comm (jWidth a) eK]

      have h1 : g' * (ϖF ^ (jWidth a * eK) * gw) = ϖF ^ (jWidth a * eK) *
          algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (((εA : AlgebraicClosure ℚ)) ^ jWidth a) * gH := by
        rw [← eqFGH, ← mul_assoc, hgg', hqe]
      rw [Algebra.smul_def]
      field_simp
      have h2 : g' * gw * ϖF ^ (jWidth a * eK) = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (((εA : AlgebraicClosure ℚ)) ^ jWidth a) * gH * ϖF ^ (jWidth a * eK) := by
        calc g' * gw * ϖF ^ (jWidth a * eK) = g' * (ϖF ^ (jWidth a * eK) * gw) := by ring
          _ = _ := h1
          _ = _ := by ring
      exact mul_right_cancel₀ (pow_ne_zero _ hϖF0) h2

    obtain ⟨hmwinv, hwinv0⟩ := CharPReduction.gaussUnit_inv (1 * q) A.toSubring red ⟨hmw, (rlHom_ne_zero_iff red _).mp hw0⟩
    have hmprod : ((gH * gw⁻¹ : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red := by
      rw [MulMemClass.coe_mul, IntermediateField.coe_inv]; exact mul_mem hmH hmwinv
    have hεpowunit : IsUnit (εA ^ jWidth a) := by
      refine (isUnit_pow_iff (by unfold jWidth; split_ifs <;> norm_num)).mpr ?_
      by_contra hnu
      apply hredε
      exact (hker _).mpr ((IsLocalRing.mem_maximalIdeal _).mpr hnu)
    have hmg' : ((g' : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red := by
      rw [key, show ((εA : AlgebraicClosure ℚ)) ^ jWidth a = ((εA ^ jWidth a : ↥A) : AlgebraicClosure ℚ) by push_cast; rfl]
      exact smul_mem_modularLocalized red (εA ^ jWidth a) hmprod
    refine ⟨hmg', Ws23.SlopeLaw0.modularRedLocHom_mem_one red ⟨_, hmg'⟩, ?_⟩

    have hprodval : rlHom red ⟨_, hmprod⟩ = rlHom red ⟨_, hmH⟩ * (rlHom red ⟨_, hmw⟩)⁻¹ := by
      have : (⟨_, hmprod⟩ : ↥(CharPReduction.modularLocalized (1 * q) A.toSubring red)) = ⟨_, hmH⟩ * ⟨_, hmwinv⟩ :=
        Subtype.ext (by
          show ((gH * gw⁻¹ : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) = _
          rw [MulMemClass.coe_mul, IntermediateField.coe_inv]; rfl)
      rw [this, map_mul, rlHom_inv red ⟨hmw, (rlHom_ne_zero_iff red _).mp hw0⟩]
    have hprod0 : rlHom red ⟨_, hmprod⟩ ≠ 0 := by rw [hprodval]; exact mul_ne_zero hz0 (inv_ne_zero hw0)
    have hordprod : (charLGeomPlaceOfPoint k a).ord (rlHom red ⟨_, hmprod⟩) = 1 := by
      rw [hprodval, Place.ord_mul _ hz0 (inv_ne_zero hw0), ord_inv' _ hw0, hz1, hordw]; rfl
    have hsmulmem : (((((εA ^ jWidth a : ↥A) : AlgebraicClosure ℚ)) • (gH * gw⁻¹) : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ))
        ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red := smul_mem_modularLocalized red (εA ^ jWidth a) hmprod
    have heqg' : (⟨_, hmg'⟩ : ↥(CharPReduction.modularLocalized (1 * q) A.toSubring red)) = ⟨_, hsmulmem⟩ :=
      Subtype.ext (by
        show ((g' : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) = _
        rw [key]; push_cast; rfl)
    have hordsmul := ord_rlHom_smul red hker (charLGeomPlaceOfPoint k a) (εA ^ jWidth a) hεpowunit hmprod ((rlHom_ne_zero_iff red _).mp hprod0) hsmulmem
    have hne : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, hsmulmem⟩ ≠ 0 := by
      rw [modularRedLocHom_smul red (εA ^ jWidth a) hmprod hsmulmem]
      refine mul_ne_zero ((map_ne_zero _).mpr ?_) ((rlHom_ne_zero_iff red _).mp hprod0)
      intro h0
      exact hredε ((hker _).mpr ((IsLocalRing.mem_maximalIdeal _).mpr (fun hu => ((hker _).mp
        (show red (εA ^ jWidth a) = 0 from h0)) |> fun hm => (IsLocalRing.mem_maximalIdeal _).mp hm hεpowunit)))
    constructor
    · rw [heqg']; exact hne
    · rw [rlHom_eq red, heqg', hordsmul, hordprod]

end
end S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728
end P2MW
export P2MW.S_ModularCurve_gaussUnit_frickeInvolutionBar_and_ord_eq_one_of_crossingPresentation_of_eq_zero_or_eq_ofNat1728 (solution)
