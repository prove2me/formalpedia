-- Prove2me | solution 1 for ModularCurve.exists_hasValue_frobNodePair_of_mem_ssJSet_of_pow_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/5e652713-eb43-5081-9f93-adb58c6a11e5

import Mathlib
import Definitions.Def_ModularCurve_NodeLocalized
import Definitions.Def_ModularCurve_SupersingularNodes
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_CuspidalClass
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Theorems.Thm_ModularCurve_CharPReduction_modularRedLocHom_mem
import Theorems.Thm_ModularCurve_exists_hasValue_frobNodePair_of_isIntegral_modularLocalizedAtPoint_of_pow_eq
import Theorems.Thm_ModularCurve_isIntegral_modularLocalizedAtPoint_of_forall_ord_nonneg
import Theorems.Thm_ModularCurve_modularFunctionFieldC_self_collapse_unconditional
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_hasValue_frobNodePair_of_mem_ssJSet_of_pow_eq
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe"
p2m_attr_erase "simp" "ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄"
p2m_attr_erase "simp" "ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero"
p2m_attr_erase "simp" "TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar"
p2m_attr_erase "simp" "ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.NodeLocalized.coe_modularEvalAt ModularCurve.ProjectiveLine.map_mk ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.qExpandAlgHomC_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

set_option autoImplicit false

p2m_open "AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_exists_hasValue_frobNodePair_of_mem_ssJSet_of_pow_eq.ModularCurve"

namespace ModularCurve p2m_export "ModularCurve" "CharPReduction.redKer CharPReduction.notMem_redKer_iff CharPReduction.redRes_ne_zero_of_notMem CharPReduction.redLoc_spec CharPReduction.modularRing CharPReduction.modularRing_le_integralCoeffs CharPReduction.modularLocalized CharPReduction.modularRedLocHom coeffEmb coeffEmb_mem_laurentBaseChange jqModC jqNModC modularFunctionFieldC qExpand qExpand_congr jq jq_mem jqd_mem_full modularFunctionField_le_full frobNodePair ssJSet frickeInvolutionBar modularFunctionFieldBar CharPReduction.modularRedLocHom_mem exists_hasValue_frobNodePair_of_isIntegral_modularLocalizedAtPoint_of_pow_eq isIntegral_modularLocalizedAtPoint_of_forall_ord_nonneg modularFunctionFieldC_self_collapse_unconditional" end ModularCurve
p2m_open_scoped "ModularCurve" in

theorem ModularCurve.solution_aux_mem {q : ℕ} [Fact q.Prime] {L : Type*} [CommRing L] (B : Subring L)
    {k : Type*} [Field k] [CharP k q] (red' : B →+* k)
    (x : CharPReduction.modularLocalized (1 * q) B red') : CharPReduction.modularRedLocHom (1 * q) B red' x ∈ modularFunctionFieldC k 1 := by
  have h := CharPReduction.modularRedLocHom_mem B red' (1 * q) x
  have e : modularFunctionFieldC k (1 * q) = modularFunctionFieldC k 1 := by
    rw [← modularFunctionFieldC_self_collapse_unconditional k (ℓ := q)]
    show IntermediateField.adjoin k {jqModC k, jqNModC k (1 * q)} = IntermediateField.adjoin k {jqModC k, jqNModC k q}
    rw [show jqNModC k (1 * q) = jqNModC k q from qExpand_congr (one_mul q) _]
  rw [e] at h; exact h

p2m_open_scoped "ModularCurve" in

theorem ModularCurve.solution_aux_inv_mem {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] (red : A →+* k) {g : LaurentSeries (AlgebraicClosure ℚ)}
    (h : g ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red)
    (h0 : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h⟩ ≠ 0) :
    ∃ h' : g⁻¹ ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red,
      CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h⟩
        * CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h'⟩ = 1 := by
  obtain ⟨r, s, hs, hgs⟩ := h

  have hspec := CharPReduction.redLoc_spec (A := A.toSubring) (red := red) (R := CharPReduction.modularRing (1 * q) A.toSubring)
    (hR := CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring) ⟨g, ⟨r, s, hs, hgs⟩⟩ (r := r) (s := s) hgs
  have hr : r ∉ CharPReduction.redKer A.toSubring red (CharPReduction.modularRing (1 * q) A.toSubring)
      (CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring) := by
    rw [CharPReduction.notMem_redKer_iff]
    intro hr0
    rw [hr0, mul_eq_zero] at hspec
    rcases hspec with h1 | h1
    · exact h0 h1
    · exact (CharPReduction.redRes_ne_zero_of_notMem (A := A.toSubring) (red := red) hs) h1
  have hg0 : g ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hgs
    apply (CharPReduction.notMem_redKer_iff _ _ _ _).mp hr
    have : (r : LaurentSeries (AlgebraicClosure ℚ)) = 0 := hgs.symm
    rw [show r = 0 from Subtype.ext this, map_zero]
  have h' : g⁻¹ ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red :=
    ⟨s, r, hr, by rw [← hgs, ← mul_assoc, inv_mul_cancel₀ hg0, one_mul]⟩
  refine ⟨h', ?_⟩
  rw [← map_mul]
  have : (⟨g, ⟨r, s, hs, hgs⟩⟩ * ⟨g⁻¹, h'⟩ : CharPReduction.modularLocalized (1 * q) A.toSubring red) = 1 :=
    Subtype.ext (mul_inv_cancel₀ hg0)
  rw [this, map_one]

p2m_open_scoped "ModularCurve" in

theorem ModularCurve.solution_aux_ord_pos {k F : Type*} [Field k] [Field F] [Algebra k F] {v : Place k F} {g : F}
    (hg : g ≠ 0) (h : v.HasValue g 0) : 0 < v.ord g := by
  obtain ⟨hmem, hres⟩ := h
  rw [map_zero, IsLocalRing.residue_eq_zero_iff, v.mem_maximalIdeal_iff_adicValuation_lt_one ⟨g, hmem⟩] at hres
  have hne : v.ord g ≠ 0 := fun h0 => by
    have := (v.ord_eq_zero_iff_adicValuation_eq_one hg).mp h0
    exact (lt_irrefl _) (this ▸ hres)

  have hnn : 0 ≤ v.ord g := by
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨g, hmem⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hg) hπ
    have hcoe : g = ((u : v.toValuationSubring) : F) * ((π : F) ^ (n : ℤ)) := by
      have h := congrArg (Subtype.val) hu
      push_cast at h
      rw [zpow_natCast]; exact h
    rw [hcoe, v.ord_unit_smul_zpow u hπ (n : ℤ)]
    exact Int.natCast_nonneg n
  omega

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [DecidableEq k] (red : A →+* k)
    (f : ↥(modularFunctionFieldBar (1 * q)))
    (h₁ : (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red)
    (h₁F : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩ ∈ modularFunctionFieldC k 1) (h₁0 : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩ ≠ 0)
    (h₂ : ((frickeInvolutionBar (1 * q) f : modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red)
    (h₂F : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₂⟩ ∈ modularFunctionFieldC k 1) (h₂0 : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₂⟩ ≠ 0)
    (a : k) (ha : a ∈ ssJSet q k) (ha2 : a ^ (q ^ 2) = a)
    (hsupp : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), W.ord f ≠ 0 →
      ¬ ((∃ x : A, red x = a ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
         (∃ y : A, red y = a ^ q ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ))))) :
    ∃ c : k, c ≠ 0 ∧
      (frobNodePair q a).1.HasValue (⟨_, h₁F⟩ : modularFunctionFieldC k 1) c ∧
      (frobNodePair q a).2.HasValue (⟨_, h₂F⟩ : modularFunctionFieldC k 1) c := by
  have hint := ModularCurve.isIntegral_modularLocalizedAtPoint_of_forall_ord_nonneg red a f h₁ h₂
    (fun W hW => hsupp W hW.ne)
  obtain ⟨c, hc₁, hc₂⟩ := ModularCurve.exists_hasValue_frobNodePair_of_isIntegral_modularLocalizedAtPoint_of_pow_eq
    red a ha ha2 f hint h₁ h₁F h₂ h₂F
  obtain ⟨h₁', hinv₁⟩ := ModularCurve.solution_aux_inv_mem red h₁ h₁0
  obtain ⟨h₂', hinv₂⟩ := ModularCurve.solution_aux_inv_mem red h₂ h₂0
  have hcoe₁ : ((f⁻¹ : modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ))
      = ((f : modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ))⁻¹ := by
    push_cast; rfl
  have hcoe₂ : ((frickeInvolutionBar (1 * q) f⁻¹ : modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ))
      = ((frickeInvolutionBar (1 * q) f : modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ))⁻¹ := by
    rw [map_inv₀]; push_cast; rfl
  have h₁'' : ((f⁻¹ : modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ))
      ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red := hcoe₁ ▸ h₁'
  have h₂'' : ((frickeInvolutionBar (1 * q) f⁻¹ : modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ))
      ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red := hcoe₂ ▸ h₂'
  have hint' := ModularCurve.isIntegral_modularLocalizedAtPoint_of_forall_ord_nonneg red a f⁻¹ h₁'' h₂''
    (fun W hW => hsupp W (by rw [Place.ord_inv] at hW; omega))
  have h₁F' := ModularCurve.solution_aux_mem A.toSubring red ⟨_, h₁''⟩
  have h₂F' := ModularCurve.solution_aux_mem A.toSubring red ⟨_, h₂''⟩
  obtain ⟨c', hc₁', -⟩ := ModularCurve.exists_hasValue_frobNodePair_of_isIntegral_modularLocalizedAtPoint_of_pow_eq
    red a ha ha2 f⁻¹ hint' h₁'' h₁F' h₂'' h₂F'
  have hprod : (⟨_, h₁F⟩ : modularFunctionFieldC k 1) * ⟨_, h₁F'⟩ = 1 := by
    apply Subtype.ext
    show CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩
        * CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁''⟩ = 1
    have e : (⟨_, h₁''⟩ : CharPReduction.modularLocalized (1 * q) A.toSubring red) = ⟨_, h₁'⟩ := Subtype.ext hcoe₁
    rw [e]; exact hinv₁
  have hone := hc₁.mul hc₁'
  rw [hprod] at hone
  have hcc : c * c' = 1 := hone.unique (frobNodePair q a).1.hasValue_one
  exact ⟨c, left_ne_zero_of_mul_eq_one hcc, hc₁, hc₂⟩

end S_ModularCurve_exists_hasValue_frobNodePair_of_mem_ssJSet_of_pow_eq
end P2MW
export P2MW.S_ModularCurve_exists_hasValue_frobNodePair_of_mem_ssJSet_of_pow_eq (solution)
