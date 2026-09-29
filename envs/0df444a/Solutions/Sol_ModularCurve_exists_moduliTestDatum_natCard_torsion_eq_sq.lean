-- Prove2me | solution 1 for ModularCurve.exists_moduliTestDatum_natCard_torsion_eq_sq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/3119b945-54b9-51ee-9e04-5736b42c58ca

import Mathlib
import Definitions.Def_ModularCurve_ModuliPlace
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Definitions.Def_WeierstrassCurve_ReduceHom
import Definitions.Def_WeierstrassCurve_MapPoint
import Definitions.Def_ModularCurve_ModuliPointMap
import Theorems.Thm_ModularCurve_exists_equivariant_torsion_reduction_ofJ_forall_place_reduceHom
import Theorems.Thm_ModularCurve_exists_equiv_algHom_modularFunctionFieldFullC_forall_dvd_apply_jqNModC_eq_cyclicQuotientJ
import Theorems.Thm_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring
import Theorems.Thm_WeierstrassCurve_nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_cyclicQuotientJ_variableChange_eq
import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_add
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_moduliTestDatum_natCard_torsion_eq_sq
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 CyclotomicUniv.instCharZeroR₀ CyclotomicUniv.instIsDomain CyclotomicUniv.instIsDomainR₀ CyclotomicUniv.instCharZero ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup"
p2m_attr_erase "instance" "ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two"
p2m_attr_erase "simp" "compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.mem_zeroComponentSubgroup_iff AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd"
p2m_attr_erase "simp" "ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂"
p2m_attr_erase "simp" "PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm CyclotomicUniv.lift₀_ζ₀ CyclotomicUniv.lift_algebraMap CyclotomicUniv.val_ζUnit CyclotomicUniv.lift_ζ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero"
p2m_attr_erase "simp" "ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun"
p2m_attr_erase "simp" "KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero"

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing ValuationSubring AlgebraicCurve ModularCurve

open scoped IntermediateField

noncomputable section

namespace P2MKcIgusaDatumA

section PlaceOver

variable (K : Type*) [Field K] [IsAlgClosed K] {M : Type*} [Field M] [Algebra K M]

omit [IsAlgClosed K] in
lemma adjoin_toSubring_eq_closure (t : M) :
    (Algebra.adjoin K ({t} : Set M)).toSubring =
      Subring.closure (Set.range ((algebraMap K M).comp (⊤ : ValuationSubring K).subtype) ∪ {t}) := by
  have hr : Set.range ((algebraMap K M).comp (⊤ : ValuationSubring K).subtype) =
      Set.range (algebraMap K M) := by
    ext x; constructor
    · rintro ⟨a, rfl⟩; exact ⟨a, rfl⟩
    · rintro ⟨a, rfl⟩; exact ⟨⟨a, ValuationSubring.mem_top a⟩, rfl⟩
  rw [hr]
  ext x
  rw [Subalgebra.mem_toSubring, Algebra.mem_adjoin_iff]

lemma exists_place_ord_pos (t : M) (htr : Transcendental K t)
    [FiniteDimensional K⟮t⟯ M] [Algebra.IsSeparable K⟮t⟯ M]
    (j₀ : K) : ∃ W₀ : Place K M, 0 < W₀.ord (t - algebraMap K M j₀) := by
  let A : ValuationSubring K := ⊤
  let B : Subring M := (Algebra.adjoin K ({t} : Set M)).toSubring
  have hconst : ∀ a : A, algebraMap K M a ∈ B := fun a =>
    (Algebra.adjoin K ({t} : Set M)).algebraMap_mem a
  have htB : t ∈ B := Algebra.self_mem_adjoin_singleton K t
  have hint : ∀ b : B, IsIntegral
      (Subring.closure (Set.range ((algebraMap K M).comp A.subtype) ∪ {t})) (b : M) := by
    intro b
    have hb : (b : M) ∈ Subring.closure (Set.range ((algebraMap K M).comp A.subtype) ∪ {t}) := by
      rw [← adjoin_toSubring_eq_closure]; exact b.2
    exact isIntegral_algebraMap (A := M)
      (x := (⟨(b : M), hb⟩ : Subring.closure (Set.range ((algebraMap K M).comp A.subtype) ∪ {t})))
  let g : B := ⟨t, htB⟩ - ⟨algebraMap K M j₀, hconst ⟨j₀, ValuationSubring.mem_top j₀⟩⟩
  have hg : ¬ IsUnit g := by
    intro hu
    let e := Polynomial.algEquivOfTranscendental K t htr
    have hge : e (Polynomial.X - Polynomial.C j₀) = g := by
      apply Subtype.ext
      simp [e, g, Polynomial.algEquivOfTranscendental_apply]
    have : IsUnit (Polynomial.X - Polynomial.C j₀ : Polynomial K) := by
      rw [← hge] at hu
      exact (MulEquiv.isUnit_map e).mp hu
    exact Polynomial.not_isUnit_X_sub_C j₀ this
  obtain ⟨𝔮, h𝔮max, hg𝔮⟩ := Ideal.exists_le_maximal (Ideal.span {g}) (Ideal.span_singleton_ne_top hg)
  haveI : 𝔮.IsPrime := h𝔮max.isPrime
  have h𝔮A : ∀ a : A, a ∈ IsLocalRing.maximalIdeal A →
      (⟨algebraMap K M a, hconst a⟩ : B) ∈ 𝔮 := by
    intro a ha
    have ha0 : a = 0 := by
      by_contra hne
      apply (IsLocalRing.mem_maximalIdeal _).mp ha
      have hne' : (a : K) ≠ 0 := fun h => hne (Subtype.ext h)
      exact ⟨⟨a, ⟨(a : K)⁻¹, ValuationSubring.mem_top _⟩,
        Subtype.ext (mul_inv_cancel₀ hne'), Subtype.ext (inv_mul_cancel₀ hne')⟩, rfl⟩
    have : (⟨algebraMap K M a, hconst a⟩ : B) = 0 := by
      apply Subtype.ext; simp [ha0]
    rw [this]; exact 𝔮.zero_mem
  have hja : (⟨t, htB⟩ : B) - ⟨algebraMap K M ((⟨j₀, ValuationSubring.mem_top j₀⟩ : A) : K),
      hconst _⟩ ∈ 𝔮 := hg𝔮 (Ideal.mem_span_singleton_self g)
  obtain ⟨w, hw, -⟩ := AlgebraicCurve.Place.exists_of_isPrime_over_valuationSubring A htr hconst htB
    hint 𝔮 h𝔮A ⟨j₀, ValuationSubring.mem_top j₀⟩ hja
  exact ⟨w, hw⟩

end PlaceOver

section Torsion

variable {K : Type*} [Field K] [DecidableEq K]

lemma natCard_torsion_congr {V₁ V₂ : WeierstrassCurve K} (h : V₁ = V₂) (N : ℕ) :
    Nat.card {P : V₁.toAffine.Point // N • P = 0} =
      Nat.card {P : V₂.toAffine.Point // N • P = 0} := by
  subst h; rfl

lemma natCard_torsion_eq_sq [IsAlgClosed K] (E₀ : WeierstrassCurve K)
    [E₀.IsElliptic] {N : ℕ} (hN : (N : K) ≠ 0) :
    Nat.card {P : E₀.toAffine.Point // N • P = 0} = N ^ 2 := by
  obtain ⟨eK⟩ := WeierstrassCurve.nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed
    (K := K) E₀ hN
  have hbc : E₀.baseChange K = E₀ := by
    rw [WeierstrassCurve.baseChange, Algebra.algebraMap_self, WeierstrassCurve.map_id]
  rw [← natCard_torsion_congr hbc]
  have e2 : {P : (E₀.baseChange K).toAffine.Point // N • P = 0} ≃
      Submodule.torsionBy ℤ (E₀.baseChange K).toAffine.Point N :=
    Equiv.subtypeEquivRight fun P => by
      rw [Submodule.mem_torsionBy_iff, natCast_zsmul]
  rw [Nat.card_congr e2, ← Nat.card_congr eK.toEquiv, Nat.card_prod, Nat.card_zmod, sq]

end Torsion

section CastPt

variable {L : Type*} [Field L]

def castPt {V V' : WeierstrassCurve L} (h : V = V') (P : V.toAffine.Point) : V'.toAffine.Point :=
  cast (congrArg (fun U : WeierstrassCurve L => U.toAffine.Point) h) P

theorem castPt_heq {V V' : WeierstrassCurve L} (h : V = V') (P : V.toAffine.Point) :
    HEq (castPt h P) P := by
  subst h; rfl

variable [DecidableEq L]

theorem castPt_nsmul {V V' : WeierstrassCurve L} (h : V = V') (n : ℕ) (P : V.toAffine.Point) :
    castPt h (n • P) = n • castPt h P := by
  subst h; rfl

theorem addOrderOf_castPt {V V' : WeierstrassCurve L} (h : V = V') (P : V.toAffine.Point) :
    addOrderOf (castPt h P) = addOrderOf P := by
  subst h; rfl

theorem addOrderOf_eq_of_heq {V V' : WeierstrassCurve L} (h : V = V') {P : V.toAffine.Point}
    {Q : V'.toAffine.Point} (hPQ : HEq P Q) : addOrderOf P = addOrderOf Q := by
  subst h; rw [eq_of_heq hPQ]

end CastPt

section VC

variable {L : Type*} [Field L] [DecidableEq L] (C : VariableChange L) (V : WeierstrassCurve L)

def vcInvHom : V.toAffine.Point →+ (C • V).toAffine.Point where
  toFun := Point.vcInvFun C V.toAffine
  map_zero' := rfl
  map_add' := Point.vcInvFun_add C V.toAffine

theorem vcInvHom_apply (P : V.toAffine.Point) :
    vcInvHom C V P = Point.vcInvFun C V.toAffine P := rfl

theorem vcInvFun_injective : Function.Injective (Point.vcInvFun C V.toAffine) :=
  (Point.vcFun_rightInverse (C := C) (W := V.toAffine)).injective

theorem vcInvFun_nsmul (n : ℕ) (P : V.toAffine.Point) :
    Point.vcInvFun C V.toAffine (n • P) = n • Point.vcInvFun C V.toAffine P :=
  map_nsmul (vcInvHom C V) n P

theorem addOrderOf_vcInvFun (P : V.toAffine.Point) :
    addOrderOf (Point.vcInvFun C V.toAffine P) = addOrderOf P :=
  addOrderOf_injective (vcInvHom C V) (vcInvFun_injective C V) P

theorem mem_zmultiples_vcInvFun_iff (P : V.toAffine.Point) (Q : (C • V).toAffine.Point) :
    Q ∈ AddSubgroup.zmultiples (Point.vcInvFun C V.toAffine P) ↔
      Point.vcFun C V.toAffine Q ∈ AddSubgroup.zmultiples P := by
  rw [← vcInvHom_apply, ← AddMonoidHom.map_zmultiples, AddSubgroup.mem_map]
  constructor
  · rintro ⟨R, hR, hRQ⟩
    rw [vcInvHom_apply] at hRQ
    rw [← hRQ, Point.vcFun_rightInverse R]
    exact hR
  · intro h
    refine ⟨_, h, ?_⟩
    rw [vcInvHom_apply, Point.vcFun_leftInverse Q]

end VC

section CQJ

variable {L : Type*} [Field L] [DecidableEq L]

theorem cyclicQuotientJ_zmultiples_congr_heq {V V' : WeierstrassCurve L} (h : V = V')
    {P : V.toAffine.Point} {Q : V'.toAffine.Point} (hPQ : HEq P Q) (n : ℕ) :
    V.cyclicQuotientJ (AddSubgroup.zmultiples P) n =
      V'.cyclicQuotientJ (AddSubgroup.zmultiples Q) n := by
  subst h; rw [eq_of_heq hPQ]

omit [DecidableEq L] in

theorem cyclicQuotientJ_mapPoint_castPt {Ω : Type*} [Field Ω] [DecidableEq Ω]
    {V V' : WeierstrassCurve L} (h : V = V') (φ : L →+* Ω) (Q : V.toAffine.Point) (n : ℕ) :
    (V'.map φ).cyclicQuotientJ
        (AddSubgroup.zmultiples (WeierstrassCurve.mapPoint φ (castPt h Q))) n =
      (V.map φ).cyclicQuotientJ (AddSubgroup.zmultiples (WeierstrassCurve.mapPoint φ Q)) n := by
  subst h; rfl

theorem cyclicQuotientJ_zmultiples_vcInvFun (C : VariableChange L) (V : WeierstrassCurve L)
    (P : V.toAffine.Point) (n : ℕ) (hn : (n : L) ≠ 0) :
    (C • V).cyclicQuotientJ (AddSubgroup.zmultiples (Point.vcInvFun C V.toAffine P)) n =
      V.cyclicQuotientJ (AddSubgroup.zmultiples P) n :=
  WeierstrassCurve.cyclicQuotientJ_variableChange_eq C V _ _
    (fun Q => mem_zmultiples_vcInvFun_iff C V P Q) n hn

end CQJ

section MapPoint

universe a b c d

variable {S : Type b} [Field S] (W : WeierstrassCurve S) {A : Type c} {B : Type d}
  [Field A] [Field B] [DecidableEq A] [DecidableEq B] [Algebra S A] [Algebra S B] [Algebra A B]
  [IsScalarTower S A B]

omit [DecidableEq A] [DecidableEq B] in

theorem map_algebraMap_baseChange :
    (W.baseChange A).map (algebraMap A B) = W.baseChange B :=
  W.map_baseChange (IsScalarTower.toAlgHom S A B)

theorem mapPoint_heq_pointMap (P : (W.baseChange A).toAffine.Point) :
    HEq (WeierstrassCurve.mapPoint (algebraMap A B) (W₀ := W.baseChange A) P)
      (WeierstrassCurve.Affine.Point.map (IsScalarTower.toAlgHom S A B) P) := by
  have hc : (W.baseChange A).map (algebraMap A B) = W.baseChange B :=
    map_algebraMap_baseChange W
  cases P with
  | zero => exact WeierstrassCurve.Affine.Point.zero_heq_zero hc
  | some x y h =>
    rw [WeierstrassCurve.mapPoint_some, WeierstrassCurve.Affine.Point.map_some]
    exact WeierstrassCurve.Affine.Point.some_heq_some hc rfl rfl

end MapPoint

section TorsionTransport

variable {L : Type*} [Field L] [DecidableEq L]

theorem castPt_symm_castPt {V V' : WeierstrassCurve L} (h : V = V') (P : V.toAffine.Point) :
    castPt h.symm (castPt h P) = P := by
  subst h; rfl

theorem castPt_castPt_symm {V V' : WeierstrassCurve L} (h : V = V') (P : V'.toAffine.Point) :
    castPt h (castPt h.symm P) = P := by
  subst h; rfl

theorem castPt_injective {V V' : WeierstrassCurve L} (h : V = V') :
    Function.Injective (castPt h) := by
  subst h; exact fun _ _ h => h

theorem castPt_zero' {V V' : WeierstrassCurve L} (h : V = V') : castPt h (0 : V.toAffine.Point) = 0 := by
  subst h; rfl

theorem natCard_torsion_transport (κ₀ : VariableChange L) (E W₁ : WeierstrassCurve L)
    (h1 : κ₀ • E = W₁) (n : ℕ) :
    Nat.card {P : W₁.toAffine.Point // n • P = 0} = Nat.card {P : E.toAffine.Point // n • P = 0} := by
  symm
  refine Nat.card_congr ?_
  refine Equiv.ofBijective
    (fun P => ⟨castPt h1 (Point.vcInvFun κ₀ E.toAffine P.1), by
      rw [← castPt_nsmul, ← vcInvFun_nsmul, P.2, Point.vcInvFun_zero, castPt_zero']⟩) ⟨?_, ?_⟩
  · intro P P' h
    have h' := congrArg Subtype.val h
    exact Subtype.ext (vcInvFun_injective κ₀ E (castPt_injective h1 h'))
  · rintro ⟨P₁, hP₁⟩
    refine ⟨⟨Point.vcFun κ₀ E.toAffine (castPt h1.symm P₁), ?_⟩, ?_⟩
    · apply vcInvFun_injective κ₀ E
      apply castPt_injective h1
      rw [vcInvFun_nsmul, castPt_nsmul, Point.vcFun_leftInverse, castPt_castPt_symm, hP₁,
        Point.vcInvFun_zero, castPt_zero']
    · apply Subtype.ext
      show castPt h1 (Point.vcInvFun κ₀ E.toAffine (Point.vcFun κ₀ E.toAffine (castPt h1.symm P₁))) = P₁
      rw [Point.vcFun_leftInverse, castPt_castPt_symm]

theorem natCard_torsion_of_dvd {F : Type*} [Field F] [DecidableEq F] (V : WeierstrassCurve F)
    [V.IsElliptic] {N n : ℕ} (hN : (N : F) ≠ 0) (hn : n ∣ N)
    (hcard : Nat.card {P : V.toAffine.Point // N • P = 0} = N ^ 2) :
    Nat.card {P : V.toAffine.Point // n • P = 0} = n ^ 2 := by
  classical
  have hN0 : N ≠ 0 := by rintro rfl; exact hN Nat.cast_zero
  set Fb := AlgebraicClosure F with hFb
  set ι : F →+* Fb := algebraMap F Fb with hι
  set Vb : WeierstrassCurve Fb := V.map ι with hVb
  have hNb : (N : Fb) ≠ 0 := by rw [← map_natCast ι, map_ne_zero]; exact hN
  have hnb : (n : Fb) ≠ 0 := by
    obtain ⟨c, hc⟩ := hn
    intro h0; apply hNb; rw [hc, Nat.cast_mul, h0, zero_mul]

  have hcardN : Nat.card {P : Vb.toAffine.Point // N • P = 0} = N ^ 2 := natCard_torsion_eq_sq Vb hNb
  have hcardn : Nat.card {P : Vb.toAffine.Point // n • P = 0} = n ^ 2 := natCard_torsion_eq_sq Vb hnb

  let f : {P : V.toAffine.Point // N • P = 0} → {P : Vb.toAffine.Point // N • P = 0} :=
    fun P => ⟨WeierstrassCurve.mapPoint ι P.1, by
      rw [← WeierstrassCurve.mapPoint_nsmul, P.2, WeierstrassCurve.mapPoint_zero]⟩
  have hf : Function.Injective f := by
    intro P P' h
    exact Subtype.ext (WeierstrassCurve.mapPoint_injective ι (congrArg Subtype.val h))
  haveI : Finite {P : Vb.toAffine.Point // N • P = 0} :=
    Nat.finite_of_card_ne_zero (by rw [hcardN]; exact pow_ne_zero _ hN0)
  have hbij : Function.Bijective f := hf.bijective_of_nat_card_le (by rw [hcardN, hcard])

  rw [← hcardn]
  refine Nat.card_congr (Equiv.ofBijective
    (fun P => ⟨WeierstrassCurve.mapPoint ι P.1, by
      rw [← WeierstrassCurve.mapPoint_nsmul, P.2, WeierstrassCurve.mapPoint_zero]⟩) ⟨?_, ?_⟩)
  · intro P P' h
    exact Subtype.ext (WeierstrassCurve.mapPoint_injective ι (congrArg Subtype.val h))
  · rintro ⟨R, hR⟩
    obtain ⟨c, hc⟩ := hn
    have hRN : N • R = 0 := by rw [hc, mul_nsmul, hR, nsmul_zero]
    obtain ⟨⟨P, hPN⟩, hP⟩ := hbij.2 ⟨R, hRN⟩
    have hPR : WeierstrassCurve.mapPoint ι P = R := congrArg Subtype.val hP
    refine ⟨⟨P, ?_⟩, Subtype.ext hPR⟩
    apply WeierstrassCurve.mapPoint_injective ι
    rw [WeierstrassCurve.mapPoint_nsmul, hPR, hR, WeierstrassCurve.mapPoint_zero]

end TorsionTransport

section Main

universe u

theorem exists_datum_mk (K : Type u) [Field K] [IsAlgClosed K] [DecidableEq K]
    (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0)
    (E₀ : WeierstrassCurve K) [hE₀ : E₀.IsElliptic] (g₀ : E₀.toAffine.Point)
    (hg₀ : addOrderOf g₀ = N) :
    ∃ (Ω : Type u) (_ : Field Ω) (_ : DecidableEq Ω) (_ : Algebra K Ω)
      (D : ModuliTestDatum K N (Quot.mk _ (⟨E₀, hE₀, g₀, hg₀⟩ : Gamma0Pair N K)) Ω),
      (∀ n : ℕ, n ∣ N →
        Nat.card {P : (D.curve.map D.W.toValuationSubring.subtype).toAffine.Point // n • P = 0}
          = n ^ 2) ∧
      ∀ [DecidableEq (IsLocalRing.ResidueField D.W.toValuationSubring)]
        (P : (D.curve.map D.W.toValuationSubring.subtype).toAffine.Point),
        N • P = 0 → reduceHom D.map_Δ_ne_zero P = 0 → P = 0 := by
  obtain ⟨p, hpK⟩ := CharP.exists K
  have hN0 : N ≠ 0 := NeZero.ne N
  have hpN : ¬ p ∣ N := by
    rintro ⟨k, rfl⟩
    apply hN
    rw [Nat.cast_mul, CharP.cast_eq_zero K p, zero_mul]

  obtain ⟨M, iF, iD, iA, t, htr, hfd, hgal, hcard, hall⟩ :=
    ModularCurve.exists_equivariant_torsion_reduction_ofJ_forall_place_reduceHom K p N hN

  obtain ⟨W₀, hW₀⟩ := exists_place_ord_pos K t htr E₀.j
  letI iR := Classical.decEq (ResidueField W₀.toValuationSubring)
  obtain ⟨WA, κ₀, e, γ₀, hΔ, θ, ρ, h1, -, h3, h4, h5, h6, h7, -, -, -, -, -⟩ :=
    hall E₀.j E₀ rfl W₀ hW₀

  have hsurj : ∀ Q : E₀.toAffine.Point, N • Q = 0 →
      ∃ P : ((WeierstrassCurve.ofJ
        (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange M).toAffine.Point,
        N • P = 0 ∧ θ P = Q := by
    intro Q hQ
    let f : {P : ((WeierstrassCurve.ofJ
        (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange M).toAffine.Point //
          N • P = 0} → {Q : E₀.toAffine.Point // N • Q = 0} :=
      fun P => ⟨θ P.1, by rw [← _root_.map_nsmul, P.2, _root_.map_zero]⟩
    have hf_val : ∀ P, (f P).1 = θ P.1 := fun P => rfl
    have hf : Function.Injective f := by
      intro P P' h
      have h' : θ P.1 = θ P'.1 := by rw [← hf_val, ← hf_val, h]
      apply Subtype.ext
      have hsub : P.1 - P'.1 = 0 :=
        h7 N (P.1 - P'.1) hpN (by rw [nsmul_sub, P.2, P'.2, sub_zero])
          (by rw [_root_.map_sub, h', sub_self])
      exact sub_eq_zero.mp hsub
    have hT₀ : Nat.card {Q : E₀.toAffine.Point // N • Q = 0} = N ^ 2 :=
      natCard_torsion_eq_sq E₀ hN
    haveI : Finite {Q : E₀.toAffine.Point // N • Q = 0} :=
      Nat.finite_of_card_ne_zero (by rw [hT₀]; exact pow_ne_zero _ hN0)
    have hbij : Function.Bijective f := hf.bijective_of_nat_card_le (by rw [hT₀, hcard])
    obtain ⟨P, hP⟩ := hbij.2 ⟨Q, hQ⟩
    exact ⟨P.1, P.2, by rw [← hf_val, hP]⟩

  obtain ⟨P, hPN, hθP⟩ := hsurj g₀ (by rw [← hg₀]; exact addOrderOf_nsmul_eq_zero g₀)
  have hPord : addOrderOf P = N := by
    refine Nat.dvd_antisymm (addOrderOf_dvd_iff_nsmul_eq_zero.mpr hPN) ?_
    have h := addOrderOf_map_dvd θ P
    rwa [hθP, hg₀] at h

  let gen : (WA.map W₀.toValuationSubring.subtype).toAffine.Point :=
    castPt h1 (Point.vcInvFun κ₀ _ P)
  have hgen_heq : HEq (Point.vcInvFun κ₀ ((WeierstrassCurve.ofJ
      (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange M).toAffine P) gen :=
    (castPt_heq h1 _).symm
  have hgen_ord : addOrderOf gen = N := by
    rw [addOrderOf_castPt, addOrderOf_vcInvFun, hPord]

  have hstar : HEq (Point.vcInvFun γ₀
      ((WA.map (residue W₀.toValuationSubring)).map e.toRingHom).toAffine
        (WeierstrassCurve.mapPoint e.toRingHom (reduceHom hΔ gen))) (θ P) := by
    rcases hred : reduceHom hΔ gen with _ | ⟨x, y, hxy⟩
    · rw [h5 P gen hgen_heq hred]
      exact ModularCurve.Point.heq_zero h4
    · obtain ⟨h', hθ⟩ := h6 P gen x y hxy hgen_heq hred
      rw [hθ]
      exact ModularCurve.Point.heq_some h4 rfl rfl
  have hord : addOrderOf (reduceHom hΔ gen) = N := by
    rw [← WeierstrassCurve.addOrderOf_mapPoint e.toRingHom, ← addOrderOf_vcInvFun γ₀,
      addOrderOf_eq_of_heq h4 hstar, hθP, hg₀]

  have hclass : ModuliPoint.map e.toRingHom
      (Quot.mk _ (⟨WA.map (residue W₀.toValuationSubring),
        ⟨isUnit_iff_ne_zero.mpr hΔ⟩, reduceHom hΔ gen, hord⟩ :
          Gamma0Pair N (ResidueField W₀.toValuationSubring))) =
      Quot.mk _ (⟨E₀, hE₀, g₀, hg₀⟩ : Gamma0Pair N K) := by
    rw [ModuliPoint.map_mk]
    refine Quot.sound ⟨γ₀, h4, 1, Nat.coprime_one_left N, ?_⟩
    rw [one_nsmul]
    exact (hstar.trans (heq_of_eq hθP)).symm

  have hjt : Transcendental K (WeierstrassCurve.ofJ
      (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).j := by
    rw [WeierstrassCurve.ofJ_j]
    exact (transcendental_algebraMap_iff (R := K) (A := M)
      (algebraMap K⟮t⟯ M).injective).mp htr
  obtain ⟨Φ, -, hval⟩ :=
    ModularCurve.exists_equiv_algHom_modularFunctionFieldFullC_forall_dvd_apply_jqNModC_eq_cyclicQuotientJ
      K N hN K⟮t⟯ M (WeierstrassCurve.ofJ
        (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)) hjt hcard
  let H : {H : AddSubgroup ((WeierstrassCurve.ofJ
      (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange M).toAffine.Point //
        IsAddCyclic H ∧ Nat.card H = N} :=
    ⟨AddSubgroup.zmultiples P, AddSubgroup.isAddCyclic_zmultiples P,
      (Nat.card_zmultiples P).trans hPord⟩

  have hpins : ∀ (Ω' : Type u) [Field Ω'] [DecidableEq Ω'] [IsAlgClosed Ω'] [Algebra M Ω']
      (d : ℕ) [NeZero d] (hd : d ∣ N),
      algebraMap M Ω' ((Φ H).1 (jqNFull K N d hd)) =
        (((WA.map W₀.toValuationSubring.subtype).map (algebraMap M Ω')).cyclicQuotientJ
          (AddSubgroup.zmultiples
            (WeierstrassCurve.mapPoint (algebraMap M Ω') ((N / d) • gen))) d) := by
    intro Ω' _ _ _ _ d _ hd
    have hd0 : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
    have hq : 0 < N / d := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hN0) hd) hd0
    have hNM : (N : M) ≠ 0 := by
      rw [← map_natCast (algebraMap K M)]
      exact (map_ne_zero _).mpr hN
    have hdM : (d : M) ≠ 0 := by
      obtain ⟨c, hc⟩ := hd
      intro h0
      apply hNM
      rw [hc, Nat.cast_mul, h0, zero_mul]
    have hdΩ : (d : Ω') ≠ 0 := by
      rw [← map_natCast (algebraMap M Ω')]
      exact (map_ne_zero _).mpr hdM
    have hd' : addOrderOf ((N / d) • P) = d := by
      rw [addOrderOf_nsmul' _ hq.ne', hPord, Nat.gcd_eq_right (Nat.div_dvd_of_dvd hd),
        Nat.div_div_self hd hN0]
    let H' : {H' : AddSubgroup ((WeierstrassCurve.ofJ
        (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange M).toAffine.Point //
          IsAddCyclic H' ∧ Nat.card H' = d} :=
      ⟨AddSubgroup.zmultiples ((N / d) • P), AddSubgroup.isAddCyclic_zmultiples _,
        (Nat.card_zmultiples _).trans hd'⟩
    have hle : H'.1 ≤ H.1 :=
      AddSubgroup.zmultiples_le_of_mem (AddSubgroup.nsmul_mem _ (AddSubgroup.mem_zmultiples P) _)
    have hv := hval Ω' H d hd H' hle
    change algebraMap M Ω' ((Φ H).1 ⟨jqNModC K d, jqModCd_mem_full K N hd⟩) = _
    rw [hv]
    change ((WeierstrassCurve.ofJ
        (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange Ω').cyclicQuotientJ
        ((AddSubgroup.zmultiples ((N / d) • P)).map
          (WeierstrassCurve.Affine.Point.map (IsScalarTower.toAlgHom K⟮t⟯ M Ω'))) d = _
    rw [AddMonoidHom.map_zmultiples]
    symm
    have hgen' : (N / d) • gen = castPt h1 (Point.vcInvFun κ₀ _ ((N / d) • P)) := by
      rw [vcInvFun_nsmul, castPt_nsmul]
    calc ((WA.map W₀.toValuationSubring.subtype).map (algebraMap M Ω')).cyclicQuotientJ
          (AddSubgroup.zmultiples (WeierstrassCurve.mapPoint (algebraMap M Ω') ((N / d) • gen))) d
        = ((κ₀ • (WeierstrassCurve.ofJ
            (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange M).map
              (algebraMap M Ω')).cyclicQuotientJ
            (AddSubgroup.zmultiples (WeierstrassCurve.mapPoint (algebraMap M Ω')
              (Point.vcInvFun κ₀ _ ((N / d) • P)))) d := by
          rw [hgen']
          exact cyclicQuotientJ_mapPoint_castPt h1 _ _ _
      _ = ((κ₀.map (algebraMap M Ω')) • ((WeierstrassCurve.ofJ
            (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange M).map
              (algebraMap M Ω')).cyclicQuotientJ
            (AddSubgroup.zmultiples (Point.vcInvFun (κ₀.map (algebraMap M Ω')) _
              (WeierstrassCurve.mapPoint (algebraMap M Ω') ((N / d) • P)))) d :=
          cyclicQuotientJ_zmultiples_congr_heq (WeierstrassCurve.map_variableChange _ κ₀ _).symm
            (ModularCurve.mapPoint_vcInvFun_heq (algebraMap M Ω') κ₀ _ _) d
      _ = (((WeierstrassCurve.ofJ
            (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange M).map
              (algebraMap M Ω')).cyclicQuotientJ
            (AddSubgroup.zmultiples (WeierstrassCurve.mapPoint (algebraMap M Ω') ((N / d) • P))) d :=
          cyclicQuotientJ_zmultiples_vcInvFun _ _ _ d hdΩ
      _ = ((WeierstrassCurve.ofJ
            (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange Ω').cyclicQuotientJ
            (AddSubgroup.zmultiples (WeierstrassCurve.Affine.Point.map
              (IsScalarTower.toAlgHom K⟮t⟯ M Ω') ((N / d) • P))) d :=
          cyclicQuotientJ_zmultiples_congr_heq
            (map_algebraMap_baseChange (A := M) (B := Ω') (WeierstrassCurve.ofJ
              (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)))
            (mapPoint_heq_pointMap (A := M) (B := Ω') (WeierstrassCurve.ofJ
              (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)) ((N / d) • P)) d

  let D : ModuliTestDatum K N (Quot.mk _ (⟨E₀, hE₀, g₀, hg₀⟩ : Gamma0Pair N K)) M :=
    { W := W₀
      curve := WA
      map_Δ_ne_zero := hΔ
      gen := gen
      addOrderOf_gen := hgen_ord
      res := e.toRingHom
      res_algebraMap := h3
      reduction := ⟨hord, hclass⟩
      emb := (Φ H).1
      emb_jqNFull := hpins }

  have hNM : (N : M) ≠ 0 := by
    rw [← map_natCast (algebraMap K M)]
    exact (map_ne_zero _).mpr hN
  refine ⟨M, iF, iD, iA, D, fun n hn => ?_, ?_⟩
  ·
    show Nat.card {P₁ : (WA.map W₀.toValuationSubring.subtype).toAffine.Point // n • P₁ = 0} = n ^ 2
    rw [natCard_torsion_transport κ₀ _ _ h1 n]
    haveI : ((WeierstrassCurve.ofJ
        (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange M).IsElliptic :=
      (inferInstance : ((WeierstrassCurve.ofJ
        (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).map (algebraMap K⟮t⟯ M)).IsElliptic)
    exact natCard_torsion_of_dvd _ hNM hn hcard
  ·
    intro inst P₁ hP₁ hred
    show P₁ = 0

    have hinst : inst = iR := Subsingleton.elim _ _
    subst hinst

    set Q := Point.vcFun κ₀ ((WeierstrassCurve.ofJ
        (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange M).toAffine
        (castPt h1.symm P₁) with hQ
    have hQP : castPt h1 (Point.vcInvFun κ₀ _ Q) = P₁ := by
      rw [hQ, Point.vcFun_leftInverse, castPt_castPt_symm]
    have hQheq : HEq (Point.vcInvFun κ₀ ((WeierstrassCurve.ofJ
        (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)).baseChange M).toAffine Q) P₁ := by
      rw [← hQP]; exact (castPt_heq h1 _).symm
    have hNQ : N • Q = 0 := by
      apply vcInvFun_injective κ₀
      apply castPt_injective h1
      rw [vcInvFun_nsmul, castPt_nsmul, hQP, hP₁, Point.vcInvFun_zero, castPt_zero']
    have hθQ : θ Q = 0 := h5 Q P₁ hQheq hred
    have hQ0 : Q = 0 := h7 N Q hpN hNQ hθQ
    rw [← hQP, hQ0, Point.vcInvFun_zero, castPt_zero']

end Main

end P2MKcIgusaDatumA

end

universe u in
theorem solution
    (K : Type u) [Field K] [IsAlgClosed K] [DecidableEq K] (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0)
    (x : ModuliPoint N K) :
    ∃ (Ω : Type u) (_ : Field Ω) (_ : DecidableEq Ω) (_ : Algebra K Ω) (D : ModuliTestDatum K N x Ω),
      (∀ n : ℕ, n ∣ N →
        Nat.card {P : (D.curve.map D.W.toValuationSubring.subtype).toAffine.Point // n • P = 0}
          = n ^ 2) ∧
      ∀ [DecidableEq (IsLocalRing.ResidueField D.W.toValuationSubring)]
        (P : (D.curve.map D.W.toValuationSubring.subtype).toAffine.Point),
        N • P = 0 → reduceHom D.map_Δ_ne_zero P = 0 → P = 0 := by
  induction x using Quot.ind with
  | _ P =>
    obtain ⟨E₀, hE₀, g₀, hg₀⟩ := P
    exact P2MKcIgusaDatumA.exists_datum_mk K N hN E₀ g₀ hg₀

end S_ModularCurve_exists_moduliTestDatum_natCard_torsion_eq_sq
end P2MW
export P2MW.S_ModularCurve_exists_moduliTestDatum_natCard_torsion_eq_sq (solution)
