-- Prove2me | solution 1 for ModularCurve.ramificationIndexAlong_mul_placeWidth_eq_placeWidth_restrictAlong
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/dceffcb4-1191-5b9a-aa3d-fce5c7842070

import Mathlib
import Definitions.Def_ModularCurve_PlaceWidth
import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_ModularCurve_placeRamificationJ_mul_jWidth_evalAt_jNGeomGen_eq
import Theorems.Thm_ModularCurve_charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_heckeAlphaCIntegral_unconditional
import Theorems.Thm_AlgebraicCurve_Place_evalAt_algebraMap_eq_evalAt_restrict
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldC_of_perfectField
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Theorems.Thm_AlgebraicCurve_Place_evalAt_algebraMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ramificationIndexAlong_mul_placeWidth_eq_placeWidth_restrictAlong
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular WeierstrassCurve.Affine.instIsDiscreteValuationRingSubtypeFunctionFieldMemValuationSubringValuationSubringWithZeroMultiplicativeIntValuationInfty WeierstrassCurve.Affine.valuationInfty_isNontrivial WeierstrassCurve.veluQuotient2_isShortNF WeierstrassCurve.instIsShortNFMk AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec"
p2m_attr_erase "simp" "compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.veluX_empty WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluPointMap2_zero"
p2m_attr_erase "simp" "WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero"
p2m_attr_erase "simp" "TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar"
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

open AlgebraicCurve ModularCurve

namespace FltWs24
namespace Width

variable {k : Type*} [Field k] [IsAlgClosed k]

theorem isRational_C (N : ℕ) [NeZero N] (x : Place k ↥(modularFunctionFieldC k N)) : x.IsRational := by
  haveI := isCurveOver_modularFunctionFieldC_of_perfectField k N
  exact (Place.isRational_iff_deg_eq_one x).2 (IsCurveOver.deg_eq_one_of_isAlgClosed x)

theorem mem_iff_mem_restrictAlong {F F' : Type*} [Field F] [Field F'] [Algebra k F] [Algebra k F']
    (φ : F →ₐ[k] F') (hφ : φ.toRingHom.IsIntegral) (P : Place k F') (g : F) (hg : g ≠ 0)
    (he : 0 < Place.ramificationIndexAlong φ P) :
    φ g ∈ P.toValuationSubring ↔ g ∈ (P.restrictAlong φ hφ).toValuationSubring := by
  have hφg : φ g ≠ 0 := (map_ne_zero φ).mpr hg
  rw [Place.mem_iff_ord_nonneg _ hφg, Place.mem_iff_ord_nonneg _ hg, Place.ord_restrictAlong φ hφ P g]
  constructor
  · intro h
    by_contra hneg
    push Not at hneg
    have : (Place.ramificationIndexAlong φ P : ℤ) * (P.restrictAlong φ hφ).ord g < 0 :=
      mul_neg_of_pos_of_neg (by exact_mod_cast he) hneg
    omega
  · intro h
    exact mul_nonneg (by positivity) h

theorem evalAt_along (N : ℕ) [NeZero N] {F' : Type*} [Field F'] [Algebra k F']
    (φ : ↥(modularFunctionFieldC k N) →ₐ[k] F') (hφ : φ.toRingHom.IsIntegral)
    (P : Place k F') (g : ↥(modularFunctionFieldC k N))
    (he : 0 < Place.ramificationIndexAlong φ P) :
    P.evalAt (φ g) = (P.restrictAlong φ hφ).evalAt g := by
  rcases eq_or_ne g 0 with rfl | hg
  · rw [map_zero, show (0 : F') = algebraMap k _ 0 from (map_zero _).symm,
      show (0 : ↥(modularFunctionFieldC k N)) = algebraMap k _ 0 from (map_zero _).symm,
      Place.evalAt_algebraMap, Place.evalAt_algebraMap]
  by_cases hmem : g ∈ (P.restrictAlong φ hφ).toValuationSubring
  · letI := AlgebraicCurve.algebraAlong φ
    haveI := AlgebraicCurve.isScalarTower_along φ
    haveI := AlgebraicCurve.isIntegral_along φ hφ
    exact Place.evalAt_algebraMap_eq_evalAt_restrict P (isRational_C N _) hmem
  · have hmem' : φ g ∉ P.toValuationSubring := fun h => hmem ((mem_iff_mem_restrictAlong φ hφ P g hg he).mp h)
    unfold Place.evalAt
    rw [dif_neg hmem', dif_neg hmem]

theorem toNat_ord_sub_along {F F' : Type*} [Field F] [Field F'] [Algebra k F] [Algebra k F']
    (φ : F →ₐ[k] F') (hφ : φ.toRingHom.IsIntegral)
    (P : Place k F') (g : F) (c : k) :
    (P.ord (φ g - algebraMap k _ c)).toNat
      = Place.ramificationIndexAlong φ P * ((P.restrictAlong φ hφ).ord (g - algebraMap k _ c)).toNat := by
  have : φ g - algebraMap k _ c = φ (g - algebraMap k _ c) := by rw [map_sub, AlgHom.commutes]
  rw [this, Place.ord_restrictAlong φ hφ P]
  set e := Place.ramificationIndexAlong φ P
  set x := (P.restrictAlong φ hφ).ord (g - algebraMap k _ c)
  rcases le_or_gt 0 x with hx | hx
  · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hx
    rw [hn, ← Nat.cast_mul, Int.toNat_natCast, Int.toNat_natCast]
  · rw [Int.toNat_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (by positivity) hx.le), Int.toNat_of_nonpos hx.le, mul_zero]

omit [IsAlgClosed k] in
theorem one_le_jWidth [DecidableEq k] (a : k) : 1 ≤ jWidth a := by
  unfold jWidth; split_ifs <;> norm_num

variable [DecidableEq k]

theorem pair_inv_roof (s M : ℕ) [NeZero s] [NeZero M] (hsk : (s : k) ≠ 0)
    (P : Place k ↥(charLDegeneracyRoof k s M))
    (he : 0 < Place.ramificationIndexAlong (heckeAlphaC k s M) P) :
    (P.ord (heckeAlphaC k s M (jGeomGen k s) - algebraMap k _ (P.evalAt (heckeAlphaC k s M (jGeomGen k s))))).toNat
        * jWidth (P.evalAt (heckeAlphaC k s M (jNGeomGen k s)))
      = (P.ord (heckeAlphaC k s M (jNGeomGen k s) - algebraMap k _ (P.evalAt (heckeAlphaC k s M (jNGeomGen k s))))).toNat
        * jWidth (P.evalAt (heckeAlphaC k s M (jGeomGen k s))) := by
  set ψ := heckeAlphaC k s M with hψdef
  have hψ : ψ.toRingHom.IsIntegral := heckeAlphaCIntegral_unconditional k s M
  set P' := P.restrictAlong ψ hψ with hP'
  have hinv := placeRamificationJ_mul_jWidth_evalAt_jNGeomGen_eq s hsk P'
  unfold placeRamificationJ at hinv
  rw [evalAt_along s ψ hψ P (jGeomGen k s) he, evalAt_along s ψ hψ P (jNGeomGen k s) he,
    toNat_ord_sub_along ψ hψ P, toNat_ord_sub_along ψ hψ P, mul_assoc, mul_assoc, hinv]

theorem rIA_pos {F F' : Type*} [Field F] [Field F'] [Algebra k F] [Algebra k F']
    (φ : F →ₐ[k] F') (hφ : φ.toRingHom.IsIntegral) (P : Place k F') :
    0 < Place.ramificationIndexAlong φ P := by
  letI := AlgebraicCurve.algebraAlong φ
  haveI := AlgebraicCurve.isScalarTower_along φ
  haveI := AlgebraicCurve.isIntegral_along φ hφ
  exact P.ramificationIndex_pos (F := F)

theorem pair_inv_of_eq (s M : ℕ) [NeZero s] [NeZero M] (hsk : (s : k) ≠ 0)
    (S : IntermediateField k (LaurentSeries k)) (hS : S = charLDegeneracyRoof k s M)
    (ha : jqModC k ∈ S) (hb : jqNModC k s ∈ S) (P : Place k ↥S) :
    (P.ord (⟨jqModC k, ha⟩ - algebraMap k ↥S (P.evalAt ⟨jqModC k, ha⟩))).toNat * jWidth (P.evalAt ⟨jqNModC k s, hb⟩)
      = (P.ord (⟨jqNModC k s, hb⟩ - algebraMap k ↥S (P.evalAt ⟨jqNModC k s, hb⟩))).toNat * jWidth (P.evalAt ⟨jqModC k, ha⟩) := by
  subst hS
  have h1 : heckeAlphaC k s M (jGeomGen k s) = ⟨jqModC k, ha⟩ := Subtype.ext (coe_heckeAlphaC k s M _)
  have h2 : heckeAlphaC k s M (jNGeomGen k s) = ⟨jqNModC k s, hb⟩ := Subtype.ext (coe_heckeAlphaC k s M _)
  have := pair_inv_roof s M hsk P (rIA_pos _ (heckeAlphaCIntegral_unconditional k s M) P)
  rwa [h1, h2] at this

theorem C_mul_eq_roof (s M : ℕ) [NeZero s] [NeZero M] (q' : ℕ) [CharP k q'] (hq' : ¬ q' ∣ M * s) :
    (haveI : NeZero (M * s) := ⟨Nat.mul_ne_zero (NeZero.ne M) (NeZero.ne s)⟩;
      modularFunctionFieldC k (M * s)) = charLDegeneracyRoof k s M := by
  haveI : NeZero (M * s) := ⟨Nat.mul_ne_zero (NeZero.ne M) (NeZero.ne s)⟩
  haveI : NeZero (s * M) := ⟨Nat.mul_ne_zero (NeZero.ne s) (NeZero.ne M)⟩
  have hq'' : ¬ q' ∣ s * M := by rwa [Nat.mul_comm]
  rw [modularFunctionFieldC_eq_modularFunctionFieldFullC k q' (M * s) hq',
    charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul k q' s M hq'']
  congr 1 <;> simp [Nat.mul_comm]

end FltWs24.Width

open FltWs24.Width in
theorem solution
    (M s q' : ℕ) [NeZero M] [NeZero s] (hs : s.Prime) [Fact q'.Prime]
    (hsq' : s ≠ q') (hq'M : ¬ q' ∣ M)
    {k : Type*} [Field k] [CharP k q'] [IsAlgClosed k] [DecidableEq k] :
    haveI : NeZero (M * s) := ⟨Nat.mul_ne_zero (NeZero.ne M) (NeZero.ne s)⟩
    ∀ (φ : Fin 2 → (↥(modularFunctionFieldC k M) →ₐ[k] ↥(modularFunctionFieldC k (M * s))))
      (hφ : ∀ i, (φ i).toRingHom.IsIntegral)
      (hφα : ∀ x, ((φ 0 x : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k) = x)
      (hφβ : ∀ x, ((φ 1 x : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k) = qExpand k s x),
    ∀ (i : Fin 2) (p : Place k (modularFunctionFieldC k (M * s))),
      placeRamificationJ (M * s) p ∣ jWidth (p.evalAt (jGeomGen k (M * s))) →
      Place.ramificationIndexAlong (φ i) p * placeWidth (M * s) p
        = placeWidth M (Place.restrictAlong (φ i) (hφ i) p) := by
  haveI : NeZero (M * s) := ⟨Nat.mul_ne_zero (NeZero.ne M) (NeZero.ne s)⟩
  intro φ hφ hφα hφβ i p hdvd
  have hq'Ms : ¬ q' ∣ M * s := by
    intro h
    rcases (Nat.Prime.dvd_mul (Fact.out : q'.Prime)).mp h with h1 | h1
    · exact hq'M h1
    · exact hsq' ((Nat.prime_dvd_prime_iff_eq (Fact.out : q'.Prime) hs).mp h1).symm
  have hsk : (s : k) ≠ 0 := by
    intro h0
    exact hsq' ((Nat.prime_dvd_prime_iff_eq (Fact.out : q'.Prime) hs).mp ((CharP.cast_eq_zero_iff k q' s).mp h0)).symm

  set x := Place.restrictAlong (φ i) (hφ i) p with hx
  set e := Place.ramificationIndexAlong (φ i) p with he
  have hepos : 0 < e := rIA_pos (φ i) (hφ i) p
  have hrM : placeRamificationJ M x * e
      = (p.ord (φ i (jGeomGen k M) - algebraMap k _ (p.evalAt (φ i (jGeomGen k M))))).toNat := by
    unfold placeRamificationJ
    rw [toNat_ord_sub_along (φ i) (hφ i) p, evalAt_along M (φ i) (hφ i) p _ hepos, Nat.mul_comm]
  have hWx : jWidth (x.evalAt (jGeomGen k M)) = jWidth (p.evalAt (φ i (jGeomGen k M))) := by
    rw [evalAt_along M (φ i) (hφ i) p _ hepos]

  set W := jWidth (p.evalAt (jGeomGen k (M * s))) with hW
  set r := placeRamificationJ (M * s) p with hr
  have hW1 : 1 ≤ W := one_le_jWidth _
  have hrpos : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · rw [h0, zero_dvd_iff] at hdvd; omega
    · exact h0
  obtain ⟨t, ht⟩ := hdvd
  have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  rcases hi with rfl | rfl
  ·
    have hj : φ 0 (jGeomGen k M) = jGeomGen k (M * s) := Subtype.ext (by rw [hφα]; rfl)
    rw [hj] at hrM hWx

    show e * (W / r) = jWidth (x.evalAt (jGeomGen k M)) / placeRamificationJ M x
    rw [hWx]
    change e * (W / r) = W / placeRamificationJ M x
    have hrM' : placeRamificationJ M x * e = r := hrM
    have hrMpos : 0 < placeRamificationJ M x := by
      rcases Nat.eq_zero_or_pos (placeRamificationJ M x) with h0 | h0
      · rw [h0, zero_mul] at hrM'; omega
      · exact h0
    rw [ht, ← hrM']
    rw [show placeRamificationJ M x * e * t / (placeRamificationJ M x * e) = t from
        Nat.mul_div_cancel_left t (Nat.mul_pos hrMpos hepos),
      show placeRamificationJ M x * e * t / placeRamificationJ M x = e * t by
        rw [mul_assoc]; exact Nat.mul_div_cancel_left (e * t) hrMpos]
  ·
    have hbmem : jqNModC k s ∈ modularFunctionFieldC k (M * s) := by
      have := (φ 1 (jGeomGen k M)).2
      rwa [show ((φ 1 (jGeomGen k M) : ↥(modularFunctionFieldC k (M * s))) : LaurentSeries k) = jqNModC k s by rw [hφβ]; rfl] at this
    have hj : φ 1 (jGeomGen k M) = ⟨jqNModC k s, hbmem⟩ := Subtype.ext (by rw [hφβ]; rfl)
    rw [hj] at hrM hWx
    have hamem : jqModC k ∈ modularFunctionFieldC k (M * s) := jqModC_mem k (M * s)
    have hinv := pair_inv_of_eq s M hsk (modularFunctionFieldC k (M * s)) (C_mul_eq_roof s M q' hq'Ms) hamem hbmem p

    have ha : (⟨jqModC k, hamem⟩ : ↥(modularFunctionFieldC k (M * s))) = jGeomGen k (M * s) := rfl
    rw [ha] at hinv
    change r * jWidth (p.evalAt ⟨jqNModC k s, hbmem⟩) = _ * W at hinv
    rw [← hrM, ← hWx] at hinv

    show e * (W / r) = jWidth (x.evalAt (jGeomGen k M)) / placeRamificationJ M x
    have hrMpos : 0 < placeRamificationJ M x := by
      rcases Nat.eq_zero_or_pos (placeRamificationJ M x) with h0 | h0
      · exfalso
        rw [h0, zero_mul, zero_mul] at hinv
        have := one_le_jWidth (x.evalAt (jGeomGen k M))
        have : r * jWidth (x.evalAt (jGeomGen k M)) ≠ 0 := Nat.mul_ne_zero hrpos.ne' (by omega)
        exact this hinv
      · exact h0
    rw [ht] at hinv ⊢
    rw [Nat.mul_div_cancel_left t hrpos]

    have hWx' : jWidth (x.evalAt (jGeomGen k M)) = placeRamificationJ M x * (e * t) := by
      have : r * jWidth (x.evalAt (jGeomGen k M)) = r * (placeRamificationJ M x * (e * t)) := by
        rw [hinv]; ring
      exact Nat.eq_of_mul_eq_mul_left hrpos this
    rw [hWx', Nat.mul_div_cancel_left _ hrMpos]

end S_ModularCurve_ramificationIndexAlong_mul_placeWidth_eq_placeWidth_restrictAlong
end P2MW
export P2MW.S_ModularCurve_ramificationIndexAlong_mul_placeWidth_eq_placeWidth_restrictAlong (solution)
