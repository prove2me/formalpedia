-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.LevelOneProlongationPair.exists_tubeEquation_smul_sub_self
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/b8685f7f-099b-5cde-b12c-e3aa8d5f0a9a

import Mathlib
import Definitions.Def_ModularCurve_LevelOneProlongationPair
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_SupersingularNodes
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_ModularCurve_NodeLocalized
import Theorems.Thm_ModularCurve_NodeLocalized_exists_hasValue_nodeCoord_of_centred
import Theorems.Thm_ModularCurve_NodeLocalized_existsUnique_place_centred_hasValue_nodeCoord
import Theorems.Thm_ModularCurve_NodeLocalized_ord_nodeCoord_sub_eq_one_of_centred
import Theorems.Thm_ValuationSubring_exists_units_mul_eq_and_residue_eq_tameCharacter_of_mem_inertiaSubgroupIn
import Theorems.Thm_ModularCurve_existsUnique_qExpand_sub_pow_eq_natCast_mul
import Theorems.Thm_ModularCurve_arithmeticGalois_smul_coeffEmb
import Theorems.Thm_ModularCurve_coeffMap_qExpand
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_frickeInvolutionBar_comp_heckeAlphaBar_one
import Theorems.Thm_ModularCurve_frickeInvolutionBar_comp_heckeBetaBar_one
import Theorems.Thm_ModularCurve_coeff_jqModC_pow_self
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_tubeEquation_smul_sub_self
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁"
p2m_attr_erase "simp" "ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right"
p2m_attr_erase "simp" "FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.cuspCount_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂"
p2m_attr_erase "simp" "PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

p2m_open "AlgebraicCurve IsLocalRing ModularCurve~coeffEmb_jqN~coeffEmb_jq P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_tubeEquation_smul_sub_self.ModularCurve ModularCurve.PlaceSpecialization P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_tubeEquation_smul_sub_self.ModularCurve.PlaceSpecialization"
open scoped Pointwise

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.LevelOneProlongationPair arithmeticGalois baseAut_arithmeticGalois modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_congr jq ModularPolynomialData jq_mem modularFunctionFieldFull jqd_mem_full modularFunctionField_le_full coeffMap coeffMap_single coeffMap_coeffMap coeffMap_congr algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_mem_laurentBaseChange jqModC jqNModC modularFunctionFieldC PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral KroneckerCongruence ssJSet frickeInvolutionBar coeffMap_jqModC coeffMap_jqNModC coeff_jqModC_of_lt modularFunctionFieldFullC coeffMap_qExpand coeff_jqModC_pow_self NodeLocalized.exists_hasValue_nodeCoord_of_centred NodeLocalized.existsUnique_place_centred_hasValue_nodeCoord NodeLocalized.ord_nodeCoord_sub_eq_one_of_centred existsUnique_qExpand_sub_pow_eq_natCast_mul arithmeticGalois_smul_coeffEmb frickeInvolutionBar_comp_heckeAlphaBar_one frickeInvolutionBar_comp_heckeBetaBar_one"
namespace TubeEqFricke
p2m_open "ModularCurve~coeffEmb_jqN~coeffEmb_jq"

noncomputable def jOne : ↥(modularFunctionFieldBar 1) :=
  ⟨coeffEmb (AlgebraicClosure ℚ) jq,
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full 1 (jq_mem 1))⟩

variable (q : ℕ) [Fact q.Prime]

theorem heckeAlphaBar_jOne :
    heckeAlphaBar (AlgebraicClosure ℚ) 1 q jOne = (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) := by
  apply Subtype.ext
  rw [coe_heckeAlphaBar]
  rfl

theorem coeffEmb_qExpand_jq :
    coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq) = qExpand (AlgebraicClosure ℚ) q (coeffEmb (AlgebraicClosure ℚ) jq) := by
  show coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) (qExpand ℚ (1 * q) jq) = _
  rw [ModularCurve.coeffMap_qExpand, qExpand_congr (one_mul q)]
  rfl

theorem heckeBetaBar_jOne :
    heckeBetaBar (AlgebraicClosure ℚ) 1 q jOne = (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) := by
  apply Subtype.ext
  rw [coe_heckeBetaBar]
  exact (coeffEmb_qExpand_jq q).symm

theorem frickeInvolutionBar_jF :
    frickeInvolutionBar (1 * q) (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) = (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) := by
  rw [← heckeAlphaBar_jOne q, ← heckeBetaBar_jOne q]
  exact AlgHom.congr_fun (frickeInvolutionBar_comp_heckeAlphaBar_one q) jOne

theorem frickeInvolutionBar_jqF :
    frickeInvolutionBar (1 * q) (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) = (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) := by
  rw [← heckeAlphaBar_jOne q, ← heckeBetaBar_jOne q]
  exact AlgHom.congr_fun (frickeInvolutionBar_comp_heckeBetaBar_one q) jOne

theorem frickeInvolutionBar_G_sub (c : AlgebraicClosure ℚ) :
    frickeInvolutionBar (1 * q)
      (((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) ^ q) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) c)
    = ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) ^ q) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) c := by
  rw [map_sub, map_sub, map_pow, frickeInvolutionBar_jF, frickeInvolutionBar_jqF, AlgEquiv.commutes]

theorem coeffEmb_jq : coeffEmb (AlgebraicClosure ℚ) jq = jqModC (AlgebraicClosure ℚ) := by
  show coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) (jqModC ℚ) = _
  exact ModularCurve.coeffMap_jqModC _

theorem coeffEmb_jqN : coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq) = jqNModC (AlgebraicClosure ℚ) (1 * q) := by
  show coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) (jqNModC ℚ (1 * q)) = _
  exact ModularCurve.coeffMap_jqNModC _ _

variable (A : ValuationSubring (AlgebraicClosure ℚ))

noncomputable def yH (c : A) : LaurentSeries A :=
  jqModC A - jqNModC A (1 * q) ^ q - HahnSeries.single 0 c

theorem coeffMap_yH (c : A) :
    coeffMap A.subtype (yH q A c)
      = ((((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) ^ q) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (c : AlgebraicClosure ℚ)
          : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) := by
  rw [yH, map_sub, map_sub, map_pow, ModularCurve.coeffMap_jqModC, ModularCurve.coeffMap_jqNModC,
    coeffMap_single]
  rw [AddSubgroupClass.coe_sub, AddSubgroupClass.coe_sub, SubmonoidClass.coe_pow]
  have h3 : ((algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (c : AlgebraicClosure ℚ)
      : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ))
      = HahnSeries.single 0 (c : AlgebraicClosure ℚ) := by
    show algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (c : AlgebraicClosure ℚ) = _
    rw [algebraMap_laurentSeries_eq_single]
  rw [h3]
  change _ = coeffEmb (AlgebraicClosure ℚ) jq - coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq) ^ q - _
  rw [coeffEmb_jq, coeffEmb_jqN]
  rfl

theorem coeffMap_yH_mem (c : A) : coeffMap A.subtype (yH q A c) ∈ modularFunctionFieldBar (1 * q) := by
  rw [coeffMap_yH]; exact SetLike.coe_mem _

noncomputable def yBar : LaurentSeries (ResidueField A) :=
  jqModC (ResidueField A) - jqNModC (ResidueField A) (1 * q) ^ q

theorem coeffMap_residue_yH {c : A} (hc : c ∈ IsLocalRing.maximalIdeal A) :
    coeffMap (IsLocalRing.residue A) (yH q A c) = yBar q A := by
  rw [yH, map_sub, map_sub, map_pow, ModularCurve.coeffMap_jqModC, ModularCurve.coeffMap_jqNModC,
    coeffMap_single, (IsLocalRing.residue_eq_zero_iff c).mpr hc, HahnSeries.single_eq_zero, sub_zero, yBar]

theorem yBar_ne_zero : yBar q A ≠ 0 := by
  intro h
  have h2 : (2 : ℤ) ≤ q := by exact_mod_cast (Fact.out : q.Prime).two_le
  have hlt : ((1 * q : ℕ) : ℤ) * (-(q : ℤ)) < -1 := by push_cast; nlinarith
  have hc := congrArg (fun y : LaurentSeries (ResidueField A) => y.coeff (((1 * q : ℕ) : ℤ) * (-(q : ℤ)))) h
  simp only [yBar, HahnSeries.coeff_sub, HahnSeries.coeff_zero] at hc
  rw [ModularCurve.coeff_jqModC_of_lt _ hlt, jqNModC, ← map_pow, qExpand_coeff_mul,
    ModularCurve.coeff_jqModC_pow_self, zero_sub, neg_eq_zero] at hc
  exact one_ne_zero hc

variable {q A}
variable {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : P.LevelOneProlongationPair)

theorem exists_mem_integers₁_H_sub {c : A} (hc : c ∈ IsLocalRing.maximalIdeal A) :
    ∃ h : (((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) ^ q) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (c : AlgebraicClosure ℚ)
          : ↥(modularFunctionFieldBar (1 * q))) ∈ R.R₁.integers,
      ((R.R₁.residue ⟨_, h⟩ : ↥(modularFunctionFieldFullC (ResidueField A) 1)) : LaurentSeries (ResidueField A))
        = yBar q A := by
  obtain ⟨h, hres⟩ := R.residue₁_coeffMap (yH q A c) (coeffMap_yH_mem q A c)
  have e : (⟨coeffMap A.subtype (yH q A c), coeffMap_yH_mem q A c⟩ : ↥(modularFunctionFieldBar (1 * q)))
      = ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) ^ q) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (c : AlgebraicClosure ℚ) :=
    Subtype.ext (coeffMap_yH q A c)
  refine ⟨e ▸ h, ?_⟩
  have hO : (⟨((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) ^ q) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (c : AlgebraicClosure ℚ), e ▸ h⟩ : R.R₁.integers)
      = ⟨_, h⟩ := Subtype.ext e.symm
  rw [hO, hres, coeffMap_residue_yH q A hc]

end ModularCurve.TubeEqFricke

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.LevelOneProlongationPair arithmeticGalois baseAut_arithmeticGalois modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_congr jq ModularPolynomialData jq_mem modularFunctionFieldFull jqd_mem_full modularFunctionField_le_full coeffMap coeffMap_single coeffMap_coeffMap coeffMap_congr algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_mem_laurentBaseChange jqModC jqNModC modularFunctionFieldC PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral KroneckerCongruence ssJSet frickeInvolutionBar coeffMap_jqModC coeffMap_jqNModC coeff_jqModC_of_lt modularFunctionFieldFullC coeffMap_qExpand coeff_jqModC_pow_self NodeLocalized.exists_hasValue_nodeCoord_of_centred NodeLocalized.existsUnique_place_centred_hasValue_nodeCoord NodeLocalized.ord_nodeCoord_sub_eq_one_of_centred existsUnique_qExpand_sub_pow_eq_natCast_mul arithmeticGalois_smul_coeffEmb frickeInvolutionBar_comp_heckeAlphaBar_one frickeInvolutionBar_comp_heckeBetaBar_one"
namespace TubeEqPin
p2m_open "ModularCurve~coeffEmb_jqN~coeffEmb_jq"

variable (q : ℕ) [Fact q.Prime]

noncomputable def S : LaurentSeries ℤ :=
  (ModularCurve.existsUnique_qExpand_sub_pow_eq_natCast_mul q (jqModC ℤ)).choose

theorem S_spec : qExpand ℤ q (jqModC ℤ) - jqModC ℤ ^ q = (q : LaurentSeries ℤ) * S q :=
  (ModularCurve.existsUnique_qExpand_sub_pow_eq_natCast_mul q (jqModC ℤ)).choose_spec.1

theorem coe_G :
    ((((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q))
          - (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) ^ q) : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ))
      = HahnSeries.C ((q : ℕ) : AlgebraicClosure ℚ) * coeffMap (Int.castRingHom (AlgebraicClosure ℚ)) (S q) := by
  rw [AddSubgroupClass.coe_sub, SubmonoidClass.coe_pow]
  change coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq) - coeffEmb (AlgebraicClosure ℚ) jq ^ q = _
  rw [TubeEqFricke.coeffEmb_jqN, TubeEqFricke.coeffEmb_jq,
    ← ModularCurve.coeffMap_jqNModC (Int.castRingHom (AlgebraicClosure ℚ)) (1 * q),
    ← ModularCurve.coeffMap_jqModC (Int.castRingHom (AlgebraicClosure ℚ)),
    ← map_pow, ← map_sub, jqNModC, qExpand_congr (one_mul q), S_spec, map_mul, map_natCast, map_natCast]

variable (A : ValuationSubring (AlgebraicClosure ℚ))

noncomputable def yP (d : A) : LaurentSeries A :=
  1 - HahnSeries.single 0 d * coeffMap (Int.castRingHom A) (S q)

theorem coeffMap_subtype_yP (d : A) :
    coeffMap A.subtype (yP q A d)
      = 1 - HahnSeries.C (d : AlgebraicClosure ℚ) * coeffMap (Int.castRingHom (AlgebraicClosure ℚ)) (S q) := by
  rw [yP, map_sub, map_one, map_mul, coeffMap_single, coeffMap_coeffMap,
    coeffMap_congr (RingHom.ext_int (A.subtype.comp (Int.castRingHom A)) (Int.castRingHom (AlgebraicClosure ℚ))),
    HahnSeries.C_apply]
  rfl

theorem coeffMap_residue_yP {d : A} (hd : d ∈ IsLocalRing.maximalIdeal A) :
    coeffMap (IsLocalRing.residue A) (yP q A d) = 1 := by
  rw [yP, map_sub, map_one, map_mul, coeffMap_single, (IsLocalRing.residue_eq_zero_iff d).mpr hd,
    HahnSeries.single_eq_zero, zero_mul, sub_zero]

theorem coe_YP (c d : A) (hcd : c * d = ((q : ℕ) : A)) :
    ((((((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q))
          - (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) ^ q) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) ((c : AlgebraicClosure ℚ)))
        * (- algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) ((c : AlgebraicClosure ℚ)))⁻¹ : ↥(modularFunctionFieldBar (1 * q)))) : LaurentSeries (AlgebraicClosure ℚ))
      = coeffMap A.subtype (yP q A d) := by
  have hq0 : ((q : ℕ) : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero
  have hcd' : (c : AlgebraicClosure ℚ) * (d : AlgebraicClosure ℚ) = ((q : ℕ) : AlgebraicClosure ℚ) := by
    have := congrArg (fun z : A => (z : AlgebraicClosure ℚ)) hcd
    simpa using this
  have hc0 : (c : AlgebraicClosure ℚ) ≠ 0 := by
    intro h; rw [h, zero_mul] at hcd'; exact hq0 hcd'.symm
  have hCc : HahnSeries.C (c : AlgebraicClosure ℚ) ≠ (0 : LaurentSeries (AlgebraicClosure ℚ)) :=
    fun h => hc0 (HahnSeries.C_injective (by rw [h, map_zero]))
  have hd : (d : AlgebraicClosure ℚ) = ((q : ℕ) : AlgebraicClosure ℚ) * (c : AlgebraicClosure ℚ)⁻¹ := by
    rw [← hcd', mul_comm, ← mul_assoc, inv_mul_cancel₀ hc0, one_mul]
  have hC : ((algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) ((c : AlgebraicClosure ℚ)) : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ))
      = HahnSeries.C (c : AlgebraicClosure ℚ) := by
    show algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (c : AlgebraicClosure ℚ) = _
    rw [algebraMap_laurentSeries_eq_single, HahnSeries.C_apply]
  rw [coeffMap_subtype_yP, IntermediateField.coe_mul, IntermediateField.coe_inv, NegMemClass.coe_neg,
    AddSubgroupClass.coe_sub, hC, coe_G, hd, map_mul, map_inv₀]
  calc (HahnSeries.C ((q : ℕ) : AlgebraicClosure ℚ) * coeffMap (Int.castRingHom (AlgebraicClosure ℚ)) (S q)
          - HahnSeries.C (c : AlgebraicClosure ℚ)) * (-HahnSeries.C (c : AlgebraicClosure ℚ))⁻¹
        = 1 - HahnSeries.C ((q : ℕ) : AlgebraicClosure ℚ) * (HahnSeries.C (c : AlgebraicClosure ℚ))⁻¹
            * coeffMap (Int.castRingHom (AlgebraicClosure ℚ)) (S q)
          - (1 - HahnSeries.C (c : AlgebraicClosure ℚ) * (HahnSeries.C (c : AlgebraicClosure ℚ))⁻¹) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hCc, sub_self, sub_zero]

variable {q A}
variable {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : P.LevelOneProlongationPair)

theorem exists_mem_integers₁_YP {c d : A} (hd : d ∈ IsLocalRing.maximalIdeal A) (hcd : c * d = ((q : ℕ) : A)) :
    ∃ h : (((((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q))
          - (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) ^ q) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) ((c : AlgebraicClosure ℚ)))
        * (- algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) ((c : AlgebraicClosure ℚ)))⁻¹ : ↥(modularFunctionFieldBar (1 * q)))) ∈ R.R₁.integers,
      R.R₁.residue ⟨_, h⟩ = 1 := by
  have hmem : coeffMap A.subtype (yP q A d) ∈ modularFunctionFieldBar (1 * q) := by
    rw [← coe_YP q A c d hcd]; exact SetLike.coe_mem _
  obtain ⟨h, hres⟩ := R.residue₁_coeffMap (yP q A d) hmem
  have e : (⟨coeffMap A.subtype (yP q A d), hmem⟩ : ↥(modularFunctionFieldBar (1 * q)))
      = (((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q))
          - (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) ^ q) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) ((c : AlgebraicClosure ℚ)))
        * (- algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) ((c : AlgebraicClosure ℚ)))⁻¹ := Subtype.ext (coe_YP q A c d hcd).symm
  refine ⟨e ▸ h, ?_⟩
  have hO : (⟨(((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q))
          - (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) ^ q) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) ((c : AlgebraicClosure ℚ)))
        * (- algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) ((c : AlgebraicClosure ℚ)))⁻¹, e ▸ h⟩ : R.R₁.integers) = ⟨_, h⟩ := Subtype.ext e.symm
  rw [hO]
  apply Subtype.ext
  rw [hres, coeffMap_residue_yP q A hd, OneMemClass.coe_one]

end ModularCurve.TubeEqPin

namespace ModularCurve p2m_export "ModularCurve" "PlaceSpecialization.LevelOneProlongationPair arithmeticGalois baseAut_arithmeticGalois modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_congr jq ModularPolynomialData jq_mem modularFunctionFieldFull jqd_mem_full modularFunctionField_le_full coeffMap coeffMap_single coeffMap_coeffMap coeffMap_congr algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_mem_laurentBaseChange jqModC jqNModC modularFunctionFieldC PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral KroneckerCongruence ssJSet frickeInvolutionBar coeffMap_jqModC coeffMap_jqNModC coeff_jqModC_of_lt modularFunctionFieldFullC coeffMap_qExpand coeff_jqModC_pow_self NodeLocalized.exists_hasValue_nodeCoord_of_centred NodeLocalized.existsUnique_place_centred_hasValue_nodeCoord NodeLocalized.ord_nodeCoord_sub_eq_one_of_centred existsUnique_qExpand_sub_pow_eq_natCast_mul arithmeticGalois_smul_coeffEmb frickeInvolutionBar_comp_heckeAlphaBar_one frickeInvolutionBar_comp_heckeBetaBar_one" namespace PlaceSpecialization p2m_export "ModularCurve.PlaceSpecialization" "LevelOneProlongationPair LevelOneProlongationPair.residue₁_apply LevelOneProlongationPair.residue₂_apply" namespace LevelOneProlongationPair p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "residue₁ residue₂ residue₁_apply residue₂_apply mem_integers₂_iff residue₂_eq R₂ residue₁_coeffMap redBar ι_coe ι R₁ redBar_residue" end ModularCurve.PlaceSpecialization.LevelOneProlongationPair
namespace ModularCurve.PlaceSpecialization.LevelOneProlongationPair
p2m_open_scoped "ModularCurve ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.LevelOneProlongationPair" in

private theorem _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.exists_mem_integersSnd_residue₂_eq_one_of_mem_maximalIdeal
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : P.LevelOneProlongationPair)
    (x s : A) (hx : x ∈ IsLocalRing.maximalIdeal A) (hs : s ∈ IsLocalRing.maximalIdeal A)
    (t : ↥(modularFunctionFieldBar (1 * q)))
    (ht : t = (((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q))
          - (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) ^ q) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) ((s : A) : AlgebraicClosure ℚ))
          * (((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q))
          - (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) ^ q) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) ((x : A) : AlgebraicClosure ℚ))⁻¹) :
    ∃ h : t ∈ R.R₂.integers, (R.residue₂ ⟨t, h⟩ : ↥(modularFunctionFieldC k 1)) = 1 := by
  classical

  obtain ⟨hHs, hresS⟩ := ModularCurve.TubeEqFricke.exists_mem_integers₁_H_sub R hs
  obtain ⟨hHx, hresX⟩ := ModularCurve.TubeEqFricke.exists_mem_integers₁_H_sub R hx
  set Hs : R.R₁.integers := ⟨_, hHs⟩ with hHs_def
  set Hx : R.R₁.integers := ⟨_, hHx⟩ with hHx_def
  have hρ : R.R₁.residue Hs = R.R₁.residue Hx := Subtype.ext (hresS.trans hresX.symm)
  have hρ0 : R.R₁.residue Hx ≠ 0 := by
    intro h0
    apply ModularCurve.TubeEqFricke.yBar_ne_zero q A
    rw [← hresX]
    rw [h0]
    rfl
  have hunit : IsUnit Hx := R.R₁.isUnit_of_residue_ne_zero hρ0

  set v : R.R₁.integers := ((hunit.unit⁻¹ : (↥R.R₁.integers)ˣ) : R.R₁.integers) with hv
  have hxv : Hx * v = 1 := by rw [hv]; exact hunit.mul_val_inv
  have hvF : (v : ↥(modularFunctionFieldBar (1 * q))) = ((Hx : ↥(modularFunctionFieldBar (1 * q))))⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    have := congrArg (fun z : R.R₁.integers => (z : ↥(modularFunctionFieldBar (1 * q)))) hxv
    simpa using this

  have hwt : frickeInvolutionBar (1 * q) t = ((Hs * v : R.R₁.integers) : ↥(modularFunctionFieldBar (1 * q))) := by
    rw [ht, map_mul, map_inv₀, ModularCurve.TubeEqFricke.frickeInvolutionBar_G_sub,
      ModularCurve.TubeEqFricke.frickeInvolutionBar_G_sub]
    push_cast
    rw [hvF]
  have hmem : frickeInvolutionBar (1 * q) t ∈ R.R₁.integers := by
    rw [hwt]; exact SetLike.coe_mem _
  refine ⟨(R.mem_integers₂_iff t).mpr hmem, ?_⟩
  rw [LevelOneProlongationPair.residue₂_apply, R.residue₂_eq]
  have hres1 : R.R₁.residue ⟨frickeInvolutionBar (1 * q) t, (R.mem_integers₂_iff t).mp ((R.mem_integers₂_iff t).mpr hmem)⟩ = 1 := by
    have e : (⟨frickeInvolutionBar (1 * q) t, (R.mem_integers₂_iff t).mp ((R.mem_integers₂_iff t).mpr hmem)⟩ : R.R₁.integers)
        = Hs * v := Subtype.ext hwt
    rw [e, map_mul, hρ, ← map_mul, hxv, map_one]
  rw [hres1, map_one]

end ModularCurve.PlaceSpecialization.LevelOneProlongationPair
p2m_export "" "ModularCurve.PlaceSpecialization.LevelOneProlongationPair.exists_mem_integersSnd_residue₂_eq_one_of_mem_maximalIdeal"
namespace ModularCurve.PlaceSpecialization.LevelOneProlongationPair
p2m_open_scoped "ModularCurve ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.LevelOneProlongationPair" in

private theorem _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.exists_mem_integersFst_residue₁_eq_algebraMap_of_mul_eq
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : P.LevelOneProlongationPair)
    (x dx : A) (u : (↥A)ˣ) (hdx : dx ∈ IsLocalRing.maximalIdeal A) (hxd : x * dx = ((q : ℕ) : A))
    (t : ↥(modularFunctionFieldBar (1 * q)))
    (ht : t = (((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q))
          - (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) ^ q) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (((u : A) * x : A) : AlgebraicClosure ℚ))
          * (((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q))
          - (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) ^ q) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) ((x : A) : AlgebraicClosure ℚ))⁻¹) :
    ∃ h : t ∈ R.R₁.integers,
      (R.residue₁ ⟨t, h⟩ : ↥(modularFunctionFieldC k 1)) = algebraMap k ↥(modularFunctionFieldC k 1) (red (u : A)) := by
  classical

  have hd₁ : ((↑(u⁻¹) : A) * dx) ∈ IsLocalRing.maximalIdeal A := Ideal.mul_mem_left _ _ hdx
  have hcd₁ : ((u : A) * x) * ((↑(u⁻¹) : A) * dx) = ((q : ℕ) : A) := by
    calc ((u : A) * x) * ((↑(u⁻¹) : A) * dx) = ((u : A) * (↑(u⁻¹) : A)) * (x * dx) := by ring
      _ = ((q : ℕ) : A) := by rw [Units.mul_inv, one_mul, hxd]
  obtain ⟨hY₁, hres₁⟩ := ModularCurve.TubeEqPin.exists_mem_integers₁_YP R hd₁ hcd₁
  obtain ⟨hY₂, hres₂⟩ := ModularCurve.TubeEqPin.exists_mem_integers₁_YP R hdx hxd
  set Y₁ : R.R₁.integers := ⟨_, hY₁⟩ with hY₁_def
  set Y₂ : R.R₁.integers := ⟨_, hY₂⟩ with hY₂_def

  set U : R.R₁.integers := ⟨algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) ((u : A) : AlgebraicClosure ℚ),
    (R.R₁.algebraMap_mem_iff _).mpr (u : A).2⟩ with hU_def
  have hresU : R.R₁.residue U = algebraMap (ResidueField A) _ (IsLocalRing.residue A (u : A)) :=
    R.R₁.residue_algebraMap (u : A)

  have hρ0 : R.R₁.residue Y₂ ≠ 0 := by rw [hres₂]; exact one_ne_zero
  have hunit : IsUnit Y₂ := R.R₁.isUnit_of_residue_ne_zero hρ0
  set v : R.R₁.integers := ((hunit.unit⁻¹ : (↥R.R₁.integers)ˣ) : R.R₁.integers) with hv
  have hxv : Y₂ * v = 1 := by rw [hv]; exact hunit.mul_val_inv
  have hvF : (v : ↥(modularFunctionFieldBar (1 * q))) = ((Y₂ : ↥(modularFunctionFieldBar (1 * q))))⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    have := congrArg (fun z : R.R₁.integers => (z : ↥(modularFunctionFieldBar (1 * q)))) hxv
    simpa using this
  have hresv : R.R₁.residue v = 1 := by
    have := congrArg R.R₁.residue hxv
    rwa [map_mul, hres₂, one_mul, map_one] at this

  have hq0 : ((q : ℕ) : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero
  have hxd' : ((x : A) : AlgebraicClosure ℚ) * ((dx : A) : AlgebraicClosure ℚ) = ((q : ℕ) : AlgebraicClosure ℚ) := by
    have := congrArg (fun z : A => (z : AlgebraicClosure ℚ)) hxd
    simpa using this
  have hx0 : ((x : A) : AlgebraicClosure ℚ) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hxd'
    exact hq0 hxd'.symm
  have hu0 : (((u : A) : A) : AlgebraicClosure ℚ) ≠ 0 := by
    intro h0
    have h1 : (u : A) = 0 := Subtype.ext h0
    exact (Units.ne_zero u) h1

  have hteq : t = ((U * Y₁ * v : R.R₁.integers) : ↥(modularFunctionFieldBar (1 * q))) := by
    rw [Subring.coe_mul, Subring.coe_mul, hvF, hU_def, hY₁_def, hY₂_def]
    simp only []
    rw [ht]
    set G : ↥(modularFunctionFieldBar (1 * q)) := ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q))
          - (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) ^ q) with hG
    set cx : ↥(modularFunctionFieldBar (1 * q)) := algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (((x : A) : AlgebraicClosure ℚ)) with hcx
    set uF : ↥(modularFunctionFieldBar (1 * q)) := algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) ((((u : A) : A) : AlgebraicClosure ℚ)) with huF
    have hc₁ : algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (((((u : A) * x : A)) : AlgebraicClosure ℚ)) = uF * cx := by
      rw [huF, hcx, ← map_mul]; rfl
    rw [hc₁]
    have huF0 : uF ≠ 0 := by rw [huF]; exact (map_ne_zero _).mpr hu0
    have hcx0 : cx ≠ 0 := by rw [hcx]; exact (map_ne_zero _).mpr hx0
    have key : uF * -cx * (-(uF * cx))⁻¹ = 1 := by
      rw [show -(uF * cx) = uF * -cx by ring]
      exact mul_inv_cancel₀ (mul_ne_zero huF0 (neg_ne_zero.mpr hcx0))
    calc (G - uF * cx) * (G - cx)⁻¹ = (G - uF * cx) * (G - cx)⁻¹ * (uF * -cx * (-(uF * cx))⁻¹) := by
          rw [key, mul_one]
      _ = uF * ((G - uF * cx) * (-(uF * cx))⁻¹) * ((G - cx) * (-cx)⁻¹)⁻¹ := by
          rw [mul_inv, inv_inv]; ring
  have hmem : t ∈ R.R₁.integers := by rw [hteq]; exact SetLike.coe_mem _
  refine ⟨hmem, ?_⟩
  have hOt : (⟨t, hmem⟩ : R.R₁.integers) = U * Y₁ * v := Subtype.ext hteq
  have hres_t : R.R₁.residue (U * Y₁ * v)
      = algebraMap (ResidueField A) _ (IsLocalRing.residue A (u : A)) := by
    rw [map_mul, map_mul, hresU, hres₁, hresv, mul_one, mul_one]
  rw [LevelOneProlongationPair.residue₁_apply, hOt, hres_t]

  apply Subtype.ext
  rw [R.ι_coe]
  change coeffMap R.redBar (algebraMap (ResidueField A) (LaurentSeries (ResidueField A)) (IsLocalRing.residue A (u : A)))
    = algebraMap k (LaurentSeries k) (red (u : A))
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single, R.redBar_residue]

end ModularCurve.PlaceSpecialization.LevelOneProlongationPair
p2m_export "" "ModularCurve.PlaceSpecialization.LevelOneProlongationPair.exists_mem_integersFst_residue₁_eq_algebraMap_of_mul_eq"
namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.LevelOneProlongationPair arithmeticGalois baseAut_arithmeticGalois modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_congr jq ModularPolynomialData jq_mem modularFunctionFieldFull jqd_mem_full modularFunctionField_le_full coeffMap coeffMap_single coeffMap_coeffMap coeffMap_congr algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_mem_laurentBaseChange jqModC jqNModC modularFunctionFieldC PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral KroneckerCongruence ssJSet frickeInvolutionBar coeffMap_jqModC coeffMap_jqNModC coeff_jqModC_of_lt modularFunctionFieldFullC coeffMap_qExpand coeff_jqModC_pow_self NodeLocalized.exists_hasValue_nodeCoord_of_centred NodeLocalized.existsUnique_place_centred_hasValue_nodeCoord NodeLocalized.ord_nodeCoord_sub_eq_one_of_centred existsUnique_qExpand_sub_pow_eq_natCast_mul arithmeticGalois_smul_coeffEmb frickeInvolutionBar_comp_heckeAlphaBar_one frickeInvolutionBar_comp_heckeBetaBar_one"
namespace TubeEqOrd
p2m_open "ModularCurve~coeffEmb_jqN~coeffEmb_jq"

theorem centred_smul
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] (red : A →+* k)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (a : k) (h0 : a ≠ 0)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (hW : ((∃ x : A, red x = a ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
         (∃ y : A, red y = a ^ q ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ))))) :
    ((∃ x : A, red x = a ∧
            0 < (arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • W).ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
         (∃ y : A, red y = a ^ q ∧
            0 < (arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • W).ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ)))) := by
  classical
  obtain ⟨hunit, htame1⟩ :=
    ValuationSubring.exists_units_mul_eq_and_residue_eq_tameCharacter_of_mem_inertiaSubgroupIn A hσ
  set g := arithmeticGalois (modularFunctionFieldFull (1 * q)) σ with hg
  have hgjF : g • (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) = (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) := by
    rw [hg]
    exact arithmeticGalois_smul_coeffEmb (modularFunctionFieldFull (1 * q)) σ
      (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))
  have hgjqF : g • (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) = (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) := by
    rw [hg]
    exact arithmeticGalois_smul_coeffEmb (modularFunctionFieldFull (1 * q)) σ
      (jqd_mem_full (1 * q) (dvd_refl (1 * q)))
  have hgc : ∀ c : AlgebraicClosure ℚ, g • algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) c = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (σ c) := by
    intro c
    rw [hg, AlgebraicCurve.SemilinearAut.smul_algebraMap, baseAut_arithmeticGalois]
    rfl
  have hred_fix : ∀ x₀ : A, red x₀ ≠ 0 →
      ∃ y₀ : A, (y₀ : AlgebraicClosure ℚ) = σ (x₀ : AlgebraicClosure ℚ) ∧ red y₀ = red x₀ := by
    intro x₀ hx₀
    have hx₀0 : ((x₀ : A) : AlgebraicClosure ℚ) ≠ 0 := by
      intro h; apply hx₀; rw [show x₀ = 0 from Subtype.ext h, map_zero]
    have hx₀u : IsUnit x₀ := by
      by_contra hnu
      exact hx₀ ((hker x₀).2 ((IsLocalRing.mem_maximalIdeal _).2 hnu))
    obtain ⟨u₀, hu₀, hu₀res⟩ := hunit _ hx₀0
    refine ⟨(u₀ : A) * x₀, by rw [Subring.coe_mul]; exact hu₀, ?_⟩
    have h1 : A.tameCharacter ((hx₀u.unit : (↥A)ˣ) : A) σ = 1 := htame1 hx₀u.unit
    rw [IsUnit.unit_spec] at h1
    rw [h1] at hu₀res
    have hu₀1 : red (u₀ : A) = 1 := by
      have hm : (u₀ : A) - 1 ∈ IsLocalRing.maximalIdeal A := by
        rw [← IsLocalRing.residue_eq_zero_iff, map_sub, hu₀res, map_one, sub_self]
      have := (hker _).2 hm
      rwa [map_sub, map_one, sub_eq_zero] at this
    rw [map_mul, hu₀1, one_mul]
  obtain ⟨⟨x₀, hx₀a, hx₀ord⟩, ⟨y₀, hy₀a, hy₀ord⟩⟩ := hW
  obtain ⟨x₁, hx₁, hx₁red⟩ := hred_fix x₀ (by rw [hx₀a]; exact h0)
  obtain ⟨y₁, hy₁, hy₁red⟩ := hred_fix y₀ (by rw [hy₀a]; exact pow_ne_zero _ h0)
  refine ⟨⟨x₁, hx₁red.trans hx₀a, ?_⟩, ⟨y₁, hy₁red.trans hy₀a, ?_⟩⟩
  · have := AlgebraicCurve.SemilinearAut.ord_smul g W ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) ((x₀ : A) : AlgebraicClosure ℚ))
    rw [smul_sub, hgjF, hgc, ← hx₁] at this
    rw [this]; exact hx₀ord
  · have := AlgebraicCurve.SemilinearAut.ord_smul g W ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) ((y₀ : A) : AlgebraicClosure ℚ))
    rw [smul_sub, hgjqF, hgc, ← hy₁] at this
    rw [this]; exact hy₀ord

theorem hasValue_sub_algebraMap {K F : Type*} [Field K] [Field F] [Algebra K F]
    (W : Place K F) (f : F) (b c : K) (hb : W.HasValue f b) :
    W.HasValue (f - algebraMap K F c) (b - c) := by
  obtain ⟨hmem, hres⟩ := hb
  refine ⟨sub_mem hmem (W.algebraMap_mem' c), ?_⟩
  have : (⟨f - algebraMap K F c, sub_mem hmem (W.algebraMap_mem' c)⟩ : W.toValuationSubring)
      = ⟨f, hmem⟩ - algebraMap K W.toValuationSubring c := by
    apply Subtype.ext; simp [AlgebraicCurve.Place.coe_algebraMap]
  rw [this, map_sub, hres, AlgebraicCurve.Place.residue_algebraMap, map_sub]

theorem ord_nodeCoord_sub_algebraMap_eq_single
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] (red : A →+* k)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (hq : 5 ≤ q) (a : k) (ha : a ∈ ssJSet q k) (ha2 : a ^ (q ^ 2) = a) (h0 : a ≠ 0) (h1728 : a ≠ 1728)
    (V' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (hV' : ((∃ x : A, red x = a ∧
            0 < V'.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
         (∃ y : A, red y = a ^ q ∧
            0 < V'.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ)))))
    (c : A) (hc : c ∈ IsLocalRing.maximalIdeal A) (hcq : ∃ d ∈ IsLocalRing.maximalIdeal A, c * d = ((q : ℕ) : A))
    (hcV' : V'.HasValue ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q))
          - (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) ^ q) ((c : A) : AlgebraicClosure ℚ))
    (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (hW : ((∃ x : A, red x = a ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
         (∃ y : A, red y = a ^ q ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ))))) :
    W.ord (((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q))
          - (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) ^ q) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) ((c : A) : AlgebraicClosure ℚ)) = (Finsupp.single V' (1 : ℤ)) W := by
  classical
  by_cases hWV : W = V'
  · subst hWV
    rw [Finsupp.single_eq_same]
    exact NodeLocalized.ord_nodeCoord_sub_eq_one_of_centred red hker hq a ha ha2 h0 h1728 W hW c hcV'
  · rw [Finsupp.single_apply, if_neg (Ne.symm hWV)]
    obtain ⟨xW, -, -, hxW⟩ := NodeLocalized.exists_hasValue_nodeCoord_of_centred red hker hq a ha ha2 h0 h1728 W hW
    have hne : ((xW : A) : AlgebraicClosure ℚ) - ((c : A) : AlgebraicClosure ℚ) ≠ 0 := by
      intro heq
      apply hWV
      have hxWc : xW = c := Subtype.ext (sub_eq_zero.1 heq)
      subst hxWc
      obtain ⟨W₀, -, huniq⟩ :=
        NodeLocalized.existsUnique_place_centred_hasValue_nodeCoord red hker hq a ha ha2 h0 h1728 xW hc hcq
      exact (huniq W ⟨hW, hxW⟩).trans (huniq V' ⟨hV', hcV'⟩).symm
    exact (hasValue_sub_algebraMap W _ _ _ hxW).ord_eq_zero hne

end ModularCurve.TubeEqOrd

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : P.LevelOneProlongationPair)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (hq : 5 ≤ q) (a : k) (ha : a ∈ ssJSet q k) (ha2 : a ^ (q ^ 2) = a) (h0 : a ≠ 0) (h1728 : a ≠ 1728)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (hV : ((∃ x : A, red x = a ∧
            0 < V.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
         (∃ y : A, red y = a ^ q ∧
            0 < V.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ))))) :
    ∃ (x : A) (u : (↥A)ˣ) (t : ↥(modularFunctionFieldBar (1 * q))) (h₁ : t ∈ R.R₁.integers) (h₂ : t ∈ R.R₂.integers),
      x ∈ IsLocalRing.maximalIdeal A ∧ (∃ d ∈ IsLocalRing.maximalIdeal A, x * d = ((q : ℕ) : A)) ∧
      σ (x : AlgebraicClosure ℚ) = ((u : A) : AlgebraicClosure ℚ) * (x : AlgebraicClosure ℚ) ∧
      V.HasValue ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q))
          - (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) ^ q) (x : AlgebraicClosure ℚ) ∧
      t = (((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q))
          - (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) ^ q) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (σ (x : AlgebraicClosure ℚ)))
          * (((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q))
          - (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) ^ q) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))⁻¹ ∧
      (R.residue₁ ⟨t, h₁⟩ : ↥(modularFunctionFieldC k 1)) = algebraMap k ↥(modularFunctionFieldC k 1) (red (u : A)) ∧
      (R.residue₂ ⟨t, h₂⟩ : ↥(modularFunctionFieldC k 1)) = 1 ∧
      ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), ((∃ x : A, red x = a ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
         (∃ y : A, red y = a ^ q ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ)))) →
        W.ord t = ((arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • (Finsupp.single V (1 : ℤ))
          - Finsupp.single V 1 : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))) W := by
  classical
  have hq0A : ((q : ℕ) : A) ≠ 0 := by
    intro h
    have : ((q : ℕ) : AlgebraicClosure ℚ) = 0 := by exact_mod_cast congrArg ((↑) : A → AlgebraicClosure ℚ) h
    exact (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero) this

  obtain ⟨x, hx𝔪, hxq, hxV⟩ :=
    NodeLocalized.exists_hasValue_nodeCoord_of_centred red hker hq a ha ha2 h0 h1728 V hV
  have hx0A : (x : A) ≠ 0 := by
    rintro rfl
    obtain ⟨d, -, hd⟩ := hxq
    exact hq0A (by simpa using hd.symm)
  have hx0 : ((x : A) : AlgebraicClosure ℚ) ≠ 0 := fun h => hx0A (Subtype.ext h)

  obtain ⟨hunit, -⟩ :=
    ValuationSubring.exists_units_mul_eq_and_residue_eq_tameCharacter_of_mem_inertiaSubgroupIn A hσ
  obtain ⟨u, hu, -⟩ := hunit ((x : A) : AlgebraicClosure ℚ) hx0
  set sx : A := (u : A) * x with hsx
  have hsxL : ((sx : A) : AlgebraicClosure ℚ) = σ ((x : A) : AlgebraicClosure ℚ) := by
    rw [hsx, Subring.coe_mul]; exact hu
  have hsx𝔪 : sx ∈ IsLocalRing.maximalIdeal A := Ideal.mul_mem_left _ _ hx𝔪
  obtain ⟨dx, hdx𝔪, hdx⟩ := hxq
  have hsxq : ∃ d ∈ IsLocalRing.maximalIdeal A, sx * d = ((q : ℕ) : A) := by
    refine ⟨(↑(u⁻¹) : A) * dx, Ideal.mul_mem_left _ _ hdx𝔪, ?_⟩
    rw [hsx]
    calc (u : A) * x * ((↑(u⁻¹) : A) * dx) = ((u : A) * (↑(u⁻¹) : A)) * (x * dx) := by ring
      _ = ((q : ℕ) : A) := by rw [Units.mul_inv, one_mul, hdx]

  set g := arithmeticGalois (modularFunctionFieldFull (1 * q)) σ with hg
  set jF : ↥(modularFunctionFieldBar (1 * q)) := (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) with hjF
  set jqF : ↥(modularFunctionFieldBar (1 * q)) := (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) with hjqF
  set G : ↥(modularFunctionFieldBar (1 * q)) := jqF - jF ^ q with hG
  set cx : ↥(modularFunctionFieldBar (1 * q)) := algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) ((x : A) : AlgebraicClosure ℚ) with hcx
  set cσx : ↥(modularFunctionFieldBar (1 * q)) := algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (σ ((x : A) : AlgebraicClosure ℚ)) with hcσx
  set t : ↥(modularFunctionFieldBar (1 * q)) := (G - cσx) * (G - cx)⁻¹ with ht

  have hgG : g • G = G := by
    rw [hG, smul_sub, smul_pow', hjF, hjqF, hg,
      arithmeticGalois_smul_coeffEmb (modularFunctionFieldFull (1 * q)) σ (modularFunctionField_le_full (1 * q) (jq_mem (1 * q))),
      arithmeticGalois_smul_coeffEmb (modularFunctionFieldFull (1 * q)) σ (jqd_mem_full (1 * q) (dvd_refl (1 * q)))]

  have hσVc := ModularCurve.TubeEqOrd.centred_smul (q := q) red hker a h0 σ hσ V hV
  have hσV : (g • V).HasValue G (σ ((x : A) : AlgebraicClosure ℚ)) := by
    have h := AlgebraicCurve.Place.HasValue.smul g hxV
    rw [hgG, hg, baseAut_arithmeticGalois] at h
    exact h

  have hA : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), ((∃ x : A, red x = a ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
         (∃ y : A, red y = a ^ q ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ)))) → W.ord (G - cx) = (Finsupp.single V (1 : ℤ)) W := by
    intro W hW
    rw [hG, hjqF, hjF, hcx]
    exact ModularCurve.TubeEqOrd.ord_nodeCoord_sub_algebraMap_eq_single red hker hq a ha ha2 h0 h1728 V hV x hx𝔪
      ⟨dx, hdx𝔪, hdx⟩ (by rw [← hjF, ← hjqF, ← hG]; exact hxV) W hW
  have hB : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), ((∃ x : A, red x = a ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
         (∃ y : A, red y = a ^ q ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ)))) → W.ord (G - cσx) = (Finsupp.single (g • V) (1 : ℤ)) W := by
    intro W hW
    rw [hG, hjqF, hjF, hcσx, ← hsxL]
    exact ModularCurve.TubeEqOrd.ord_nodeCoord_sub_algebraMap_eq_single red hker hq a ha ha2 h0 h1728 (g • V) hσVc sx hsx𝔪
      hsxq (by rw [hsxL, ← hjF, ← hjqF, ← hG]; exact hσV) W hW
  have hGcx_ne : G - cx ≠ 0 := by
    intro h0'
    have := hA V hV
    rw [h0', Finsupp.single_eq_same] at this
    simp at this
  have hGcσx_ne : G - cσx ≠ 0 := by
    intro h0'
    have := hB (g • V) hσVc
    rw [h0', Finsupp.single_eq_same] at this
    simp at this
  have hord : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), ((∃ x : A, red x = a ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
         (∃ y : A, red y = a ^ q ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ)))) →
      W.ord t = ((arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • (Finsupp.single V (1 : ℤ))
          - Finsupp.single V 1 : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))) W := by
    intro W hW
    rw [← hg, AlgebraicCurve.SemilinearAut.smul_single, Finsupp.sub_apply, ht,
      AlgebraicCurve.Place.ord_mul _ hGcσx_ne (inv_ne_zero hGcx_ne), AlgebraicCurve.Place.ord_inv, hA W hW, hB W hW]
    ring

  obtain ⟨h₁, hres₁⟩ := R.exists_mem_integersFst_residue₁_eq_algebraMap_of_mul_eq x dx u hdx𝔪 hdx t
    (by rw [ht, hG, hjqF, hjF, hcσx, hcx, ← hsxL, hsx])
  obtain ⟨h₂, hres₂⟩ := R.exists_mem_integersSnd_residue₂_eq_one_of_mem_maximalIdeal x sx hx𝔪 hsx𝔪 t
    (by rw [ht, hG, hjqF, hjF, hcσx, hcx, ← hsxL])
  exact ⟨x, u, t, h₁, h₂, hx𝔪, ⟨dx, hdx𝔪, hdx⟩, hu.symm, hxV, rfl, hres₁, hres₂, hord⟩

end S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_tubeEquation_smul_sub_self
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_tubeEquation_smul_sub_self (solution)
