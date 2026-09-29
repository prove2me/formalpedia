-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.mem_modularLocalizedAtPoint_iff_exists_mem_nodeIntegersOver
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/d2a64611-0015-56a9-b2c5-47fa3f36e3a9

import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Definitions.Def_ModularCurve_CharLFrobeniusGeomLevel
import Definitions.Def_ModularCurve_SupersingularNodes
import Definitions.Def_ModularCurve_CuspidalClass
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_GluedPic0
import Theorems.Thm_ModularCurve_pow_q_sq_eq_self_of_mem_ssJSet
import Theorems.Thm_ModularCurve_PlaceSpecialization_reduceFst_eq_iff_centred_levelOne
import Theorems.Thm_ModularCurve_isIntegral_modularLocalizedAtPoint_coeffSubring_of_forall_pole_not_centred
import Theorems.Thm_ModularCurve_NodeLocalized_exists_mul_eq_of_mem_fieldOver
import Theorems.Thm_ModularCurve_isIntegrallyClosed_modularLocalizedAtPoint_coeffSubring_of_lt_five
import Theorems.Thm_ModularCurve_isIntegrallyClosed_modularLocalizedAtPoint_coeffSubring_of_eq_zero_or_eq_1728
import Theorems.Thm_ModularCurve_isIntegrallyClosed_modularLocalizedAtPoint_coeffSubring_of_ne_zero_of_ne_1728
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_mem_modularLocalizedAtPoint_iff_exists_mem_nodeIntegersOver
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase instTopologicallyFGOfFiniteType AdicCompletion.instIsLocalRingMaximalIdeal"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₂_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₁_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong AlgebraicCurve.Pic.baseChange_mk"
p2m_attr_erase "simp" "AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring ModularCurve.NodeLocalized.coe_modularEvalAt AdicCompletion.evalₐ_mapₐ AdicCompletion.mapAlgEquivOfBijective_apply AdicCompletion.levelMapₐ_mk AdicCompletion.mapₐ_of AdicCompletion.mapAlgEquiv_symm_apply AdicCompletion.mapAlgEquiv_apply AdicCompletion.evalₐ_ofLevelwiseEquiv AdicCompletion.evalₐ_levelwiseHom AdicCompletion.localizationEquiv_of AdicCompletion.evalₐ_ofLevelwiseEquiv_symm Localization.AtPrime.quotientPowEquiv_mk ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one"
p2m_attr_erase "simp" "TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero AdicCompletion.transportOf_of AdicCompletion.selfCompletion_smul_of AdicCompletion.tensorRingEquiv_tmul AdicCompletion.completionOfAlgHom_apply AdicCompletion.completionBaseChangeHom_of AdicCompletion.tensorRingHom_tmul AdicCompletion.stabilizerToCompletionAut_of"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

p2m_open "AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_mem_modularLocalizedAtPoint_iff_exists_mem_nodeIntegersOver.ModularCurve"
p2m_open "ModularCurve.PlaceSpecialization~jFun P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_mem_modularLocalizedAtPoint_iff_exists_mem_nodeIntegersOver.ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_mem_modularLocalizedAtPoint_iff_exists_mem_nodeIntegersOver.ModularCurve.PlaceSpecialization.ProlongationTuple"
open ModularCurve.NodeLocalized

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple modularFunctionFieldBar qExpand qExpand_one_apply qExpand_congr jq ModularPolynomialData jq_mem modularFunctionFieldFull jqd_mem_full modularFunctionField_le_full coeffMap coeffMap_single coeffMap_coeffMap algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_mem_laurentBaseChange jqModC jqNModC jqModC_rat map_jqModC modularFunctionFieldC PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral qExpand_jqModC_eq_pow frobOnPlacesGeomLevel exists_ramification_frobenius KroneckerCongruence IsSupersingularPlace ssPlaces jGeomGen jNGeomGen jGeomGen_sub_algebraMap_ne_zero IsCentreOf frobeniusGeomLevel_jGeomGen_sub_pow IsCentreOf.frobOnPlacesGeomLevel transcendental_jqModC ssJSet IsAtkinLehnerAutFull atkinLehnerInvolutionFull isAtkinLehnerAutFull_atkinLehnerInvolutionFull atkinLehnerInvolutionFull_eq_refl frickeInvolutionBar frickeInvolutionBar_def IsFrickeAutFull frickeInvolutionFull isFrickeAutFull_frickeInvolutionFull frickeInvolutionFull_eq_refl geomAut geomAut_coeffEmb modularFunctionFieldFullC coeffMap_qExpand CharPReduction.modularLocalized NodeLocalized.coeffSubring NodeLocalized.redRestrict NodeLocalized.fieldOver NodeLocalized.modularLocalizedAtPoint pow_q_sq_eq_self_of_mem_ssJSet isIntegral_modularLocalizedAtPoint_coeffSubring_of_forall_pole_not_centred NodeLocalized.exists_mul_eq_of_mem_fieldOver isIntegrallyClosed_modularLocalizedAtPoint_coeffSubring_of_lt_five isIntegrallyClosed_modularLocalizedAtPoint_coeffSubring_of_eq_zero_or_eq_1728 isIntegrallyClosed_modularLocalizedAtPoint_coeffSubring_of_ne_zero_of_ne_1728"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "ProlongationTuple.atkinLehnerBar ProlongationTuple.jFun ProlongationTuple.jQFun ProlongationTuple reduceFst sp d0_j d0_j_pole d1 reduceFst_eq_iff_centred_levelOne"
namespace ProlongationTuple
p2m_export "ModularCurve.PlaceSpecialization.ProlongationTuple" "nodeIntegersOver atkinLehnerBar jFun jQFun mem_integers₂_iff residue₁ residue₁_apply IsModel RegularityLaw ι_coe R₁ redBar_residue mem_integersFst_iff R₂ redBar residue₁_coeffMap mem_integersSnd_iff"
namespace NLPG2
p2m_open "ModularCurve.PlaceSpecialization.ProlongationTuple ModularCurve.PlaceSpecialization~jFun ModularCurve"

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ}

local notation "ℚ̄" => AlgebraicClosure ℚ
local notation "𝔽" => modularFunctionFieldBar (N * q)

theorem coe_jFun : ((ProlongationTuple.jFun N q : ↥𝔽) : LaurentSeries ℚ̄) = jqModC ℚ̄ := by
  show coeffMap (algebraMap ℚ ℚ̄) jq = jqModC ℚ̄
  rw [← jqModC_rat]
  exact map_jqModC (algebraMap ℚ ℚ̄)

theorem coe_jQFun :
    ((ProlongationTuple.jQFun N q : ↥𝔽) : LaurentSeries ℚ̄) = qExpand ℚ̄ q (jqModC ℚ̄) := by
  show coeffMap (algebraMap ℚ ℚ̄) (qExpand ℚ q jq) = qExpand ℚ̄ q (jqModC ℚ̄)
  rw [coeffMap_qExpand, ← jqModC_rat]
  exact congrArg _ (map_jqModC (algebraMap ℚ ℚ̄))

theorem jqNModC_one_mul (L : Type*) [CommRing L] : jqNModC L (1 * q) = qExpand L q (jqModC L) := by
  rw [jqNModC]
  exact qExpand_congr (one_mul q) _

variable (N q) in

@[reducible] noncomputable def constF (K : IntermediateField ℚ ℚ̄) : ↥(coeffSubring A K) →+* ↥𝔽 :=
  (algebraMap ℚ̄ ↥𝔽).comp (coeffSubring A K).subtype

variable (N q) in

@[reducible] noncomputable def evalF (K : IntermediateField ℚ ℚ̄) (G : Fin 2 → ↥𝔽) : MvPolynomial (Fin 2) ↥(coeffSubring A K) →+* ↥𝔽 :=
  MvPolynomial.eval₂Hom (constF (A := A) (N := N) (q := q) K) G

variable (N q) in

@[reducible] noncomputable def stdPair : Fin 2 → ↥𝔽 := ![ProlongationTuple.jFun N q, ProlongationTuple.jQFun N q]

variable (N q) in
@[reducible] noncomputable def swapPair : Fin 2 → ↥𝔽 := ![ProlongationTuple.jQFun N q, ProlongationTuple.jFun N q]

theorem coe_evalF_stdPair (K : IntermediateField ℚ ℚ̄) (p : MvPolynomial (Fin 2) ↥(coeffSubring A K)) :
    ((evalF (A := A) (N := N) (q := q) K (stdPair (N := N) (q := q)) p : ↥𝔽) : LaurentSeries ℚ̄)
      = modularEval (1 * q) (coeffSubring A K) p := by
  have h : ((modularFunctionFieldBar (N * q)).val.toRingHom.comp (evalF (A := A) (N := N) (q := q) K (stdPair (N := N) (q := q))))
      = modularEval (1 * q) (coeffSubring A K) := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun i => ?_)
    · rw [RingHom.comp_apply, MvPolynomial.eval₂Hom_C, modularEval, MvPolynomial.eval₂Hom_C]
      rfl
    · rw [RingHom.comp_apply, MvPolynomial.eval₂Hom_X', modularEval, MvPolynomial.eval₂Hom_X']
      fin_cases i
      · show ((ProlongationTuple.jFun N q : ↥𝔽) : LaurentSeries ℚ̄) = jqModC ℚ̄
        exact coe_jFun
      · show ((ProlongationTuple.jQFun N q : ↥𝔽) : LaurentSeries ℚ̄) = jqNModC ℚ̄ (1 * q)
        rw [coe_jQFun, jqNModC_one_mul]
  exact RingHom.congr_fun h p

variable (R : ProlongationTuple P)

@[reducible] noncomputable def evalk (K : IntermediateField ℚ ℚ̄) (Gk : Fin 2 → LaurentSeries k) :
    MvPolynomial (Fin 2) ↥(coeffSubring A K) →+* LaurentSeries k :=
  MvPolynomial.eval₂Hom ((algebraMap k (LaurentSeries k)).comp (redRestrict red K)) Gk

theorem exists_mem_integersFst_evalF (K : IntermediateField ℚ ℚ̄) (G : Fin 2 → ↥𝔽)
    (Y : Fin 2 → LaurentSeries A) (hGY : ∀ i, coeffMap A.subtype (Y i) = ((G i : ↥𝔽) : LaurentSeries ℚ̄))
    (p : MvPolynomial (Fin 2) ↥(coeffSubring A K)) :
    ∃ h : evalF (A := A) (N := N) (q := q) K G p ∈ R.R₁.integers,
      ((R.residue₁ ⟨evalF (A := A) (N := N) (q := q) K G p, h⟩ : ↥(modularFunctionFieldC k N)) : LaurentSeries k)
        = evalk (red := red) K (fun i => coeffMap red (Y i)) p := by

  let incl : ↥(coeffSubring A K) →+* A := Subring.inclusion inf_le_left
  let CA : A →+* LaurentSeries A := HahnSeries.C
  let y : LaurentSeries A := MvPolynomial.eval₂Hom (CA.comp incl) Y p
  have hy : coeffMap A.subtype y = ((evalF (A := A) (N := N) (q := q) K G p : ↥𝔽) : LaurentSeries ℚ̄) := by
    have h1 : (coeffMap A.subtype).comp (MvPolynomial.eval₂Hom (CA.comp incl) Y)
        = (modularFunctionFieldBar (N * q)).val.toRingHom.comp (evalF (A := A) (N := N) (q := q) K G) := by
      refine MvPolynomial.ringHom_ext (fun c => ?_) (fun i => ?_)
      · rw [RingHom.comp_apply, RingHom.comp_apply, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C,
          RingHom.comp_apply]
        show coeffMap A.subtype (HahnSeries.C (incl c)) = (((algebraMap ℚ̄ ↥𝔽) (c : ℚ̄) : ↥𝔽) : LaurentSeries ℚ̄)
        rw [HahnSeries.C_apply, coeffMap_single]
        show HahnSeries.single 0 ((c : ℚ̄)) = algebraMap ℚ̄ (LaurentSeries ℚ̄) (c : ℚ̄)
        rw [algebraMap_laurentSeries_eq_single]
      · rw [RingHom.comp_apply, RingHom.comp_apply, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X']
        exact hGY i
    exact RingHom.congr_fun h1 p
  have hyF : coeffMap A.subtype y ∈ modularFunctionFieldBar (N * q) := by
    rw [hy]; exact SetLike.coe_mem _
  obtain ⟨h, hres⟩ := R.residue₁_coeffMap y hyF
  have heq : (⟨coeffMap A.subtype y, hyF⟩ : ↥𝔽) = evalF (A := A) (N := N) (q := q) K G p := Subtype.ext hy
  have h' : evalF (A := A) (N := N) (q := q) K G p ∈ R.R₁.integers := heq ▸ h
  refine ⟨h', ?_⟩
  have hres' : ((R.R₁.residue ⟨evalF (A := A) (N := N) (q := q) K G p, h'⟩ : ↥(modularFunctionFieldFullC (ResidueField A) N)) :
      LaurentSeries (ResidueField A)) = coeffMap (IsLocalRing.residue A) y := by
    have : (⟨evalF (A := A) (N := N) (q := q) K G p, h'⟩ : ↥R.R₁.integers) = ⟨⟨coeffMap A.subtype y, hyF⟩, h⟩ :=
      Subtype.ext heq.symm
    rw [this]; exact hres
  have hcomp : R.redBar.comp (IsLocalRing.residue A) = red := RingHom.ext R.redBar_residue
  rw [residue₁_apply, R.ι_coe, hres', coeffMap_coeffMap, hcomp]

  have h2 : (coeffMap red).comp (MvPolynomial.eval₂Hom (CA.comp incl) Y)
      = evalk (red := red) K (fun i => coeffMap red (Y i)) := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun i => ?_)
    · rw [RingHom.comp_apply, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C, RingHom.comp_apply,
        RingHom.comp_apply]
      show coeffMap red (HahnSeries.C (incl c)) = algebraMap k (LaurentSeries k) (redRestrict red K c)
      rw [HahnSeries.C_apply, coeffMap_single, algebraMap_laurentSeries_eq_single]
      rfl
    · rw [RingHom.comp_apply, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X']
  exact RingHom.congr_fun h2 p

theorem coeffMap_subtype_jqModC : coeffMap A.subtype (jqModC A) = ((ProlongationTuple.jFun N q : ↥𝔽) : LaurentSeries ℚ̄) := by
  rw [coe_jFun]; exact map_jqModC A.subtype

theorem coeffMap_subtype_qExpand_jqModC :
    coeffMap A.subtype (qExpand A q (jqModC A)) = ((ProlongationTuple.jQFun N q : ↥𝔽) : LaurentSeries ℚ̄) := by
  rw [coe_jQFun, coeffMap_qExpand]
  exact congrArg _ (map_jqModC A.subtype)

theorem coeffMap_red_jqModC : coeffMap red (jqModC A) = jqModC k := map_jqModC red

theorem coeffMap_red_qExpand_jqModC : coeffMap red (qExpand A q (jqModC A)) = qExpand k q (jqModC k) := by
  rw [coeffMap_qExpand]; exact congrArg _ (map_jqModC red)

theorem evalk_std_ne_zero (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
    (K : IntermediateField ℚ ℚ̄) (a : k)
    (s : MvPolynomial (Fin 2) ↥(coeffSubring A K)) (hs : pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) s ≠ 0) :
    evalk (red := red) K ![jqModC k, qExpand k q (jqModC k)] s ≠ 0 := by
  intro h0
  apply hs

  let sbar : MvPolynomial (Fin 2) k := MvPolynomial.map (redRestrict red K) s
  let Q : Polynomial k := MvPolynomial.aeval ![Polynomial.X, Polynomial.X ^ q] sbar
  have hQ : Polynomial.aeval (jqModC k) Q = 0 := by
    have h1 : Polynomial.aeval (jqModC k) Q = MvPolynomial.aeval ![jqModC k, jqModC k ^ q] sbar := by
      show ((Polynomial.aeval (jqModC k)).comp (MvPolynomial.aeval ![Polynomial.X, Polynomial.X ^ q])) sbar = _
      rw [MvPolynomial.comp_aeval]
      congr 2
      funext i
      fin_cases i
      · show Polynomial.aeval (jqModC k) (Polynomial.X : Polynomial k) = jqModC k
        exact Polynomial.aeval_X _
      · show Polynomial.aeval (jqModC k) ((Polynomial.X : Polynomial k) ^ q) = jqModC k ^ q
        rw [map_pow, Polynomial.aeval_X]
    rw [h1, ← qExpand_jqModC_eq_pow k data hKr]
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
    exact h0
  have hQ0 : Q = 0 := by
    by_contra hne
    exact transcendental_jqModC k ⟨Q, hne, hQ⟩

  have h2 : Polynomial.eval a Q = pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) s := by
    show Polynomial.evalRingHom a (MvPolynomial.eval₂ (algebraMap k (Polynomial k))
      ![Polynomial.X, Polynomial.X ^ q] sbar) = _
    rw [MvPolynomial.eval₂_comp_left, MvPolynomial.eval₂_map]
    show MvPolynomial.eval₂Hom _ _ s = MvPolynomial.eval₂Hom _ _ s
    have h3 : MvPolynomial.eval₂Hom (((Polynomial.evalRingHom a).comp (algebraMap k (Polynomial k))).comp
        (redRestrict red K)) (⇑(Polynomial.evalRingHom a) ∘ ![Polynomial.X, Polynomial.X ^ q])
        = MvPolynomial.eval₂Hom (redRestrict red K) ![a, a ^ q] := by
      refine MvPolynomial.ringHom_ext (fun c => ?_) (fun i => ?_)
      · rw [MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C, RingHom.comp_apply, RingHom.comp_apply]
        show Polynomial.eval a (algebraMap k (Polynomial k) (redRestrict red K c)) = redRestrict red K c
        rw [Polynomial.algebraMap_eq, Polynomial.eval_C]
      · rw [MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X']
        fin_cases i
        · show Polynomial.eval a (Polynomial.X : Polynomial k) = a
          exact Polynomial.eval_X
        · show Polynomial.eval a ((Polynomial.X : Polynomial k) ^ q) = a ^ q
          rw [Polynomial.eval_pow, Polynomial.eval_X]
    exact RingHom.congr_fun h3 s
  rw [← h2, hQ0, Polynomial.eval_zero]

theorem evalk_swap_ne_zero (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
    (K : IntermediateField ℚ ℚ̄) (a : k) (ha2 : a ^ (q ^ 2) = a)
    (s : MvPolynomial (Fin 2) ↥(coeffSubring A K)) (hs : pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) s ≠ 0) :
    evalk (red := red) K ![qExpand k q (jqModC k), jqModC k] s ≠ 0 := by
  intro h0
  apply hs
  let sbar : MvPolynomial (Fin 2) k := MvPolynomial.map (redRestrict red K) s
  let Q : Polynomial k := MvPolynomial.aeval ![Polynomial.X ^ q, Polynomial.X] sbar
  have hQ : Polynomial.aeval (jqModC k) Q = 0 := by
    have h1 : Polynomial.aeval (jqModC k) Q = MvPolynomial.aeval ![jqModC k ^ q, jqModC k] sbar := by
      show ((Polynomial.aeval (jqModC k)).comp (MvPolynomial.aeval ![Polynomial.X ^ q, Polynomial.X])) sbar = _
      rw [MvPolynomial.comp_aeval]
      congr 2
      funext i
      fin_cases i
      · show Polynomial.aeval (jqModC k) ((Polynomial.X : Polynomial k) ^ q) = jqModC k ^ q
        rw [map_pow, Polynomial.aeval_X]
      · show Polynomial.aeval (jqModC k) (Polynomial.X : Polynomial k) = jqModC k
        exact Polynomial.aeval_X _
    rw [h1, ← qExpand_jqModC_eq_pow k data hKr]
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
    exact h0
  have hQ0 : Q = 0 := by
    by_contra hne
    exact transcendental_jqModC k ⟨Q, hne, hQ⟩
  have h2 : Polynomial.eval (a ^ q) Q = pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) s := by
    show Polynomial.evalRingHom (a ^ q) (MvPolynomial.eval₂ (algebraMap k (Polynomial k))
      ![Polynomial.X ^ q, Polynomial.X] sbar) = _
    rw [MvPolynomial.eval₂_comp_left, MvPolynomial.eval₂_map]
    show MvPolynomial.eval₂Hom _ _ s = MvPolynomial.eval₂Hom _ _ s
    have h3 : MvPolynomial.eval₂Hom (((Polynomial.evalRingHom (a ^ q)).comp (algebraMap k (Polynomial k))).comp
        (redRestrict red K)) (⇑(Polynomial.evalRingHom (a ^ q)) ∘ ![Polynomial.X ^ q, Polynomial.X])
        = MvPolynomial.eval₂Hom (redRestrict red K) ![a, a ^ q] := by
      refine MvPolynomial.ringHom_ext (fun c => ?_) (fun i => ?_)
      · rw [MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C, RingHom.comp_apply, RingHom.comp_apply]
        show Polynomial.eval (a ^ q) (algebraMap k (Polynomial k) (redRestrict red K c)) = redRestrict red K c
        rw [Polynomial.algebraMap_eq, Polynomial.eval_C]
      · rw [MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X']
        fin_cases i
        · show Polynomial.eval (a ^ q) ((Polynomial.X : Polynomial k) ^ q) = a
          rw [Polynomial.eval_pow, Polynomial.eval_X, ← pow_mul, ← pow_two, ha2]
        · show Polynomial.eval (a ^ q) (Polynomial.X : Polynomial k) = a ^ q
          exact Polynomial.eval_X
    exact RingHom.congr_fun h3 s
  rw [← h2, hQ0, Polynomial.eval_zero]

theorem inv_mem_integersFst_of_residue₁_coe_ne_zero {g : ↥𝔽} (h : g ∈ R.R₁.integers)
    (hne : ((R.residue₁ ⟨g, h⟩ : ↥(modularFunctionFieldC k N)) : LaurentSeries k) ≠ 0) :
    g⁻¹ ∈ R.R₁.integers := by
  have hres : R.R₁.residue ⟨g, h⟩ ≠ 0 := by
    intro h0
    apply hne
    rw [residue₁_apply, h0, map_zero]
    rfl
  obtain ⟨u, hu⟩ := R.R₁.isUnit_of_residue_ne_zero hres
  have hg : ((u : ↥R.R₁.integers) : ↥𝔽) = g := by rw [hu]
  have hinv : (((u⁻¹ : (↥R.R₁.integers)ˣ) : ↥R.R₁.integers) : ↥𝔽) = g⁻¹ := by
    have h1 : g * (((u⁻¹ : (↥R.R₁.integers)ˣ) : ↥R.R₁.integers) : ↥𝔽) = 1 := by
      rw [← hg, ← MulMemClass.coe_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]; rfl
    exact (inv_eq_of_mul_eq_one_right h1).symm
  rw [← hinv]
  exact SetLike.coe_mem _

theorem atkinLehnerBar_evalF (K : IntermediateField ℚ ℚ̄) :
    (∀ p, atkinLehnerBar N q (evalF (A := A) (N := N) (q := q) K (stdPair (N := N) (q := q)) p) = evalF (A := A) (N := N) (q := q) K (stdPair (N := N) (q := q)) p) ∨
    (∀ p, atkinLehnerBar N q (evalF (A := A) (N := N) (q := q) K (stdPair (N := N) (q := q)) p) = evalF (A := A) (N := N) (q := q) K (swapPair (N := N) (q := q)) p) := by
  classical
  by_cases hex : ∃ σ : modularFunctionFieldFull (N * q) ≃ₐ[ℚ] modularFunctionFieldFull (N * q),
      IsAtkinLehnerAutFull N q σ
  · right
    have hAL := (isAtkinLehnerAutFull_atkinLehnerInvolutionFull N q hex) 1 inferInstance (one_dvd N)

    let f₁ : ↥(modularFunctionFieldFull (N * q)) :=
      ⟨qExpand ℚ 1 jq, jqd_mem_full (N * q) (Dvd.dvd.mul_right (one_dvd N) q)⟩
    let f₂ : ↥(modularFunctionFieldFull (N * q)) :=
      ⟨qExpand ℚ (1 * q) jq, jqd_mem_full (N * q) (Nat.mul_dvd_mul_right (one_dvd N) q)⟩
    have e₁ : ProlongationTuple.jFun N q
        = ⟨coeffEmb ℚ̄ (f₁ : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange ℚ̄ f₁.2⟩ :=
      Subtype.ext (by
        show coeffEmb ℚ̄ jq = coeffEmb ℚ̄ (qExpand ℚ 1 jq)
        rw [qExpand_one_apply])
    have e₂ : ProlongationTuple.jQFun N q
        = ⟨coeffEmb ℚ̄ (f₂ : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange ℚ̄ f₂.2⟩ :=
      Subtype.ext (by
        show coeffEmb ℚ̄ (qExpand ℚ q jq) = coeffEmb ℚ̄ (qExpand ℚ (1 * q) jq)
        rw [qExpand_congr (one_mul q)])
    have hj : atkinLehnerBar N q (ProlongationTuple.jFun N q) = ProlongationTuple.jQFun N q := by
      rw [e₁, atkinLehnerBar, geomAut_coeffEmb, e₂]
      exact Subtype.ext (congrArg (fun z : ↥(modularFunctionFieldFull (N * q)) => coeffEmb ℚ̄ (z : LaurentSeries ℚ)) hAL.1)
    have hjq : atkinLehnerBar N q (ProlongationTuple.jQFun N q) = ProlongationTuple.jFun N q := by
      rw [e₂, atkinLehnerBar, geomAut_coeffEmb, e₁]
      exact Subtype.ext (congrArg (fun z : ↥(modularFunctionFieldFull (N * q)) => coeffEmb ℚ̄ (z : LaurentSeries ℚ)) hAL.2)
    have hcomp : (atkinLehnerBar N q).toAlgHom.toRingHom.comp (evalF (A := A) (N := N) (q := q) K (stdPair (N := N) (q := q)))
        = evalF (A := A) (N := N) (q := q) K (swapPair (N := N) (q := q)) := by
      refine MvPolynomial.ringHom_ext (fun c => ?_) (fun i => ?_)
      · rw [RingHom.comp_apply, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C]
        show atkinLehnerBar N q (algebraMap ℚ̄ ↥𝔽 (c : ℚ̄)) = algebraMap ℚ̄ ↥𝔽 (c : ℚ̄)
        exact AlgEquiv.commutes _ _
      · rw [RingHom.comp_apply, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X']
        fin_cases i
        · exact hj
        · exact hjq
    intro p
    exact RingHom.congr_fun hcomp p
  · left
    intro p
    rw [show atkinLehnerBar N q = geomAut ℚ̄ (modularFunctionFieldFull (N * q)) (atkinLehnerInvolutionFull N q)
        from rfl, atkinLehnerInvolutionFull_eq_refl N q hex,
      show (AlgEquiv.refl : ↥(modularFunctionFieldFull (N * q)) ≃ₐ[ℚ] ↥(modularFunctionFieldFull (N * q))) = 1
        from rfl, map_one, AlgEquiv.one_apply]

variable (N) in

noncomputable def jLevel : ↥(modularFunctionFieldBar N) :=
  ⟨coeffEmb ℚ̄ jq, coeffEmb_mem_laurentBaseChange ℚ̄ (modularFunctionField_le_full N (jq_mem N))⟩

theorem heckeAlphaBar_jLevel : heckeAlphaBar ℚ̄ N q (jLevel N) = ProlongationTuple.jFun N q :=
  Subtype.ext (coe_heckeAlphaBar N q _)

theorem heckeBetaBar_jLevel : heckeBetaBar ℚ̄ N q (jLevel N) = ProlongationTuple.jQFun N q := by
  apply Subtype.ext
  rw [coe_heckeBetaBar]
  show qExpand ℚ̄ q (coeffEmb ℚ̄ jq) = coeffEmb ℚ̄ (qExpand ℚ q jq)
  rw [coeffEmb, coeffMap_qExpand]

theorem evalAt_jGeomGen_eq_of_ord_pos {v : Place k ↥(modularFunctionFieldC k N)} {c : k}
    (h : 0 < v.ord (jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) c)) :
    v.evalAt (jGeomGen k N) = c := by
  have hmem : jGeomGen k N ∈ v.toValuationSubring := by
    have h1 : jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) c ∈ v.toValuationSubring :=
      v.mem_of_ord_nonneg (jGeomGen_sub_algebraMap_ne_zero k N c) h.le
    have := add_mem h1 (v.algebraMap_mem' c)
    rwa [sub_add_cancel] at this
  rw [v.evalAt_congr hmem (v.algebraMap_mem' c) (Or.inr h), v.evalAt_algebraMap]

theorem exists_values_of_reduceFst_eq [IsAlgClosed k] [DecidableEq k]
    {w : Place k ↥(modularFunctionFieldC k N)} (hw : w ∈ ssPlaces q N k) {a : k} (ha : w.evalAt (jGeomGen k N) = a)
    {V : Place ℚ̄ ↥𝔽} (hV : P.reduceFst V = w) :
    (∃ x : A, red x = a ∧ 0 < V.ord (ProlongationTuple.jFun N q - algebraMap ℚ̄ ↥𝔽 (x : ℚ̄))) ∧
    (∃ y : A, red y = a ^ q ∧ 0 < V.ord (ProlongationTuple.jQFun N q - algebraMap ℚ̄ ↥𝔽 (y : ℚ̄))) := by
  have hss : IsSupersingularPlace q N k w := hw
  have hcen : IsCentreOf k N (w.evalAt (jGeomGen k N), w.evalAt (jNGeomGen k N)) w := hss.isCentreOf_evalAt
  have haS : a ∈ ssJSet q k := ha ▸ hss.2.2
  have ha2 : a ^ (q ^ 2) = a := pow_q_sq_eq_self_of_mem_ssJSet q haS
  set vα := V.restrictAlong (heckeAlphaBar ℚ̄ N q) hα with hvα
  set vβ := V.restrictAlong (heckeBetaBar ℚ̄ N q) hβ with hvβ
  have hspα : P.sp vα = w := hV
  constructor
  ·
    have hmem : jGeomGen k N ∈ (P.sp vα).toValuationSubring := by rw [hspα]; exact hcen.jGeomGen_mem
    have hx : ∃ x : A, 0 < vα.ord (jLevel N - algebraMap ℚ̄ ↥(modularFunctionFieldBar N) (x : ℚ̄)) := by
      by_contra hne
      have hle : ∀ x : A, vα.ord (jLevel N - algebraMap ℚ̄ ↥(modularFunctionFieldBar N) (x : ℚ̄)) ≤ 0 :=
        fun x => not_lt.mp fun hlt => hne ⟨x, hlt⟩
      exact absurd (P.d0_j_pole vα hle) (not_lt.mpr (Place.ord_nonneg_of_mem _ hmem))
    obtain ⟨x, hx⟩ := hx
    refine ⟨x, ?_, ?_⟩
    · have hz := P.d0_j vα x hx
      rw [hspα] at hz
      rw [← ha]
      exact (evalAt_jGeomGen_eq_of_ord_pos hz).symm
    · have hord := Place.ord_restrictAlong (heckeAlphaBar ℚ̄ N q) hα V
        (jLevel N - algebraMap ℚ̄ ↥(modularFunctionFieldBar N) (x : ℚ̄))
      rw [map_sub, AlgHom.commutes, heckeAlphaBar_jLevel] at hord
      rw [hord]
      refine mul_pos ?_ hx
      have : 0 < Place.ramificationIndexAlong (heckeAlphaBar ℚ̄ N q) V := by
        letI := algebraAlong (heckeAlphaBar ℚ̄ N q)
        haveI := isScalarTower_along (heckeAlphaBar ℚ̄ N q)
        haveI := isIntegral_along (heckeAlphaBar ℚ̄ N q) hα
        exact V.ramificationIndex_pos (F := ↥(modularFunctionFieldBar N))
      exact_mod_cast this
  ·
    have hβpos : 0 < (P.sp vβ).ord (jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) (a ^ q)) := by
      rcases P.d1 V with h | h
      ·
        have hw' : frobOnPlacesGeomLevel k N data hKr (P.sp vβ) = w := h.symm.trans hspα
        obtain ⟨e, he, -, hord⟩ := exists_ramification_frobenius k N data hKr (P.sp vβ)
        have hkey := hord (jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) ((a ^ q) ^ q))
        rw [frobeniusGeomLevel_jGeomGen_sub_pow k N data hKr (a ^ q), hw',
          show (jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) (a ^ q)) ^ q
            = (jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) (a ^ q)) ^ ((q : ℕ) : ℤ)
            from (zpow_natCast _ q).symm, Place.ord_zpow, ← pow_mul, ← pow_two, ha2] at hkey
        have hwa : 0 < w.ord (jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) a) := by
          have := hcen.1; rwa [ha] at this
        have hq : 0 < ((q : ℕ) : ℤ) := by exact_mod_cast (Fact.out : q.Prime).pos
        have hprod : 0 < ((q : ℕ) : ℤ) * (P.sp vβ).ord (jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) (a ^ q)) := by
          rw [hkey]; exact mul_pos (by exact_mod_cast he) hwa
        by_contra hle
        push_neg at hle
        nlinarith
      ·
        have hw' : P.sp vβ = frobOnPlacesGeomLevel k N data hKr w := h.symm.trans (congrArg _ hspα)
        rw [hw']
        have := (IsCentreOf.frobOnPlacesGeomLevel data hKr hcen).1
        rwa [ha] at this
    have hmem : jGeomGen k N ∈ (P.sp vβ).toValuationSubring := by
      have h1 : jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) (a ^ q) ∈ (P.sp vβ).toValuationSubring :=
        (P.sp vβ).mem_of_ord_nonneg (jGeomGen_sub_algebraMap_ne_zero k N (a ^ q)) hβpos.le
      have := add_mem h1 ((P.sp vβ).algebraMap_mem' (a ^ q))
      rwa [sub_add_cancel] at this
    have hy : ∃ y : A, 0 < vβ.ord (jLevel N - algebraMap ℚ̄ ↥(modularFunctionFieldBar N) (y : ℚ̄)) := by
      by_contra hne
      have hle : ∀ y : A, vβ.ord (jLevel N - algebraMap ℚ̄ ↥(modularFunctionFieldBar N) (y : ℚ̄)) ≤ 0 :=
        fun y => not_lt.mp fun hlt => hne ⟨y, hlt⟩
      exact absurd (P.d0_j_pole vβ hle) (not_lt.mpr (Place.ord_nonneg_of_mem _ hmem))
    obtain ⟨y, hy⟩ := hy
    refine ⟨y, ?_, ?_⟩
    · have hz := P.d0_j vβ y hy
      rw [← evalAt_jGeomGen_eq_of_ord_pos hβpos]
      exact (evalAt_jGeomGen_eq_of_ord_pos hz).symm
    · have hord := Place.ord_restrictAlong (heckeBetaBar ℚ̄ N q) hβ V
        (jLevel N - algebraMap ℚ̄ ↥(modularFunctionFieldBar N) (y : ℚ̄))
      rw [map_sub, AlgHom.commutes, heckeBetaBar_jLevel] at hord
      rw [hord]
      refine mul_pos ?_ hy
      have : 0 < Place.ramificationIndexAlong (heckeBetaBar ℚ̄ N q) V := by
        letI := algebraAlong (heckeBetaBar ℚ̄ N q)
        haveI := isScalarTower_along (heckeBetaBar ℚ̄ N q)
        haveI := isIntegral_along (heckeBetaBar ℚ̄ N q) hβ
        exact V.ramificationIndex_pos (F := ↥(modularFunctionFieldBar N))
      exact_mod_cast this

theorem evalF_mul_inv_mem_of_values (K : IntermediateField ℚ ℚ̄) {V : Place ℚ̄ ↥𝔽} {x y : A}
    (hx : 0 < V.ord (ProlongationTuple.jFun N q - algebraMap ℚ̄ ↥𝔽 (x : ℚ̄)))
    (hy : 0 < V.ord (ProlongationTuple.jQFun N q - algebraMap ℚ̄ ↥𝔽 (y : ℚ̄)))
    (r s : MvPolynomial (Fin 2) ↥(coeffSubring A K))
    (hs : red (MvPolynomial.eval₂ (Subring.inclusion inf_le_left : ↥(coeffSubring A K) →+* ↥A) ![x, y] s) ≠ 0) :
    evalF (A := A) (N := N) (q := q) K (stdPair (N := N) (q := q)) r * (evalF (A := A) (N := N) (q := q) K (stdPair (N := N) (q := q)) s)⁻¹ ∈ V.toValuationSubring := by
  set O := V.toValuationSubring with hO

  have memj : ProlongationTuple.jFun N q ∈ O := by
    have hne : ProlongationTuple.jFun N q - algebraMap ℚ̄ ↥𝔽 (x : ℚ̄) ≠ 0 := by
      intro h0; rw [h0, Place.ord_zero] at hx; exact lt_irrefl _ hx
    have h1 := V.mem_of_ord_nonneg hne hx.le
    have := add_mem h1 (V.algebraMap_mem' (x : ℚ̄))
    rwa [sub_add_cancel] at this
  have memjq : ProlongationTuple.jQFun N q ∈ O := by
    have hne : ProlongationTuple.jQFun N q - algebraMap ℚ̄ ↥𝔽 (y : ℚ̄) ≠ 0 := by
      intro h0; rw [h0, Place.ord_zero] at hy; exact lt_irrefl _ hy
    have h1 := V.mem_of_ord_nonneg hne hy.le
    have := add_mem h1 (V.algebraMap_mem' (y : ℚ̄))
    rwa [sub_add_cancel] at this

  let incl : ↥(coeffSubring A K) →+* A := Subring.inclusion inf_le_left
  let cO : A →+* ↥O := (algebraMap ℚ̄ ↥O).comp A.subtype
  let evalO : MvPolynomial (Fin 2) ↥(coeffSubring A K) →+* ↥O :=
    MvPolynomial.eval₂Hom (cO.comp incl) ![⟨_, memj⟩, ⟨_, memjq⟩]
  have hevH : O.subtype.comp evalO = evalF (A := A) (N := N) (q := q) K (stdPair (N := N) (q := q)) := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun i => ?_)
    · rw [RingHom.comp_apply, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C]
      show ((algebraMap ℚ̄ ↥O ((c : ℚ̄))) : ↥𝔽) = algebraMap ℚ̄ ↥𝔽 (c : ℚ̄)
      exact Place.coe_algebraMap V _
    · rw [RingHom.comp_apply, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X']
      fin_cases i <;> rfl
  have hev : ∀ p, ((evalO p : ↥O) : ↥𝔽) = evalF (A := A) (N := N) (q := q) K (stdPair (N := N) (q := q)) p :=
    fun p => RingHom.congr_fun hevH p

  let c : A := MvPolynomial.eval₂Hom incl ![x, y] s
  have hc0 : (c : ℚ̄) ≠ 0 := by
    intro h0
    apply hs
    have : c = 0 := Subtype.ext h0
    show red c = 0
    rw [this, map_zero]
  have hresj : IsLocalRing.residue ↥O ⟨_, memj⟩ = IsLocalRing.residue ↥O (algebraMap ℚ̄ ↥O (x : ℚ̄)) := by
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    have hsub : ((⟨_, memj⟩ : ↥O) - algebraMap ℚ̄ ↥O (x : ℚ̄) : ↥O)
        = ⟨ProlongationTuple.jFun N q - algebraMap ℚ̄ ↥𝔽 (x : ℚ̄), sub_mem memj (V.algebraMap_mem' _)⟩ := by
      apply Subtype.ext
      show ProlongationTuple.jFun N q - ((algebraMap ℚ̄ ↥O (x : ℚ̄) : ↥O) : ↥𝔽) = _
      rw [Place.coe_algebraMap]
    rw [hsub]
    exact V.mk_mem_maximalIdeal_of_ord_pos _ hx
  have hresjq : IsLocalRing.residue ↥O ⟨_, memjq⟩ = IsLocalRing.residue ↥O (algebraMap ℚ̄ ↥O (y : ℚ̄)) := by
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    have hsub : ((⟨_, memjq⟩ : ↥O) - algebraMap ℚ̄ ↥O (y : ℚ̄) : ↥O)
        = ⟨ProlongationTuple.jQFun N q - algebraMap ℚ̄ ↥𝔽 (y : ℚ̄), sub_mem memjq (V.algebraMap_mem' _)⟩ := by
      apply Subtype.ext
      show ProlongationTuple.jQFun N q - ((algebraMap ℚ̄ ↥O (y : ℚ̄) : ↥O) : ↥𝔽) = _
      rw [Place.coe_algebraMap]
    rw [hsub]
    exact V.mk_mem_maximalIdeal_of_ord_pos _ hy
  have hresH : (IsLocalRing.residue ↥O).comp evalO
      = ((IsLocalRing.residue ↥O).comp cO).comp (MvPolynomial.eval₂Hom incl ![x, y]) := by
    refine MvPolynomial.ringHom_ext (fun d => ?_) (fun i => ?_)
    · rw [RingHom.comp_apply, RingHom.comp_apply, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C]
      rfl
    · rw [RingHom.comp_apply, RingHom.comp_apply, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X']
      fin_cases i
      · exact hresj
      · exact hresjq
  have hres : IsLocalRing.residue ↥O (evalO s) = IsLocalRing.residue ↥O (cO c) :=
    RingHom.congr_fun hresH s
  have hunit : IsUnit (evalO s) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, hres, IsLocalRing.residue_ne_zero_iff_isUnit]
    exact (isUnit_iff_ne_zero.mpr hc0).map (algebraMap ℚ̄ ↥O)
  obtain ⟨u, hu⟩ := hunit
  have hinv : (((u⁻¹ : (↥O)ˣ) : ↥O) : ↥𝔽) = (evalF (A := A) (N := N) (q := q) K (stdPair (N := N) (q := q)) s)⁻¹ := by
    have h1 : evalF (A := A) (N := N) (q := q) K (stdPair (N := N) (q := q)) s * (((u⁻¹ : (↥O)ˣ) : ↥O) : ↥𝔽) = 1 := by
      rw [← hev s, ← hu, ← MulMemClass.coe_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]; rfl
    exact (inv_eq_of_mul_eq_one_right h1).symm
  rw [← hev r, ← hinv]
  exact mul_mem (SetLike.coe_mem _) (SetLike.coe_mem _)

theorem exists_mem_nodeIntegersOver_of_mem_modularLocalizedAtPoint [IsAlgClosed k] [DecidableEq k]
    (K : IntermediateField ℚ ℚ̄)
    (hjqK : qExpand ℚ̄ q (jqModC ℚ̄) ∈ NodeLocalized.fieldOver (N * q) K)
    {w : Place k ↥(modularFunctionFieldC k N)} (hw : w ∈ ssPlaces q N k)
    {a : k} (ha : w.evalAt (jGeomGen k N) = a)
    {f : LaurentSeries ℚ̄}
    (hf : f ∈ modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) :
    ∃ g : ↥𝔽, g ∈ R.nodeIntegersOver K w ∧ (g : LaurentSeries ℚ̄) = f := by
  obtain ⟨r, s, hs, hfs⟩ := hf
  have hss : IsSupersingularPlace q N k w := hw
  have haS : a ∈ ssJSet q k := ha ▸ hss.2.2
  have ha2 : a ^ (q ^ 2) = a := pow_q_sq_eq_self_of_mem_ssJSet q haS

  have hstd : ∀ i, coeffMap A.subtype ((![jqModC A, qExpand A q (jqModC A)] : Fin 2 → LaurentSeries A) i)
      = (((stdPair (N := N) (q := q) : Fin 2 → ↥𝔽) i : ↥𝔽) : LaurentSeries ℚ̄) := by
    intro i; fin_cases i
    · exact coeffMap_subtype_jqModC (N := N) (q := q)
    · exact coeffMap_subtype_qExpand_jqModC (N := N) (q := q)
  have hswap : ∀ i, coeffMap A.subtype ((![qExpand A q (jqModC A), jqModC A] : Fin 2 → LaurentSeries A) i)
      = (((swapPair (N := N) (q := q) : Fin 2 → ↥𝔽) i : ↥𝔽) : LaurentSeries ℚ̄) := by
    intro i; fin_cases i
    · exact coeffMap_subtype_qExpand_jqModC (N := N) (q := q)
    · exact coeffMap_subtype_jqModC (N := N) (q := q)
  have hredstd : (fun i => coeffMap red ((![jqModC A, qExpand A q (jqModC A)] : Fin 2 → LaurentSeries A) i))
      = ![jqModC k, qExpand k q (jqModC k)] := by
    funext i; fin_cases i
    · exact coeffMap_red_jqModC
    · exact coeffMap_red_qExpand_jqModC
  have hredswap : (fun i => coeffMap red ((![qExpand A q (jqModC A), jqModC A] : Fin 2 → LaurentSeries A) i))
      = ![qExpand k q (jqModC k), jqModC k] := by
    funext i; fin_cases i
    · exact coeffMap_red_qExpand_jqModC
    · exact coeffMap_red_jqModC

  obtain ⟨hr₁, -⟩ := exists_mem_integersFst_evalF R K (stdPair (N := N) (q := q)) _ hstd r
  obtain ⟨hs₁, hsres⟩ := exists_mem_integersFst_evalF R K (stdPair (N := N) (q := q)) _ hstd s
  rw [hredstd] at hsres
  have hsne : ((R.residue₁ ⟨_, hs₁⟩ : ↥(modularFunctionFieldC k N)) : LaurentSeries k) ≠ 0 := by
    rw [hsres]; exact evalk_std_ne_zero data hKr K a s hs
  have hsinv₁ : (evalF (A := A) (N := N) (q := q) K (stdPair (N := N) (q := q)) s)⁻¹ ∈ R.R₁.integers :=
    inv_mem_integersFst_of_residue₁_coe_ne_zero R hs₁ hsne
  have hs0 : evalF (A := A) (N := N) (q := q) K (stdPair (N := N) (q := q)) s ≠ 0 := by
    intro h0
    apply hsne
    have : (⟨_, hs₁⟩ : ↥R.R₁.integers) = 0 := Subtype.ext h0
    rw [this, map_zero]; rfl

  have hsL : modularEval (1 * q) (coeffSubring A K) s ≠ 0 := by
    rw [← coe_evalF_stdPair (N := N) K s]; exact fun h => hs0 (Subtype.ext h)
  have hfrs : f = modularEval (1 * q) (coeffSubring A K) r * (modularEval (1 * q) (coeffSubring A K) s)⁻¹ :=
    (eq_mul_inv_iff_mul_eq₀ hsL).mpr hfs
  refine ⟨evalF (A := A) (N := N) (q := q) K (stdPair (N := N) (q := q)) r * (evalF (A := A) (N := N) (q := q) K (stdPair (N := N) (q := q)) s)⁻¹, ⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩
  ·
    exact mul_mem hr₁ hsinv₁
  ·
    rw [R.mem_integers₂_iff, map_mul, map_inv₀]
    rcases atkinLehnerBar_evalF (A := A) (N := N) (q := q) K with hid | hsw
    · rw [hid, hid]; exact mul_mem hr₁ hsinv₁
    · rw [hsw, hsw]
      obtain ⟨hr₁', -⟩ := exists_mem_integersFst_evalF R K (swapPair (N := N) (q := q)) _ hswap r
      obtain ⟨hs₁', hsres'⟩ := exists_mem_integersFst_evalF R K (swapPair (N := N) (q := q)) _ hswap s
      rw [hredswap] at hsres'
      have hsne' : ((R.residue₁ ⟨_, hs₁'⟩ : ↥(modularFunctionFieldC k N)) : LaurentSeries k) ≠ 0 := by
        rw [hsres']; exact evalk_swap_ne_zero data hKr K a ha2 s hs
      exact mul_mem hr₁' (inv_mem_integersFst_of_residue₁_coe_ne_zero R hs₁' hsne')
  ·
    intro V hV
    have hvals : (∃ x : A, red x = a ∧ 0 < V.ord (ProlongationTuple.jFun N q - algebraMap ℚ̄ ↥𝔽 (x : ℚ̄))) ∧
        (∃ y : A, red y = a ^ q ∧ 0 < V.ord (ProlongationTuple.jQFun N q - algebraMap ℚ̄ ↥𝔽 (y : ℚ̄))) :=
      exists_values_of_reduceFst_eq hw ha hV
    obtain ⟨⟨x, hxa, hx⟩, ⟨y, hya, hy⟩⟩ := hvals
    refine evalF_mul_inv_mem_of_values (k := k) (red := red) K hx hy r s ?_
    have hH : red.comp (MvPolynomial.eval₂Hom
        (Subring.inclusion inf_le_left : ↥(coeffSubring A K) →+* ↥A) ![x, y])
        = MvPolynomial.eval₂Hom (redRestrict red K) ![a, a ^ q] := by
      refine MvPolynomial.ringHom_ext (fun c => ?_) (fun i => ?_)
      · rw [RingHom.comp_apply, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C]; rfl
      · rw [RingHom.comp_apply, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X']
        fin_cases i
        · exact hxa
        · exact hya
    have := RingHom.congr_fun hH s
    rw [RingHom.comp_apply] at this
    show red (MvPolynomial.eval₂Hom (Subring.inclusion inf_le_left : ↥(coeffSubring A K) →+* ↥A) ![x, y] s) ≠ 0
    rw [this]
    exact hs
  ·
    have hmem : ∀ p, modularEval (1 * q) (coeffSubring A K) p ∈ NodeLocalized.fieldOver (N * q) K := by
      intro p
      induction p using MvPolynomial.induction_on
      next c =>
        rw [modularEval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C]
        exact Subfield.subset_closure (Or.inl ⟨⟨(c : ℚ̄), c.2.2⟩, rfl⟩)
      next p₁ p₂ h₁ h₂ => rw [map_add]; exact add_mem h₁ h₂
      next p i hp =>
        rw [map_mul]
        refine mul_mem hp ?_
        rw [modularEval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]
        fin_cases i
        · exact Subfield.subset_closure (Or.inr (Set.mem_insert _ _))
        · show jqNModC ℚ̄ (1 * q) ∈ NodeLocalized.fieldOver (N * q) K
          rw [jqNModC_one_mul]; exact hjqK
    show (((evalF (A := A) (N := N) (q := q) K (stdPair (N := N) (q := q)) r * (evalF (A := A) (N := N) (q := q) K (stdPair (N := N) (q := q)) s)⁻¹ : ↥𝔽)) : LaurentSeries ℚ̄)
      ∈ NodeLocalized.fieldOver (N * q) K
    rw [show (((evalF (A := A) (N := N) (q := q) K (stdPair (N := N) (q := q)) r * (evalF (A := A) (N := N) (q := q) K (stdPair (N := N) (q := q)) s)⁻¹ : ↥𝔽)) : LaurentSeries ℚ̄)
        = ((evalF (A := A) (N := N) (q := q) K (stdPair (N := N) (q := q)) r : ↥𝔽) : LaurentSeries ℚ̄)
          * (((evalF (A := A) (N := N) (q := q) K (stdPair (N := N) (q := q)) s : ↥𝔽) : LaurentSeries ℚ̄))⁻¹ from rfl,
      coe_evalF_stdPair, coe_evalF_stdPair, ← div_eq_mul_inv]
    exact div_mem (hmem r) (hmem s)
  ·
    show ((evalF (A := A) (N := N) (q := q) K (stdPair (N := N) (q := q)) r : ↥𝔽) : LaurentSeries ℚ̄)
        * (((evalF (A := A) (N := N) (q := q) K (stdPair (N := N) (q := q)) s : ↥𝔽) : LaurentSeries ℚ̄))⁻¹ = f
    rw [coe_evalF_stdPair, coe_evalF_stdPair, hfrs]

end ModularCurve.PlaceSpecialization.ProlongationTuple.NLPG2

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple modularFunctionFieldBar qExpand qExpand_one_apply qExpand_congr jq ModularPolynomialData jq_mem modularFunctionFieldFull jqd_mem_full modularFunctionField_le_full coeffMap coeffMap_single coeffMap_coeffMap algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_mem_laurentBaseChange jqModC jqNModC jqModC_rat map_jqModC modularFunctionFieldC PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral qExpand_jqModC_eq_pow frobOnPlacesGeomLevel exists_ramification_frobenius KroneckerCongruence IsSupersingularPlace ssPlaces jGeomGen jNGeomGen jGeomGen_sub_algebraMap_ne_zero IsCentreOf frobeniusGeomLevel_jGeomGen_sub_pow IsCentreOf.frobOnPlacesGeomLevel transcendental_jqModC ssJSet IsAtkinLehnerAutFull atkinLehnerInvolutionFull isAtkinLehnerAutFull_atkinLehnerInvolutionFull atkinLehnerInvolutionFull_eq_refl frickeInvolutionBar frickeInvolutionBar_def IsFrickeAutFull frickeInvolutionFull isFrickeAutFull_frickeInvolutionFull frickeInvolutionFull_eq_refl geomAut geomAut_coeffEmb modularFunctionFieldFullC coeffMap_qExpand CharPReduction.modularLocalized NodeLocalized.coeffSubring NodeLocalized.redRestrict NodeLocalized.fieldOver NodeLocalized.modularLocalizedAtPoint pow_q_sq_eq_self_of_mem_ssJSet isIntegral_modularLocalizedAtPoint_coeffSubring_of_forall_pole_not_centred NodeLocalized.exists_mul_eq_of_mem_fieldOver isIntegrallyClosed_modularLocalizedAtPoint_coeffSubring_of_lt_five isIntegrallyClosed_modularLocalizedAtPoint_coeffSubring_of_eq_zero_or_eq_1728 isIntegrallyClosed_modularLocalizedAtPoint_coeffSubring_of_ne_zero_of_ne_1728"
namespace NLPC
p2m_open "ModularCurve"

p2m_open "ModularCurve.PlaceSpecialization~jFun P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_mem_modularLocalizedAtPoint_iff_exists_mem_nodeIntegersOver.ModularCurve.PlaceSpecialization"

theorem mk_qExpand_congr (M : ℕ) {d e : ℕ} [NeZero d] [NeZero e] (hde : d = e)
    (hd : qExpand ℚ d jq ∈ modularFunctionFieldFull M) (he : qExpand ℚ e jq ∈ modularFunctionFieldFull M) :
    (⟨qExpand ℚ d jq, hd⟩ : modularFunctionFieldFull M) = ⟨qExpand ℚ e jq, he⟩ := by
  subst hde
  rfl

theorem algEquiv_modularFunctionFieldFull_ext (M : ℕ)
    (σ τ : modularFunctionFieldFull M ≃ₐ[ℚ] modularFunctionFieldFull M)
    (h : ∀ (d : ℕ) (_ : NeZero d) (hd : d ∣ M),
      σ ⟨qExpand ℚ d jq, jqd_mem_full M hd⟩ = τ ⟨qExpand ℚ d jq, jqd_mem_full M hd⟩) :
    σ = τ := by
  apply AlgEquiv.ext
  rintro ⟨x, hx⟩
  suffices hmain : ∀ (y : LaurentSeries ℚ) (hy : y ∈ modularFunctionFieldFull M),
      ((σ ⟨y, hy⟩ : modularFunctionFieldFull M) : LaurentSeries ℚ) = (τ ⟨y, hy⟩ : modularFunctionFieldFull M) from
    Subtype.ext (hmain x hx)
  intro y hy
  induction hy using IntermediateField.adjoin_induction with
  | mem y hy =>
    obtain ⟨d, hd0, hdM, rfl⟩ := hy
    exact congrArg Subtype.val (h d hd0 hdM)
  | algebraMap r =>
    have e : (⟨_, IntermediateField.algebraMap_mem (modularFunctionFieldFull M) r⟩ : modularFunctionFieldFull M)
        = ((r : ℚ) : modularFunctionFieldFull M) := by
      apply Subtype.ext
      rw [SubfieldClass.coe_ratCast]
      exact eq_ratCast _ r
    rw [e, map_ratCast, map_ratCast]
  | add y z hy hz ihy ihz =>
    have e : (⟨y + z, add_mem hy hz⟩ : modularFunctionFieldFull M) = ⟨y, hy⟩ + ⟨z, hz⟩ := rfl
    rw [e, map_add, map_add]
    show ((σ ⟨y, hy⟩ : modularFunctionFieldFull M) : LaurentSeries ℚ) + (σ ⟨z, hz⟩ : modularFunctionFieldFull M)
      = ((τ ⟨y, hy⟩ : modularFunctionFieldFull M) : LaurentSeries ℚ) + (τ ⟨z, hz⟩ : modularFunctionFieldFull M)
    rw [ihy, ihz]
  | inv y hy ihy =>
    have e : (⟨y⁻¹, inv_mem hy⟩ : modularFunctionFieldFull M) = (⟨y, hy⟩ : modularFunctionFieldFull M)⁻¹ := rfl
    rw [e, map_inv₀, map_inv₀]
    show (((σ ⟨y, hy⟩ : modularFunctionFieldFull M) : LaurentSeries ℚ))⁻¹
      = (((τ ⟨y, hy⟩ : modularFunctionFieldFull M) : LaurentSeries ℚ))⁻¹
    rw [ihy]
  | mul y z hy hz ihy ihz =>
    have e : (⟨y * z, mul_mem hy hz⟩ : modularFunctionFieldFull M) = ⟨y, hy⟩ * ⟨z, hz⟩ := rfl
    rw [e, map_mul, map_mul]
    show ((σ ⟨y, hy⟩ : modularFunctionFieldFull M) : LaurentSeries ℚ) * (σ ⟨z, hz⟩ : modularFunctionFieldFull M)
      = ((τ ⟨y, hy⟩ : modularFunctionFieldFull M) : LaurentSeries ℚ) * (τ ⟨z, hz⟩ : modularFunctionFieldFull M)
    rw [ihy, ihz]

theorem isAtkinLehnerAutFull_one_iff (q : ℕ) [Fact q.Prime]
    (σ : modularFunctionFieldFull (1 * q) ≃ₐ[ℚ] modularFunctionFieldFull (1 * q)) :
    haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
    IsAtkinLehnerAutFull 1 q σ ↔ IsFrickeAutFull (1 * q) σ := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hq : q.Prime := Fact.out
  constructor
  · intro hAL a b hab ha hb
    obtain ⟨h1, h2⟩ := hAL 1 inferInstance (dvd_refl 1)
    have ha' : a ∣ q := ⟨b, by omega⟩
    rcases (Nat.dvd_prime hq).mp ha' with ha1 | haq
    · have hb' : b = 1 * q := by rw [ha1] at hab; omega
      rw [mk_qExpand_congr (1 * q) ha1 _ (jqd_mem_full (1 * q) (one_dvd _)),
        mk_qExpand_congr (1 * q) hb' _ (jqd_mem_full (1 * q) (dvd_refl _))]
      exact h1
    · have hb' : b = 1 := by
        have : q * b = q * 1 := by rw [haq] at hab; rw [mul_one, hab, one_mul]
        exact Nat.eq_of_mul_eq_mul_left hq.pos this
      rw [mk_qExpand_congr (1 * q) (haq.trans (one_mul q).symm) _ (jqd_mem_full (1 * q) (dvd_refl _)),
        mk_qExpand_congr (1 * q) hb' _ (jqd_mem_full (1 * q) (one_dvd _))]
      exact h2
  · intro hF d hd0 hd
    obtain rfl : d = 1 := Nat.dvd_one.mp hd
    constructor
    · exact hF 1 (1 * q) (by ring) inferInstance inferInstance
    · exact hF (1 * q) 1 (by ring) inferInstance inferInstance

theorem atkinLehnerInvolutionFull_one (q : ℕ) [Fact q.Prime] :
    haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
    atkinLehnerInvolutionFull 1 q = frickeInvolutionFull (1 * q) := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hq : q.Prime := Fact.out
  by_cases hex : ∃ σ : modularFunctionFieldFull (1 * q) ≃ₐ[ℚ] modularFunctionFieldFull (1 * q),
      IsFrickeAutFull (1 * q) σ
  · have hex' : ∃ σ : modularFunctionFieldFull (1 * q) ≃ₐ[ℚ] modularFunctionFieldFull (1 * q),
        IsAtkinLehnerAutFull 1 q σ := by
      obtain ⟨σ, hσ⟩ := hex
      exact ⟨σ, (isAtkinLehnerAutFull_one_iff q σ).mpr hσ⟩
    have h1 := (isAtkinLehnerAutFull_one_iff q _).mp (isAtkinLehnerAutFull_atkinLehnerInvolutionFull 1 q hex')
    have h2 := isFrickeAutFull_frickeInvolutionFull (1 * q) hex
    apply algEquiv_modularFunctionFieldFull_ext
    intro d hd0 hd
    have hd' : d ∣ q := by rwa [one_mul] at hd
    rcases (Nat.dvd_prime hq).mp hd' with hd1 | hdq
    · have e1 := h1 1 (1 * q) (by ring) inferInstance inferInstance
      have e2 := h2 1 (1 * q) (by ring) inferInstance inferInstance
      rw [mk_qExpand_congr (1 * q) hd1 _ (jqd_mem_full (1 * q) (one_dvd _))]
      exact e1.trans e2.symm
    · have e1 := h1 (1 * q) 1 (by ring) inferInstance inferInstance
      have e2 := h2 (1 * q) 1 (by ring) inferInstance inferInstance
      rw [mk_qExpand_congr (1 * q) (hdq.trans (one_mul q).symm) _ (jqd_mem_full (1 * q) (dvd_refl _))]
      exact e1.trans e2.symm
  · have hex' : ¬ ∃ σ : modularFunctionFieldFull (1 * q) ≃ₐ[ℚ] modularFunctionFieldFull (1 * q),
        IsAtkinLehnerAutFull 1 q σ := fun ⟨σ, hσ⟩ => hex ⟨σ, (isAtkinLehnerAutFull_one_iff q σ).mp hσ⟩
    rw [atkinLehnerInvolutionFull_eq_refl 1 q hex', frickeInvolutionFull_eq_refl (1 * q) hex]

theorem atkinLehnerBar_one (q : ℕ) [Fact q.Prime] :
    haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
    ProlongationTuple.atkinLehnerBar 1 q = frickeInvolutionBar (1 * q) := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  show geomAut (AlgebraicClosure ℚ) (modularFunctionFieldFull (1 * q)) (atkinLehnerInvolutionFull 1 q) = _
  rw [frickeInvolutionBar_def, atkinLehnerInvolutionFull_one]

theorem mem_of_isIntegral_of_isIntegrallyClosed
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] (red : A →+* k) (a : k) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (hic : IsIntegrallyClosed ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))
    {x : LaurentSeries (AlgebraicClosure ℚ)} (hxF : x ∈ fieldOver (1 * q) K)
    (hint : IsIntegral ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) x) :
    x ∈ modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) := by
  classical
  obtain ⟨y, z, hy, hz, hz0, hxz⟩ := NodeLocalized.exists_mul_eq_of_mem_fieldOver red a K hxF
  set R := modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) with hR
  have hinj : Function.Injective (algebraMap ↥R (LaurentSeries (AlgebraicClosure ℚ))) := Subtype.val_injective
  let φ : FractionRing ↥R →ₐ[↥R] LaurentSeries (AlgebraicClosure ℚ) :=
    { IsFractionRing.lift hinj with commutes' := fun r => IsFractionRing.lift_algebraMap hinj r }
  have hφ : Function.Injective φ := φ.toRingHom.injective
  let w : FractionRing ↥R := algebraMap ↥R _ ⟨y, hy⟩ / algebraMap ↥R _ ⟨z, hz⟩
  have hw : φ w = x := by
    have h1 : φ (algebraMap ↥R _ ⟨y, hy⟩) = y := IsFractionRing.lift_algebraMap hinj _
    have h2 : φ (algebraMap ↥R _ ⟨z, hz⟩) = z := IsFractionRing.lift_algebraMap hinj _
    rw [map_div₀, h1, h2, div_eq_iff hz0, hxz]
  have hwint : IsIntegral ↥R w := by
    rw [← isIntegral_algHom_iff φ hφ, hw]; exact hint
  obtain ⟨r, hr⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ↥R) (K := FractionRing ↥R)).mp hwint
  have : (r : LaurentSeries (AlgebraicClosure ℚ)) = x := by
    rw [← hw, ← hr]; exact (IsFractionRing.lift_algebraMap hinj r).symm
  rw [← this]; exact r.2

end ModularCurve.NLPC

open ModularCurve.PlaceSpecialization.ProlongationTuple.NLPG2 ModularCurve.NLPC in
theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα₁ : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ₁ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P₁ : PlaceSpecialization A q 1 data hKr k red hα₁ hβ₁}
    (R : ProlongationTuple P₁) [IsAlgClosed k] [DecidableEq k] (hmodel : R.IsModel)
    (W : Finset (Place k (modularFunctionFieldC k 1))) (hW : ∀ w ∈ W, w ∈ ssPlaces q 1 k)
    (hreg : R.RegularityLaw W)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W)
    (a : k) (ha : w.evalAt (jGeomGen k 1) = a)
    (x : ↥(NodeLocalized.coeffSubring A K)) (hx : NodeLocalized.redRestrict red K x = a)
    (f : LaurentSeries (AlgebraicClosure ℚ)) :
    f ∈ NodeLocalized.modularLocalizedAtPoint (1 * q) (NodeLocalized.coeffSubring A K)
        (NodeLocalized.redRestrict red K) a (a ^ q) ↔
      ∃ g : ↥(modularFunctionFieldBar (1 * q)), g ∈ R.nodeIntegersOver K w ∧
        (g : LaurentSeries (AlgebraicClosure ℚ)) = f := by
  have hw' : w ∈ ssPlaces q 1 k := hW w hw
  have hss : IsSupersingularPlace q 1 k w := hw'
  have haS : a ∈ ssJSet q k := ha ▸ hss.2.2
  have ha2 : a ^ (q ^ 2) = a := pow_q_sq_eq_self_of_mem_ssJSet q haS
  constructor
  ·
    intro hf
    have hjqK : qExpand (AlgebraicClosure ℚ) q (jqModC (AlgebraicClosure ℚ)) ∈ NodeLocalized.fieldOver (1 * q) K := by
      rw [← jqNModC_one_mul]
      exact Subfield.subset_closure (Or.inr (Set.mem_insert_of_mem _ rfl))
    exact exists_mem_nodeIntegersOver_of_mem_modularLocalizedAtPoint R K hjqK hw' ha hf
  ·
    rintro ⟨g, hg, rfl⟩
    have hK : (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ NodeLocalized.fieldOver (1 * q) K := hg.2
    have h₁ : (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red :=
      (R.mem_integersFst_iff g).mp hg.1.1
    have h₂ : ((frickeInvolutionBar (1 * q) g : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ))
        ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red := by
      rw [← atkinLehnerBar_one]
      exact (R.mem_integersSnd_iff g).mp hg.1.2.1

    have hpole : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), V.ord g < 0 →
        ¬ ((∃ x : A, red x = a ∧
              0 < V.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
                coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                  (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q))
                - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
           (∃ y : A, red y = a ^ q ∧
              0 < V.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
                coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                  (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q))
                - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ)))) := by
      rintro V hV ⟨hxV, ⟨y, hya, hyV⟩⟩
      have hjq : (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩
              : modularFunctionFieldBar (1 * q)) = ProlongationTuple.jQFun 1 q :=
        Subtype.ext (congrArg (coeffEmb (AlgebraicClosure ℚ)) (qExpand_congr (one_mul q) jq))
      rw [hjq] at hyV
      have hred : P₁.reduceFst V = w :=
        (P₁.reduceFst_eq_iff_centred_levelOne w hw' a ha V).mpr ⟨hxV, ⟨y, hya, hyV⟩⟩
      have h0 : 0 ≤ V.ord g := Place.ord_nonneg_of_mem _ (hg.1.2.2 V hred)
      exact absurd hV (not_lt.mpr h0)
    have hint := isIntegral_modularLocalizedAtPoint_coeffSubring_of_forall_pole_not_centred red a K g hK h₁ h₂ hpole

    have hic : IsIntegrallyClosed ↥(NodeLocalized.modularLocalizedAtPoint (1 * q) (NodeLocalized.coeffSubring A K)
        (NodeLocalized.redRestrict red K) a (a ^ q)) := by
      by_cases hq : q < 5
      · exact isIntegrallyClosed_modularLocalizedAtPoint_coeffSubring_of_lt_five red a haS ha2 hq K ⟨x, hx⟩
      · by_cases h01 : a = 0 ∨ a = 1728
        · exact isIntegrallyClosed_modularLocalizedAtPoint_coeffSubring_of_eq_zero_or_eq_1728 red a haS ha2
            (not_lt.mp hq) h01 K ⟨x, hx⟩
        · push_neg at h01
          exact isIntegrallyClosed_modularLocalizedAtPoint_coeffSubring_of_ne_zero_of_ne_1728 red a haS ha2
            (not_lt.mp hq) h01.1 h01.2 K ⟨x, hx⟩
    exact mem_of_isIntegral_of_isIntegrallyClosed red a K hic hK hint

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_mem_modularLocalizedAtPoint_iff_exists_mem_nodeIntegersOver
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_mem_modularLocalizedAtPoint_iff_exists_mem_nodeIntegersOver (solution)
