-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.LevelOneProlongationPair.regularityLaw
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/2dbfa3d5-7e09-529e-a1f5-facd1e7af7cc

import Definitions.Def_ModularCurve_LevelOneProlongationPairRegularity
import Definitions.Def_ModularCurve_SupersingularModuli
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_mem_integersFst_iff_coe_mem_modularLocalized
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_mem_integersSnd_iff_coe_frickeInvolutionBar_mem_modularLocalized
import Theorems.Thm_ModularCurve_exists_hasValue_frobNodePair_of_forall_pole_not_centred
import Theorems.Thm_ModularCurve_exists_hasValue_and_hasValue_frobNodePair_of_forall_pole_not_centred
import Theorems.Thm_ModularCurve_PlaceSpecialization_redFst_eq_charLGeomPlaceOfPoint_of_ord_pos
import Theorems.Thm_ModularCurve_PlaceSpecialization_redFst_cuspInftyBar
import Theorems.Thm_P2M_Dup_AlgebraicCurve_RationalFunctionField_eq_placeOfPoint_or_eq_placeInfty
import Theorems.Thm_ModularCurve_frobOnPlacesGeomLevel_charLGeomPlaceOfPoint
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_regularityLaw
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁"
p2m_attr_erase "simp" "ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right"
p2m_attr_erase "simp" "FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.NodeLocalized.coe_modularEvalAt ModularCurve.ProjectiveLine.map_mk ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_regularityLaw.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.LevelOneProlongationPair modularFunctionFieldBar qExpand jq ModularPolynomialData jq_mem jqd_mem_full modularFunctionField_le_full coeffEmb coeffEmb_mem_laurentBaseChange modularFunctionFieldC PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral KroneckerCongruence frobNodePair frobNodePair_fst frobNodePair_snd charLGeomPlaceEquiv charLGeomPlaceOfPoint charLGeomPlaceOfPoint_injective ssJSet frickeInvolutionBar exists_hasValue_frobNodePair_of_forall_pole_not_centred exists_hasValue_and_hasValue_frobNodePair_of_forall_pole_not_centred frobOnPlacesGeomLevel_charLGeomPlaceOfPoint"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "LevelOneProlongationPair redFst redFst_eq_charLGeomPlaceOfPoint_of_ord_pos redFst_cuspInftyBar"
namespace LevelOneProlongationPair
p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "RegularityLaw residue₁ residue₂ residue₁_apply residue₂_apply residue₁_eq_modularRedLocHom residue₂_eq R₂ ι R₁ mem_integersFst_iff_coe_mem_modularLocalized mem_integersSnd_iff_coe_frickeInvolutionBar_mem_modularLocalized"
p2m_open "ModularCurve.PlaceSpecialization.LevelOneProlongationPair ModularCurve.PlaceSpecialization ModularCurve"
p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_regularityLaw.ModularCurve ModularCurve.CharPReduction"

set_option maxHeartbeats 12800000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem regularityLaw'
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : P.LevelOneProlongationPair)
    {S₀ : Finset k} (hS₀ : ∀ a ∈ S₀, a ∈ ssJSet q k) :
    R.RegularityLaw S₀ := by
  classical

  have jAlpha : heckeAlphaBar (AlgebraicClosure ℚ) 1 q (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full 1 (jq_mem 1))⟩ : modularFunctionFieldBar 1)
      = (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) :=
    Subtype.ext (coe_heckeAlphaBar (L := AlgebraicClosure ℚ) (N := 1) (ℓ := q) _)

  have trans : ∀ (f : ↥(modularFunctionFieldBar (1 * q))) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers),
      ∃ (hm₁ : (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ modularLocalized (1 * q) A.toSubring red)
        (hm₂ : ((frickeInvolutionBar (1 * q) f : ↥(modularFunctionFieldBar (1 * q))) :
            LaurentSeries (AlgebraicClosure ℚ)) ∈ modularLocalized (1 * q) A.toSubring red)
        (h₁F : modularRedLocHom (1 * q) A.toSubring red ⟨_, hm₁⟩ ∈ modularFunctionFieldC k 1)
        (h₂F : modularRedLocHom (1 * q) A.toSubring red ⟨_, hm₂⟩ ∈ modularFunctionFieldC k 1),
        (R.residue₁ ⟨f, h₁⟩ : ↥(modularFunctionFieldC k 1)) = ⟨_, h₁F⟩ ∧
        (R.residue₂ ⟨f, h₂⟩ : ↥(modularFunctionFieldC k 1)) = ⟨_, h₂F⟩ := by
    intro f h₁ h₂
    have hm₁ := (R.mem_integersFst_iff_coe_mem_modularLocalized f).mp h₁
    have hm₂ := (R.mem_integersSnd_iff_coe_frickeInvolutionBar_mem_modularLocalized f).mp h₂
    obtain ⟨h₁', hh₁⟩ := R.residue₁_eq_modularRedLocHom f hm₁
    obtain ⟨h₂', hh₂⟩ := R.residue₁_eq_modularRedLocHom (frickeInvolutionBar (1 * q) f) hm₂
    have h₁F : modularRedLocHom (1 * q) A.toSubring red ⟨_, hm₁⟩ ∈ modularFunctionFieldC k 1 := by
      rw [← hh₁]; exact (R.ι (R.R₁.residue ⟨f, h₁'⟩)).2
    have h₂F : modularRedLocHom (1 * q) A.toSubring red ⟨_, hm₂⟩ ∈ modularFunctionFieldC k 1 := by
      rw [← hh₂]; exact (R.ι (R.R₁.residue ⟨_, h₂'⟩)).2
    refine ⟨hm₁, hm₂, h₁F, h₂F, ?_, ?_⟩
    · apply Subtype.ext
      rw [residue₁_apply]
      exact hh₁
    · apply Subtype.ext
      rw [residue₂_apply, R.residue₂_eq f h₂]
      exact hh₂

  have transPole : ∀ (f : ↥(modularFunctionFieldBar (1 * q))) (a : k),
      (∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)),
          P.redFst W = (frobNodePair q a).1 → 0 ≤ W.ord f) →
      ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), W.ord f < 0 →
      ¬ ((∃ x : A, red x = a ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
         (∃ y : A, red y = a ^ q ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ)))) := by
    intro f a hreg W hlt hcen
    obtain ⟨⟨x, hx, hxW⟩, -⟩ := hcen
    have hred : P.redFst W = charLGeomPlaceOfPoint k (red x) := by
      apply redFst_eq_charLGeomPlaceOfPoint_of_ord_pos P W x
      rw [jAlpha]
      exact hxW
    have := hreg W (by rw [hred, hx, frobNodePair_fst])
    omega
  refine ⟨?_, ?_⟩
  ·
    intro f h₁ h₂ v hfix hne hreg
    obtain ⟨hm₁, hm₂, h₁F, h₂F, hr₁, hr₂⟩ := trans f h₁ h₂

    obtain ⟨a, rfl⟩ : ∃ a : k, v = charLGeomPlaceOfPoint k a := by
      rcases AlgebraicCurve.RationalFunctionField.eq_placeOfPoint_or_eq_placeInfty k
          ((charLGeomPlaceEquiv k).symm v) with ⟨a, ha⟩ | hinf
      · refine ⟨a, ?_⟩
        rw [charLGeomPlaceOfPoint, ← ha, Equiv.apply_symm_apply]
      · exfalso
        apply hne
        rw [redFst_cuspInftyBar, ← hinf, Equiv.apply_symm_apply]
    have ha2 : a ^ (q ^ 2) = a := by
      rw [frobOnPlacesGeomLevel_charLGeomPlaceOfPoint, frobOnPlacesGeomLevel_charLGeomPlaceOfPoint,
        ← pow_mul, ← pow_two] at hfix
      exact charLGeomPlaceOfPoint_injective k hfix
    have hreg' : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)),
        P.redFst W = (frobNodePair q a).1 → 0 ≤ W.ord f := by
      intro W hW; exact hreg W (by rw [hW, frobNodePair_fst])
    obtain ⟨c₁, c₂, hv₁, hv₂⟩ :=
      exists_hasValue_and_hasValue_frobNodePair_of_forall_pole_not_centred red a ha2 f hm₁ h₁F hm₂ h₂F
        (transPole f a hreg')
    refine ⟨fun _ => ?_, fun _ => ?_⟩
    · rw [hr₁]
      rw [frobNodePair_fst] at hv₁
      exact Place.ord_nonneg_of_mem _ hv₁.mem
    · rw [hr₂, frobOnPlacesGeomLevel_charLGeomPlaceOfPoint]
      rw [frobNodePair_snd] at hv₂
      exact Place.ord_nonneg_of_mem _ hv₂.mem
  ·
    intro f h₁ h₂ a haS ha2 hreg
    obtain ⟨hm₁, hm₂, h₁F, h₂F, hr₁, hr₂⟩ := trans f h₁ h₂
    obtain ⟨c, hv₁, hv₂⟩ :=
      exists_hasValue_frobNodePair_of_forall_pole_not_centred red a (hS₀ a haS) ha2 f hm₁ h₁F hm₂ h₂F
        (transPole f a hreg)
    exact ⟨c, by rw [hr₁]; exact hv₁, by rw [hr₂]; exact hv₂⟩

end ModularCurve.PlaceSpecialization.LevelOneProlongationPair

open AlgebraicCurve _root_.ModularCurve _root_.P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_regularityLaw.ModularCurve in
theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : P.LevelOneProlongationPair)
    {S₀ : Finset k} (hS₀ : ∀ a ∈ S₀, a ∈ ssJSet q k) :
    R.RegularityLaw S₀ :=
  ModularCurve.PlaceSpecialization.LevelOneProlongationPair.regularityLaw' R hS₀

end S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_regularityLaw
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_regularityLaw (solution)
