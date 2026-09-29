-- Prove2me | solution 1 for ModularCurve.FullLevel.inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/8003c9e0-507b-5efd-9f99-21ba80b28a51

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringGuards
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_PhiGen
import Theorems.Thm_ModularCurve_isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_ssPlaces_nonempty
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_algebraicClosure_rat
import Theorems.Thm_ModularCurve_FullLevel_exists_igusaValuationSubrings_of_eq_three
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringNaturality
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Theorems.Thm_AlgebraicCurve_exists_transcendental_isSeparable_of_finrank_kaehlerDifferential_eq_one
import Theorems.Thm_AlgebraicCurve_isAlgebraic_adjoin_of_transcendental
import Theorems.Thm_ModularCurve_transcendental_coeffEmb_jq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid CuspForm.instModuleZModIntTwoCuspForms CuspForm.instAddCommGroupIntTwoCuspForms ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent CuspForm.instModuleTwoCuspForms CuspForm.instIsScalarTowerTwoCuspForms CuspForm.instAddCommGroupTwoCuspForms CuspForm.instIsScalarTowerSelfTwoCuspForms CuspForm.instModuleQuotientTwoCuspForms CuspForm.GammaH_finiteIndex"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.qExpandAlgHomC_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_heckeBetaModLHOf ModularCurve.pairDiagModL_apply ModularCurve.coe_heckeAlphaModLH ModularCurve.pairUpModL_apply ModularCurve.coeff_qDecimate ModularCurve.coe_qExpFrobeniusModL ModularCurve.coe_qExpFrobeniusDegZeroPullbackModL ModularCurve.coe_qExpFrobeniusDegZeroPushforwardModL ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D"
p2m_attr_erase "simp" "ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.gluedPolarDifferentials.coe_fst_apply AlgebraicCurve.gluedPolarDifferentials.coe_snd_apply CuspForm.heckeGenH_T CuspForm.coe_twoCuspEnd_apply CuspForm.twoCuspEndMod_reduce CuspForm.heckeGenH_U CuspForm.heckeGenH_dia ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply"

section Inlined_w1_W1c_tube_penw2

set_option autoImplicit false

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel IsLocalRing CongruenceSubgroup"
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "xHFunctionFieldC xHFunctionField intFormRatiosC qExpFunctionFieldC intFormRatiosC_subset modularFunctionFieldBar qExpand jq jq_mem jqN_mem modularFunctionField_le_full coeffMap coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange jq_mem_full instDecidableEqResidueFieldSemistable instAlgebraResidueFieldModularFunctionFieldCSemistable jqModC modularFunctionFieldC ssPlaces jGeomGen jNGeomGen transcendental_jqModC ssJSet isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField jqModC_mem_intFormRatiosC ssPlaces_nonempty transcendental_coeffEmb_jq"
namespace FullLevel
p2m_export "ModularCurve.FullLevel" "lineInfty SemistableCovering levelH fieldBar Idx IsLevelAutBar levelAutBar redQ exists_igusaValuationSubrings_of_eq_three SemistableCovering.LevelPinClauses"
namespace W1c
namespace Plumbing
p2m_open "ModularCurve.FullLevel ModularCurve"

set_option synthInstance.maxHeartbeats 1600000 in

def InTube (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (A : ValuationSubring (AlgebraicClosure ℚ))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')) (P : Place (AlgebraicClosure ℚ) (fieldBar q M')) : Prop :=
  ∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
          (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
            0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
              ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
          (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
              (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
            ∀ a : A, residue A a =
                (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) →
              ∃ h : P.evalAt (IntermediateField.inclusion hle f : fieldBar q M') - (a : AlgebraicClosure ℚ) ∈ A,
                (⟨_, h⟩ : A) ∈ maximalIdeal A

def jBar (M' : ℕ) [NeZero M'] : ↥(modularFunctionFieldBar M') :=
  ⟨coeffEmb (AlgebraicClosure ℚ) jq,
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩

def jNBar (M' : ℕ) [NeZero M'] : ↥(modularFunctionFieldBar M') :=
  ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ M' jq),
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jqN_mem M'))⟩

@[scoped simp] theorem coe_jBar (M' : ℕ) [NeZero M'] :
    ((jBar M' : ↥(modularFunctionFieldBar M')) : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) jq := rfl

@[scoped simp] theorem coe_jNBar (M' : ℕ) [NeZero M'] :
    ((jNBar M' : ↥(modularFunctionFieldBar M')) : LaurentSeries (AlgebraicClosure ℚ)) =
      coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ M' jq) := rfl

set_option synthInstance.maxHeartbeats 1600000 in

def InTubeJ (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (A : ValuationSubring (AlgebraicClosure ℚ))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')) (P : Place (AlgebraicClosure ℚ) (fieldBar q M')) : Prop :=
  ((IntermediateField.inclusion hle (jBar M') : fieldBar q M') ∈ P.toValuationSubring ∧
    ∀ a : A, residue A a = s.evalAt (jGeomGen (ResidueField A) M') →
      ∃ h : P.evalAt (IntermediateField.inclusion hle (jBar M') : fieldBar q M') - (a : AlgebraicClosure ℚ) ∈ A,
        (⟨_, h⟩ : A) ∈ maximalIdeal A) ∧
  ((IntermediateField.inclusion hle (jNBar M') : fieldBar q M') ∈ P.toValuationSubring ∧
    ∀ a : A, residue A a = s.evalAt (jNGeomGen (ResidueField A) M') →
      ∃ h : P.evalAt (IntermediateField.inclusion hle (jNBar M') : fieldBar q M') - (a : AlgebraicClosure ℚ) ∈ A,
        (⟨_, h⟩ : A) ∈ maximalIdeal A)

namespace Idx

private def _root_.ModularCurve.FullLevel.W1c.Plumbing.Idx.unit {q : ℕ} [Fact q.Prime] (ζ : Idx q) : (AlgebraicClosure ℚ)ˣ :=
  (ζ.isPrimitiveRoot.isUnit (Fact.out : q.Prime).ne_zero).unit

end Idx
p2m_export "ModularCurve.FullLevel.W1c.Plumbing" "Idx.unit"
@[scoped simp] theorem Idx.coe_unit {q : ℕ} [Fact q.Prime] (ζ : Idx q) : (Idx.unit ζ : AlgebraicClosure ℚ) = ζ.val := rfl

p2m_reactivate "P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c.Plumbing.Idx"
end ModularCurve.FullLevel.W1c.Plumbing
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c.Plumbing.Idx P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c.Plumbing"
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c.Plumbing.Idx P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c"
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c.Plumbing.Idx P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel"
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c.Plumbing.Idx P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c.Plumbing.Idx P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c.Plumbing"

end Inlined_w1_W1c_tube_penw2
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c.Plumbing.Idx P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c.Plumbing"

section Inlined_w1_W1c_plumbing_penw2

set_option autoImplicit false

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel IsLocalRing CongruenceSubgroup"
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "xHFunctionFieldC xHFunctionField intFormRatiosC qExpFunctionFieldC intFormRatiosC_subset modularFunctionFieldBar qExpand jq jq_mem jqN_mem modularFunctionField_le_full coeffMap coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange jq_mem_full instDecidableEqResidueFieldSemistable instAlgebraResidueFieldModularFunctionFieldCSemistable jqModC modularFunctionFieldC ssPlaces jGeomGen jNGeomGen transcendental_jqModC ssJSet isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField jqModC_mem_intFormRatiosC ssPlaces_nonempty transcendental_coeffEmb_jq"
namespace FullLevel
p2m_export "ModularCurve.FullLevel" "lineInfty SemistableCovering levelH fieldBar Idx IsLevelAutBar levelAutBar redQ exists_igusaValuationSubrings_of_eq_three SemistableCovering.LevelPinClauses"
namespace W1c
namespace Plumbing
p2m_open "ModularCurve.FullLevel ModularCurve"

set_option synthInstance.maxHeartbeats 1600000 in

theorem fieldBar_isRational (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] :
    ∀ P : Place (AlgebraicClosure ℚ) (fieldBar q M'), P.IsRational := by
  intro P
  haveI : NeZero (q ^ 2 * M') := ⟨mul_ne_zero (pow_ne_zero _ (Fact.out : q.Prime).ne_zero) (NeZero.ne M')⟩
  haveI : IsCurveOver (AlgebraicClosure ℚ) (fieldBar q M') :=
    (ModularCurve.isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField
      (AlgebraicClosure ℚ) (q ^ 2 * M') (levelH q M')).1
  haveI : Module.Finite (AlgebraicClosure ℚ) P.ResidueField := IsCurveOver.finiteResidue P
  haveI : Algebra.IsIntegral (AlgebraicClosure ℚ) P.ResidueField :=
    Algebra.IsIntegral.of_finite (AlgebraicClosure ℚ) P.ResidueField
  show Function.Surjective (algebraMap (AlgebraicClosure ℚ) P.ResidueField)
  exact IsAlgClosed.algebraMap_bijective_of_isIntegral.2

set_option synthInstance.maxHeartbeats 1600000 in

theorem igusaField_transcendental (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime q) :
    ∃ t : (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')), Transcendental (ResidueField A) t := by
  refine ⟨⟨jqModC (ResidueField A), ?_⟩, ?_⟩
  · show jqModC (ResidueField A) ∈
      qExpFunctionFieldC (ResidueField A) (CohCarrier.GammaH (q ^ 2 * M') (levelH q M'))
    exact intFormRatiosC_subset _ _ (jqModC_mem_intFormRatiosC _ _)
  · exact (transcendental_algebraMap_iff
      (algebraMap (↥(xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')))
        (LaurentSeries (ResidueField A))).injective).1 (transcendental_jqModC (ResidueField A))

set_option synthInstance.maxHeartbeats 1600000 in

theorem exists_inftyProlongation
    (q : ℕ) [Fact q.Prime] (hq3 : q = 3) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (ζ : Idx q)
    (OIg : CuspidalType.ProjLine q → ValuationSubring (fieldBar q M'))
    (OSS : ↥W → ValuationSubring (fieldBar q M'))

    (hIg_inf : ∀ f : fieldBar q M', f ∈ OIg (lineInfty q) ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (hIg : ∀ ℓ, ∃ γ : SL(2, ℤ), γ ∈ Gamma0 M' ∧ redQ q γ • lineInfty q = ℓ ∧
      OIg ℓ = (OIg (lineInfty q)).comap (levelAutBar q M' ζ γ).toAlgHom.toRingHom)
    (hIg_inj : Function.Injective OIg)
    (hIg_perm : ∀ (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
      ∃ σ : Equiv.Perm (CuspidalType.ProjLine q),
        ∀ ℓ, (OIg ℓ).comap (levelAutBar q M' ζ' γ).toAlgHom.toRingHom = OIg (σ ℓ))

    (hSS_A : ∀ s (x : AlgebraicClosure ℚ), algebraMap (AlgebraicClosure ℚ) (fieldBar q M') x ∈ OSS s ↔ x ∈ A)
    (hSS_over : ∀ (s : ↥W) (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
      (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
      (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
          (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
        (IntermediateField.inclusion hle f : fieldBar q M') ∈ OSS s ∧
        ∀ a : A, residue A a =
            (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) →
          ∃ h : (IntermediateField.inclusion hle f : fieldBar q M')
              - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ OSS s,
            (⟨_, h⟩ : OSS s) ∈ maximalIdeal (OSS s))
    (hSS_fix : ∀ (s : ↥W) (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
      (OSS s).comap (levelAutBar q M' ζ' γ).toAlgHom.toRingHom = OSS s)

    (hSS_tr : ∀ s : ↥W, ∃ t : fieldBar q M', t ∈ OSS s ∧ ∀ a : A,
      ∃ h : t - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ OSS s, IsUnit (⟨_, h⟩ : OSS s))
    :
    ∃ R : RegularProlongation A (fieldBar q M') (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')), R.integers = OIg (lineInfty q) := by
  obtain ⟨OIg', R, hR, hinf', -, -, -, -⟩ := exists_igusaValuationSubrings_of_eq_three q hq3 M' hqM' A hA ζ
  refine ⟨R, ?_⟩
  rw [hR]
  ext f
  rw [hinf', hIg_inf]

set_option synthInstance.maxHeartbeats 1600000 in

theorem W_card_pos (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M') (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime q)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A)) : 0 < W.card := by
  haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def (Fact.out : q.Prime) hA
  haveI : IsAlgClosed (ResidueField A) := ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat A
  obtain ⟨w, hw⟩ := ModularCurve.ssPlaces_nonempty q M' hqM' (ResidueField A)
  exact Finset.card_pos.2 ⟨w, (hW w).2 hw⟩

end ModularCurve.FullLevel.W1c.Plumbing
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c.Plumbing.Idx P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c.Plumbing"
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c.Plumbing.Idx P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c.Plumbing"
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c.Plumbing.Idx P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c.Plumbing"
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c.Plumbing.Idx P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c.Plumbing"

end
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c.Plumbing.Idx P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c.Plumbing"

end Inlined_w1_W1c_plumbing_penw2
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c.Plumbing.Idx P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c.Plumbing"

section Inlined_w1_pen_LevelPin_pen

set_option autoImplicit false

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel IsLocalRing CongruenceSubgroup"
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "xHFunctionFieldC xHFunctionField intFormRatiosC qExpFunctionFieldC intFormRatiosC_subset modularFunctionFieldBar qExpand jq jq_mem jqN_mem modularFunctionField_le_full coeffMap coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange jq_mem_full instDecidableEqResidueFieldSemistable instAlgebraResidueFieldModularFunctionFieldCSemistable jqModC modularFunctionFieldC ssPlaces jGeomGen jNGeomGen transcendental_jqModC ssJSet isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField jqModC_mem_intFormRatiosC ssPlaces_nonempty transcendental_coeffEmb_jq"
namespace FullLevel
p2m_export "ModularCurve.FullLevel" "lineInfty SemistableCovering levelH fieldBar Idx IsLevelAutBar levelAutBar redQ exists_igusaValuationSubrings_of_eq_three SemistableCovering.LevelPinClauses"
namespace W1c
namespace Pen
p2m_open "ModularCurve.FullLevel ModularCurve"

theorem mem_maximalIdeal_of_valuationSubring_eq {F : Type*} [Field F] {O₁ O₂ : ValuationSubring F}
    (e : O₁ = O₂) {x : F} (h₁ : x ∈ O₁) (h₂ : x ∈ O₂) (hm : (⟨x, h₁⟩ : O₁) ∈ maximalIdeal ↥O₁) :
    (⟨x, h₂⟩ : O₂) ∈ maximalIdeal ↥O₂ := by
  subst e; exact hm

set_option synthInstance.maxHeartbeats 1600000 in

theorem levelPin_ss_of_integers_eq
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (OSS : ↥W → ValuationSubring (fieldBar q M'))
    (hSS_over : ∀ (s : ↥W) (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
      (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
      (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
          (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
        (IntermediateField.inclusion hle f : fieldBar q M') ∈ OSS s ∧
        ∀ a : A, residue A a =
            (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) →
          ∃ h : (IntermediateField.inclusion hle f : fieldBar q M')
              - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ OSS s,
            (⟨_, h⟩ : OSS s) ∈ maximalIdeal (OSS s))
    (s : ↥W) {FSS : Type} [Field FSS] [Algebra (ResidueField A) FSS]
    (C : ComponentChart A (fieldBar q M') FSS) (hCint : C.integers = OSS s)
    (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers)
    (hreg : ∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M')))
    (hs : (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
          (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring) :
    ∃ hC : (IntermediateField.inclusion hle f : fieldBar q M') ∈ C.integers,
      C.residue ⟨_, hC⟩ = algebraMap (ResidueField A) FSS
        ((s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩)) := by
  obtain ⟨hO, hmax⟩ := hSS_over s f hf hreg hs
  have hCf : (IntermediateField.inclusion hle f : fieldBar q M') ∈ C.integers := by rw [hCint]; exact hO
  refine ⟨hCf, ?_⟩
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (I := maximalIdeal ↥A)
    ((s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩))
  have ha' : residue A a =
      (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) := ha
  obtain ⟨hsub, hmx⟩ := hmax a ha'
  have haC : algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ C.integers :=
    (C.algebraMap_mem_iff a).mpr a.2
  have hsubC : (IntermediateField.inclusion hle f : fieldBar q M')
      - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ C.integers :=
    C.integers.toSubring.sub_mem hCf haC
  have hmxC : (⟨_, hsubC⟩ : C.integers) ∈ maximalIdeal ↥C.integers :=
    mem_maximalIdeal_of_valuationSubring_eq hCint.symm hsub hsubC hmx
  rw [← C.ker_residue, RingHom.mem_ker] at hmxC
  have hsplit : (⟨_, hsubC⟩ : C.integers) = ⟨_, hCf⟩ - ⟨_, haC⟩ := Subtype.ext rfl
  rw [hsplit, map_sub, C.residue_algebraMap a, sub_eq_zero] at hmxC
  rw [hmxC, ha']

end ModularCurve.FullLevel.W1c.Pen
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c.Plumbing.Idx P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c.Plumbing"
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c.Plumbing.Idx P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c.Plumbing"
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c.Plumbing.Idx P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c.Plumbing"
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c.Plumbing.Idx P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c.Plumbing"

end
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c.Plumbing.Idx P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c.Plumbing"

end Inlined_w1_pen_LevelPin_pen
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c.Plumbing.Idx P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c.Plumbing"

section Inlined_w1_W1c_spec

set_option autoImplicit false

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel IsLocalRing CongruenceSubgroup"
open scoped MatrixGroups

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "xHFunctionFieldC xHFunctionField intFormRatiosC qExpFunctionFieldC intFormRatiosC_subset modularFunctionFieldBar qExpand jq jq_mem jqN_mem modularFunctionField_le_full coeffMap coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange jq_mem_full instDecidableEqResidueFieldSemistable instAlgebraResidueFieldModularFunctionFieldCSemistable jqModC modularFunctionFieldC ssPlaces jGeomGen jNGeomGen transcendental_jqModC ssJSet isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField jqModC_mem_intFormRatiosC ssPlaces_nonempty transcendental_coeffEmb_jq"
namespace FullLevel
p2m_export "ModularCurve.FullLevel" "lineInfty SemistableCovering levelH fieldBar Idx IsLevelAutBar levelAutBar redQ exists_igusaValuationSubrings_of_eq_three SemistableCovering.LevelPinClauses"
namespace W1c
p2m_open "ModularCurve.FullLevel ModularCurve"

section Spec

variable (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (A : ValuationSubring (AlgebraicClosure ℚ))

set_option synthInstance.maxHeartbeats 1600000 in

def LevelAuts : Subgroup ((fieldBar q M') ≃ₐ[(AlgebraicClosure ℚ)] (fieldBar q M')) :=
  Subgroup.closure {τ | ∃ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' ∧ τ = levelAutBar q M' ζ γ}

set_option synthInstance.maxHeartbeats 1600000 in
theorem levelAutBar_mem_levelAuts (ζ : Idx q) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M') :
    levelAutBar q M' ζ γ ∈ LevelAuts q M' :=
  Subgroup.subset_closure ⟨ζ, γ, hγ, rfl⟩

end Spec
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c.Plumbing.Idx P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c.Plumbing"

@[reducible] private def _root_.AlgebraicCurve.ComponentChart.toRegularProlongation
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
    (C : ComponentChart A F Fbar) : RegularProlongation A F Fbar where
  integers := C.integers
  residue := C.residue
  algebraMap_mem_iff := C.algebraMap_mem_iff
  residue_surjective := C.residue_surjective
  ker_residue := C.ker_residue
  residue_algebraMap := C.residue_algebraMap
  exists_smul_mem := C.exists_smul_mem

p2m_alias "P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.AlgebraicCurve.ComponentChart.toRegularProlongation" "AlgebraicCurve.ComponentChart.toRegularProlongation"
end ModularCurve.FullLevel.W1c
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c.Plumbing.Idx P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c.Plumbing"
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c.Plumbing.Idx P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c.Plumbing"
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c.Plumbing.Idx P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c.Plumbing"

end
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c.Plumbing.Idx P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c.Plumbing"

end Inlined_w1_W1c_spec
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c.Plumbing.Idx P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c.Plumbing"

section Inlined_w1_pen_H3_pen

set_option autoImplicit false

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel IsLocalRing CongruenceSubgroup"
open scoped MatrixGroups
open ModularCurve.FullLevel.W1c.Plumbing (InTube)

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "xHFunctionFieldC xHFunctionField intFormRatiosC qExpFunctionFieldC intFormRatiosC_subset modularFunctionFieldBar qExpand jq jq_mem jqN_mem modularFunctionField_le_full coeffMap coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange jq_mem_full instDecidableEqResidueFieldSemistable instAlgebraResidueFieldModularFunctionFieldCSemistable jqModC modularFunctionFieldC ssPlaces jGeomGen jNGeomGen transcendental_jqModC ssJSet isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField jqModC_mem_intFormRatiosC ssPlaces_nonempty transcendental_coeffEmb_jq"
namespace FullLevel
p2m_export "ModularCurve.FullLevel" "lineInfty SemistableCovering levelH fieldBar Idx IsLevelAutBar levelAutBar redQ exists_igusaValuationSubrings_of_eq_three SemistableCovering.LevelPinClauses"
namespace W1c
namespace Pen
p2m_open "ModularCurve.FullLevel ModularCurve"

theorem evalAt_sub_of_mem {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) (hv : v.IsRational)
    {x y : F} (hx : x ∈ v.toValuationSubring) (hy : y ∈ v.toValuationSubring) :
    v.evalAt (x - y) = v.evalAt x - v.evalAt y := by
  have hxy : x - y ∈ v.toValuationSubring := sub_mem hx hy
  apply Place.algebraMap_residueField_injective v
  rw [v.algebraMap_evalAt hv hxy, map_sub, v.algebraMap_evalAt hv hx, v.algebraMap_evalAt hv hy, ← map_sub]
  congr 1

open scoped Classical in
set_option synthInstance.maxHeartbeats 1600000 in
theorem drinfeldDiscs_inTube_proof
    (q : ℕ) [Fact q.Prime] (hq3 : q = 3) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (ζ : Idx q)
    (OIg : CuspidalType.ProjLine q → ValuationSubring (fieldBar q M'))
    (OSS : ↥W → ValuationSubring (fieldBar q M'))

    (hIg_inf : ∀ f : fieldBar q M', f ∈ OIg (lineInfty q) ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (hIg : ∀ ℓ, ∃ γ : SL(2, ℤ), γ ∈ Gamma0 M' ∧ redQ q γ • lineInfty q = ℓ ∧
      OIg ℓ = (OIg (lineInfty q)).comap (levelAutBar q M' ζ γ).toAlgHom.toRingHom)
    (hIg_inj : Function.Injective OIg)
    (hIg_perm : ∀ (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
      ∃ σ : Equiv.Perm (CuspidalType.ProjLine q),
        ∀ ℓ, (OIg ℓ).comap (levelAutBar q M' ζ' γ).toAlgHom.toRingHom = OIg (σ ℓ))

    (hSS_A : ∀ s (x : AlgebraicClosure ℚ), algebraMap (AlgebraicClosure ℚ) (fieldBar q M') x ∈ OSS s ↔ x ∈ A)
    (hSS_over : ∀ (s : ↥W) (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
      (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
      (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
          (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
        (IntermediateField.inclusion hle f : fieldBar q M') ∈ OSS s ∧
        ∀ a : A, residue A a =
            (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) →
          ∃ h : (IntermediateField.inclusion hle f : fieldBar q M')
              - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ OSS s,
            (⟨_, h⟩ : OSS s) ∈ maximalIdeal (OSS s))
    (hSS_fix : ∀ (s : ↥W) (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
      (OSS s).comap (levelAutBar q M' ζ' γ).toAlgHom.toRingHom = OSS s)

    (hSS_tr : ∀ s : ↥W, ∃ t : fieldBar q M', t ∈ OSS s ∧ ∀ a : A,
      ∃ h : t - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ OSS s, IsUnit (⟨_, h⟩ : OSS s))
    (s : ↥W) {FSS : Type} [Field FSS] [Algebra (ResidueField A) FSS]
    (Cb : ComponentChart A (fieldBar q M') FSS) (hCb : Cb.integers = OSS s)
    (xt : CuspidalType.ProjLine q → Place (ResidueField A) FSS)
    (disc : Place (ResidueField A) FSS → Set (Place (AlgebraicClosure ℚ) (fieldBar q M'))) (coord : Place (ResidueField A) FSS → (fieldBar q M'))
    (hfam : haveI := Fintype.ofFinite (CuspidalType.ProjLine q);
      Cb.toRegularProlongation.DiscFamily (Finset.univ.image xt) disc coord)

    (hcusp : ∀ Q : Place (ResidueField A) FSS, Q ∉ Set.range xt → ∀ P ∈ disc Q,
        0 ≤ P.ord (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
            ↥(modularFunctionFieldBar M')) : fieldBar q M'))

    (hrestr : ∀ (w : Place (AlgebraicClosure ℚ) (fieldBar q M')) (f : ↥(modularFunctionFieldBar M')),
      (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
      (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
            ↥(modularFunctionFieldBar M')) : fieldBar q M') ∈ w.toValuationSubring →
      (IntermediateField.inclusion hle f : fieldBar q M') ∈ w.toValuationSubring) :
    ∀ Q, Q ∉ Set.range xt → ∀ P ∈ disc Q, InTube q M' A hle R₀ s P := by
  intro Q hQ P hP
  letI hft : Fintype (CuspidalType.ProjLine q) := Fintype.ofFinite _
  have hQ' : Q ∉ (Finset.univ.image xt) := by
    intro h
    obtain ⟨ℓ, -, rfl⟩ := Finset.mem_image.mp h
    exact hQ ⟨ℓ, rfl⟩
  have hRD : Cb.toRegularProlongation.IsResidueDisc Q (disc Q) (coord Q) := hfam.1 Q hQ'
  have hPr : P.IsRational := (hRD.1.1 P hP).1
  unfold ModularCurve.FullLevel.W1c.Plumbing.InTube
  intro f hf hreg hs a ha
  obtain ⟨hfO, hmax⟩ := hSS_over s f hf hreg hs
  obtain ⟨hFO, hFmax⟩ := hmax a ha
  have hFR : (IntermediateField.inclusion hle f : fieldBar q M')
      - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ Cb.toRegularProlongation.integers := by
    show _ ∈ Cb.integers
    rw [hCb]; exact hFO
  have hres0 : Cb.toRegularProlongation.residue ⟨_, hFR⟩ = 0 := by
    have hm : (⟨_, hFR⟩ : Cb.toRegularProlongation.integers) ∈ maximalIdeal ↥Cb.toRegularProlongation.integers :=
      mem_maximalIdeal_of_valuationSubring_eq (O₂ := Cb.integers) hCb.symm hFO hFR hFmax
    rwa [← Cb.toRegularProlongation.ker_residue, RingHom.mem_ker] at hm

  have hjmem : ∀ w ∈ disc Q, (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
            ↥(modularFunctionFieldBar M')) : fieldBar q M') ∈ w.toValuationSubring := by
    intro w hw
    by_cases h0 : (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
            ↥(modularFunctionFieldBar M')) : fieldBar q M') = 0
    · rw [h0]; exact zero_mem _
    · exact w.mem_toValuationSubring_of_ord_nonneg_alt h0 (hcusp Q hQ w hw)
  have hfmem : ∀ w ∈ disc Q, (IntermediateField.inclusion hle f : fieldBar q M') ∈ w.toValuationSubring :=
    fun w hw => hrestr w f hreg (hjmem w hw)
  have hamem : ∀ w : Place (AlgebraicClosure ℚ) (fieldBar q M'),
      algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ w.toValuationSubring :=
    fun w => w.algebraMap_mem' _
  have hreg' : ∀ w ∈ disc Q, (IntermediateField.inclusion hle f : fieldBar q M')
      - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ w.toValuationSubring :=
    fun w hw => sub_mem (hfmem w hw) (hamem w)
  obtain ⟨hm, hA', e⟩ := hRD.2.1 P hP hPr _ hFR hreg'
  have hzero : (⟨Cb.toRegularProlongation.residue ⟨_, hFR⟩, hm⟩ : (Q.toValuationSubring)) = 0 := Subtype.ext hres0
  rw [hzero, map_zero, map_eq_zero_iff _ (algebraMap (ResidueField A) Q.ResidueField).injective,
    IsLocalRing.residue_eq_zero_iff] at e

  have hev : P.evalAt ((IntermediateField.inclusion hle f : fieldBar q M')
      - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ))
      = P.evalAt (IntermediateField.inclusion hle f : fieldBar q M') - (a : AlgebraicClosure ℚ) := by
    rw [evalAt_sub_of_mem P hPr (hfmem P hP) (hamem P), Place.evalAt_algebraMap_eq]
  refine ⟨hev ▸ hA', ?_⟩
  have hsub : (⟨P.evalAt (IntermediateField.inclusion hle f : fieldBar q M') - (a : AlgebraicClosure ℚ), hev ▸ hA'⟩ : A)
      = ⟨_, hA'⟩ := Subtype.ext hev.symm
  rw [hsub]; exact e

open scoped Classical in
set_option synthInstance.maxHeartbeats 1600000 in

theorem tube_exhaustion_proof
    (q : ℕ) [Fact q.Prime] (hq3 : q = 3) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (ζ : Idx q)
    (OIg : CuspidalType.ProjLine q → ValuationSubring (fieldBar q M'))
    (OSS : ↥W → ValuationSubring (fieldBar q M'))

    (hIg_inf : ∀ f : fieldBar q M', f ∈ OIg (lineInfty q) ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (hIg : ∀ ℓ, ∃ γ : SL(2, ℤ), γ ∈ Gamma0 M' ∧ redQ q γ • lineInfty q = ℓ ∧
      OIg ℓ = (OIg (lineInfty q)).comap (levelAutBar q M' ζ γ).toAlgHom.toRingHom)
    (hIg_inj : Function.Injective OIg)
    (hIg_perm : ∀ (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
      ∃ σ : Equiv.Perm (CuspidalType.ProjLine q),
        ∀ ℓ, (OIg ℓ).comap (levelAutBar q M' ζ' γ).toAlgHom.toRingHom = OIg (σ ℓ))

    (hSS_A : ∀ s (x : AlgebraicClosure ℚ), algebraMap (AlgebraicClosure ℚ) (fieldBar q M') x ∈ OSS s ↔ x ∈ A)
    (hSS_over : ∀ (s : ↥W) (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
      (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
      (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
          (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
        (IntermediateField.inclusion hle f : fieldBar q M') ∈ OSS s ∧
        ∀ a : A, residue A a =
            (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) →
          ∃ h : (IntermediateField.inclusion hle f : fieldBar q M')
              - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ OSS s,
            (⟨_, h⟩ : OSS s) ∈ maximalIdeal (OSS s))
    (hSS_fix : ∀ (s : ↥W) (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
      (OSS s).comap (levelAutBar q M' ζ' γ).toAlgHom.toRingHom = OSS s)

    (hSS_tr : ∀ s : ↥W, ∃ t : fieldBar q M', t ∈ OSS s ∧ ∀ a : A,
      ∃ h : t - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ OSS s, IsUnit (⟨_, h⟩ : OSS s))
    (s : ↥W) {FSS : Type} [Field FSS] [Algebra (ResidueField A) FSS]
    (Cb : ComponentChart A (fieldBar q M') FSS) (hCb : Cb.integers = OSS s)
    (An' : CuspidalType.ProjLine q → Annulus A (fieldBar q M')) (xt : CuspidalType.ProjLine q → Place (ResidueField A) FSS)
    (hxt_att : ∀ ℓ, ∃ hz : (An' ℓ).param ∈ Cb.toRegularProlongation.integers, (xt ℓ).ord (Cb.toRegularProlongation.residue ⟨(An' ℓ).param, hz⟩) = 1 ∧
          ∀ (f : fieldBar q M') (hf : f ∈ Cb.toRegularProlongation.integers), Cb.toRegularProlongation.residue ⟨f, hf⟩ ≠ 0 →
            (∀ P ∈ (An' ℓ).dom, P.ord f = 0) →
              ∀ P ∈ (An' ℓ).dom,
                ∃ h : P.evalAt f * (P.evalAt (An' ℓ).param) ^ (-((xt ℓ).ord (Cb.toRegularProlongation.residue ⟨f, hf⟩))) ∈ A,
                  IsUnit (⟨_, h⟩ : A))
    (hAn_tube : ∀ ℓ, ∀ P ∈ (An' ℓ).dom, InTube q M' A hle R₀ s P)
    (disc : Place (ResidueField A) FSS → Set (Place (AlgebraicClosure ℚ) (fieldBar q M'))) (coord : Place (ResidueField A) FSS → (fieldBar q M'))
    (hfam : haveI := Fintype.ofFinite (CuspidalType.ProjLine q);
      Cb.toRegularProlongation.DiscFamily (Finset.univ.image xt) disc coord)

    (hcover : ∀ P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M'), P.IsRational →
        (∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
          (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
            0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
              ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
          (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
              (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
            ∀ a : A, residue A a =
                (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) →
              ∃ h : P.evalAt (IntermediateField.inclusion hle f : fieldBar q M') - (a : AlgebraicClosure ℚ) ∈ A,
                (⟨_, h⟩ : A) ∈ maximalIdeal A) →
        (∃ Q : Place (ResidueField A) FSS, Q ∉ Set.range xt ∧ P ∈ disc Q) ∨ ∃ ℓ : CuspidalType.ProjLine q, P ∈ (An' ℓ).dom) :
    ∀ P : Place (AlgebraicClosure ℚ) (fieldBar q M'), InTube q M' A hle R₀ s P →
      (∃ Q, Q ∉ Set.range xt ∧ P ∈ disc Q) ∨ ∃ ℓ, P ∈ (An' ℓ).dom := by
  intro P hP
  exact hcover P (ModularCurve.FullLevel.W1c.Plumbing.fieldBar_isRational q M' P) hP

end ModularCurve.FullLevel.W1c.Pen
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c.Plumbing.Idx P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c.Plumbing"
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c.Plumbing.Idx P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c.Plumbing"
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c.Plumbing.Idx P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c.Plumbing"
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c.Plumbing.Idx P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c.Plumbing"

end
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c.Plumbing.Idx P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c.Plumbing"

end Inlined_w1_pen_H3_pen
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c.Plumbing.Idx P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c.Plumbing"

section Inlined_MAIN

set_option autoImplicit false

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel IsLocalRing CongruenceSubgroup"
open scoped MatrixGroups IntermediateField
open ModularCurve.FullLevel.W1c.Plumbing (InTube)

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "xHFunctionFieldC xHFunctionField intFormRatiosC qExpFunctionFieldC intFormRatiosC_subset modularFunctionFieldBar qExpand jq jq_mem jqN_mem modularFunctionField_le_full coeffMap coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange jq_mem_full instDecidableEqResidueFieldSemistable instAlgebraResidueFieldModularFunctionFieldCSemistable jqModC modularFunctionFieldC ssPlaces jGeomGen jNGeomGen transcendental_jqModC ssJSet isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField jqModC_mem_intFormRatiosC ssPlaces_nonempty transcendental_coeffEmb_jq"
namespace FullLevel
p2m_export "ModularCurve.FullLevel" "lineInfty SemistableCovering levelH fieldBar Idx IsLevelAutBar levelAutBar redQ exists_igusaValuationSubrings_of_eq_three SemistableCovering.LevelPinClauses"
namespace W1c
namespace Pen
p2m_open "ModularCurve.FullLevel ModularCurve"

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

theorem isAlgebraic_fieldBar_of_le (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M') :
    letI : Algebra ↥(modularFunctionFieldBar M') ↥(fieldBar q M') := (IntermediateField.inclusion hle).toRingHom.toAlgebra
    Algebra.IsAlgebraic ↥(modularFunctionFieldBar M') ↥(fieldBar q M') := by
  letI alg : Algebra ↥(modularFunctionFieldBar M') ↥(fieldBar q M') := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  have halg : ∀ x : ↥(modularFunctionFieldBar M'), algebraMap ↥(modularFunctionFieldBar M') ↥(fieldBar q M') x =
      IntermediateField.inclusion hle x := fun _ => rfl
  haveI : IsScalarTower (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M') ↥(fieldBar q M') :=
    IsScalarTower.of_algebraMap_eq (fun x => ((IntermediateField.inclusion hle).commutes x).symm)
  haveI : NeZero (q ^ 2 * M') := ⟨mul_ne_zero (pow_ne_zero _ (Fact.out : q.Prime).ne_zero) (NeZero.ne M')⟩
  obtain ⟨hcurve, hess⟩ := ModularCurve.isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField
    (AlgebraicClosure ℚ) (q ^ 2 * M') (levelH q M')
  haveI : IsCurveOver (AlgebraicClosure ℚ) ↥(fieldBar q M') := hcurve
  haveI : Algebra.EssFiniteType (AlgebraicClosure ℚ) ↥(fieldBar q M') := hess

  set jB : ↥(modularFunctionFieldBar M') := ⟨coeffEmb (AlgebraicClosure ℚ) jq,
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full M')⟩ with hjB
  have hjt : Transcendental (AlgebraicClosure ℚ) jB := ModularCurve.transcendental_coeffEmb_jq (AlgebraicClosure ℚ) M'
  have hinj : Function.Injective (algebraMap ↥(modularFunctionFieldBar M') ↥(fieldBar q M')) :=
    (algebraMap ↥(modularFunctionFieldBar M') ↥(fieldBar q M')).injective
  have hj't : Transcendental (AlgebraicClosure ℚ) (IntermediateField.inclusion hle jB) := by
    have h := (transcendental_algebraMap_iff hinj).mpr hjt
    rwa [halg] at h
  haveI : Algebra.Transcendental (AlgebraicClosure ℚ) ↥(fieldBar q M') := ⟨⟨_, hj't⟩⟩
  obtain ⟨t, ht, hfin, -⟩ := AlgebraicCurve.exists_transcendental_isSeparable_of_finrank_kaehlerDifferential_eq_one
    (K := AlgebraicClosure ℚ) (F := ↥(fieldBar q M')) hcurve.kaehler_free_rank_one.2
  haveI := hfin
  haveI : Algebra.IsAlgebraic ↥(AlgebraicClosure ℚ)⟮t⟯ ↥(fieldBar q M') := Algebra.IsAlgebraic.of_finite _ _
  have hA1 : Algebra.IsAlgebraic ↥(AlgebraicClosure ℚ)⟮IntermediateField.inclusion hle jB⟯ ↥(fieldBar q M') :=
    AlgebraicCurve.isAlgebraic_adjoin_of_transcendental t hj't

  haveI hIST : IsScalarTower ↥((AlgebraicClosure ℚ)⟮jB⟯) ↥(modularFunctionFieldBar M') ↥(fieldBar q M') :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hmem : ∀ y : ↥((AlgebraicClosure ℚ)⟮jB⟯), IntermediateField.inclusion hle (y : ↥(modularFunctionFieldBar M')) ∈
      (AlgebraicClosure ℚ)⟮IntermediateField.inclusion hle jB⟯ := by
    intro y
    obtain ⟨r, s, hy⟩ := (IntermediateField.mem_adjoin_simple_iff (AlgebraicClosure ℚ) _).mp y.2
    rw [hy, map_div₀, ← Polynomial.aeval_algHom_apply, ← Polynomial.aeval_algHom_apply]
    exact (IntermediateField.mem_adjoin_simple_iff (AlgebraicClosure ℚ) _).mpr ⟨r, s, rfl⟩
  let f : ↥((AlgebraicClosure ℚ)⟮jB⟯) →+* ↥((AlgebraicClosure ℚ)⟮IntermediateField.inclusion hle jB⟯) :=
    ((IntermediateField.inclusion hle).toRingHom.comp (algebraMap ↥((AlgebraicClosure ℚ)⟮jB⟯) ↥(modularFunctionFieldBar M'))).codRestrict
      ((AlgebraicClosure ℚ)⟮IntermediateField.inclusion hle jB⟯) hmem
  have hfsurj : Function.Surjective f := by
    rintro ⟨z, hz⟩
    obtain ⟨r, s, hz'⟩ := (IntermediateField.mem_adjoin_simple_iff (AlgebraicClosure ℚ) _).mp hz
    refine ⟨⟨Polynomial.aeval jB r / Polynomial.aeval jB s,
      (IntermediateField.mem_adjoin_simple_iff (AlgebraicClosure ℚ) _).mpr ⟨r, s, rfl⟩⟩, Subtype.ext ?_⟩
    show IntermediateField.inclusion hle (Polynomial.aeval jB r / Polynomial.aeval jB s) = z
    rw [hz', map_div₀, ← Polynomial.aeval_algHom_apply, ← Polynomial.aeval_algHom_apply]
  refine ⟨fun x => ?_⟩
  have hx := hA1.isAlgebraic x
  have hxR : IsAlgebraic ↥((AlgebraicClosure ℚ)⟮jB⟯) x :=
    IsAlgebraic.of_ringHom_of_comp_eq (A := ↥(fieldBar q M')) f (RingHom.id ↥(fieldBar q M')) (a := x) hx
      hfsurj (fun a b h => h) (by ext y; rfl)
  exact IsAlgebraic.extendScalars (S := ↥(modularFunctionFieldBar M')) (A := ↥(fieldBar q M'))
    (algebraMap ↥((AlgebraicClosure ℚ)⟮jB⟯) ↥(modularFunctionFieldBar M')).injective hxR

theorem ord_nonneg_of_mem' {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {f : F}
    (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have hcoe : f = ((u : v.toValuationSubring) : F) * ((π : F) ^ (n : ℤ)) := by
    have h := congrArg (Subtype.val) hu
    push_cast at h
    rw [zpow_natCast]
    exact h
  rw [hcoe, v.ord_unit_smul_zpow u hπ (n : ℤ)]
  exact Int.natCast_nonneg n

set_option synthInstance.maxHeartbeats 1600000 in

theorem hrestr_proof (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hle : modularFunctionFieldBar M' ≤ fieldBar q M') :
    ∀ (w : Place (AlgebraicClosure ℚ) (fieldBar q M')) (f : ↥(modularFunctionFieldBar M')),
      (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
      (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
            ↥(modularFunctionFieldBar M')) : fieldBar q M') ∈ w.toValuationSubring →
      (IntermediateField.inclusion hle f : fieldBar q M') ∈ w.toValuationSubring := by
  intro w f hreg hj
  letI alg : Algebra ↥(modularFunctionFieldBar M') ↥(fieldBar q M') := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  haveI : IsScalarTower (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M') ↥(fieldBar q M') :=
    IsScalarTower.of_algebraMap_eq (fun x => ((IntermediateField.inclusion hle).commutes x).symm)
  haveI : Algebra.IsIntegral ↥(modularFunctionFieldBar M') ↥(fieldBar q M') :=
    (isAlgebraic_fieldBar_of_le q M' hle).isIntegral
  by_cases hf0 : f = 0
  · rw [hf0, map_zero]; exact zero_mem _
  have hjP : 0 ≤ (w.restrict ↥(modularFunctionFieldBar M')).ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) :=
    ord_nonneg_of_mem' _ ((Place.mem_restrict_iff (w := w)).mpr hj)
  have hfP : f ∈ (w.restrict ↥(modularFunctionFieldBar M')).toValuationSubring :=
    Place.mem_toValuationSubring_of_ord_nonneg_alt _ hf0 (hreg _ hjP)
  exact (Place.mem_restrict_iff (w := w)).mp hfP

open scoped Classical in
set_option synthInstance.maxHeartbeats 1600000 in

theorem drinfeldDiscs_inTube_proof'
    (q : ℕ) [Fact q.Prime] (hq3 : q = 3) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (ζ : Idx q)
    (OIg : CuspidalType.ProjLine q → ValuationSubring (fieldBar q M'))
    (OSS : ↥W → ValuationSubring (fieldBar q M'))

    (hIg_inf : ∀ f : fieldBar q M', f ∈ OIg (lineInfty q) ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (hIg : ∀ ℓ, ∃ γ : SL(2, ℤ), γ ∈ Gamma0 M' ∧ redQ q γ • lineInfty q = ℓ ∧
      OIg ℓ = (OIg (lineInfty q)).comap (levelAutBar q M' ζ γ).toAlgHom.toRingHom)
    (hIg_inj : Function.Injective OIg)
    (hIg_perm : ∀ (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
      ∃ σ : Equiv.Perm (CuspidalType.ProjLine q),
        ∀ ℓ, (OIg ℓ).comap (levelAutBar q M' ζ' γ).toAlgHom.toRingHom = OIg (σ ℓ))

    (hSS_A : ∀ s (x : AlgebraicClosure ℚ), algebraMap (AlgebraicClosure ℚ) (fieldBar q M') x ∈ OSS s ↔ x ∈ A)
    (hSS_over : ∀ (s : ↥W) (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
      (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
      (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
          (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
        (IntermediateField.inclusion hle f : fieldBar q M') ∈ OSS s ∧
        ∀ a : A, residue A a =
            (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) →
          ∃ h : (IntermediateField.inclusion hle f : fieldBar q M')
              - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ OSS s,
            (⟨_, h⟩ : OSS s) ∈ maximalIdeal (OSS s))
    (hSS_fix : ∀ (s : ↥W) (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
      (OSS s).comap (levelAutBar q M' ζ' γ).toAlgHom.toRingHom = OSS s)

    (hSS_tr : ∀ s : ↥W, ∃ t : fieldBar q M', t ∈ OSS s ∧ ∀ a : A,
      ∃ h : t - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ OSS s, IsUnit (⟨_, h⟩ : OSS s))
    (s : ↥W) {FSS : Type} [Field FSS] [Algebra (ResidueField A) FSS]
    (Cb : ComponentChart A (fieldBar q M') FSS) (hCb : Cb.integers = OSS s)
    (xt : CuspidalType.ProjLine q → Place (ResidueField A) FSS)
    (disc : Place (ResidueField A) FSS → Set (Place (AlgebraicClosure ℚ) (fieldBar q M'))) (coord : Place (ResidueField A) FSS → (fieldBar q M'))
    (hfam : haveI := Fintype.ofFinite (CuspidalType.ProjLine q);
      Cb.toRegularProlongation.DiscFamily (Finset.univ.image xt) disc coord)

    (hcusp : ∀ Q : Place (ResidueField A) FSS, Q ∉ Set.range xt → ∀ P ∈ disc Q,
        0 ≤ P.ord (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
            ↥(modularFunctionFieldBar M')) : fieldBar q M')) :
    ∀ Q, Q ∉ Set.range xt → ∀ P ∈ disc Q, InTube q M' A hle R₀ s P :=
  drinfeldDiscs_inTube_proof q hq3 M' hqM' A hA W hW hle R₀ hR₀ ζ OIg OSS hIg_inf hIg hIg_inj hIg_perm hSS_A hSS_over hSS_fix
    hSS_tr s Cb hCb xt disc coord hfam hcusp (hrestr_proof q M' hle)

end ModularCurve.FullLevel.W1c.Pen
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c.Plumbing.Idx P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c.Plumbing"
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c.Plumbing.Idx P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c.Plumbing"
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c.Plumbing.Idx P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c.Plumbing"
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c.Plumbing.Idx P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c.Plumbing"

end
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c.Plumbing.Idx P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c.Plumbing"

end Inlined_MAIN
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c.Plumbing.Idx P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel.W1c.Plumbing"

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd.ModularCurve.FullLevel IsLocalRing CongruenceSubgroup"
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

open scoped Classical in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (q : ℕ) [Fact q.Prime] (hq3 : q = 3) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓ12 : ℓ % 12 = 11) (hℓM' : ℓ ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (ζ : Idx q)
    (OIg : CuspidalType.ProjLine q → ValuationSubring (fieldBar q M'))
    (OSS : ↥W → ValuationSubring (fieldBar q M'))

    (hIg_inf : ∀ f : fieldBar q M', f ∈ OIg (lineInfty q) ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (hIg : ∀ ℓ, ∃ γ : SL(2, ℤ), γ ∈ Gamma0 M' ∧ redQ q γ • lineInfty q = ℓ ∧
      OIg ℓ = (OIg (lineInfty q)).comap (levelAutBar q M' ζ γ).toAlgHom.toRingHom)
    (hIg_inj : Function.Injective OIg)
    (hIg_perm : ∀ (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
      ∃ σ : Equiv.Perm (CuspidalType.ProjLine q),
        ∀ ℓ, (OIg ℓ).comap (levelAutBar q M' ζ' γ).toAlgHom.toRingHom = OIg (σ ℓ))

    (hSS_A : ∀ s (x : AlgebraicClosure ℚ), algebraMap (AlgebraicClosure ℚ) (fieldBar q M') x ∈ OSS s ↔ x ∈ A)
    (hSS_over : ∀ (s : ↥W) (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
      (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
      (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
          (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
        (IntermediateField.inclusion hle f : fieldBar q M') ∈ OSS s ∧
        ∀ a : A, residue A a =
            (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) →
          ∃ h : (IntermediateField.inclusion hle f : fieldBar q M')
              - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ OSS s,
            (⟨_, h⟩ : OSS s) ∈ maximalIdeal (OSS s))
    (hSS_fix : ∀ (s : ↥W) (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
      (OSS s).comap (levelAutBar q M' ζ' γ).toAlgHom.toRingHom = OSS s)

    (hSS_tr : ∀ s : ↥W, ∃ t : fieldBar q M', t ∈ OSS s ∧ ∀ a : A,
      ∃ h : t - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ OSS s, IsUnit (⟨_, h⟩ : OSS s))
    (s : ↥W) {FSS : Type} [Field FSS] [Algebra (ResidueField A) FSS]
    (Cb : ComponentChart A (fieldBar q M') FSS) (hCb : Cb.integers = OSS s)
    (xt : CuspidalType.ProjLine q → Place (ResidueField A) FSS)
    (disc : Place (ResidueField A) FSS → Set (Place (AlgebraicClosure ℚ) (fieldBar q M'))) (coord : Place (ResidueField A) FSS → (fieldBar q M'))
    (hfam : haveI := Fintype.ofFinite (CuspidalType.ProjLine q);
      (⟨Cb.integers, Cb.residue, Cb.algebraMap_mem_iff, Cb.residue_surjective, Cb.ker_residue, Cb.residue_algebraMap,
        Cb.exists_smul_mem⟩ : RegularProlongation A ↥(fieldBar q M') FSS).DiscFamily (Finset.univ.image xt) disc coord)

    (hcusp : ∀ Q : Place (ResidueField A) FSS, Q ∉ Set.range xt → ∀ P ∈ disc Q,
        0 ≤ P.ord (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
            ↥(modularFunctionFieldBar M')) : fieldBar q M')) :
    ∀ Q, Q ∉ Set.range xt → ∀ P ∈ disc Q, (∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
        (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
          0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
            ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
        (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
            (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
          ∀ a : A, residue A a =
              (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) →
            ∃ h : P.evalAt (IntermediateField.inclusion hle f : fieldBar q M') - (a : AlgebraicClosure ℚ) ∈ A,
              (⟨_, h⟩ : A) ∈ maximalIdeal A)  :=
  ModularCurve.FullLevel.W1c.Pen.drinfeldDiscs_inTube_proof' q hq3 M' hqM' A hA W hW hle R₀ hR₀ ζ OIg OSS hIg_inf hIg hIg_inj hIg_perm hSS_A hSS_over hSS_fix hSS_tr s Cb hCb xt disc coord hfam hcusp

end S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd
end P2MW
export P2MW.S_ModularCurve_FullLevel_inTube_of_mem_drinfeldDisc_of_cuspFree_of_eq_three_of_dvd (solution)
