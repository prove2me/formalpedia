-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_igusaValuationSubrings_of_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/80973fe1-f0a9-5249-b24d-356bf885962d

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ModularCurve_exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC
import Theorems.Thm_ModularCurve_FullLevel_levelAutBar_mul
import Theorems.Thm_ModularCurve_FullLevel_levelAutBar_pow_inv_eq_levelAutBar_of_diag_conj
import Theorems.Thm_ModularCurve_FullLevel_comap_levelAutBar_eq_of_redQ_smul_lineInfty_eq_of_eq_two
import Theorems.Thm_ModularCurve_FullLevel_redQ_smul_lineInfty_eq_of_comap_levelAutBar_eq_of_eq_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_igusaValuationSubrings_of_eq_two
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid CuspForm.instModuleZModIntTwoCuspForms CuspForm.instAddCommGroupIntTwoCuspForms ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent ModularCurve.Gamma0Pair.isElliptic CuspForm.instModuleTwoCuspForms CuspForm.instIsScalarTowerTwoCuspForms CuspForm.instAddCommGroupTwoCuspForms CuspForm.instIsScalarTowerSelfTwoCuspForms CuspForm.instModuleQuotientTwoCuspForms CuspForm.GammaH_finiteIndex"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qExpandAlgHomC_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_heckeBetaModLHOf ModularCurve.pairDiagModL_apply ModularCurve.coe_heckeAlphaModLH ModularCurve.pairUpModL_apply ModularCurve.coeff_qDecimate ModularCurve.coe_qExpFrobeniusModL ModularCurve.coe_qExpFrobeniusDegZeroPullbackModL ModularCurve.coe_qExpFrobeniusDegZeroPushforwardModL ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.qEulerFun_coeff"
p2m_attr_erase "simp" "ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.gluedPolarDifferentials.coe_fst_apply AlgebraicCurve.gluedPolarDifferentials.coe_snd_apply ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero CuspForm.heckeGenH_T CuspForm.coe_twoCuspEnd_apply CuspForm.twoCuspEndMod_reduce CuspForm.heckeGenH_U CuspForm.heckeGenH_dia ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply"
p2m_attr_erase "simp" "ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply"

set_option autoImplicit false
set_option linter.unusedSectionVars false

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_FullLevel_exists_igusaValuationSubrings_of_eq_two.ModularCurve ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_exists_igusaValuationSubrings_of_eq_two.ModularCurve.FullLevel IsLocalRing CongruenceSubgroup"
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "translation_mem_GammaH xHFunctionFieldC qExpFunctionFieldC coeffMap laurentBaseChange instDecidableEqResidueFieldSemistable instAlgebraResidueFieldModularFunctionFieldCSemistable exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC FullLevel.levelAutBar_mul FullLevel.levelAutBar_pow_inv_eq_levelAutBar_of_diag_conj FullLevel.comap_levelAutBar_eq_of_redQ_smul_lineInfty_eq_of_eq_two FullLevel.redQ_smul_lineInfty_eq_of_comap_levelAutBar_eq_of_eq_two"
namespace FullLevel
p2m_export "ModularCurve.FullLevel" "lineInfty levelH fieldBar Idx Idx.ext Idx.val_pow levelAutBar redQ levelAutBar_mul levelAutBar_pow_inv_eq_levelAutBar_of_diag_conj comap_levelAutBar_eq_of_redQ_smul_lineInfty_eq_of_eq_two redQ_smul_lineInfty_eq_of_comap_levelAutBar_eq_of_eq_two"
namespace W1a
namespace Lift
p2m_open "ModularCurve.FullLevel ModularCurve"

variable (q : ℕ) [Fact q.Prime] (M' : ℕ)

private theorem natCast_M'_ne_zero (hqM' : ¬ q ∣ M') : ((M' : ℕ) : ZMod q) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  exact hqM'

noncomputable def crt (r : ZMod q) : ℤ := ((r * ((M' : ℕ) : ZMod q)⁻¹).val : ℤ) * (M' : ℤ)

private theorem crt_cast (hqM' : ¬ q ∣ M') (r : ZMod q) : ((crt q M' r : ℤ) : ZMod q) = r := by
  unfold crt
  push_cast
  rw [ZMod.natCast_zmod_val, inv_mul_cancel_right₀ (natCast_M'_ne_zero q M' hqM')]

private theorem crt_dvd (r : ZMod q) : (M' : ℤ) ∣ crt q M' r := ⟨_, by unfold crt; ring⟩

private theorem crt_castM' (r : ZMod q) : ((crt q M' r : ℤ) : ZMod M') = 0 := by
  obtain ⟨k, hk⟩ := crt_dvd q M' r
  rw [hk]; push_cast; simp

private def Tz (a : ℤ) : SL(2, ℤ) := ⟨!![1, a; 0, 1], by simp [Matrix.det_fin_two_of]⟩

private def Lz (b : ℤ) : SL(2, ℤ) := ⟨!![1, 0; b, 1], by simp [Matrix.det_fin_two_of]⟩

private theorem Tz_mem_gamma0 (a : ℤ) : Tz a ∈ Gamma0 M' := by
  rw [Gamma0_mem]; simp [Tz]

private theorem Lz_mem_gamma0 {b : ℤ} (hb : ((b : ℤ) : ZMod M') = 0) : Lz b ∈ Gamma0 M' := by
  rw [Gamma0_mem]; simpa [Lz] using hb

variable {q}

private def Tq (a : ZMod q) : SL(2, ZMod q) := ⟨!![1, a; 0, 1], by simp [Matrix.det_fin_two_of]⟩

private def Lq (b : ZMod q) : SL(2, ZMod q) := ⟨!![1, 0; b, 1], by simp [Matrix.det_fin_two_of]⟩

local notation "red" => Matrix.SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod q))

private theorem red_Tz (a : ℤ) : red (Tz a) = Tq (a : ZMod q) := by
  ext i j
  rw [Matrix.SpecialLinearGroup.map_apply_coe]
  fin_cases i <;> fin_cases j <;> simp [Tz, Tq]

private theorem red_Lz (b : ℤ) : red (Lz b) = Lq (b : ZMod q) := by
  ext i j
  rw [Matrix.SpecialLinearGroup.map_apply_coe]
  fin_cases i <;> fin_cases j <;> simp [Lz, Lq]

private theorem coe_Tq_Lq_Tq (x c y : ZMod q) :
    ((Tq x * Lq c * Tq y : SL(2, ZMod q)) : Matrix (Fin 2) (Fin 2) (ZMod q)) =
      !![1 + x * c, (1 + x * c) * y + x; c, c * y + 1] := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Tq, Lq, Matrix.mul_apply, Fin.sum_univ_two]

private theorem eq_Tq_Lq_Tq (g : SL(2, ZMod q)) (hc : (g : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 0 ≠ 0) :
    g = Tq (((g : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 0 - 1) / (g : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 0) *
      Lq ((g : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 0) *
      Tq (((g : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 1 - 1) / (g : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 0) := by
  have hdet : (g : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 0 * (g : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 1 -
      (g : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 1 * (g : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 0 = 1 := by
    have h := g.det_coe
    rw [Matrix.det_fin_two] at h
    exact h
  have hx : 1 + ((g : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 0 - 1) / (g : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 0 *
      (g : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 0 = (g : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 0 := by
    rw [div_mul_cancel₀ _ hc]; ring
  have hy : (g : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 0 *
      (((g : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 1 - 1) / (g : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 0) + 1 =
      (g : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 1 := by
    rw [mul_div_cancel₀ _ hc]; ring
  have hb : (g : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 0 *
      (((g : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 1 - 1) / (g : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 0) +
      ((g : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 0 - 1) / (g : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 0 =
      (g : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 1 := by
    field_simp
    linear_combination hdet
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [coe_Tq_Lq_Tq, hx]
  fin_cases i <;> fin_cases j
  · simp
  · simpa using hb.symm
  · simp
  · simpa using hy.symm

variable (q)

private theorem exists_mem_gamma0_map_eq (hqM' : ¬ q ∣ M') (g : SL(2, ZMod q)) :
    ∃ γ : SL(2, ℤ), γ ∈ Gamma0 M' ∧ red γ = g := by

  have key : ∀ g : SL(2, ZMod q), (g : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 0 ≠ 0 →
      ∃ γ : SL(2, ℤ), γ ∈ Gamma0 M' ∧ red γ = g := by
    intro g hc
    refine ⟨Tz (crt q M' (((g : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 0 - 1) / (g : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 0)) *
        Lz (crt q M' ((g : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 0)) *
        Tz (crt q M' (((g : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 1 - 1) / (g : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 0)), ?_, ?_⟩
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Tz_mem_gamma0 M' _)
        (Lz_mem_gamma0 M' (crt_castM' q M' _))) (Tz_mem_gamma0 M' _)
    · rw [map_mul, map_mul, red_Tz, red_Lz, red_Tz, crt_cast q M' hqM', crt_cast q M' hqM',
        crt_cast q M' hqM']
      exact (eq_Tq_Lq_Tq g hc).symm
  by_cases hc : (g : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 0 ≠ 0
  · exact key g hc
  · push Not at hc

    have hdet : (g : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 0 * (g : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 1 -
        (g : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 1 * (g : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 0 = 1 := by
      have h := g.det_coe
      rw [Matrix.det_fin_two] at h
      exact h
    have ha : (g : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 0 ≠ 0 := by
      intro h0; rw [h0, hc] at hdet; simp at hdet
    have hc' : ((Lq (1 : ZMod q) * g : SL(2, ZMod q)) : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 0 ≠ 0 := by
      rw [Matrix.SpecialLinearGroup.coe_mul]
      simp [Lq, Matrix.mul_apply, Fin.sum_univ_two, hc, ha]
    obtain ⟨γ', hγ', hred'⟩ := key _ hc'
    refine ⟨(Lz (crt q M' 1))⁻¹ * γ', Subgroup.mul_mem _ (Subgroup.inv_mem _ (Lz_mem_gamma0 M' (crt_castM' q M' _))) hγ', ?_⟩
    rw [map_mul, map_inv, hred', red_Lz, crt_cast q M' hqM', inv_mul_cancel_left]

private def swapElem (t : ZMod q) : SL(2, ZMod q) := ⟨!![t, -t ^ 2 - 1; 1, -t], by
  rw [Matrix.det_fin_two_of]; ring⟩

private theorem swapElem_mulVec_inf (t : ZMod q) :
    (swapElem q t : Matrix (Fin 2) (Fin 2) (ZMod q)).mulVec ![1, 0] = ![t, 1] := by
  ext i; fin_cases i <;> simp [swapElem, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

private theorem swapElem_mulVec_pt (t : ZMod q) :
    (swapElem q t : Matrix (Fin 2) (Fin 2) (ZMod q)).mulVec ![t, 1] = ![-1, 0] := by
  ext i; fin_cases i <;> simp [swapElem, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

end ModularCurve.FullLevel.W1a.Lift

namespace ModularCurve
p2m_export "ModularCurve" "translation_mem_GammaH xHFunctionFieldC qExpFunctionFieldC coeffMap laurentBaseChange instDecidableEqResidueFieldSemistable instAlgebraResidueFieldModularFunctionFieldCSemistable exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC FullLevel.levelAutBar_mul FullLevel.levelAutBar_pow_inv_eq_levelAutBar_of_diag_conj FullLevel.comap_levelAutBar_eq_of_redQ_smul_lineInfty_eq_of_eq_two FullLevel.redQ_smul_lineInfty_eq_of_comap_levelAutBar_eq_of_eq_two"
namespace FullLevel
p2m_export "ModularCurve.FullLevel" "lineInfty levelH fieldBar Idx Idx.ext Idx.val_pow levelAutBar redQ levelAutBar_mul levelAutBar_pow_inv_eq_levelAutBar_of_diag_conj comap_levelAutBar_eq_of_redQ_smul_lineInfty_eq_of_eq_two redQ_smul_lineInfty_eq_of_comap_levelAutBar_eq_of_eq_two"
namespace W1a
p2m_open "ModularCurve.FullLevel ModularCurve"

variable (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']

private abbrev gammaQ : Subgroup SL(2, ℤ) := CohCarrier.GammaH (q ^ 2 * M') (levelH q M')

private theorem fieldBar_eq :
    fieldBar q M' = laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (gammaQ q M')) := rfl

private theorem xHFunctionFieldC_eq (K : Type*) [Field K] :
    xHFunctionFieldC K (q ^ 2 * M') (levelH q M') = qExpFunctionFieldC K (gammaQ q M') := rfl

section Rings

set_option synthInstance.maxHeartbeats 1600000

variable (A : ValuationSubring (AlgebraicClosure ℚ))

private theorem exists_inftyProlongation :
    ∃ R : RegularProlongation A (fieldBar q M') (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')),
      (∀ f : fieldBar q M', f ∈ R.integers ↔
        ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
          (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x) ∧
      ∀ (y : LaurentSeries A) (hy : coeffMap A.subtype y ∈ fieldBar q M'),
        ∃ hO : (⟨coeffMap A.subtype y, hy⟩ : fieldBar q M') ∈ R.integers,
          ((R.residue ⟨_, hO⟩ : xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')) :
              LaurentSeries (ResidueField A)) = coeffMap (IsLocalRing.residue A) y :=
  ModularCurve.exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC
    (AlgebraicClosure ℚ) A (gammaQ q M') (ModularCurve.translation_mem_GammaH _ _)

private def RInfty : RegularProlongation A (fieldBar q M') (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')) :=
  (exists_inftyProlongation q M' A).choose

private def OInfty : ValuationSubring (fieldBar q M') := (RInfty q M' A).integers

private theorem mem_OInfty_iff (f : fieldBar q M') :
    f ∈ OInfty q M' A ↔ ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
      (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x :=
  (exists_inftyProlongation q M' A).choose_spec.1 f

end Rings

section LevelAut

variable {q M'}

local notation "τ" => levelAutBar q M'

private theorem levelAutBar_one (hqM' : ¬ q ∣ M') (ζ : Idx q) : τ ζ 1 = AlgEquiv.refl := by
  have h := ModularCurve.FullLevel.levelAutBar_mul q M' hqM' ζ 1 1 (Subgroup.one_mem _) (Subgroup.one_mem _)
  rw [mul_one] at h
  refine AlgEquiv.ext fun x => ?_
  have hx : τ ζ 1 x = τ ζ 1 (τ ζ 1 x) := by
    conv_lhs => rw [h]
    rfl
  exact ((τ ζ 1).injective hx).symm

variable (O : ValuationSubring (fieldBar q M'))

private abbrev cm (e : fieldBar q M' ≃ₐ[AlgebraicClosure ℚ] fieldBar q M') : ValuationSubring (fieldBar q M') :=
  O.comap e.toAlgHom.toRingHom

private theorem cm_refl : cm O AlgEquiv.refl = O := by
  ext x; simp [ValuationSubring.mem_comap]

private theorem cm_trans (e₁ e₂ : fieldBar q M' ≃ₐ[AlgebraicClosure ℚ] fieldBar q M') :
    cm O (e₁.trans e₂) = cm (cm O e₂) e₁ := by
  ext x; simp [ValuationSubring.mem_comap]

private theorem cm_injective (e : fieldBar q M' ≃ₐ[AlgebraicClosure ℚ] fieldBar q M')
    {O₁ O₂ : ValuationSubring (fieldBar q M')} (h : cm O₁ e = cm O₂ e) : O₁ = O₂ := by
  ext x
  have := SetLike.ext_iff.mp h (e.symm x)
  simpa [ValuationSubring.mem_comap] using this

end LevelAut

section Holes

variable (A : ValuationSubring (AlgebraicClosure ℚ))

private theorem OInfty_comap_eq_of_smul_lineInfty_eq (hq2 : q = 2) (hqM' : ¬ q ∣ M') (hA : A.LiesOverPrime q)
    (ζ : Idx q) (δ : SL(2, ℤ)) (hδ : δ ∈ Gamma0 M') (hfix : redQ q δ • lineInfty q = lineInfty q) :
    (OInfty q M' A).comap (levelAutBar q M' ζ δ).toAlgHom.toRingHom = OInfty q M' A :=
  ModularCurve.FullLevel.comap_levelAutBar_eq_of_redQ_smul_lineInfty_eq_of_eq_two q hq2 M' hqM' A hA ζ (OInfty q M' A)
    (mem_OInfty_iff q M' A) δ hδ hfix

private theorem smul_lineInfty_eq_of_OInfty_comap_eq (hq2 : q = 2) (hqM' : ¬ q ∣ M') (hA : A.LiesOverPrime q)
    (ζ : Idx q) (δ : SL(2, ℤ)) (hδ : δ ∈ Gamma0 M')
    (h : (OInfty q M' A).comap (levelAutBar q M' ζ δ).toAlgHom.toRingHom = OInfty q M' A) :
    redQ q δ • lineInfty q = lineInfty q :=
  ModularCurve.FullLevel.redQ_smul_lineInfty_eq_of_comap_levelAutBar_eq_of_eq_two q hq2 M' hqM' A hA ζ (OInfty q M' A)
    (mem_OInfty_iff q M' A) δ hδ h

end Holes

section RingOf

variable {q M'} (A : ValuationSubring (AlgebraicClosure ℚ))
variable (hq2 : q = 2) (hqM' : ¬ q ∣ M') (hA : A.LiesOverPrime q) (ζ : Idx q)

variable (M') in

private def ringOf (β : SL(2, ℤ)) : ValuationSubring (fieldBar q M') :=
  (OInfty q M' A).comap (levelAutBar q M' ζ β).toAlgHom.toRingHom

include hq2 hqM' hA in
private theorem ringOf_eq_of_smul_eq {β₁ β₂ : SL(2, ℤ)} (h₁ : β₁ ∈ Gamma0 M') (h₂ : β₂ ∈ Gamma0 M')
    (h : redQ q β₁ • lineInfty q = redQ q β₂ • lineInfty q) :
    ringOf M' A ζ β₁ = ringOf M' A ζ β₂ := by
  have hδ : β₂⁻¹ * β₁ ∈ Gamma0 M' := Subgroup.mul_mem _ (Subgroup.inv_mem _ h₂) h₁
  have hfix : redQ q (β₂⁻¹ * β₁) • lineInfty q = lineInfty q := by
    rw [map_mul, map_inv, mul_smul, h, inv_smul_smul]
  have hK := OInfty_comap_eq_of_smul_lineInfty_eq q M' A hq2 hqM' hA ζ _ hδ hfix
  have hβ : β₁ = β₂ * (β₂⁻¹ * β₁) := by group
  unfold ringOf
  conv_lhs => rw [hβ, ModularCurve.FullLevel.levelAutBar_mul q M' hqM' ζ _ _ h₂ hδ]
  change cm (OInfty q M' A) ((levelAutBar q M' ζ β₂).trans (levelAutBar q M' ζ (β₂⁻¹ * β₁))) = _
  rw [cm_trans]
  change ((OInfty q M' A).comap (levelAutBar q M' ζ (β₂⁻¹ * β₁)).toAlgHom.toRingHom).comap _ = _
  rw [hK]

include hq2 hqM' hA in
private theorem smul_eq_of_ringOf_eq {β₁ β₂ : SL(2, ℤ)} (h₁ : β₁ ∈ Gamma0 M') (h₂ : β₂ ∈ Gamma0 M')
    (h : ringOf M' A ζ β₁ = ringOf M' A ζ β₂) :
    redQ q β₁ • lineInfty q = redQ q β₂ • lineInfty q := by
  have hδ : β₂⁻¹ * β₁ ∈ Gamma0 M' := Subgroup.mul_mem _ (Subgroup.inv_mem _ h₂) h₁
  have hβ : β₁ = β₂ * (β₂⁻¹ * β₁) := by group
  have h' : cm ((OInfty q M' A).comap (levelAutBar q M' ζ (β₂⁻¹ * β₁)).toAlgHom.toRingHom)
      (levelAutBar q M' ζ β₂) = cm (OInfty q M' A) (levelAutBar q M' ζ β₂) := by
    change _ = ringOf M' A ζ β₂
    rw [← h]
    unfold ringOf
    conv_rhs => rw [hβ, ModularCurve.FullLevel.levelAutBar_mul q M' hqM' ζ _ _ h₂ hδ]
    exact (cm_trans (OInfty q M' A) _ _).symm
  have hK := smul_lineInfty_eq_of_OInfty_comap_eq q M' A hq2 hqM' hA ζ _ hδ (cm_injective _ h')
  rw [map_mul, map_inv, mul_smul] at hK
  calc redQ q β₁ • lineInfty q
      = redQ q β₂ • ((redQ q β₂)⁻¹ • redQ q β₁ • lineInfty q) := by rw [smul_inv_smul]
    _ = redQ q β₂ • lineInfty q := by rw [hK]

end RingOf

section Transport

variable {q M'} (hqM' : ¬ q ∣ M')

private theorem redQ_coe (γ : SL(2, ℤ)) :
    ((redQ q γ : CuspidalType.GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) =
      ((Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)) γ : SL(2, ZMod q)) :
        Matrix (Fin 2) (Fin 2) (ZMod q)) := rfl

private theorem mulVec_ne_zero (g : CuspidalType.GL2 q) {v : Fin 2 → ZMod q} (hv : v ≠ 0) :
    (g : Matrix (Fin 2) (Fin 2) (ZMod q)).mulVec v ≠ 0 := by
  intro h0
  apply hv
  have h1 := congrArg ((g⁻¹ : CuspidalType.GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)).mulVec h0
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_zero, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.one_mulVec] at h1
  exact h1

private theorem redQ_smul_mk (γ : SL(2, ℤ)) (v : Fin 2 → ZMod q) (hv : v ≠ 0) :
    redQ q γ • Projectivization.mk (ZMod q) v hv =
      Projectivization.mk (ZMod q)
        (((Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)) γ : SL(2, ZMod q)) :
          Matrix (Fin 2) (Fin 2) (ZMod q)).mulVec v)
        (mulVec_ne_zero (redQ q γ) hv) := by
  rw [Projectivization.smul_mk]
  rfl

private theorem mk_neg_one_zero :
    Projectivization.mk (ZMod q) (![-1, 0] : Fin 2 → ZMod q) (by simp) = lineInfty q := by
  rw [lineInfty, Projectivization.mk_eq_mk_iff']
  exact ⟨-1, by ext i; fin_cases i <;> simp⟩

include hqM' in

private theorem exists_symmetric_transporter (ℓ : CuspidalType.ProjLine q) :
    ∃ γ : SL(2, ℤ), γ ∈ Gamma0 M' ∧ redQ q γ • lineInfty q = ℓ ∧ redQ q γ • ℓ = lineInfty q := by
  induction ℓ using Projectivization.ind with
  | h v hv =>
    by_cases h1 : v 1 = 0
    ·
      have h0 : v 0 ≠ 0 := by
        intro h0; apply hv; ext i; fin_cases i <;> simp [h0, h1]
      have hℓ : Projectivization.mk (ZMod q) v hv = lineInfty q := by
        rw [lineInfty, Projectivization.mk_eq_mk_iff']
        exact ⟨v 0, by ext i; fin_cases i <;> simp [h1]⟩
      refine ⟨1, Subgroup.one_mem _, ?_, ?_⟩ <;> rw [hℓ, map_one, one_smul]
    · set t : ZMod q := v 0 / v 1 with ht
      have hℓ : Projectivization.mk (ZMod q) v hv =
          Projectivization.mk (ZMod q) ![t, 1] (by simp) := by
        rw [Projectivization.mk_eq_mk_iff']
        refine ⟨v 1, ?_⟩
        ext i; fin_cases i
        · simp [ht, mul_div_cancel₀ _ h1]
        · simp
      obtain ⟨γ, hγ, hred⟩ := Lift.exists_mem_gamma0_map_eq q M' hqM' (Lift.swapElem q t)
      refine ⟨γ, hγ, ?_, ?_⟩
      · rw [hℓ, lineInfty, redQ_smul_mk]
        simp_rw [hred, Lift.swapElem_mulVec_inf]
      · rw [hℓ, redQ_smul_mk]
        simp_rw [hred, Lift.swapElem_mulVec_pt]
        exact mk_neg_one_zero

open Classical in

private def transporter (ℓ : CuspidalType.ProjLine q) : SL(2, ℤ) :=
  if ℓ = lineInfty q then 1 else (exists_symmetric_transporter hqM' ℓ).choose

private theorem transporter_lineInfty : transporter hqM' (lineInfty q) = 1 := by
  simp [transporter]

private theorem transporter_mem (ℓ : CuspidalType.ProjLine q) : transporter hqM' ℓ ∈ Gamma0 M' := by
  unfold transporter
  split_ifs with h
  · exact Subgroup.one_mem _
  · exact (exists_symmetric_transporter hqM' ℓ).choose_spec.1

private theorem transporter_smul_lineInfty (ℓ : CuspidalType.ProjLine q) :
    redQ q (transporter hqM' ℓ) • lineInfty q = ℓ := by
  unfold transporter
  split_ifs with h
  · subst h; rw [map_one, one_smul]
  · exact (exists_symmetric_transporter hqM' ℓ).choose_spec.2.1

private theorem transporter_smul (ℓ : CuspidalType.ProjLine q) :
    redQ q (transporter hqM' ℓ) • ℓ = lineInfty q := by
  unfold transporter
  split_ifs with h
  · subst h; rw [map_one, one_smul]
  · exact (exists_symmetric_transporter hqM' ℓ).choose_spec.2.2

variable (A : ValuationSubring (AlgebraicClosure ℚ)) (ζ : Idx q)

private def OIg (ℓ : CuspidalType.ProjLine q) : ValuationSubring (fieldBar q M') :=
  ringOf M' A ζ (transporter hqM' ℓ)

private theorem OIg_lineInfty : OIg hqM' A ζ (lineInfty q) = OInfty q M' A := by
  unfold OIg ringOf
  rw [transporter_lineInfty, levelAutBar_one hqM']
  exact cm_refl _

end Transport

section Reciprocity

variable {q M'} (hqM' : ¬ q ∣ M')

private theorem Idx.exists_eq_pow_inv (ζ ζ' : Idx q) : ∃ d : (ZMod q)ˣ, ζ' = ζ.pow d⁻¹ := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  obtain ⟨i, hi, h⟩ := ζ.isPrimitiveRoot.eq_pow_of_pow_eq_one ζ'.isPrimitiveRoot.pow_eq_one
  have hcop : i.Coprime q := by
    have := (ζ.isPrimitiveRoot.pow_iff_coprime (Fact.out : q.Prime).pos i).mp (h ▸ ζ'.isPrimitiveRoot)
    exact this
  refine ⟨(ZMod.unitOfCoprime i hcop)⁻¹, Idx.ext ?_⟩
  rw [inv_inv, Idx.val_pow, ZMod.coe_unitOfCoprime, ZMod.val_cast_of_lt hi, h]

private def diagConj (d : (ZMod q)ˣ) (g : SL(2, ZMod q)) : SL(2, ZMod q) :=
  ⟨!![(1 : ZMod q), 0; 0, (d : ZMod q)] * (g : Matrix (Fin 2) (Fin 2) (ZMod q)) * !![(1 : ZMod q), 0; 0, (d : ZMod q)⁻¹], by
    rw [Matrix.det_mul, Matrix.det_mul, g.det_coe, Matrix.det_fin_two_of, Matrix.det_fin_two_of]
    simp only [mul_zero, sub_zero, one_mul, mul_one]
    exact mul_inv_cancel₀ d.ne_zero⟩

private theorem diagConj_mul_diag (d : (ZMod q)ˣ) (g : SL(2, ZMod q)) :
    (diagConj d g : Matrix (Fin 2) (Fin 2) (ZMod q)) * !![(1 : ZMod q), 0; 0, (d : ZMod q)] =
      !![(1 : ZMod q), 0; 0, (d : ZMod q)] * (g : Matrix (Fin 2) (Fin 2) (ZMod q)) := by
  change !![(1 : ZMod q), 0; 0, (d : ZMod q)] * (g : Matrix (Fin 2) (Fin 2) (ZMod q)) *
    !![(1 : ZMod q), 0; 0, (d : ZMod q)⁻¹] * !![(1 : ZMod q), 0; 0, (d : ZMod q)] = _
  have hD : !![(1 : ZMod q), 0; 0, (d : ZMod q)⁻¹] * !![(1 : ZMod q), 0; 0, (d : ZMod q)] = 1 := by
    rw [Matrix.mul_fin_two, Matrix.one_fin_two]
    simp only [mul_one, mul_zero, add_zero, zero_add, one_mul, zero_mul, inv_mul_cancel₀ d.ne_zero]
  rw [Matrix.mul_assoc, hD, Matrix.mul_one]

include hqM' in

private theorem exists_levelAutBar_eq (ζ ζ' : Idx q) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') :
    ∃ (γ' : SL(2, ℤ)) (d : (ZMod q)ˣ), γ' ∈ Gamma0 M' ∧
      Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)) γ' =
        diagConj d (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)) γ) ∧
      levelAutBar q M' ζ' γ = levelAutBar q M' ζ γ' := by
  obtain ⟨d, rfl⟩ := Idx.exists_eq_pow_inv ζ ζ'
  obtain ⟨γ', hγ', hred⟩ := Lift.exists_mem_gamma0_map_eq q M' hqM'
    (diagConj d (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)) γ))
  refine ⟨γ', d, hγ', hred, ?_⟩
  apply ModularCurve.FullLevel.levelAutBar_pow_inv_eq_levelAutBar_of_diag_conj q M' hqM' ζ d γ γ' hγ hγ'
  have h1 : (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod q) =
      ((Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)) γ : SL(2, ZMod q)) :
        Matrix (Fin 2) (Fin 2) (ZMod q)) := by
    rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Int.coe_castRingHom]
  have h2 : (γ' : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod q) =
      ((Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)) γ' : SL(2, ZMod q)) :
        Matrix (Fin 2) (Fin 2) (ZMod q)) := by
    rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Int.coe_castRingHom]
  rw [h1, h2, hred, diagConj_mul_diag]

end Reciprocity

section Clauses

variable {q M'} (A : ValuationSubring (AlgebraicClosure ℚ))
variable (hq2 : q = 2) (hqM' : ¬ q ∣ M') (hA : A.LiesOverPrime q) (ζ : Idx q)

private theorem clause_a2 (ℓ : CuspidalType.ProjLine q) :
    ∃ γ : SL(2, ℤ), γ ∈ Gamma0 M' ∧ redQ q γ • lineInfty q = ℓ ∧
      OIg hqM' A ζ ℓ = (OIg hqM' A ζ (lineInfty q)).comap (levelAutBar q M' ζ γ).toAlgHom.toRingHom :=
  ⟨transporter hqM' ℓ, transporter_mem hqM' ℓ, transporter_smul_lineInfty hqM' ℓ, by rw [OIg_lineInfty]; rfl⟩

include hq2 hA in
private theorem clause_a3 : Function.Injective (OIg hqM' A ζ) := by
  intro ℓ₁ ℓ₂ h
  have := smul_eq_of_ringOf_eq A hq2 hqM' hA ζ (transporter_mem hqM' ℓ₁) (transporter_mem hqM' ℓ₂) h
  rwa [transporter_smul_lineInfty, transporter_smul_lineInfty] at this

include hq2 hA in
private theorem clause_a4 (ζ' : Idx q) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') :
    ∃ σ : Equiv.Perm (CuspidalType.ProjLine q),
      ∀ ℓ, (OIg hqM' A ζ ℓ).comap (levelAutBar q M' ζ' γ).toAlgHom.toRingHom = OIg hqM' A ζ (σ ℓ) := by
  obtain ⟨γ', d, hγ', -, hτ⟩ := exists_levelAutBar_eq hqM' ζ ζ' γ hγ
  refine ⟨MulAction.toPerm (redQ q γ'), fun ℓ => ?_⟩
  rw [hτ, MulAction.toPerm_apply]
  unfold OIg

  have hmul := ModularCurve.FullLevel.levelAutBar_mul q M' hqM' ζ γ' (transporter hqM' ℓ) hγ'
    (transporter_mem hqM' ℓ)
  have step : (ringOf M' A ζ (transporter hqM' ℓ)).comap (levelAutBar q M' ζ γ').toAlgHom.toRingHom =
      ringOf M' A ζ (γ' * transporter hqM' ℓ) := by
    unfold ringOf
    rw [hmul]
    exact (cm_trans (OInfty q M' A) _ _).symm
  rw [step]
  apply ringOf_eq_of_smul_eq A hq2 hqM' hA ζ (Subgroup.mul_mem _ hγ' (transporter_mem hqM' ℓ))
    (transporter_mem hqM' _)
  rw [map_mul, mul_smul, transporter_smul_lineInfty, transporter_smul_lineInfty]

end Clauses

end ModularCurve.FullLevel.W1a

open ModularCurve.FullLevel.W1a in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    (q : ℕ) [Fact q.Prime] (hq2 : q = 2) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) (ζ : Idx q) :
    ∃ (OIg : CuspidalType.ProjLine q → ValuationSubring (fieldBar q M'))
      (R : RegularProlongation A (fieldBar q M')
        (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))),

      R.integers = OIg (lineInfty q) ∧
      (∀ f : fieldBar q M', f ∈ OIg (lineInfty q) ↔
        ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
          (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x) ∧
      (∀ (y : LaurentSeries A) (hy : coeffMap A.subtype y ∈ fieldBar q M'),
        ∃ hO : (⟨coeffMap A.subtype y, hy⟩ : fieldBar q M') ∈ R.integers,
          ((R.residue ⟨_, hO⟩ : xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')) :
              LaurentSeries (ResidueField A)) = coeffMap (IsLocalRing.residue A) y) ∧

      (∀ ℓ, ∃ γ : SL(2, ℤ), γ ∈ Gamma0 M' ∧ redQ q γ • lineInfty q = ℓ ∧
        OIg ℓ = (OIg (lineInfty q)).comap (levelAutBar q M' ζ γ).toAlgHom.toRingHom) ∧

      Function.Injective OIg ∧

      (∀ (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
        ∃ σ : Equiv.Perm (CuspidalType.ProjLine q),
          ∀ ℓ, (OIg ℓ).comap (levelAutBar q M' ζ' γ).toAlgHom.toRingHom = OIg (σ ℓ)) := by
  refine ⟨OIg hqM' A ζ, RInfty q M' A, ?_, ?_, ?_, clause_a2 A hqM' ζ, clause_a3 A hq2 hqM' hA ζ,
    clause_a4 A hq2 hqM' hA ζ⟩
  · rw [OIg_lineInfty]; rfl
  · intro f; rw [OIg_lineInfty]; exact mem_OInfty_iff q M' A f
  · exact (exists_inftyProlongation q M' A).choose_spec.2

end

end S_ModularCurve_FullLevel_exists_igusaValuationSubrings_of_eq_two
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_igusaValuationSubrings_of_eq_two (solution)
