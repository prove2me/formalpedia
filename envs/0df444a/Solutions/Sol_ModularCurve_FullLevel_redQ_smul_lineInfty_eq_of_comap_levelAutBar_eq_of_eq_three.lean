-- Prove2me | solution 1 for ModularCurve.FullLevel.redQ_smul_lineInfty_eq_of_comap_levelAutBar_eq_of_eq_three
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/e1cec696-0fc8-53d6-82ed-8f2a87364f66

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ModularCurve_FullLevel_levelAutBar_mul
import Theorems.Thm_ModularCurve_FullLevel_comap_levelAutBar_eq_of_redQ_smul_lineInfty_eq_of_eq_three
import Theorems.Thm_ModularCurve_FullLevel_comap_levelAutBar_ne_of_dvd_of_eq_three
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_redQ_smul_lineInfty_eq_of_comap_levelAutBar_eq_of_eq_three
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid CuspForm.instModuleZModIntTwoCuspForms CuspForm.instAddCommGroupIntTwoCuspForms ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent ModularCurve.Gamma0Pair.isElliptic CuspForm.instModuleTwoCuspForms CuspForm.instIsScalarTowerTwoCuspForms CuspForm.instAddCommGroupTwoCuspForms CuspForm.instIsScalarTowerSelfTwoCuspForms CuspForm.instModuleQuotientTwoCuspForms CuspForm.GammaH_finiteIndex"
p2m_attr_erase "simp" "AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qExpandAlgHomC_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_heckeBetaModLHOf ModularCurve.pairDiagModL_apply ModularCurve.coe_heckeAlphaModLH ModularCurve.pairUpModL_apply ModularCurve.coeff_qDecimate ModularCurve.coe_qExpFrobeniusModL ModularCurve.coe_qExpFrobeniusDegZeroPullbackModL ModularCurve.coe_qExpFrobeniusDegZeroPushforwardModL"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.gluedPolarDifferentials.coe_fst_apply AlgebraicCurve.gluedPolarDifferentials.coe_snd_apply ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero CuspForm.heckeGenH_T CuspForm.coe_twoCuspEnd_apply CuspForm.twoCuspEndMod_reduce CuspForm.heckeGenH_U CuspForm.heckeGenH_dia ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat ModularCurve.baseAut_x1ArithFrobC_apply"
p2m_attr_erase "simp" "ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply"

set_option autoImplicit false
set_option linter.unusedSectionVars false

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_FullLevel_redQ_smul_lineInfty_eq_of_comap_levelAutBar_eq_of_eq_three.ModularCurve ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_redQ_smul_lineInfty_eq_of_comap_levelAutBar_eq_of_eq_three.ModularCurve.FullLevel IsLocalRing CongruenceSubgroup"
open scoped MatrixGroups

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "coeffMap FullLevel.levelAutBar_mul"
namespace FullLevel
p2m_export "ModularCurve.FullLevel" "lineInfty fieldBar Idx levelAutBar redQ levelAutBar_mul comap_levelAutBar_eq_of_redQ_smul_lineInfty_eq_of_eq_three comap_levelAutBar_ne_of_dvd_of_eq_three"
namespace W1a
namespace Lift
p2m_open "ModularCurve.FullLevel ModularCurve"

variable (q : ℕ) [Fact q.Prime] (M' : ℕ)

private theorem natCast_M'_ne_zero (hqM' : ¬ q ∣ M') : ((M' : ℕ) : ZMod q) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  exact hqM'

private noncomputable def crt (r : ZMod q) : ℤ := ((r * ((M' : ℕ) : ZMod q)⁻¹).val : ℤ) * (M' : ℤ)

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
p2m_export "ModularCurve" "coeffMap FullLevel.levelAutBar_mul"
namespace FullLevel
p2m_export "ModularCurve.FullLevel" "lineInfty fieldBar Idx levelAutBar redQ levelAutBar_mul comap_levelAutBar_eq_of_redQ_smul_lineInfty_eq_of_eq_three comap_levelAutBar_ne_of_dvd_of_eq_three"
namespace W1a
p2m_open "ModularCurve.FullLevel ModularCurve"

variable (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']

section ProjLine

variable {q M'}

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

end ProjLine

end ModularCurve.FullLevel.W1a

open _root_.ModularCurve.FullLevel _root_.P2MW.S_ModularCurve_FullLevel_redQ_smul_lineInfty_eq_of_comap_levelAutBar_eq_of_eq_three.ModularCurve.FullLevel in

theorem solution
    (q : ℕ) [Fact q.Prime] (hq3 : q = 3) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) (ζ : Idx q)
    (O : ValuationSubring (fieldBar q M'))
    (hO : ∀ f : fieldBar q M', f ∈ O ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (δ : SL(2, ℤ)) (hδ : δ ∈ Gamma0 M')
    (h : O.comap (levelAutBar q M' ζ δ).toAlgHom.toRingHom = O) :
    redQ q δ • lineInfty q = lineInfty q  := by
  classical
  by_contra hne

  set g : SL(2, ZMod q) := Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)) δ with hg
  have hcol : redQ q δ • lineInfty q =
      Projectivization.mk (ZMod q) ((g : Matrix (Fin 2) (Fin 2) (ZMod q)).mulVec ![1, 0])
        (W1a.mulVec_ne_zero (redQ q δ) (by simp)) := by
    rw [lineInfty, W1a.redQ_smul_mk]
  have hmv : (g : Matrix (Fin 2) (Fin 2) (ZMod q)).mulVec ![1, 0] =
      ![(g : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 0, (g : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 0] := by
    ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

  have hc : (g : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 0 ≠ 0 := by
    intro hc
    apply hne
    have ha0 : (g : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 0 ≠ 0 := by
      intro ha0
      have hdet := g.det_coe
      rw [Matrix.det_fin_two, ha0, hc] at hdet
      simp at hdet
    rw [hcol, lineInfty, Projectivization.mk_eq_mk_iff']
    refine ⟨(g : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 0, ?_⟩
    rw [hmv, hc]
    ext i; fin_cases i <;> simp

  obtain ⟨b, hb, hbred⟩ := W1a.Lift.exists_mem_gamma0_map_eq q M' hqM'
    (W1a.Lift.Tq (-((g : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 0) / (g : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 0))
  have hbfix : redQ q b • lineInfty q = lineInfty q := by
    rw [lineInfty, W1a.redQ_smul_mk]
    simp_rw [hbred]
    congr 1
    ext i; fin_cases i <;> simp [W1a.Lift.Tq, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hK1 := comap_levelAutBar_eq_of_redQ_smul_lineInfty_eq_of_eq_three q hq3 M' hqM' A hA ζ O hO b hb hbfix

  have hstab : O.comap (levelAutBar q M' ζ (b * δ)).toAlgHom.toRingHom = O := by
    rw [ModularCurve.FullLevel.levelAutBar_mul q M' hqM' ζ b δ hb hδ]
    have : O.comap ((levelAutBar q M' ζ b).trans (levelAutBar q M' ζ δ)).toAlgHom.toRingHom =
        (O.comap (levelAutBar q M' ζ δ).toAlgHom.toRingHom).comap (levelAutBar q M' ζ b).toAlgHom.toRingHom := by
      ext x; simp [ValuationSubring.mem_comap]
    rw [this, h, hK1]

  have ha : (q : ℤ) ∣ ((b * δ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have h1 : ((((b * δ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ) : ZMod q) =
        ((Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)) (b * δ) : SL(2, ZMod q)) :
          Matrix (Fin 2) (Fin 2) (ZMod q)) 0 0 := by
      rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply, eq_intCast]
    rw [h1, map_mul, hbred, ← hg, Matrix.SpecialLinearGroup.coe_mul]
    simp [W1a.Lift.Tq, Matrix.mul_apply, Fin.sum_univ_two]
    field_simp
    ring
  exact comap_levelAutBar_ne_of_dvd_of_eq_three q hq3 M' hqM' A hA ζ O hO (b * δ) (Subgroup.mul_mem _ hb hδ) ha hstab

end

end S_ModularCurve_FullLevel_redQ_smul_lineInfty_eq_of_comap_levelAutBar_eq_of_eq_three
end P2MW
export P2MW.S_ModularCurve_FullLevel_redQ_smul_lineInfty_eq_of_comap_levelAutBar_eq_of_eq_three (solution)
